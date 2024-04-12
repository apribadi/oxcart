use std::alloc::Layout;
use std::alloc;
use std::cell::Cell;
use std::fmt;
use std::hint::black_box;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::mem::align_of;
use std::mem::offset_of;
use std::mem::size_of;
use std::panic::RefUnwindSafe;
use std::ptr::NonNull;
use std::str;
use pop::ptr;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

pub struct Store(NonNull<Root>);

pub struct Arena<'a>(Cell<Span>, PhantomData<&'a ()>);

pub struct Slot<'a, T>(NonNull<T>, PhantomData<&'a ()>)
where
  T: ?Sized;

#[derive(Debug)]
pub struct AllocError;

unsafe impl Send for Store { }

unsafe impl Sync for Store { }

impl<'a> RefUnwindSafe for Arena<'a> { }

unsafe impl<'a, T> Send for Slot<'a, T> where T: ?Sized { }

unsafe impl<'a, T> Sync for Slot<'a, T> where T: ?Sized { }

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

// NB:
//
// `repr(C)` guarantees (among other things) that the first field is at offset
// zero.

#[derive(Clone, Copy)]
#[repr(C)]
struct Span {
  ptr: ptr,
  len: usize,
}

#[repr(C)]
struct Link {
  next: Span,
  root: ptr,
}

#[repr(C)]
struct Root {
  link: Link,
  is_growing: bool,
  total_allocated: usize,
}

const _: () = assert!(size_of::<Span>() % WORD == 0 && align_of::<Span>() == WORD);
const _: () = assert!(size_of::<Link>() % WORD == 0 && align_of::<Link>() == WORD);
const _: () = assert!(size_of::<Root>() % WORD == 0 && align_of::<Root>() == WORD);

enum Error {
  AllocSizeTooLarge,
  SystemAllocatorFailed(Layout),
  Unimplemented,
}

enum Panicked { }

trait Fail: Sized {
  fn fail<T>(_: Error) -> Result<T, Self>;
}

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

const DEFAULT_INITIAL_CHUNK_SIZE: usize = 1 << 14; // 16384
const MAX_CHUNK_SIZE: usize = isize::MAX as usize - WORD + 1;
const NULL: ptr = ptr::NULL;
const WORD: usize = size_of::<usize>();

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
fn unwrap<T>(x: Result<T, Panicked>) -> T {
  match x {
    Ok(x) => x,
    Err(e) => match e { }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Panicked
//
////////////////////////////////////////////////////////////////////////////////

impl Fail for Panicked {
  #[inline(never)]
  #[cold]
  fn fail<T>(e: Error) -> Result<T, Self> {
    match e {
      Error::AllocSizeTooLarge => panic!("oxcart: alloc size too large!"),
      Error::SystemAllocatorFailed(layout) => alloc::handle_alloc_error(layout),
      Error::Unimplemented => panic!("oxcart: unimplemented!"),
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// AllocError
//
////////////////////////////////////////////////////////////////////////////////

impl Fail for AllocError {
  #[inline(always)]
  fn fail<T>(_: Error) -> Result<T, Self> {
    Err(AllocError)
  }
}

impl fmt::Display for AllocError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str("oxcart: failed to allocate memory!")
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Span
//
////////////////////////////////////////////////////////////////////////////////

impl Span {
  #[inline(always)]
  fn new(ptr: ptr, len: usize) -> Self {
    Self { ptr, len, }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Store
//
////////////////////////////////////////////////////////////////////////////////

fn chunk<E>(n: usize) -> Result<NonNull<u8>, E>
where
  E: Fail
{
  assert!(n > 0);
  assert!(n <= MAX_CHUNK_SIZE);

  let layout = Layout::from_size_align(n, WORD).unwrap();
  let p = unsafe { alloc::alloc(layout) };
  let p = NonNull::new(p);
  let Some(p) = p else { return E::fail(Error::SystemAllocatorFailed(layout)); };
  Ok(p)
}

fn store<E>(n: usize) -> Result<Store, E>
where
  E: Fail
{
  let m = size_of::<Root>();
  let n = n.clamp(m, MAX_CHUNK_SIZE);
  let k = n - m & ! (WORD - 1);
  let n = k + m;
  let p = chunk(n)?;
  let p = ptr::from(p);
  let r = p + k;

  let x =
    Root {
      link: Link { next: Span { ptr: p, len: k }, root: r, },
      is_growing: false,
      total_allocated: n,
    };

  unsafe { r.write(x) };
  let r = unsafe { r.as_non_null() };
  Ok(Store(r))
}

impl Store {
  pub fn new() -> Self {
    unwrap(store(DEFAULT_INITIAL_CHUNK_SIZE))
  }

  pub fn try_new() -> Result<Self, AllocError> {
    store(DEFAULT_INITIAL_CHUNK_SIZE)
  }

  pub fn arena(&mut self) -> Arena<'_> {
    let r = ptr::from(self.0);
    let r = unsafe { r.as_mut_ref::<Root>() };
    r.is_growing = false;
    Arena(Cell::new(r.link.next), PhantomData)
  }
}

impl Drop for Store {
  fn drop(&mut self) {
    let _ = self;
    // TODO
  }
}

impl fmt::Debug for Store {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let r = ptr::from(self.0);
    let r = unsafe { r.as_ref::<Root>() };
    let total_allocated = r.total_allocated;
    f.debug_struct("Store")
      .field("total_allocated", &total_allocated)
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Arena
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast<E>(state: Span, layout: Layout) -> (Span, Result<NonNull<u8>, E>)
where
  E: Fail
{
  let p = state.ptr;
  let n = state.len;

  if p.addr() & WORD - 1 != 0 { unsafe { unreachable_unchecked() }; }

  let u = ! (WORD - 1) & layout.align() - 1 & - p;
  let v = u + (! (WORD - 1) & WORD - 1 + layout.size());

  if v > n  { return unsafe { alloc_slow(state, layout) }; }

  (Span::new(p + v, n - v), Ok(unsafe { (p + u).as_non_null() }))
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow<E>(state: Span, layout: Layout) -> (Span, Result<NonNull<u8>, E>)
where
  E: Fail
{
  let _ = black_box(state);
  let _ = black_box(layout);

  let r: ptr;

  'grow: {
    let t = state.ptr + state.len;
    let a = unsafe { t.read::<Link>() };
    r = a.root;
    let s = a.next;

    if t == r {
      break 'grow;
    }

    if unsafe { (r + offset_of!(Root, is_growing)).read::<bool>() } {
      break 'grow;
    }

    let p = s.ptr;
    let n = s.len;
    let a = ! (WORD - 1) & layout.align() - 1 & - p;
    let b = a + (! (WORD - 1) & WORD - 1 + layout.size());

    if b > n {
      break 'grow;
    }

    return (Span::new(p + b, n - b), Ok(unsafe { (p + a).as_non_null() }));
  };

  // compute the chunk size needed to guarantee we can fit the allocation.

  // let s = y.size();
  // let a = y.align();
  // let n = usize::max(a, WORD) - WORD + s;
  //
  // let n = usize::max(r.link.next.len, r.total_allocated / 4 + 1);
  // let n = n.next_power_of_two();
  // next power of two

  if black_box(true) {
    (Span::new(NULL, 0), E::fail(Error::Unimplemented))
  } else {
    (Span::new(NULL, 0), Ok(NonNull::dangling()))
  }
}

/*
#[inline(never)]
#[cold]
unsafe fn reserve(x: Span, n: usize) -> Span {
  let l = ptr::as_ref::<Link>(x.tail());
  let r = l.root;

  if ! ptr::is_null(r) && ! ptr::as_ref::<Root>(r).is_growing {
    return l.next;
  }

  let r =
    if ! ptr::is_null(r) {
      ptr::as_mut_ref::<Root>(r)
    } else {
      ptr::as_mut_ref::<Root>(l)
    };

  let c = alloc::alloc(Layout::from_size_align_unchecked(SLAB, WORD_SIZE));

  if ptr::is_null(c) {
    panic!("alloc::alloc failed!")
  }

  let _ = n;
  let n = SLAB;
  let c = Span { ptr: ptr::from_mut_ptr(c), len: n - size_of::<Link>() >> WORD_LOG2 };
  let l = c.tail();
  let b = r.link.next;
  ptr::write::<Link>(l, Link { next: b, root: ptr::from_ref(r) });
  r.link.next = c;
  b
}
*/

#[inline(always)]
fn alloc_layout<'a, E>(arena: &mut Arena<'a>, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
where
  E: Fail
{
  let a = arena.0.get_mut();
  let (s, x) = unsafe { alloc_fast(*a, layout) };
  *a = s;
  let x = x?;
  let x = ptr::from(x);
  let x = unsafe { x.as_slice_mut_ref(layout.size()) };
  Ok(x)
}

#[inline(always)]
fn alloc<'a, T, E>(arena: &mut Arena<'a>) -> Result<Slot<'a, T>, E>
where
  E: Fail
{
  let x = alloc_layout(arena, Layout::new::<T>())?;
  let x = ptr::from(x);
  let x = unsafe { x.as_non_null::<T>() };
  Ok(Slot(x, PhantomData))
}

#[inline(always)]
fn alloc_slice<'a, T, E>(arena: &mut Arena<'a>, len: usize) -> Result<Slot<'a, [T]>, E>
where
  E: Fail
{
  if size_of::<T>() != 0 && len > isize::MAX as usize / size_of::<T>() {
    return E::fail(Error::AllocSizeTooLarge);
  }

  let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
  let x = alloc_layout(arena, l)?;
  let x = ptr::from(x);
  let x = unsafe { x.as_slice_non_null(len) };
  Ok(Slot(x, PhantomData))
}

#[inline(always)]
fn copy_slice<'a, T, E>(arena: &mut Arena<'a>, src: &[T]) -> Result<&'a mut [T], E>
where
  T: Copy,
  E: Fail
{
  let x = alloc_layout(arena, Layout::for_value(src))?;
  let n = src.len();
  let x = ptr::from(x);
  let y = ptr::from(src);
  unsafe { ptr::copy_nonoverlapping::<T>(y, x, n) };
  let x = unsafe { x.as_slice_mut_ref::<T>(n) };
  Ok(x)
}

#[inline(always)]
fn copy_str<'a, E>(arena: &mut Arena<'a>, src: &str) -> Result<&'a mut str, E>
where
  E: Fail
{
  let x = copy_slice(arena, src.as_bytes())?;
  let x = unsafe { str::from_utf8_unchecked_mut(x) };
  Ok(x)
}

impl<'a> Arena<'a> {
  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
    unwrap(alloc_layout(self, layout))
  }

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError> {
    alloc_layout(self, layout)
  }

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    unwrap(alloc(self))
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError> {
    alloc(self)
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    unwrap(alloc_slice(self, len))
  }

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, AllocError> {
    alloc_slice(self, len)
  }

  #[inline(always)]
  pub fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    unwrap(copy_slice(self, src))
  }

  #[inline(always)]
  pub fn try_copy_slice<T>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError>
  where
    T: Copy
  {
    copy_slice(self, src)
  }

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    unwrap(copy_str(self, src))
  }

  #[inline(always)]
  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    copy_str(self, src)
  }
}

impl<'a> fmt::Debug for Arena<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let Span { ptr, len } = self.0.get();
    f.debug_tuple("Arena").field(&ptr).field(&len).finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Slot
//
////////////////////////////////////////////////////////////////////////////////

impl<'a, T> Slot<'a, T> {
  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    let x = ptr::from(self.0);
    unsafe { x.as_mut_ref() }
  }

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    let x = ptr::from(self.0);
    unsafe { x.write(value) }
    unsafe { x.as_mut_ref() }
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  #[inline(always)]
  pub fn as_uninit_array(self) -> &'a mut [MaybeUninit<T>; N] {
    let x = ptr::from(self.0);
    unsafe { x.as_mut_ref() }
  }

  #[inline(always)]
  pub fn init_array<F>(self, f: F) -> &'a mut [T; N]
  where
    F: FnMut(usize) -> T
  {
    let x = ptr::from(self.0);
    let mut f = f;
    let mut i = 0;
    let mut y = x;

    while i < N {
      unsafe { y.write(f(i)) };
      i = i + 1;
      y = y + size_of::<T>();
    }

    // SAFETY:
    //
    // Every array element has been initialized.

    unsafe { x.as_mut_ref() }
  }
}

impl<'a, T> Slot<'a, [T]> {
  #[inline(always)]
  pub fn as_uninit_slice(self) -> &'a mut [MaybeUninit<T>] {
    let n = self.0.len();
    let x = ptr::from(self.0);
    unsafe { x.as_slice_mut_ref(n) }
  }

  #[inline(always)]
  pub fn init_slice<F>(self, f: F) -> &'a mut [T]
  where
    F: FnMut(usize) -> T
  {
    let n = self.0.len();
    let x = ptr::from(self.0);
    let mut f = f;
    let mut i = 0;
    let mut y = x;

    while i < n {
      unsafe { y.write(f(i)) };
      i = i + 1;
      y = y + size_of::<T>();
    }

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { x.as_slice_mut_ref(n) }
  }
}

impl<'a, T> fmt::Debug for Slot<'a, T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Slot")
      .field(&ptr::from(&self.0))
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Allocator API
//
////////////////////////////////////////////////////////////////////////////////

unsafe impl<'a> allocator_api2::alloc::Allocator for Arena<'a> {
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, allocator_api2::alloc::AllocError> {
    let s = self.0.get();
    let (s, x) = unsafe { alloc_fast::<AllocError>(s, layout) };
    self.0.set(s);
    let Ok(x) = x else { return Err(allocator_api2::alloc::AllocError); };
    let n = layout.size();
    let x = ptr::from(x);
    let x = unsafe { x.as_slice_non_null(n) };
    Ok(x)
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    let _ = self;
    let _ = ptr;
    let _ = layout;
  }
}

////////////////////////////////////////////////////////////////////////////////

pub fn foo<'a>(a: &mut Arena<'a>) -> &'a mut u64 {
  a.alloc().init(1_u64)
}

pub fn bar<'a>(a: &mut Arena<'a>, n: usize) -> &'a mut [u64] {
  a.alloc_slice(n).init_slice(|_| 1_u64)
}

pub fn baz<'a>(a: &mut Arena<'a>, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
  a.alloc_layout(layout)
}
