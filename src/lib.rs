use std::alloc::Layout;
use std::alloc;
use std::cell::Cell;
use std::cmp::max;
use std::cmp::min;
use std::fmt;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::mem::align_of;
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

pub use allocator_api2::alloc::AllocError;

pub struct Store(NonNull<Root>);

pub struct Arena<'a>(Cell<Span>, PhantomData<&'a ()>);

pub struct Slot<'a, T>(NonNull<T>, PhantomData<&'a ()>)
where
  T: ?Sized;

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
  SystemAllocatorFailed(Layout),
  TooLarge,
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

const NULL: ptr = ptr::NULL;
const BITS: usize = usize::BITS as usize;
const WORD: usize = size_of::<usize>();  // 0b00...001000
const MASK: usize = WORD.wrapping_neg(); // 0b11...111000

const INITIAL_CHUNK_SIZE: usize = 1 << 14; // 16384
const MAX_CHUNK_SIZE: usize = 1 << BITS - 2;
const MAX_ALLOC_SIZE: usize = 1 << BITS - 3;
const MAX_ALIGN: usize = 1 << BITS - 4;

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
fn clz(x: usize) -> usize {
  x.leading_zeros() as usize
}

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
      Error::SystemAllocatorFailed(layout) => alloc::handle_alloc_error(layout),
      Error::TooLarge => panic!("oxcart: attempted a too large allocation!"),
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

  #[inline(always)]
  fn tail(self) -> ptr {
    self.ptr + self.len
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
  assert!(n >= 1);
  assert!(n <= MAX_CHUNK_SIZE);
  assert!(n % WORD == 0);

  let l = Layout::from_size_align(n, WORD).unwrap();
  let x = unsafe { alloc::alloc(l) };
  let x = NonNull::new(x);
  let Some(x) = x else { return E::fail(Error::SystemAllocatorFailed(l)); };
  Ok(x)
}

fn store<E>(n: usize) -> Result<Store, E>
where
  E: Fail
{
  let m = size_of::<Root>();
  let n = min(max(m, n & MASK), MAX_CHUNK_SIZE);
  let k = n - m;
  let p = chunk(n)?;
  let p = ptr::from(p);
  let r = p + k;

  unsafe {
    r.write(
      Root {
        link: Link { next: Span { ptr: p, len: k }, root: r, },
        is_growing: false,
        total_allocated: n,
      }
    )
  };

  Ok(Store(unsafe { r.as_non_null() }))
}

impl Store {
  pub fn new() -> Self {
    unwrap(store(INITIAL_CHUNK_SIZE))
  }

  pub fn try_new() -> Result<Self, AllocError> {
    store(INITIAL_CHUNK_SIZE)
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
    let _ = self;
    // let r = ptr::from(self.0);
    // let r = unsafe { r.as_ref::<Root>() };
    f.debug_struct("Store")
      // .field("chunk_size_last", &r.chunk_size_last)
      // .field("chunk_size_total", &r.chunk_size_total)
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Arena
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast<E>(state: Span, layout: Layout) -> Result<(Span, NonNull<u8>), E>
where
  E: Fail
{
  let p = state.ptr;
  let n = state.len;

  if p.addr() & WORD - 1 != 0 { unsafe { unreachable_unchecked() }; }

  let u = MASK & layout.align() - 1 & - p;
  let v = u + (MASK & WORD - 1 + layout.size());

  if v > n  {
    return match unsafe { alloc_slow(state, layout) } {
      (_, Err(e)) => Err(e),
      (s, Ok(x)) => Ok((s, x)),
    }
  }

  Ok((Span::new(p + v, n - v), unsafe { (p + u).as_non_null() }))
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow<E>(state: Span, layout: Layout) -> (Span, Result<NonNull<u8>, E>)
where
  E: Fail
{
  let t = unsafe { state.tail().as_ref::<Link>() };
  let r = unsafe { t.root.as_ref::<Root>() };

  'grow: {
    if ptr::from(t) == ptr::from(r) || r.is_growing { break 'grow; }

    let p = t.next.ptr;
    let n = t.next.len;
    let u = MASK & layout.align() - 1 & - p;
    let v = u + (MASK & WORD - 1 + layout.size());

    if v > n { break 'grow; }

    return (Span::new(p + v, n - v), Ok(unsafe { (p + u).as_non_null() }));
  };

  if layout.size() > MAX_ALLOC_SIZE || layout.align() > MAX_ALIGN {
    return (state, E::fail(Error::TooLarge));
  }

  let a = (MASK & layout.align() - 1) + (MASK & WORD - 1 + layout.size()) + size_of::<Link>();
  let b = r.total_allocated / 4 + 1;
  let n = 1 << BITS - clz(max(a, b) - 1);

  /*
  let p = chunk(n)?;
  let p = ptr::from(p);
  let m = size_of::<Link>();
  let k = n - m;
  let t = p + k;

  unsafe {
    t.write(
      Link {
        next: r.next,
        root: ptr::from_ref(r),
      }
    )
  };

  r.link.next = Span::new(p, k);
  r.is_growing = true;
  r.total_allocated = r.total_allocated.saturating_add(n);

  let u = MASK & layout.align() - 1 & - p;
  let v = u + (MASK & WORD - 1 + layout.size());

  return (Span::new(p + v, k - v), Ok(unsafe { (p + u).as_non_null() }));
  */
  unimplemented!()
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
  let (s, x) = unsafe { alloc_fast(*a, layout) }?;
  *a = s;
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
  let x = unsafe { ptr::from(x).as_non_null::<T>() };
  Ok(Slot(x, PhantomData))
}

#[inline(always)]
fn alloc_slice<'a, T, E>(arena: &mut Arena<'a>, len: usize) -> Result<Slot<'a, [T]>, E>
where
  E: Fail
{
  if size_of::<T>() != 0 && len > MAX_ALLOC_SIZE / size_of::<T>() {
    return E::fail(Error::TooLarge);
  }

  let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
  let x = alloc_layout(arena, l)?;
  let x = unsafe { ptr::from(x).as_slice_non_null(len) };
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
    unsafe { ptr::from(self.0).as_mut_ref() }
  }

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    unsafe { ptr::from(self.0).write(value) }
    unsafe { ptr::from(self.0).as_mut_ref() }
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  #[inline(always)]
  pub fn as_uninit_array(self) -> &'a mut [MaybeUninit<T>; N] {
    unsafe { ptr::from(self.0).as_mut_ref() }
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
    unsafe { ptr::from(self.0).as_slice_mut_ref(n) }
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
      .field(&ptr::from(self.0))
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
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    let s = self.0.get();
    let (s, x) = unsafe { alloc_fast(s, layout) }?;
    self.0.set(s);
    let n = layout.size();
    let x = unsafe { ptr::from(x).as_slice_non_null(n) };
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

pub fn qux<'a>(a: &mut Arena<'a>) -> Result<&'a mut u64, AllocError> {
  a.try_alloc().map(|x| x.init(1_u64))
}

