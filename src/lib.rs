use pop::ptr;
use std::alloc::Layout;
use std::alloc;
use std::fmt;
use std::hint::black_box;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::mem::align_of;
use std::mem::size_of;
use std::ptr::NonNull;
use std::str;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

pub struct Arena { root: NonNull<Root> }

pub struct Allocator<'a>(Span, PhantomData<&'a ()>);

#[derive(Debug)]
pub struct AllocError;

pub struct Slot<'a, T>(NonNull<T>, PhantomData<&'a ()>)
where
  T: ?Sized;

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

enum ErrorInfo {
  AllocSizeTooLarge,
  SystemAllocatorFailed(Layout),
  Unimplemented,
}

enum Panicked { }

trait Fail: Sized {
  fn fail<T>(_: ErrorInfo) -> Result<T, Self>;
}

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

const DEFAULT_INITIAL_CHUNK_SIZE: usize = 1 << 14; // 16384
const MAX_CHUNK_SIZE: usize = usize::MAX / 4 + 1;
const NULL: ptr = ptr::NULL;
const WORD: usize = size_of::<usize>();

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

// SAFETY:
//
// - `x` must be `true`

#[inline(always)]
unsafe fn assume(x: bool) {
  if ! x { unsafe { unreachable_unchecked() }; }
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
  fn fail<T>(x: ErrorInfo) -> Result<T, Self> {
    match x {
      ErrorInfo::AllocSizeTooLarge => panic!("oxcart: alloc size too large!"),
      ErrorInfo::SystemAllocatorFailed(layout) => alloc::handle_alloc_error(layout),
      ErrorInfo::Unimplemented => panic!("oxcart: unimplemented!"),
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
  fn fail<T>(_: ErrorInfo) -> Result<T, Self> {
    Err(AllocError)
  }
}

impl fmt::Display for AllocError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str("oxcart: failed to allocate memory")
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
// Arena
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

  if let Some(p) = NonNull::new(p) {
    return Ok(p);
  }

  return E::fail(ErrorInfo::SystemAllocatorFailed(layout));
}

fn arena<E>(n: usize) -> Result<Arena, E>
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
      link: Link { next: Span { ptr: p, len: k }, root: NULL, },
      is_growing: false,
      total_allocated: n,
    };

  unsafe { r.write(x) };
  let r = unsafe { r.as_non_null() };
  Ok(Arena { root: r })
}

impl Arena {
  pub fn new() -> Self {
    unwrap(arena(DEFAULT_INITIAL_CHUNK_SIZE))
  }

  pub fn try_new() -> Result<Self, AllocError> {
    arena(DEFAULT_INITIAL_CHUNK_SIZE)
  }

  pub fn allocator(&mut self) -> Allocator<'_> {
    let r = ptr::from(self.root);
    let r = unsafe { r.as_mut_ref::<Root>() };
    r.is_growing = false;
    Allocator(r.link.next, PhantomData)
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    let _ = self;
    // TODO
  }
}

impl fmt::Debug for Arena {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let r = ptr::from(self.root);
    let r = unsafe { r.as_ref::<Root>() };
    let total_allocated = r.total_allocated;
    f.debug_struct("Arena")
      .field("total_allocated", &total_allocated)
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Allocator
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast<E>(x: Span, y: Layout) -> (Span, Result<NonNull<u8>, E>)
where
  E: Fail
{
  let p = x.ptr;
  let n = x.len;
  let s = y.size();
  let a = y.align();

  unsafe { assume(p.addr() & WORD - 1 == 0) };

  let i = - p & a - 1;                 // <= 0b0111...1
  let j = WORD - 1 + s & ! (WORD - 1); // <= 0b1000...0
  let k = i + j;

  if k > n  { return unsafe { alloc_slow(x, y) }; }

  let u = Span::new(p + k, n - k);
  let v = p + i;
  let v = unsafe { v.as_non_null() };

  return (u, Ok(v));
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow<E>(x: Span, y: Layout) -> (Span, Result<NonNull<u8>, E>)
where
  E: Fail
{
  // TODO
  let _ = x;
  let _ = y;

  let r: &mut Root = {
    let t = x.ptr + x.len; // tail
    let t = t.as_mut_ref::<Link>();
    let r = t.root;
    let r = if r.is_null() { ptr::from(t) } else { r };
    r.as_mut_ref::<Root>()
  };

  // let s = y.size();
  // let a = y.align();
  // let n = usize::max(a, WORD) - WORD + s;
  let n = usize::max(r.link.next.len, r.total_allocated / 4 + 1);
  let n = n.next_power_of_two();
  // next power of two

  let _ = n;

  if black_box(true) {
    (Span::new(NULL, 0), E::fail(ErrorInfo::Unimplemented))
  } else {
    (Span::new(NULL, 0), Ok(NonNull::dangling()))
  }
}

#[inline(always)]
fn alloc_layout<'a, E>(x: &mut Allocator<'a>, y: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
where
  E: Fail
{
  let (s, o) = unsafe { alloc_fast(x.0, y) };
  x.0 = s;
  let o = o?;
  let o = ptr::from(o);
  let o = unsafe { o.as_slice_mut_ref::<MaybeUninit<u8>>(y.size()) };
  Ok(o)
}

#[inline(always)]
fn alloc<'a, T, E>(x: &mut Allocator<'a>) -> Result<Slot<'a, T>, E>
where
  E: Fail
{
  let o = alloc_layout(x, Layout::new::<T>())?;
  let o = ptr::from(o);
  let o = unsafe { o.as_non_null::<T>() };
  Ok(Slot(o, PhantomData))
}

#[inline(always)]
fn alloc_slice<'a, T, E>(x: &mut Allocator<'a>, y: usize) -> Result<Slot<'a, [T]>, E>
where
  E: Fail
{
  if size_of::<T>() != 0 && y > MAX_CHUNK_SIZE / size_of::<T>() {
    return E::fail(ErrorInfo::AllocSizeTooLarge);
  }

  let z = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * y, align_of::<T>()) };
  let o = alloc_layout(x, z)?;
  let o = ptr::from(o);
  let o = unsafe { o.as_slice_non_null(y) };
  Ok(Slot(o, PhantomData))
}

#[inline(always)]
fn copy_slice<'a, T, E>(x: &mut Allocator<'a>, y: &[T]) -> Result<&'a mut [T], E>
where
  T: Copy,
  E: Fail
{
  let o = alloc_layout(x, Layout::for_value(y))?;
  let o = ptr::from(o);
  unsafe { ptr::copy_nonoverlapping::<T>(ptr::from(y), o, y.len()) };
  let o = unsafe { o.as_slice_mut_ref::<T>(y.len()) };
  Ok(o)
}

#[inline(always)]
fn copy_str<'a, E>(x: &mut Allocator<'a>, y: &str) -> Result<&'a mut str, E>
where
  E: Fail
{
  let o = copy_slice(x, y.as_bytes())?;
  let o = unsafe { str::from_utf8_unchecked_mut(o) };
  Ok(o)
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

impl<'a> Allocator<'a> {
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

impl<'a> fmt::Debug for Allocator<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Allocator")
      .field(&self.0.ptr)
      .field(&self.0.len)
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Slot
//
////////////////////////////////////////////////////////////////////////////////

unsafe impl<'a, T> Send for Slot<'a, T> where T: ?Sized { }

unsafe impl<'a, T> Sync for Slot<'a, T> where T: ?Sized { }

impl<'a, T> Slot<'a, T> {
  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    let x = ptr::from(self.0);
    unsafe { x.write(value) };
    unsafe { x.as_mut_ref() }
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  #[inline(always)]
  pub fn init_array<F>(self, f: F) -> &'a mut [T; N]
  where
    F: FnMut(usize) -> T
  {
    let mut f = f;
    let x = ptr::from(self.0);

    for i in 0 .. N {
      let y = x + size_of::<T>() * i;
      unsafe { y.write(f(i)) };
    }

    // SAFETY:
    //
    // Every array element has been initialized.

    unsafe { x.as_mut_ref() }
  }
}

impl<'a, T> Slot<'a, [T]> {
  #[inline(always)]
  pub fn init_slice<F>(self, f: F) -> &'a mut [T]
  where
    F: FnMut(usize) -> T
  {
    let mut f = f;
    let x = ptr::from(self.0);
    let n = self.0.len();

    for i in 0 .. n {
      let y = x + size_of::<T>() * i;
      unsafe { y.write(f(i)) };
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

pub fn foo<'a>(a: &mut Allocator<'a>, n: usize) {
  // let mut a = a;
  let mut x = 1_u64;

  for _ in 0 .. n {
    let _: _ =  a.alloc().init(x);
    x = x ^ x << 7;
    x = x ^ x >> 9;
  }
}

pub fn aaa0<'a>(a: &mut Allocator<'a>, x: u32) -> &'a mut u32 {
  a.alloc().init(x)
}

pub fn aaa1<'a>(a: &mut Allocator<'a>, x: u64) -> &'a mut u64 {
  a.alloc().init(x)
}

pub fn aaa2<'a>(a: &mut Allocator<'a>, x: u128) -> &'a mut u128 {
  a.alloc().init(x)
}

#[repr(align(32))]
pub struct A(pub [u8; 65]);

pub fn aaa3<'a>(a: &mut Allocator<'a>, x: A) -> &'a mut A {
  a.alloc().init(x)
}

pub fn aaa4<'a>(a: &mut Allocator<'a>, n: usize) -> &'a mut [u64] {
  let mut x = 1_u64;
  a.alloc_slice(n).init_slice(|_| {
    let y = x;
    x = x ^ x << 7;
    x = x ^ x >> 9;
    y
  })
}

pub fn aaa5<'a>(a: &mut Allocator<'a>, x: u64) -> Result<&'a mut u64, AllocError> {
  a.try_alloc().map(|s| s.init(x))
}
