pub mod pop;

use std::alloc::Layout;
use std::cell::Cell;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::mem::align_of;
use std::mem::size_of;
use std::ptr::NonNull;
use pop::ptr;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

pub struct Arena { root: ptr }

pub struct Allocator<'a>(Cell<Span>, PhantomData<&'a mut ()>);

#[derive(Clone, Copy, Debug)]
pub struct AllocError;

#[repr(transparent)]
pub struct Slot<T>(T::Uninit)
where
  T: ?Sized + Object;

pub trait Object { type Uninit: ?Sized; }

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

/*
#[cfg(not(test))]
const IS_TEST: bool = false;

#[cfg(test)]
const IS_TEST: bool = true;

const WORD_LOG2: usize = size_of::<usize>().ilog2() as usize;
const SLAB_SIZE: usize = 1 << SLAB_LOG2;
const SLAB_LOG2: usize = if IS_TEST { 3 } else { 12 - WORD_LOG2 };
*/
const NULL: ptr = ptr::NULL;
const WORD: usize = size_of::<usize>();


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
}

const _: () = assert!(align_of::<Span>() <= WORD);
const _: () = assert!(align_of::<Link>() <= WORD);
const _: () = assert!(align_of::<Root>() <= WORD);

enum Panicked { }

enum Error {
  GlobalAllocatorFailed,
  LayoutOverflow,
}

trait Fail: Sized {
  fn fail<T>(_: Error) -> Result<T, Self>;
}

impl Fail for Panicked {
  #[inline(never)]
  #[cold]
  fn fail<T>(x: Error) -> Result<T, Self> {
    match x {
      Error::GlobalAllocatorFailed => panic!("oxcart: global allocator failed!"),
      Error::LayoutOverflow => panic!("oxcart: layout overflow!"),
    }
  }
}

impl Fail for AllocError {
  #[inline(always)]
  fn fail<T>(_: Error) -> Result<T, Self> {
    Err(AllocError)
  }
}

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
// Object
//
////////////////////////////////////////////////////////////////////////////////

impl<T> Object for T {
  type Uninit = MaybeUninit<T>;
}

impl<T> Object for [T] {
  type Uninit = [MaybeUninit<T>];
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

impl Arena {
  pub fn new() -> Self {
    // TODO
    Self { root: NULL }
  }

  pub fn allocator(&mut self) -> Allocator<'_> {
    let r = unsafe { self.root.as_mut_ref::<Root>() };
    r.is_growing = false;
    Allocator(Cell::new(r.link.next), PhantomData)
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    let _ = self;
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
  let a = y.align();
  let s = y.size();

  unsafe { assume(p.addr() & WORD - 1 == 0) };

  let i = - p & a - 1;                 // <= 0b0111...1
  let j = WORD - 1 + s & ! (WORD - 1); // <= 0b1000...0
  let k = i + j;

  if k > n  { return unsafe { alloc_slow(x, y) }; }

  let u = Span::new(p + k, n - k);
  let v = unsafe { (p + i).as_non_null() };

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
  if std::hint::black_box(true) {
    (Span::new(NULL, 0), E::fail(Error::GlobalAllocatorFailed))
  } else {
    (Span::new(NULL, 0), Ok(NonNull::dangling()))
  }
}

#[inline(always)]
fn alloc_layout<'a, E>(allocator: &mut Allocator<'a>, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
where
  E: Fail
{
  let x = allocator.0.get_mut();
  let (y, o) = unsafe { alloc_fast(*x, layout) };
  *x = y;
  let o = o?;
  let o = ptr::from(o);
  let o = unsafe { o.as_slice_mut_ref::<MaybeUninit<u8>>(layout.size()) };
  Ok(o)
}

#[inline(always)]
fn alloc<'a, T, E>(allocator: &mut Allocator<'a>) -> Result<&'a mut Slot<T>, E>
where
  E: Fail
{
  let o = alloc_layout(allocator, Layout::new::<T>())?;
  let o = ptr::from(o);
  let o = unsafe { o.as_mut_ref() };
  Ok(o)
}

#[inline(always)]
fn alloc_slice<'a, T, E>(allocator: &mut Allocator<'a>, len: usize) -> Result<&'a mut Slot<[T]>, E>
where
  E: Fail
{
  if size_of::<T>() != 0 && len > isize::MAX as usize / size_of::<T>() {
    return E::fail(Error::LayoutOverflow);
  }

  let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
  let o = alloc_layout(allocator, l)?;
  let o = ptr::from(o);
  let o = o.as_slice_mut_ptr::<T>(len);
  let o = unsafe { &mut *std::mem::transmute::<*mut [T], *mut Slot<[T]>>(o) };
  Ok(o)
}

#[inline(always)]
fn copy_slice<'a, T, E>(allocator: &mut Allocator<'a>, src: &[T]) -> Result<&'a mut [T], E>
where
  T: Copy,
  E: Fail
{
  let o = alloc_layout(allocator, Layout::for_value(src))?;
  let o = ptr::from(o);
  unsafe { ptr::copy_nonoverlapping::<T>(ptr::from(src), o, src.len()) };
  let o = unsafe { o.as_slice_mut_ref::<T>(src.len()) };
  Ok(o)
}

#[inline(always)]
fn copy_str<'a, E>(allocator: &mut Allocator<'a>, src: &str) -> Result<&'a mut str, E>
where
  E: Fail
{
  let o = copy_slice(allocator, src.as_bytes())?;
  let o = unsafe { std::str::from_utf8_unchecked_mut(o) };
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

  let c = std::alloc::alloc(Layout::from_size_align_unchecked(SLAB, WORD_SIZE));

  if ptr::is_null(c) {
    panic!("std::alloc::alloc failed!")
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
  pub fn alloc<T>(&mut self) -> &'a mut Slot<T> {
    unwrap(alloc(self))
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<&'a mut Slot<T>, AllocError> {
    alloc(self)
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> &'a mut Slot<[T]> {
    unwrap(alloc_slice(self, len))
  }

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<&'a mut Slot<[T]>, AllocError> {
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

impl<'a> std::fmt::Debug for Allocator<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let Span { ptr, len } = self.0.get();
    f.debug_tuple("Allocator")
      .field(&ptr)
      .field(&len)
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Slot
//
////////////////////////////////////////////////////////////////////////////////

impl<T> Slot<T> {
  #[inline(always)]
  pub fn as_uninit(&mut self) -> &mut MaybeUninit<T> {
    &mut self.0
  }

  #[inline(always)]
  pub fn init(&mut self, value: T) -> &mut T {
    self.0.write(value)
  }
}

impl<T, const N: usize> Slot<[T; N]> {
  #[inline(always)]
  pub fn as_uninit_array(&mut self) -> &mut [MaybeUninit<T>; N] {
    // SAFETY:
    //
    // The layouts of `MaybeUninit<[T; N]>` and `[MaybeUninit<T>; N]` are
    // guaranteed to be the same.

    unsafe { ptr::from(&mut self.0).as_mut_ref() }
  }

  #[inline(always)]
  pub fn init_array<F>(&mut self, f: F) -> &mut [T; N]
  where
    F: FnMut(usize) -> T
  {
    let mut f = f;

    for (i, x) in self.as_uninit_array().iter_mut().enumerate() {
      let _: _ = x.write(f(i));
    }

    // SAFETY:
    //
    // Every array element has been initialized.

    unsafe { ptr::from(&mut self.0).as_mut_ref() }
  }
}

impl<T> Slot<[T]> {
  #[inline(always)]
  pub fn as_uninit_slice(&mut self) -> &mut [MaybeUninit<T>] {
    &mut self.0
  }

  #[inline(always)]
  pub fn init_slice<F>(&mut self, f: F) -> &mut [T]
  where
    F: FnMut(usize) -> T
  {
    let mut f = f;

    for (i, x) in self.as_uninit_slice().iter_mut().enumerate() {
      let _: _ = x.write(f(i));
    }

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { ptr::from(&mut self.0).as_slice_mut_ref(self.0.len()) }
  }
}

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
