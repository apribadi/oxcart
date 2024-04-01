pub mod pop;

use std::alloc::Layout;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::mem::align_of;
use std::mem::size_of;
use pop::ptr;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

pub struct Arena { root: ptr }

pub struct Allocator<'a>(Span, PhantomData<&'a mut ()>);

#[repr(transparent)]
pub struct Slot<T: ?Sized + Object>(T::Uninit);

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
const WORD_SIZE: usize = size_of::<usize>();

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

// +-=
// |
// |

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

const _: () = assert!(align_of::<Span>() <= WORD_SIZE);
const _: () = assert!(align_of::<Link>() <= WORD_SIZE);
const _: () = assert!(align_of::<Root>() <= WORD_SIZE);

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn assume(x: bool) {
  if ! x { unsafe { unreachable_unchecked() }; }
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

  #[inline(always)]
  fn tail(self) -> ptr {
    self.ptr + self.len
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// core operations
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast(x: Span, y: Layout) -> (Span, ptr) {
  // NB:
  //
  // - This implementation optimizes well when the `Layout` is constant or
  //   partially constant.
  //
  // - `i + j` cannot overflow because of `Layout` invariants.

  let w = size_of::<usize>();
  let p = x.ptr;
  let n = x.len;
  let a = y.align();
  let s = y.size();

  unsafe { assume(p.addr() & w - 1 == 0) };

  let i = - p & a - 1;
  let j = w - 1 + s & ! (w - 1);
  let k = i + j;

  if k <= n { return (Span::new(p + k, n - k), p + i); }

  return unsafe { alloc_slow(x, y) };
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow(x: Span, y: Layout) -> (Span, ptr) {
  // TODO
  let _ = x;
  let _ = y;
  std::hint::black_box((Span::new(ptr::NULL, 0), ptr::NULL))
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

////////////////////////////////////////////////////////////////////////////////
//
// Arena
//
////////////////////////////////////////////////////////////////////////////////

impl Arena {
  pub fn new() -> Self {
    Self { root: ptr::NULL }
  }

  pub fn allocator(&mut self) -> Allocator<'_> {
    let r = unsafe { self.root.as_mut_ref::<Root>() };
    r.is_growing = false;
    Allocator(r.link.next, PhantomData)
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

#[inline(never)]
#[cold]
fn panic_layout_overflow() -> ! {
  panic!("layout overflow!")
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn alloc_internal(&mut self, layout: Layout) -> ptr {
    let (x, y) = unsafe { alloc_fast(self.0, layout) };
    self.0 = x;
    y
  }

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> &'a mut Slot<T> {
    let x = self.alloc_internal(Layout::new::<T>());
    unsafe { x.as_mut_ref() }
  }

  // #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut Slot<[u8]> {
    let x = self.alloc_internal(layout).as_slice_mut_ptr::<u8>(layout.size());
    unsafe { &mut *std::mem::transmute::<*mut [u8], *mut Slot<[u8]>>(x) }
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> &'a mut Slot<[T]> {
    if size_of::<T>() != 0 && len > (isize::MAX as usize) / size_of::<T>() {
      panic_layout_overflow()
    }

    let x = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
    let y = self.alloc_internal(x).as_slice_mut_ptr::<T>(len);
    unsafe { &mut *std::mem::transmute::<*mut [T], *mut Slot<[T]>>(y) }
  }

  pub fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    let x = ptr::from(src);
    let y = self.alloc_internal(Layout::for_value(src));
    unsafe { ptr::copy_nonoverlapping::<T>(x, y, src.len()) };
    unsafe { y.as_slice_mut_ref::<T>(src.len()) }
  }

  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    let x = self.copy_slice(src.as_bytes());
    unsafe { std::str::from_utf8_unchecked_mut(x) }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Slot
//
////////////////////////////////////////////////////////////////////////////////

impl<T> Slot<T>
where
  T: ?Sized + Object
{
  #[inline(always)]
  pub fn as_uninit(&mut self) -> &mut T::Uninit {
    &mut self.0
  }
}

impl<T> Slot<T> {
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
    let x = self.as_uninit_array();

    for (i, y) in x.iter_mut().enumerate() {
      let _: _ = y.write(f(i));
    }

    // SAFETY:
    //
    // Every array element has been initialized.

    unsafe { ptr::from(x).as_mut_ref() }
  }
}

impl<T> Slot<[T]> {
  #[inline(always)]
  pub fn init_slice<F>(&mut self, f: F) -> &mut [T]
  where
    F: FnMut(usize) -> T
  {
    let mut f = f;
    let x = &mut self.0;

    for (i, y) in x.iter_mut().enumerate() {
      let _: _ = y.write(f(i));
    }

    let n = x.len();

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { ptr::from(x).as_slice_mut_ref(n) }
  }
}

pub fn foo<'a>(a: Allocator<'a>, n: usize) {
  let mut a = a;
  let mut x = 1_u64;

  for _ in 0 .. n {
    let _: _ =  a.alloc().init(x);
    x = x ^ x << 7;
    x = x ^ x >> 9;
  }
}

pub fn aaa0<'a>(a: &mut Allocator<'a>, x: u64, y: u64) -> &'a mut (u64, u64) {
  a.alloc().init((x, y))
}

pub fn aaa1<'a>(a: &mut Allocator<'a>, x: u128) -> &'a mut u128 {
  a.alloc().init(x)
}

#[repr(align(32))]
pub struct A(pub u64);

pub fn aaa2<'a>(a: &mut Allocator<'a>, x: A) -> &'a mut A {
  a.alloc().init(x)
}
