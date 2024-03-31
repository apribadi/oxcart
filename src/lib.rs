use std::alloc::Layout;
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
pub struct Slot<T: Object + ?Sized>(T::Uninit);

pub unsafe trait Object { type Uninit: ?Sized; }

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

#[cfg(not(test))]
const IS_TEST: bool = false;

#[cfg(test)]
const IS_TEST: bool = true;

const SLAB: usize = 1 << SLAB_LOG2;
const SLAB_LOG2: usize = if IS_TEST { 3 } else { 12 - WORD_LOG2 };

const WORD_LOG2: usize = size_of::<usize>().ilog2() as usize;
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
const _: () = assert!(size_of::<Root>() <= WORD_SIZE * SLAB);

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
//
// Object
//
////////////////////////////////////////////////////////////////////////////////

unsafe impl<T> Object for T {
  type Uninit = MaybeUninit<T>;
}

unsafe impl<T> Object for [T] {
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

  #[inline(always)]
  fn chop(self, n: usize) -> Self {
    Self { ptr: self.ptr + n, len: self.len - n, }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// core operations
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast(s: Span, l: Layout) -> (Span, ptr) {
  // NB:
  //
  // - This must optimize well when `l` is a constant, and when `l.align()` is
  //   a constant.
  //
  // - `x + y` cannot overflow.

  let m = l.align();
  let n = l.size();
  let x = WORD_SIZE.wrapping_neg() & m - 1 & ptr::addr(s.ptr).wrapping_neg();
  let y = WORD_SIZE.wrapping_neg() & WORD_SIZE - 1 + n;
  let z = x + y;
  if z <= s.len {
    return (Span::new(s.ptr + z, s.len - z), s.ptr + x);
  } else {
    return unsafe { alloc_slow(s, l) };
  }
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow(s: Span, l: Layout) -> (Span, ptr) {
  // TODO
  let _ = s;
  let _ = l;
  std::hint::black_box((Span::new(ptr::NULL, 0), ptr::NULL))
}

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
    let x = unsafe { ptr::as_mut_ref::<Root>(self.root) };
    x.is_growing = false;
    Allocator(x.link.next, PhantomData)
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
    let s = self.0;
    let (s, o) = unsafe { alloc_fast(s, layout) };
    self.0 = s;
    o
  }

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> &'a mut Slot<T> {
    let o = self.alloc_internal(Layout::new::<T>());
    unsafe { ptr::as_mut_ref(o) }
  }

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut Slot<[u8]> {
    let o = self.alloc_internal(layout);
    let o = ptr::as_slice_mut_ptr::<u8>(o, layout.size());
    unsafe { &mut *std::mem::transmute::<*mut [u8], *mut Slot<[u8]>>(o) }
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> &'a mut Slot<[T]> {
    if size_of::<T>() != 0 && len > (isize::MAX as usize) / size_of::<T>() {
      panic_layout_overflow()
    }

    let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
    let o = self.alloc_internal(l);
    let o = ptr::as_slice_mut_ptr::<T>(o, len);
    unsafe { &mut *std::mem::transmute::<*mut [T], *mut Slot<[T]>>(o) }
  }

  pub fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    // NB: Unlike `alloc_slice`, this can assume that the size calculations
    // don't overflow, because `src` exists.

    let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * src.len(), align_of::<T>()) };
    let o = self.alloc_internal(l);
    unsafe { ptr::copy_nonoverlapping::<T>(src, o, src.len()) };
    unsafe { ptr::as_slice_mut_ref::<T>(o, src.len()) }
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
  T: Object + ?Sized
{
  #[inline(always)]
  pub fn as_uninit(&mut self) -> &mut T::Uninit {
    &mut self.0
  }
}

impl<T> Slot<T> {
  #[inline(always)]
  pub fn init(&mut self, value: T) -> &mut T {
    self.as_uninit().write(value)
  }
}

impl<T, const N: usize> Slot<[T; N]> {
  #[inline(always)]
  pub fn as_uninit_array(&mut self) -> &mut [MaybeUninit<T>; N] {
    // SAFETY:
    //
    // The layouts of `MaybeUninit<[T; N]>` and `[MaybeUninit<T>; N]` are
    // guaranteed to be the same.

    unsafe { ptr::as_mut_ref(self.as_uninit()) }
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

    unsafe { ptr::as_mut_ref(x) }
  }
}

impl<T> Slot<[T]> {
  #[inline(always)]
  pub fn init_slice<F>(&mut self, f: F) -> &mut [T]
  where
    F: FnMut(usize) -> T
  {
    let mut f = f;

    let x = self.as_uninit();

    for (i, y) in x.iter_mut().enumerate() {
      let _: _ = y.write(f(i));
    }

    let n = x.len();

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { ptr::as_slice_mut_ref(x, n) }
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
