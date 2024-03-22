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

const SLAB_LOG2: usize = if IS_TEST { 3 } else { 12 - WORD_LOG2 };
const SLAB: usize = 1 << SLAB_LOG2;
const WORD_LOG2: usize = size_of::<usize>().ilog2() as usize;
const WORD: usize = 1 << WORD_LOG2;

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

const _: () = assert!(align_of::<Span>() <= WORD);
const _: () = assert!(align_of::<Link>() <= WORD);
const _: () = assert!(align_of::<Root>() <= WORD);
const _: () = assert!(size_of::<Root>() <= WORD * SLAB);

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
  fn tail(self) -> ptr {
    self.ptr + WORD * self.len
  }

  #[inline(always)]
  fn chop(self, n: usize) -> Self {
    let ptr = self.ptr + WORD * n;
    let len = self.len - n;
    Self { ptr, len }
  }

  #[inline(always)]
  fn is_null(self) -> bool {
    self.ptr.is_null()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// core operations
//
////////////////////////////////////////////////////////////////////////////////

#[inline(never)]
#[cold]
unsafe fn reserve(x: Span, n: usize) -> Span {
  let l = x.tail();
  let l = l.as_ref::<Link>();
  let r = l.root;

  if ! r.is_null() && ! r.as_ref::<Root>().is_growing {
    return l.next;
  }

  let r = if ! r.is_null() { r } else { ptr::from(l) };
  let r = r.as_mut_ref::<Root>();

  let c = std::alloc::alloc(Layout::from_size_align_unchecked(SLAB, WORD));
  let c = ptr::from(c);

  if c.is_null() {
    panic!("std::alloc::alloc failed!")
  }

  let _ = n;
  let n = SLAB;
  let c = Span { ptr: c, len: n - size_of::<Link>() >> WORD_LOG2 };
  let l = c.tail();
  let b = r.link.next;
  l.write::<Link>(Link { next: b, root: ptr::from_ref(r) });
  r.link.next = c;
  s
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
    let x = unsafe { self.root.as_mut_ref::<Root>() };
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
  pub fn alloc<T>(&mut self) -> &'a mut Slot<T> {
    if align_of::<T>() <= WORD {
      let n = WORD - 1 + size_of::<T>() >> WORD_LOG2;
      let x = self.0;
      let x = if n <= x.len { x } else { unsafe { reserve(x, n) } };
      let y = x.ptr;
      let x = x.chop(n);
      self.0 = x;
      unsafe { y.as_mut_ref() }
    } else {
      unimplemented!()
    }
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> &'a mut Slot<[T]> {
    if align_of::<T>() <= WORD {
      if size_of::<T>() != 0 && len > isize::MAX as usize / size_of::<T>() {
        panic_layout_overflow()
      }

      let n = WORD - 1 + size_of::<T>() * len >> WORD_LOG2;
      let x = self.0;
      let x = if n <= x.len { x } else { unsafe { reserve(x, n) } };
      let y = x.ptr;
      let x = x.chop(n);
      self.0 = x;
      let y = y.as_slice_mut_ptr::<T>(len);
      unsafe { &mut *std::mem::transmute::<*mut [T], *mut Slot<[T]>>(y) }
    } else {
      if size_of::<T>() != 0 && len > isize::MAX as usize / size_of::<T>() {
        panic_layout_overflow()
      }

      unimplemented!()
    }
  }

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut Slot<[u8]> {
    assert!(false);
    let x = self.0;
    let b = layout.size();
    let y: ptr = ptr::NULL;
    let y = y.as_slice_mut_ptr::<u8>(b);
    self.0 = x;
    unsafe { &mut *std::mem::transmute::<*mut [u8], *mut Slot<[u8]>>(y) }
  }

  pub fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    assert!(align_of::<T>() <= WORD);

    // NB: Unlike `alloc_slice`, this can assume that the size calculations
    // don't overflow, because `src` exists.

    let n = WORD - 1 + size_of::<T>() * src.len() >> WORD_LOG2;
    let x = self.0;
    let x = if n <= x.len { x } else { unsafe { reserve(x, n) } };
    let y = x.ptr;
    let x = x.chop(n);
    self.0 = x;
    unsafe { ptr::copy_nonoverlapping::<T>(ptr::from(src), y, src.len()) };
    unsafe { y.as_slice_mut_ref(src.len()) }
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
  pub fn as_uninit_slice(&mut self) -> &mut [MaybeUninit<T>] {
    &mut self.0
  }

  #[inline(always)]
  pub fn init_slice<F>(&mut self, f: F) -> &mut [T]
  where
    F: FnMut(usize) -> T
  {
    let mut f = f;

    let x = self.as_uninit_slice();

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

  for i in 0 .. n {
    let _: _ =  a.alloc().init(i as u64);
  }
}

pub fn bar<'a>(a: &mut Allocator<'a>, x: u64, y: u64) -> &'a mut (u64, u64) {
  a.alloc().init((x, y))
}
