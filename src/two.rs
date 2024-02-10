use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use pop::Ptr as ptr;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

pub struct Arena(Ptr);

pub struct Allocator<'a>(
  p: Ptr,
  n: isize,
  w: PhantomData<&'a ()>,
}

#[repr(transparent)]
pub struct Slot<T: Object + ?Sized>(T::Uninit);

pub trait Object {
  type Uninit: ?Sized;
}

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

#[repr(C)]
#[derive(Copy, Clone)]
struct Raw(Ptr, usize);

struct Footer {
  next: Ptr,
  size: usize,
}

trait FromError {
  fn global_alloc_error(_: Layout) -> Self;
  fn layout_overflow() -> Self;
}

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

const WORD_SIZE: usize = core::mem::size_of::<usize>();

#[cfg(not(test))]
const MIN_CHUNK_SIZE: usize = 1 << 16; // 64kb

#[cfg(test)]
const MIN_CHUNK_SIZE: usize = 1 << 6; // 64b

const _: () = assert!(core::mem::align_of::<Footer>() == WORD_SIZE);
const _: () = assert!(core::mem::size_of::<Footer>() <= MIN_CHUNK_SIZE);

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

impl<T> Object for T {
  type Uninit = MaybeUninit<T>;
}

impl<T> Object for [T] {
  type Uninit = [MaybeUninit<T>];
}

////////////////////////////////////////////////////////////////////////////////
//
// Arena
//
////////////////////////////////////////////////////////////////////////////////

impl Arena {
  pub fn new() -> Self {
    unimplemented!()
  }

  pub fn allocator(&mut self) -> Allocator<'_> {
    let _ = self;
    unimplemented!()
  }

  pub fn reset(&mut self) {
    let _ = self;
    unimplemented!()
  }
}

/*
#[inline(never)]
#[cold]
unsafe fn try_alloc_chunk<E>(lo: Ptr, hi: Ptr) -> Result<(Ptr, Ptr), E>
where
  E: FromError
{
  let _ = lo;
  let _ = hi;
  Ok((core::hint::black_box(Ptr::NULL), core::hint::black_box(Ptr::NULL)))
}

*/

#[inline(never)]
#[cold]
extern "rust-cold" fn try_alloc_chunk<E>(p: Ptr, n: isize) -> Result<(Ptr, isize), E>
where
  E: FromError
{
  let _ = p;
  let _ = n;
  Ok((core::hint::black_box(Ptr::NULL), core::hint::black_box(0)))
}

#[inline(always)]
fn try_alloc<'a, T, E>(allocator: &mut Allocator<'a>) -> Result<&'a mut Slot<T>, E>
where
  E: FromError
{
  // PRECONDITIONS:
  //
  // -

  let s = core::mem::size_of::<T>();
  let a = core::mem::align_of::<T>();
  let k = s + WORD_SIZE - 1 & ! (WORD_SIZE - 1);

  assert!(a <= WORD_SIZE);

  allocator.p = allocator.p - k;
  allocator.n = allocator.n.wrapping_sub_unsigned(k);

  while allocator.n < 0 {
    let (x, y) = try_alloc_chunk(allocator.p, allocator.n)?;
    allocator.p = x;
    allocator.n = y;
    allocator.p = allocator.p - k;
    allocator.n = allocator.n.wrapping_sub_unsigned(k);
  }

  Ok(unsafe { allocator.p.as_mut_ref() })
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  pub fn alloc<T>(&mut self) -> &'a mut Slot<T> {
    Panicked::unwrap(try_alloc::<T, Panicked>(self))
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<&'a mut Slot<T>, AllocError> {
    try_alloc::<T, AllocError>(self)
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> &'a mut Slot<[T]> {
    let _ = self;
    let _ = len;
    unimplemented!()
  }

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<&'a mut Slot<[T]>, AllocError> {
    let _ = self;
    let _ = len;
    unimplemented!()
  }

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut Slot<[u8]> {
    let _ = self;
    let _ = layout;
    unimplemented!()
  }

  #[inline(always)]
  pub fn try_alloc_layout<T>(&mut self, layout: Layout) -> Result<&'a mut Slot<[u8]>, AllocError> {
    let _ = self;
    let _ = layout;
    unimplemented!()
  }

  pub fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    let _ = self;
    let _ = src;
    unimplemented!()
  }

  pub fn try_copy_slice<T>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError>
  where
    T: Copy
  {
    let _ = self;
    let _ = src;
    unimplemented!()
  }

  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    let _ = self;
    let _ = src;
    unimplemented!()
  }

  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    let _ = self;
    let _ = src;
    unimplemented!()
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
    assert!(!  core::mem::needs_drop::<T>());

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

    unsafe { Ptr::from(&mut self.0).as_mut_ref() }
  }

  #[inline(always)]
  pub fn init_array<F>(&mut self, f: F) -> &mut [T; N]
  where
    F: FnMut(usize) -> T
  {
    assert!(!  core::mem::needs_drop::<T>());

    let mut f = f;

    let x = self.as_uninit_array();

    for (i, y) in x.iter_mut().enumerate() {
      let _: _ = y.write(f(i));
    }

    // SAFETY:
    //
    // Every array element has been initialized.

    unsafe { Ptr::from(x).as_mut_ref() }
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
    assert!(!  core::mem::needs_drop::<T>());

    let mut f = f;

    let x = self.as_uninit_slice();

    for (i, y) in x.iter_mut().enumerate() {
      let _: _ = y.write(f(i));
    }

    let n = x.len();

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { Ptr::from(x).as_slice_mut_ref(n) }
  }
}

pub fn foo<'a>(allocator: &mut Allocator<'a>) -> &'a mut (u64, u64) {
  allocator.alloc::<(u64, u64)>().init((0, 0))
}

pub fn bar<'a>(allocator: Allocator<'a>) -> &'a mut (u64, u64) {
  let mut allocator = allocator;
  allocator.alloc::<(u64, u64)>().init((0, 0))
}

pub fn baz<'a, 'b>(allocator: &mut Allocator<'a>, slice: &'b mut [Option<&'a u64>]) {
  for elt in slice.iter_mut() {
    *elt = Some(allocator.alloc().init(13))
  }
}
