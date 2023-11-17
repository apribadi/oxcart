use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr::NonNull;
use pop::Ptr;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

pub struct Arena(Header);

pub struct Allocator<'a> {
  lo: Ptr,
  hi: Ptr,
  pd: PhantomData<&'a ()>,
}

#[repr(transparent)]
pub struct Slot<T: Initializable + ?Sized>(T::Uninit);

#[derive(Debug)]
pub struct AllocError;

pub trait Initializable {
  type Uninit: ?Sized;
}

impl<T> Initializable for T {
  type Uninit = MaybeUninit<T>;
}

impl<T> Initializable for [T] {
  type Uninit = [MaybeUninit<T>];
}

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

#[repr(C)]
struct Header {
  next: Ptr
}

enum Raised {}

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
const MIN_CHUNK_SIZE_LOG2: u32 = 16; // 64kb

#[cfg(test)]
const MIN_CHUNK_SIZE_LOG2: u32 = 6; // 64b

const MIN_CHUNK_SIZE: usize = 1 << MIN_CHUNK_SIZE_LOG2;

const CHUNK_ALIGN: usize = WORD_SIZE;

const _: () = assert!(WORD_SIZE.is_power_of_two());
const _: () = assert!(core::mem::align_of::<Header>() <= CHUNK_ALIGN);
const _: () = assert!(core::mem::size_of::<Header>() <= MIN_CHUNK_SIZE);

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
//
// Raised
//
////////////////////////////////////////////////////////////////////////////////

impl Raised {
  #[inline(always)]
  fn unwrap<T>(x: Result<T, Raised>) -> T {
    match x {
      Ok(x) => x,
      Err(e) => match e {}
    }
  }
}

impl FromError for Raised {
  #[inline(never)]
  #[cold]
  fn global_alloc_error(layout: Layout) -> Self {
    alloc::alloc::handle_alloc_error(layout)
  }

  #[inline(never)]
  #[cold]
  fn layout_overflow() -> Self {
    panic!("layout overflow")
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// AllocError
//
////////////////////////////////////////////////////////////////////////////////

impl core::fmt::Display for AllocError {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.write_str("memory allocation failed")
  }
}

impl FromError for AllocError {
  #[inline(always)]
  fn global_alloc_error(_: Layout) -> Self { Self }

  #[inline(always)]
  fn layout_overflow() -> Self { Self }
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

#[inline(never)]
#[cold]
unsafe fn try_alloc_chunk_for_layout<E>(x: Ptr, layout: Layout) -> Result<(Ptr, Ptr), E>
where
  E: FromError
{
  // let s = layout.size();
  // let a = layout.align();
  // let h = unsafe { x.gep::<Header>(-1).as_mut_ref() };
  let _ = x;
  let _ = layout;
  panic!()
}

#[inline(never)]
#[cold]
unsafe fn try_alloc_chunk_for<T, E>(x: Ptr) -> Result<(Ptr, Ptr), E>
where
  E: FromError
{
  unsafe { try_alloc_chunk_for_layout::<E>(x, Layout::new::<T>()) }
}

#[inline(always)]
pub fn try_alloc<'a, T, E>(allocator: &mut Allocator<'a>) -> Result<&'a mut Slot<T>, E>
where
  E: FromError
{
  // PRECONDITIONS:
  //
  // - s <= isize::MAX
  // - a is a power of two
  // - s % a == 0
  // - lo.addr() <= isize::MAX
  // - hi.addr() <= isize::MAX

  let s = core::mem::size_of::<T>();
  let a = core::mem::align_of::<T>();
  let n = s + WORD_SIZE - 1 & ! (WORD_SIZE - 1);

  let x = allocator.lo;
  let y = allocator.hi;

  let y =
    if a <= WORD_SIZE {
      y - n
    } else {
      y - n & ! (WORD_SIZE - 1)
    };

  if (x.addr() as isize) <= (y.addr() as isize)  {
    allocator.hi = y;
    Ok(unsafe { y.as_mut_ref() })
  } else {
    let (x, y) = unsafe { try_alloc_chunk_for::<T, E>(x) }?;
    allocator.lo = x;
    allocator.hi = y;
    Ok(unsafe { y.as_mut_ref() })
  }
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  pub fn alloc<T>(&mut self) -> &'a mut Slot<T> {
    Raised::unwrap(try_alloc::<T, Raised>(self))
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<&'a mut Slot<T>, AllocError> {
    let _ = self;
    unimplemented!()
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
