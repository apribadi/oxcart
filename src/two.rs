use core::alloc::Layout;
use core::marker::PhantomData;
use pop::Ptr;

pub struct Arena {
  list: Ptr,
}

pub struct Allocator<'a> {
  lo: Ptr,
  hi: Ptr,
  pd: PhantomData<&'a ()>,
}

pub struct Slot<'a, T>
where
  T: Pointee + ?Sized
{
  nn: core::ptr::NonNull<()>,
  md: T::Metadata,
  pd: PhantomData<(&'a (), fn(T))>,
}

#[derive(Debug)]
pub struct AllocError;

pub trait Pointee {
  #[allow(missing_docs)]
  type Metadata: Copy + Send + Sync + Ord + core::hash::Hash + Unpin;
}

impl<T> Pointee for T {
  type Metadata = ();
}

impl<T> Pointee for [T] {
  type Metadata = usize;
}

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

impl<'a> Allocator<'a> {
  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    let _ = self;
    unimplemented!()
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError> {
    let _ = self;
    unimplemented!()
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    let _ = self;
    let _ = len;
    unimplemented!()
  }

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, AllocError> {
    let _ = self;
    let _ = len;
    unimplemented!()
  }

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> Slot<'a, [u8]> {
    let _ = self;
    let _ = layout;
    unimplemented!()
  }

  #[inline(always)]
  pub fn try_alloc_layout<T>(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, AllocError> {
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
