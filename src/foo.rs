use core::ptr::NonNull;

#[inline(always)]
pub(crate) fn from_ref<T>(x: &T) -> NonNull<T>
where
  T: ?Sized
{
  NonNull::from(x)
}

#[inline(always)]
pub(crate) fn addr<T>(x: NonNull<T>) -> usize {
  // NB: This must not be a `const` function.
  //
  // Transmuting a pointer into an integer in a const context is undefined
  // behavior.

  // Once the `strict_provenance` feature has been stabilized, this should
  // use the `addr` method on the primitive pointer type.

  unsafe { core::mem::transmute::<*mut T, usize>(x.as_ptr()) }
}

#[inline(always)]
pub(crate) unsafe fn align_up<T, U>(x: NonNull<T>) -> NonNull<U> {
  add(x, align_of::<U>() - 1 & addr(x).wrapping_neg())
}

#[inline(always)]
pub(crate) const fn cast<T, U>(x: NonNull<T>) -> NonNull<U>
where
  T: ?Sized
{
  x.cast()
}

#[inline(always)]
pub(crate) const unsafe fn add<T, U>(x: NonNull<T>, y: usize) -> NonNull<U> {
  NonNull::new_unchecked(x.as_ptr().byte_add(y).cast())
}

#[inline(always)]
pub(crate) unsafe fn read<T>(x: NonNull<T>) -> T {
  x.as_ptr().read()
}

#[inline(always)]
pub(crate) unsafe fn write<T>(x: NonNull<T>, y: T) {
  x.as_ptr().write(y)
}

#[inline(always)]
pub(crate) fn as_slice<T>(x: NonNull<T>, y: usize) -> NonNull<[T]> {
  unsafe { NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(x.as_ptr(), y)) }
}

#[inline(always)]
pub(crate) unsafe fn as_ref<'a, T>(x: NonNull<T>) -> &'a T
where
  T: ?Sized
{
  &*x.as_ptr()
}

#[inline(always)]
pub(crate) unsafe fn as_mut_ref<'a, T>(x: NonNull<T>) -> &'a mut T
where
  T: ?Sized
{
  &mut *x.as_ptr()
}

#[inline(always)]
pub(crate) unsafe fn as_slice_mut_ref<'a, T>(x: NonNull<T>, y: usize) -> &'a mut [T] {
  &mut *core::ptr::slice_from_raw_parts_mut(x.as_ptr(), y)
}

#[inline(always)]
pub(crate) unsafe fn copy_nonoverlapping<T>(src: NonNull<T>, dst: NonNull<T>, len: usize) {
  core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_ptr(), len)
}

/*

#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct Ptr(*mut u8);

unsafe impl Send for Ptr { }

unsafe impl Sync for Ptr { }

impl Ptr {

  #[inline(always)]
  pub(crate) fn addr(self) -> usize {
    // NB: This must not be a `const` function.
    //
    // Transmuting a pointer into an integer in a const context is undefined
    // behavior.

    unsafe { core::mem::transmute::<*mut u8, usize>(self.0) }
  }

  #[inline(always)]
  pub const fn from_non_null<T: ?Sized>(x: NonNull<T>) -> Ptr {
    Ptr(x.cast().as_ptr())
  }

  #[inline(always)]
  pub const fn as_const_ptr<T>(self) -> *const T {
    self.as_mut_ptr()
  }

  #[inline(always)]
  pub const fn as_mut_ptr<T>(self) -> *mut T {
    self.0.cast()
  }

  #[inline(always)]
  pub const fn as_non_null<T>(self) -> NonNull<T> {
    self.0.cast()
  }

  #[inline(always)]
  pub const unsafe fn as_ref<'a, T>(self) -> &'a T {
    let x = self.as_const_ptr();
    unsafe { &*x }
  }

  #[inline(always)]
  pub unsafe fn as_mut_ref<'a, T>(self) -> &'a mut T {
    let x = self.as_mut_ptr();
    unsafe { &mut *x }
  }

  #[inline(always)]
  pub const unsafe fn sub(self, n: usize) -> Ptr {
    Ptr(self.0.sub(n))
  }

  #[inline(always)]
  pub fn is_aligned_to(self, align: usize) -> bool {
    self.addr() & align - 1 == 0
  }
}

*/
