use std::alloc::Layout;
use std::ptr::NonNull;

#[inline(always)]
pub(crate) unsafe fn from_ref<T: ?Sized>(x: &T) -> NonNull<T> {
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
pub(crate) fn is_aligned_to<T>(x: NonNull<T>, y: usize) -> bool {
  addr(x) & y - 1 == 0
}

#[inline(always)]
pub(crate) const fn cast<T: ?Sized, U>(x: NonNull<T>) -> NonNull<U> {
  x.cast()
}

#[inline(always)]
pub(crate) const unsafe fn add<T>(x: NonNull<T>, y: usize) -> NonNull<T> {
  NonNull::new_unchecked(x.as_ptr().add(y))
}

#[inline(always)]
pub(crate) const unsafe fn sub<T>(x: NonNull<T>, y: usize) -> NonNull<T> {
  NonNull::new_unchecked(x.as_ptr().sub(y))
}

#[inline(always)]
pub(crate) unsafe fn write<T>(x: NonNull<T>, y: T) {
  x.as_ptr().write(y)
}

#[inline(always)]
pub(crate) fn as_slice<T>(x: NonNull<T>, y: usize) -> NonNull<[T]> {
  let x = std::ptr::slice_from_raw_parts_mut(x.as_ptr(), y);
  unsafe { NonNull::new_unchecked(x) }
}

#[inline(always)]
pub(crate) unsafe fn as_ref<'a, T: ?Sized>(x: NonNull<T>) -> &'a T {
  &*x.as_ptr()
}

#[inline(always)]
pub(crate) unsafe fn as_mut_ref<'a, T: ?Sized>(x: NonNull<T>) -> &'a mut T {
  &mut *x.as_ptr()
}

#[inline(always)]
pub(crate) unsafe fn as_slice_mut_ref<'a, T>(x: NonNull<T>, y: usize) -> &'a mut [T] {
  &mut *std::ptr::slice_from_raw_parts_mut(x.as_ptr(), y)
}

#[inline(always)]
pub(crate) unsafe fn copy_nonoverlapping<T>(src: NonNull<T>, dst: NonNull<T>, len: usize) {
  std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_ptr(), len)
}

#[inline(always)]
pub(crate) unsafe fn alloc(layout: Layout) -> Option<NonNull<u8>> {
  NonNull::new(std::alloc::alloc(layout))
}
