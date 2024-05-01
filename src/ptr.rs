use alloc::alloc::Layout;
use core::ptr::NonNull;
use allocator_api2::alloc::AllocError;

#[inline(always)]
pub(crate) fn from_ref<T>(x: &T) -> NonNull<T>
where
  T: ?Sized
{
  NonNull::from(x)
}

#[inline(always)]
pub(crate) fn from_mut_ref<T>(x: &mut T) -> NonNull<T>
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
pub(crate) fn is_aligned_to<T>(x: NonNull<T>, y: usize) -> bool {
  addr(x) & y - 1 == 0
}

#[inline(always)]
pub(crate) unsafe fn align_up<T, U>(x: NonNull<T>, y: usize) -> NonNull<U> {
  add(x, y - 1 & addr(x).wrapping_neg())
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
pub(crate) const unsafe fn sub<T, U>(x: NonNull<T>, y: usize) -> NonNull<U> {
  NonNull::new_unchecked(x.as_ptr().byte_sub(y).cast())
}

#[inline(always)]
pub(crate) const unsafe fn inc<T>(x: NonNull<T>) -> NonNull<T> {
  NonNull::new_unchecked(x.as_ptr().add(1))
}

#[inline(always)]
pub(crate) unsafe fn write<T>(x: NonNull<T>, y: T) {
  x.as_ptr().write(y)
}

#[inline(always)]
pub(crate) fn as_slice<T>(x: NonNull<T>, y: usize) -> NonNull<[T]> {
  let x = core::ptr::slice_from_raw_parts_mut(x.as_ptr(), y);
  unsafe { NonNull::new_unchecked(x) }
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

#[inline(always)]
pub(crate) fn alloc<T>(layout: Layout) -> Result<NonNull<T>, AllocError> {
  if layout.size() == 0 {
    return Err(AllocError);
  }

  let Some(p) = NonNull::new(unsafe { alloc::alloc::alloc(layout) }) else {
    return Err(AllocError);
  };

  Ok(cast(p))
}

#[inline(always)]
pub(crate) unsafe fn dealloc<T>(x: NonNull<T>, layout: Layout) {
  alloc::alloc::dealloc(cast(x).as_ptr(), layout)
}
