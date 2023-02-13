pub(crate) extern crate alloc;
pub(crate) use core::alloc::Layout;
pub(crate) use core::cmp::max;
pub(crate) use core::fmt;
pub(crate) use core::marker::PhantomData;
pub(crate) use core::mem::MaybeUninit;
pub(crate) use core::mem::align_of;
pub(crate) use core::mem::needs_drop;
pub(crate) use core::mem::size_of;
pub(crate) use core::ptr::NonNull;
pub(crate) use core::ptr;
pub(crate) use core::slice;
pub(crate) use core::str;

// feature strict_provenance - `core::ptr`

#[inline(always)]
pub(crate) fn invalid_mut<T>(addr: usize) -> *mut T {
  unsafe { core::mem::transmute(addr) }
}

// feature strict_provenance - method of `*const T`

#[inline(always)]
pub(crate) fn addr<T>(p: *const T) -> usize {
  unsafe { core::mem::transmute(p) }
}

// feature ptr_mask - method of `*mut T`

#[inline(always)]
pub(crate) fn mask<T>(p: *mut T, mask: usize) -> *mut T {
  let p = p as *mut u8;
  p.wrapping_sub(addr(p) & ! mask) as *mut _
}

// feature slice_assume_init_mut - `core::mem::MaybeUninit`

#[inline(always)]
pub(crate) unsafe fn slice_assume_init_mut<T>(p: &mut [MaybeUninit<T>]) -> &mut [T] {
  let p = p as *mut _;
  let p = p as *mut _;
  unsafe { &mut *p }
}
