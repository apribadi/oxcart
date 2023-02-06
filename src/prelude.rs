pub(crate) extern crate alloc;
pub(crate) use core::alloc::Layout;
pub(crate) use core::cmp::max;
pub(crate) use core::convert::Infallible;
pub(crate) use core::marker::PhantomData;
pub(crate) use core::mem::MaybeUninit;
pub(crate) use core::mem::align_of;
pub(crate) use core::mem::needs_drop;
pub(crate) use core::mem::size_of;
pub(crate) use core::ptr::NonNull;
pub(crate) use core::slice;

// feature strict_provenance - `core::ptr::invalid_mut`

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
  (p as *mut u8).wrapping_sub(addr(p) & ! mask) as *mut T
}
