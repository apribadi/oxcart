//! TODO: writeme
//!

use core::alloc::Layout;
use core::ptr::NonNull;
use crate::ptr;

pub unsafe trait Allocator {
  //! TODO: writeme
  //!

  /// TODO: writeme
  ///

  fn alloc(&mut self, layout: Layout) -> Option<NonNull<u8>>;

  /// TODO: writeme
  ///

  unsafe fn free(&mut self, ptr: NonNull<u8>, layout: Layout);
}

/// TODO: writeme
///

#[derive(Clone, Copy)]
pub struct Global;

unsafe impl Allocator for Global {
  #[inline(always)]
  fn alloc(&mut self, layout: Layout) -> Option<NonNull<u8>> {
    if layout.size() == 0 {
      return Some(unsafe { ptr::invalid(layout.align()) });
    }

    return NonNull::new(unsafe { alloc::alloc::alloc(layout) });
  }

  #[inline(always)]
  unsafe fn free(&mut self, ptr: NonNull<u8>, layout: Layout) {
    if layout.size() == 0 {
      return;
    }

    alloc::alloc::dealloc(ptr.as_ptr(), layout);
  }
}
