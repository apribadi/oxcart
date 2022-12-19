use crate::prelude::*;

const CHUNK_ALIGNMENT: usize = 1 << 12; // 4kb
const CHUNK_QUANTUM: usize = 1 << 16; // 64kb

pub struct Arena {
  available: Cell<isize>,
  base: Cell<*mut u8>,
}

impl Arena {
  #[inline(always)]
  pub fn allocate<T>(&self) -> &mut MaybeUninit<T> {
    // These initial expressions are all be compile-time constants, but we
    // can't use `const` bindings because the Rust compiler isn't (yet) able to
    // handle expressions with type parameters in such situations.
    // 
    // Any reasonable optimizing compiler should be able to do the requisite
    // constant propagation.

    let layout = Layout::new::<T>();
    let align = layout.align();
    let size = layout.size();
    let align_mask = ! (align - 1);

    // 4kb of alignment ought to be enough for anybody.

    assert!(align < CHUNK_ALIGNMENT);

    // For the `Layout` of `T`, it is guaranteed that
    //
    // - `align` is a power of two, and
    // - `size` rounded up to a multiple of `align` is less than or equal to
    //   `isize::MAX`.
    //
    // This is enough to ensure that the following calculations are correct and
    // don't underflow.

    let offset = self.available.get();
    let offset = offset - (size as isize);
    let offset = offset & (align_mask as isize);

    if offset < 0 { return self.allocate_slow::<T>(); }

    self.available.set(offset);

    let ptr = self.base.get();
    let ptr = ptr.wrapping_offset(offset);
    let ptr = ptr.cast::<MaybeUninit<T>>();

    unsafe { &mut *ptr }
  }

  #[inline(never)]
  pub fn allocate_slow<T>(&self) -> &mut MaybeUninit<T> {
    unimplemented!()
  }
}

pub fn foo(arena: &Arena) -> &mut i64 {
  arena.allocate().write(13i64)
}
