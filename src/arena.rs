use crate::prelude::*;

const _: () = assert!(isize::BITS == usize::BITS);

const CHUNK_ALIGN: usize = 1 << 6; // 64b
const CHUNK_QUANTUM: usize = 1 << 16; // 64kb

pub struct Arena {
  chunk_remaining: isize,
  chunk_base: *mut u8,
  chunk_size_index: u8,
}


#[derive(Clone, Copy)]
struct ChunkSizeClass(u8);

impl ChunkSizeClass {

  const MIN: Self = Self(16);
  const MAX: Self = Self(usize::BITS as u8 - 2);

  fn size(self) -> usize {
    1 << self.0
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    let _ = self;
    // TODO: free all chunks.
  }
}

impl Arena {

  pub fn new() -> Self {
    Self {
      chunk_remaining: 0,
      chunk_base: core::ptr::null_mut(),
      chunk_size_index: 0,
    }
  }

  //
  // # Panics
  // - out of memory
  // - non-trivial drop
  // - aligned to more than 64b

  #[inline(always)]
  pub fn allocate<T>(&mut self) -> &mut MaybeUninit<T> {
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

    // We support at most 64 byte (i.e. 512 bit) alignment.

    assert!(align <= CHUNK_ALIGN);

    // This requirement is not essential because leaking values is not unsafe,
    // but allocating values with a non-trivial `drop` is usually a mistake.

    assert!(! needs_drop::<T>());

    // For the `Layout` of `T`, it is guaranteed that
    //
    // - `align` is a power of two, and
    // - `size` rounded up to a multiple of `align` is less than or equal to
    //   `isize::MAX`.
    //
    // This is enough to ensure that the following calculations are correct and
    // don't underflow.

    let offset = self.chunk_remaining;
    let offset = offset - (size as isize);
    let offset = offset & (align_mask as isize);

    if offset < 0 {
      return self.allocate_slow::<T>();
    }

    self.chunk_remaining = offset;

    let ptr = self.chunk_base;
    let ptr = ptr.wrapping_offset(offset);
    let ptr = ptr.cast::<MaybeUninit<T>>();

    unsafe { &mut *ptr }
  }

  // The `allocate_slow` function is just a wrapper that constructs the
  // appropriate `Layout` and jumps to `allocate_slow_layout`.

  #[cold]
  #[inline(never)]
  fn allocate_slow<T>(&mut self) -> &mut MaybeUninit<T> {
    let ptr = self.allocate_slow_layout(Layout::new::<T>());
    let ptr = ptr.cast::<MaybeUninit<T>>();
    unsafe { &mut *ptr }
  }

  // Request a chunk from the system allocator, and cut off a piece to satify
  // the current allocation.

  #[inline(never)]
  fn allocate_slow_layout(&mut self, layout: Layout) -> *mut u8 {
    let align = layout.align();
    let size = layout.size();
    let align_mask = ! (align - 1);

    let chunk_size_index = self.chunk_size_index;

    // The sequence of chunk sizes as a multiple of `CHUNK_QUANTUM` is
    //
    //   1, 1, 1, 1, 2, 2, 4, 4, 8, 8, ...

    let chunk_size =
      if chunk_size_index <= 1 {
        CHUNK_QUANTUM
      } else {
        CHUNK_QUANTUM << ((chunk_size_index - 2) >> 1)
      };

    // unless the current allocation requires a larger size, in which case we
    // round up to a multiple of `CHUNK_QUANTUM`.

    let chunk_size =
      if size <= chunk_size {
        chunk_size
      } else {
        (size + (CHUNK_QUANTUM - 1)) & ! (CHUNK_QUANTUM - 1)
      };

    assert!(chunk_size >= size);

    let chunk_layout = Layout::from_size_align(chunk_size, CHUNK_ALIGN).unwrap();

    // SAFETY: `chunk_layout.size()` (`== chunk_size`) is positive.

    let chunk_base = unsafe { std::alloc::alloc(chunk_layout) };

    let offset = chunk_size as isize;
    let offset = offset - (size as isize);
    let offset = offset & (align_mask as isize);

    let ptr = chunk_base.wrapping_offset(offset);

    self.chunk_remaining = offset;
    self.chunk_base = chunk_base;
    self.chunk_size_index = chunk_size_index + 1;

    ptr
  }
}

pub fn foo(arena: &mut Arena, x: i64) -> &mut i64 {
  arena.allocate().write(x)
}

pub fn bar(arena: &mut Arena, x: Vec<i64>) -> &mut Vec<i64> {
  arena.allocate().write(x)
}
