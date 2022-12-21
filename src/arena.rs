use crate::prelude::*;

const _: () = assert!(isize::BITS == usize::BITS);

const MAX_OBJECT_ALIGN: usize = 64;

pub struct Arena {
  chunk_offset: Cell<isize>,
  chunk_base: Cell<*mut u8>,
  total_reserved: Cell<usize>,
  // chunks: Vec<(*mut u8, Layout)>, // TODO: thin vec
}

#[derive(Clone, Copy)]
struct ChunkSizeClass(u8);

impl ChunkSizeClass {
  const MIN: Self = Self(16);
  const MAX: Self = Self(usize::BITS as u8 - 2);

  #[inline]
  fn size(self) -> usize {
    1 << self.0
  }

  #[inline]
  fn with_size_at_least(n: usize) -> Option<Self> {
    if n <= Self::MIN.size() {
      Some(Self::MIN)
    } else if n > Self::MAX.size() {
      None
    } else {
      Some(Self((usize::BITS - (n - 1).leading_zeros()) as u8))
    }
  }
}

/*
impl Drop for Arena {
  fn drop(&mut self) {
    for (chunk, layout) in self.chunks.drain(..) {
      unsafe { alloc::dealloc(chunk, layout) }
    }
  }
}
*/

impl Arena {
  pub fn new() -> Self {
    Self {
      chunk_offset: Cell::new(0),
      chunk_base: Cell::new(ptr::null_mut()),
      total_reserved: Cell::new(0),
      // chunks: Vec::new(),
    }
  }

  // # Panics
  //
  // - out of memory
  // - non-trivial drop
  // - aligned to more than 64b

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

    // We support at most 64 byte (i.e. 512 bit) alignment.

    assert!(align <= MAX_OBJECT_ALIGN);

    // Becuase leaking values is not unsafe, this requirement is not actually
    // essential. We check it anyway because it's usually a mistake.

    assert!(! mem::needs_drop::<T>());

    // For the `Layout` of `T`, it is guaranteed that
    //
    // - `align` is a power of two, and
    // - `size` rounded up to a multiple of `align` is less than or equal to
    //   `isize::MAX`.
    //
    // This is enough to ensure that the following calculations are correct and
    // don't underflow.

    let offset = self.chunk_offset.get();
    let base = self.chunk_base.get();
    let offset = offset - (size as isize);
    let offset = offset & (align_mask as isize);

    if offset < 0 {
      return self.allocate_slow::<T>();
    }

    self.chunk_offset.set(offset);

    let ptr = base.wrapping_offset(offset).cast::<MaybeUninit<T>>();

    unsafe { &mut *ptr }
  }

  // The `allocate_slow` function is just a wrapper that constructs the
  // appropriate `Layout` and jumps to `allocate_slow_layout`.

  #[cold]
  #[inline(never)]
  fn allocate_slow<T>(&self) -> &mut MaybeUninit<T> {
    let ptr = self.allocate_slow_layout(Layout::new::<T>()).cast::<MaybeUninit<T>>();

    unsafe { &mut *ptr }
  }

  // Request a chunk from the system allocator, and cut off a piece to satify
  // the current allocation.

  #[inline(never)]
  fn allocate_slow_layout(&self, layout: Layout) -> *mut u8 {
    let align = layout.align();
    let size = layout.size();
    let align_mask = ! (align - 1);

    let total_reserved = self.total_reserved.get();
    let min_chunk_size = cmp::max(size, total_reserved / 4 + 1);

    let chunk_size_class = ChunkSizeClass::with_size_at_least(min_chunk_size).unwrap();
    let chunk_size = chunk_size_class.size();
    let chunk_layout = Layout::from_size_align(chunk_size, MAX_OBJECT_ALIGN).unwrap();

    // SAFETY: `chunk_size` is positive.

    let base = unsafe { alloc::alloc(chunk_layout) };

    let offset = chunk_size as isize;
    let offset = offset - (size as isize);
    let offset = offset & (align_mask as isize);

    let ptr = base.wrapping_offset(offset);

    let total_reserved = total_reserved.checked_add(chunk_size).unwrap();

    self.chunk_offset.set(offset);
    self.chunk_base.set(base);
    self.total_reserved.set(total_reserved);
    // self.chunks.push((base, chunk_layout));

    ptr
  }
}

pub fn foo(arena: &mut Arena, x: i64) -> &mut i64 {
  arena.allocate().write(x)
}

pub fn bar(arena: &mut Arena) -> &mut i64 {
  arena.allocate().write(42)
}
