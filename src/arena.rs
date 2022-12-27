use crate::prelude::*;

const CHUNK_ALIGN_LOG2: u8 = 6;
const CHUNK_ALIGN: usize = 1 << CHUNK_ALIGN_LOG2;
const MIN_CHUNK_SIZE_LOG2: u8 = 16;
const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_CHUNK_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;
const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;
const MAX_OBJECT_SIZE: usize = MAX_CHUNK_SIZE;

pub struct Arena {
  total_reserved: usize,
  chunks: Vec<Chunk>,
}

pub struct ArenaAllocator<'a> {
  offset: isize,
  base: *mut u8,
  arena: &'a mut Arena,
}

pub struct ArenaSlot<'a, T>(&'a mut MaybeUninit<T>);

pub struct ArenaSliceSlot<'a, T>(&'a mut [MaybeUninit<T>]);

struct Chunk { base: *mut u8, size: usize, }

struct ChunkSizeClass(u8);

impl ChunkSizeClass {
  const MIN: Self = Self(MIN_CHUNK_SIZE_LOG2);
  const MAX: Self = Self(MAX_CHUNK_SIZE_LOG2);

  // `1 <= size <= isize::MAX`

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

impl Arena {
  pub fn new() -> Self {
    Self {
      total_reserved: 0,
      chunks: Vec::new(),
    }
  }

  pub fn reset(&mut self) {
    if self.total_reserved > 0 {
      self.reset_slow();
    }
  }

  #[inline(never)]
  #[cold]
  fn reset_slow(&mut self) {
    // SAFETY:
    //
    // - Because this method is called with `&mut self`, we know that every
    //   lifetime of a reference to a previously allocated slot has ended. It
    //   follows that it is safe to deallocate the chunks' memory.
    // - The `layout` is the same as in `alloc_chunk`, so it is valid.
    // - The `base` pointer was returned from `alloc::alloc` in `alloc_chunk`.

    self.total_reserved = 0;

    for Chunk { base, size } in self.chunks.drain(..) {
      let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

      unsafe { alloc::dealloc(base, layout) }
    }
  }

  pub fn allocator(&mut self) -> ArenaAllocator<'_> {
    self.reset();

    ArenaAllocator { offset: 0, base: ptr::null_mut(), arena: self, }
  }

  #[inline(never)]
  #[cold]
  fn alloc_chunk(&mut self, at_least: usize) -> Chunk {
    let total_reserved = self.total_reserved;

    // If we don't do any large single allocations, we'll get a sequence of
    // chunk sizes that looks like
    //
    //   1, 1, 1, 1, 2, 2, 4, 4, 8, 8, ...
    //
    // as multiples of the minimum chunk size.

    let at_least = cmp::max(at_least, total_reserved / 4 + 1);
    let size_class = ChunkSizeClass::with_size_at_least(at_least).unwrap();
    let size = size_class.size();
    let total_reserved = total_reserved.checked_add(size).unwrap();

    // SAFETY:
    //
    // - `CHUNK_ALIGN != 0`
    // - `CHUNK_ALIGN` is a power of two
    // - `size` rounded up to a multiple of `CHUNK_ALIGN` is `<= isize::MAX`

    let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

    // SAFETY:
    //
    // - `size != 0`

    let base = unsafe { alloc::alloc(layout) };

    self.total_reserved = total_reserved;
    self.chunks.push(Chunk { base, size });

    Chunk { base, size }
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    self.reset()
  }
}

impl<'a> ArenaAllocator<'a> {
  fn alloc_chunk(&mut self, at_least: usize) {
    let Chunk { base, size } = self.arena.alloc_chunk(at_least);

    self.offset = size as isize; // NB: `size <= isize::MAX`
    self.base = base;
  }

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> ArenaSlot<'a, T> {
    let align = mem::align_of::<T>();
    let size = mem::size_of::<T>();

    assert!(align <= MAX_OBJECT_ALIGN);
    assert!(size <= MAX_OBJECT_SIZE);

    let offset = self.offset;
    let base = self.base;

    let offset = offset - (size as isize);
    let offset = offset & ((! (align - 1)) as isize);

    if offset < 0 { return self.alloc_slow(); }

    self.offset = offset;

    let slot = base.wrapping_offset(offset).cast::<MaybeUninit<T>>();
    let slot = unsafe { &mut *slot };

    ArenaSlot(slot)
  }

  #[inline(never)]
  #[cold]
  fn alloc_slow<T>(&mut self) -> ArenaSlot<'a, T> {
    self.alloc_chunk(mem::size_of::<T>());
    self.alloc()
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> ArenaSliceSlot<'_, T> {
    let align = mem::align_of::<T>();
    let size_of_element = mem::size_of::<T>();
    let max_len = MAX_OBJECT_SIZE / size_of_element;

    assert!(align <= MAX_OBJECT_ALIGN);

    if len > max_len { match self.alloc_slice_slow_slice_too_long(len) { } }

    let offset = self.offset;
    let base = self.base;

    let offset = offset - ((size_of_element * len) as isize);
    let offset = offset & ((! (align - 1)) as isize);

    if offset < 0 { return self.alloc_slice_slow_alloc_chunk(len); }

    self.offset = offset;

    let slot = base.wrapping_offset(offset).cast::<MaybeUninit<T>>();
    let slot = unsafe { slice::from_raw_parts_mut(slot, len) };

    ArenaSliceSlot(slot)
  }

  #[inline(never)]
  #[cold]
  pub fn alloc_slice_slow_slice_too_long(&mut self, len: usize) -> ! {
    let _ = len;
    panic!()
  }

  #[inline(never)]
  #[cold]
  pub fn alloc_slice_slow_alloc_chunk<T>(&mut self, len: usize) -> ArenaSliceSlot<'_, T> {
    self.alloc_chunk(mem::size_of::<T>() * len);
    self.alloc_slice(len)
  }
}

impl<'a, T> ArenaSlot<'a, T> {
  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    self.0.write(value)
  }
}

impl<'a, T> ArenaSliceSlot<'a, T> {
  #[inline(always)]
  pub fn init<F>(self, mut f: F) -> &'a mut [T] where F: FnMut(usize) -> T {
    for (i, element) in self.0.iter_mut().enumerate() {
      element.write(f(i));
    }

    let slot = self.0 as *mut [MaybeUninit<T>] as *mut [T];

    unsafe { &mut *slot }
  }
}
pub fn bar<'a>(alloc: &mut ArenaAllocator<'a>, x: i64) {
  for _ in 0 .. 100 {
    let _ = alloc.alloc().init(x);
  }
}
