use crate::prelude::*;

const CHUNK_ALIGN_LOG2: u8 = 6;
const CHUNK_ALIGN: usize = 1 << CHUNK_ALIGN_LOG2;
const MIN_CHUNK_SIZE_LOG2: u8 = 16;
const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_CHUNK_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;
const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;
const MAX_OBJECT_SIZE: usize = MAX_CHUNK_SIZE;

pub struct Arena<'a> {
  offset: usize,
  base: *mut u8,
  store: &'a mut Store,
}

pub struct ArenaSlot<'a, T>(&'a mut MaybeUninit<T>);

pub struct ArenaSliceSlot<'a, T>(&'a mut [MaybeUninit<T>]);

struct Store {
  total_reserved: usize,
  chunks: Vec<Chunk>,
}

struct Chunk {
  base: *mut u8,
  size: usize,
}

struct ChunkSizeClass(u8);

// `Arena` contains a raw pointer, so we need to add declarations for `Send`
// and `Sync`.
//
// SAFETY:
//
// ???

unsafe impl<'a> Send for Arena<'a> {}
unsafe impl<'a> Sync for Arena<'a> {}

impl ChunkSizeClass {
  const MIN: Self = Self(MIN_CHUNK_SIZE_LOG2);
  const MAX: Self = Self(MAX_CHUNK_SIZE_LOG2);

  // `1 <= size <= isize::MAX`

  fn size(self) -> usize {
    1 << self.0
  }

  fn at_least(n: usize) -> Option<Self> {
    if n <= Self::MIN.size() {
      Some(Self::MIN)
    } else if n > Self::MAX.size() {
      None
    } else {
      Some(Self((usize::BITS - (n - 1).leading_zeros()) as u8))
    }
  }
}

impl Store {
  fn new() -> Self {
    Self {
      total_reserved: 0,
      chunks: Vec::new(),
    }
  }

  fn arena(&mut self) -> Arena<'_> {
    Arena { offset: 0, base: ptr::null_mut(), store: self, }
  }

  #[inline(never)]
  #[cold]
  fn alloc_chunk(&mut self, min_size: usize) -> Chunk {
    let total_reserved = self.total_reserved;

    // If we don't allocate any large individual objects, we get a sequence of
    // chunk sizes that looks like
    //
    //   1, 1, 1, 1, 2, 2, 4, 4, 8, 8, ...
    //
    // as multiples of the minimum chunk size.

    let size_class = ChunkSizeClass::at_least(max(min_size, total_reserved / 4 + 1)).unwrap();
    let size = size_class.size();

    // SAFETY:
    //
    // - `CHUNK_ALIGN != 0`
    // - `CHUNK_ALIGN` is a power of two
    // - `size` rounded up to a multiple of `CHUNK_ALIGN` is `<= isize::MAX`

    let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

    // SAFETY:
    //
    // - `size != 0`

    let base = unsafe { std::alloc::alloc(layout) };

    if base.is_null() { match std::alloc::handle_alloc_error(layout) {} }

    self.total_reserved = total_reserved.saturating_add(size);
    self.chunks.push(Chunk { base, size });

    Chunk { base, size }
  }
}

impl Drop for Store {
  fn drop(&mut self) {
    // SAFETY:
    //
    // - Every lifetime of a reference to a previously allocated slot has
    //   ended. It follows that it is safe to deallocate the chunks' memory.
    // - The `layout` is the same as in `alloc_chunk`, so it has a valid size
    //   and alignment.
    // - The `base` pointer was returned from `std::alloc::alloc` in
    //   `alloc_chunk` and hasn't been deallocated yet.

    for Chunk { base, size } in self.chunks.drain(..) {
      let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

      unsafe { std::alloc::dealloc(base, layout) }
    }
  }
}

impl<'a> Arena<'a> {
  fn alloc_chunk(&mut self, min_size: usize) {
    let Chunk { base, size } = self.store.alloc_chunk(min_size);

    self.offset = size;
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

    if size > offset { return self.alloc_cold(); }

    let offset = (offset - size) & ! (align - 1);

    self.offset = offset;

    let slot = base.wrapping_add(offset).cast::<MaybeUninit<T>>();
    let slot = unsafe { &mut *slot };

    ArenaSlot(slot)
  }

  #[inline(never)]
  #[cold]
  fn alloc_cold<T>(&mut self) -> ArenaSlot<'a, T> {
    self.alloc_chunk(mem::size_of::<T>());
    self.alloc()
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> ArenaSliceSlot<'a, T> {
    let align = mem::align_of::<T>();
    let size_of_element = mem::size_of::<T>();
    let max_len = MAX_OBJECT_SIZE / size_of_element;

    assert!(align <= MAX_OBJECT_ALIGN);

    if len > max_len { match self.alloc_slice_cold_slice_too_long(len) {} }

    let offset = self.offset;
    let base = self.base;
    let size = size_of_element * len;

    if size > offset { return self.alloc_slice_cold_alloc_chunk(len); }

    let offset = (offset - size) & ! (align - 1);

    self.offset = offset;

    let slot = base.wrapping_add(offset).cast::<MaybeUninit<T>>();
    let slot = unsafe { slice::from_raw_parts_mut(slot, len) };

    ArenaSliceSlot(slot)
  }

  #[inline(never)]
  #[cold]
  fn alloc_slice_cold_slice_too_long(&mut self, len: usize) -> ! {
    let _ = len;
    panic!()
  }

  #[inline(never)]
  #[cold]
  fn alloc_slice_cold_alloc_chunk<T>(&mut self, len: usize) -> ArenaSliceSlot<'a, T> {
    self.alloc_chunk(mem::size_of::<T>() * len);
    self.alloc_slice(len)
  }

  #[inline(always)]
  pub fn with<F, A>(f: F) -> A where for<'b> F: FnOnce(Arena<'b>) -> A {
    let mut store = Store::new();
    f(store.arena())
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
    for (i, a) in self.0.iter_mut().enumerate() {
      a.write(f(i));
    }

    // We can use `mem::slice_assume_init_mut` after it's stabilized.

    let slot = self.0 as *mut [MaybeUninit<T>] as *mut [T];

    unsafe { &mut *slot }
  }
}
