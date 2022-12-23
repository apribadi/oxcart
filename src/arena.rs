use crate::prelude::*;

// TODO:
//
// - smaller footprint chunks field w/o RefCell
// - configurable MIN_CHUNK_SIZE

const MIN_CHUNK_SIZE_LOG2: u8 = 16;
const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_OBJECT_ALIGN: usize = 64;
const MAX_OBJECT_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;

pub struct Arena {
  chunk_offset: Cell<isize>,
  chunk_base: Cell<*mut u8>,
  total_reserved: Cell<usize>,
  chunks: RefCell<Vec<(*mut u8, Layout)>>,
}

pub struct ArenaSlot<'a, T>(&'a mut MaybeUninit<T>);

pub struct ArenaSliceSlot<'a, T>(&'a mut [MaybeUninit<T>]);

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
      chunk_offset: Cell::new(0),
      chunk_base: Cell::new(ptr::null_mut()),
      total_reserved: Cell::new(0),
      chunks: RefCell::new(Vec::new()),
    }
  }

  #[inline(never)]
  fn add_chunk_with_size_at_least(&self, n: usize) {
    // If we don't need to do any large allocations, we'll get a sequence of
    // chunk sizes that looks like
    //
    //   1, 1, 1, 1, 2, 2, 4, 4, 8, 8, ...
    //
    // as multiples of the minimum chunk size.

    let total_reserved = self.total_reserved.get();

    let at_least = cmp::max(n, total_reserved / 4 + 1);
    let chunk_size_class = ChunkSizeClass::with_size_at_least(at_least).unwrap();
    let chunk_size = chunk_size_class.size();
    let chunk_offset = chunk_size.try_into().unwrap();
    let chunk_layout = Layout::from_size_align(chunk_size, MAX_OBJECT_ALIGN).unwrap();
    let total_reserved = total_reserved.checked_add(chunk_size).unwrap();

    // SAFETY: `ChunkSizeClass` guarantees that its associated size is
    // positive.

    let chunk_base = unsafe { alloc::alloc(chunk_layout) };

    self.chunk_offset.set(chunk_offset);
    self.chunk_base.set(chunk_base);
    self.total_reserved.set(total_reserved);
    self.chunks.borrow_mut().push((chunk_base, chunk_layout));
  }

  #[inline(always)]
  pub fn alloc<T>(&self) -> ArenaSlot<'_, T> {
    let align = mem::align_of::<T>();
    let size = mem::size_of::<T>();

    assert!(align <= MAX_OBJECT_ALIGN);
    assert!(size <= MAX_OBJECT_SIZE);

    let offset = self.chunk_offset.get();
    let base = self.chunk_base.get();
    let offset = offset - (size as isize);
    let offset = offset & ((! (align - 1)) as isize);

    if offset < 0 { return self.alloc_slow_path_add_chunk(); }

    self.chunk_offset.set(offset);

    let slot = base.wrapping_offset(offset).cast::<MaybeUninit<T>>();
    let slot = unsafe { &mut *slot };

    ArenaSlot(slot)
  }

  #[inline(never)]
  #[cold]
  fn alloc_slow_path_add_chunk<T>(&self) -> ArenaSlot<'_, T> {
    self.add_chunk_with_size_at_least(mem::size_of::<T>());
    self.alloc()
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&self, len: usize) -> ArenaSliceSlot<'_, T> {
    let align = mem::align_of::<T>();
    let element_size = mem::size_of::<T>();
    let max_len = MAX_OBJECT_SIZE / element_size;

    assert!(align <= MAX_OBJECT_ALIGN);

    if len > max_len { return self.alloc_slice_slow_path_too_long(len); }

    let size = element_size * len;
    let offset = self.chunk_offset.get();
    let base = self.chunk_base.get();
    let offset = offset - (size as isize);
    let offset = offset & ((! (align - 1)) as isize);

    if offset < 0 { return self.alloc_slice_slow_path_add_chunk(len); }

    self.chunk_offset.set(offset);

    let slot = base.wrapping_offset(offset).cast::<MaybeUninit<T>>();
    let slot = unsafe { slice::from_raw_parts_mut(slot, len) };

    ArenaSliceSlot(slot)
  }

  #[inline(never)]
  #[cold]
  pub fn alloc_slice_slow_path_too_long<T>(&self, len: usize) -> ArenaSliceSlot<'_, T> {
    let _ = len;
    panic!()
  }

  #[inline(never)]
  #[cold]
  pub fn alloc_slice_slow_path_add_chunk<T>(&self, len: usize) -> ArenaSliceSlot<'_, T> {
    self.add_chunk_with_size_at_least(mem::size_of::<T>().checked_mul(len).unwrap());
    self.alloc_slice(len)
  }

  pub fn reset(&mut self) {
    for (chunk, layout) in self.chunks.take().drain(..) {
      unsafe { alloc::dealloc(chunk, layout) }
    }
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    self.reset()
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
    for (i, p) in self.0.iter_mut().enumerate() {
      p.write(f(i));
    }

    let slot = self.0 as *mut [MaybeUninit<T>] as *mut [T];

    unsafe { &mut *slot }
  }
}

pub fn foo(arena: &mut Arena, x: i64) -> &mut i64 {
  arena.alloc().init(x)
}

pub fn bar<'a, 'b>(arena: &'a mut Arena, x: &'b [i64]) -> &'a mut [i64] {
  arena.alloc_slice(x.len()).init(|i| x[i])
}
