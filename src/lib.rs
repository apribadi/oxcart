#![feature(strict_provenance)]
#![feature(ptr_mask)]

use core::alloc::Layout;
use core::cmp::max;
use core::mem::MaybeUninit;
use core::mem;
use core::slice;
use core::ptr;

const CHUNK_ALIGN_LOG2: u8 = 6;
const CHUNK_ALIGN: usize = 1 << CHUNK_ALIGN_LOG2;
const MIN_CHUNK_SIZE_LOG2: u8 = 16;
const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_CHUNK_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;
const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;
const MAX_OBJECT_SIZE: usize = MAX_CHUNK_SIZE;

pub struct ArenaStorage {
  total_reserved: usize,
  chunks: Vec<Chunk>,
}

unsafe impl Send for ArenaStorage {}

unsafe impl Sync for ArenaStorage {}

pub struct Arena<'a> {
  lo: *mut u8,
  hi: *mut u8,
  storage: &'a mut ArenaStorage,
}

unsafe impl<'a> Send for Arena<'a> {}

unsafe impl<'a> Sync for Arena<'a> {}

pub struct ArenaSlot<'a, T>(&'a mut MaybeUninit<T>);

pub struct ArenaSliceSlot<'a, T>(&'a mut [MaybeUninit<T>]);

struct Chunk {
  lo: *mut u8,
  hi: *mut u8,
}

struct ChunkSizeClass(u8);

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

impl ArenaStorage {
  pub fn new() -> Self {
    Self {
      total_reserved: 0,
      chunks: Vec::new(),
    }
  }

  pub fn arena(&mut self) -> Arena<'_> {
    Arena {
      lo: ptr::invalid_mut(0),
      hi: ptr::invalid_mut(0),
      storage: self,
    }
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

    let lo = unsafe { std::alloc::alloc(layout) };

    if lo.is_null() { match std::alloc::handle_alloc_error(layout) {} }

    let hi = lo.wrapping_add(size);

    self.total_reserved = total_reserved.saturating_add(size);
    self.chunks.push(Chunk { lo, hi });

    Chunk { lo, hi }
  }
}

impl Drop for ArenaStorage {
  fn drop(&mut self) {
    // SAFETY:
    //
    // - Every lifetime of a reference to a previously allocated slot has
    //   ended. It follows that it is safe to deallocate the chunks' memory.
    // - The `layout` is the same as in `alloc_chunk`, so it has a valid size
    //   and alignment.
    // - The `lo` pointer was returned from `std::alloc::alloc` in
    //   `alloc_chunk` and hasn't been deallocated yet.

    for Chunk { lo, hi } in self.chunks.drain(..) {
      let size = hi.addr() - lo.addr();
      let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

      unsafe { std::alloc::dealloc(lo, layout) }
    }
  }
}

impl<'a> Arena<'a> {
  #[inline(always)]
  pub fn alloc<T>(&mut self) -> ArenaSlot<'a, T> {
    let align = mem::align_of::<T>();
    let size = mem::size_of::<T>();

    assert!(align <= MAX_OBJECT_ALIGN);
    assert!(size <= MAX_OBJECT_SIZE);

    if size > self.hi.addr() - self.lo.addr() {
      let Chunk { lo, hi } = self.storage.alloc_chunk(size);
      self.lo = lo;
      self.hi = hi;
    }

    let hi = self.hi.wrapping_sub(size).mask(! (align - 1));
    let slot = unsafe { &mut *hi.cast() };

    self.hi = hi;

    ArenaSlot(slot)
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> ArenaSliceSlot<'a, T> {
    let align = mem::align_of::<T>();
    let size_of_element = mem::size_of::<T>();
    let max_len = MAX_OBJECT_SIZE / size_of_element;

    assert!(align <= MAX_OBJECT_ALIGN);

    if len > max_len { match self.alloc_slice_cold_slice_too_long(len) {} }

    let size = size_of_element * len;

    if size > self.hi.addr() - self.lo.addr() {
      let Chunk { lo, hi } = self.storage.alloc_chunk(size);
      self.lo = lo;
      self.hi = hi;
    }

    let hi = self.hi.wrapping_sub(size).mask(! (align - 1));
    let slot = hi.cast::<MaybeUninit<T>>();
    let slot = unsafe { slice::from_raw_parts_mut(slot, len) };

    self.hi = hi;

    ArenaSliceSlot(slot)
  }

  #[inline(never)]
  #[cold]
  fn alloc_slice_cold_slice_too_long(&mut self, len: usize) -> ! {
    let _ = len;
    panic!()
  }

  #[inline(always)]
  pub fn with<F, A>(f: F) -> A where for<'b> F: FnOnce(Arena<'b>) -> A {
    let mut storage = ArenaStorage::new();
    f(storage.arena())
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
