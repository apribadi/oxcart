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
const MIN_CHUNK_SIZE: usize = 1 << MIN_CHUNK_SIZE_LOG2;
const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_CHUNK_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;
const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;
const MAX_OBJECT_SIZE: usize = MAX_CHUNK_SIZE;

pub struct ArenaStorage {
  average: usize,
  capacity: usize,
  chunks: Vec<Chunk>,
}

pub struct Arena<'a> {
  lo: *mut u8,
  hi: *mut u8,
  storage: &'a mut ArenaStorage,
}

// SAFETY:
//
// The `ArenaStorage` and `Arena` types conform to the usual shared xor mutable
// discipline.

unsafe impl Send for ArenaStorage {}

unsafe impl Sync for ArenaStorage {}

unsafe impl<'a> Send for Arena<'a> {}

unsafe impl<'a> Sync for Arena<'a> {}

pub struct ArenaSlot<'a, T: 'a>(&'a mut MaybeUninit<T>);

pub struct ArenaSliceSlot<'a, T: 'a>(&'a mut [MaybeUninit<T>]);

#[derive(Clone, Debug)]
pub enum ArenaError {
  GlobalAllocError,
  ObjectAlignTooLarge,
  ObjectSizeTooLarge,
  ObjectTypeNeedsDrop,
  SliceTooLong,
}

enum Panicked {}

trait InternalError {
  fn from_global_alloc_error(layout: Layout) -> Self;
  fn from_object_align_too_large(align: usize) -> Self;
  fn from_object_size_too_large(size: usize) -> Self;
  fn from_object_type_needs_drop() -> Self;
  fn from_slice_too_long(len: usize) -> Self;
}

struct Chunk {
  lo: *mut u8,
  hi: *mut u8,
}

struct ChunkSizeClass(u8);

#[inline(always)]
#[cold]
fn cold() {}

#[inline(always)]
fn unlikely(p: bool) -> bool {
  if p { cold() }
  p
}

#[inline(always)]
fn ok<T>(x: Result<T, Panicked>) -> T {
  match x { Ok(t) => t, Err(e) => match e {} }
}

impl InternalError for ArenaError {
  #[inline(always)]
  fn from_global_alloc_error(_: Layout) -> Self {
    Self::GlobalAllocError
  }

  #[inline(always)]
  fn from_object_align_too_large(_: usize) -> Self {
    Self::ObjectAlignTooLarge
  }

  #[inline(always)]
  fn from_object_size_too_large(_: usize) -> Self {
    Self::ObjectSizeTooLarge
  }

  #[inline(always)]
  fn from_object_type_needs_drop() -> Self {
    Self::ObjectTypeNeedsDrop
  }

  #[inline(always)]
  fn from_slice_too_long(_: usize) -> Self {
    Self::SliceTooLong
  }
}

impl InternalError for Panicked {
  #[inline(never)]
  fn from_global_alloc_error(layout: Layout) -> Self {
    std::alloc::handle_alloc_error(layout)
  }

  #[inline(never)]
  fn from_object_align_too_large(align: usize) -> Self {
    panic!("object align too large: {:?}", align)
  }

  #[inline(never)]
  fn from_object_size_too_large(size: usize) -> Self {
    panic!("object size too large: {:?}", size)
  }

  #[inline(never)]
  fn from_object_type_needs_drop() -> Self {
    panic!("object type needs drop")
  }

  #[inline(never)]
  fn from_slice_too_long(len: usize) -> Self {
    panic!("slice too long: {:?}", len)
  }
}

impl ChunkSizeClass {
  const MIN: Self = Self(MIN_CHUNK_SIZE_LOG2);
  const MAX: Self = Self(MAX_CHUNK_SIZE_LOG2);

  // `1 <= size <= isize::MAX`

  fn size(self) -> usize {
    1 << self.0
  }

  fn from_target(n: usize) -> Self {
    if n <= Self::MIN.size() {
      Self::MIN
    } else if n > Self::MAX.size() {
      Self::MAX
    } else {
      Self((usize::BITS - (n - 1).leading_zeros()) as u8)
    }
  }
}

impl ArenaStorage {
  #[inline]
  pub fn new() -> Self {
    Self {
      average: MIN_CHUNK_SIZE,
      capacity: 0,
      chunks: Vec::new(),
    }
  }

  #[inline]
  pub fn arena(&mut self) -> Arena<'_> {
    self.reset();

    Arena {
      lo: ptr::invalid_mut(0),
      hi: ptr::invalid_mut(0),
      storage: self,
    }
  }

  #[inline]
  pub fn reset(&mut self) {
    if self.capacity > 0 {
      self.internal_reset()
    }
  }

  #[inline(never)]
  fn internal_reset(&mut self) {
    let average = self.average;
    let capacity = self.capacity;

    self.average = average / 2 + capacity / 2;
    self.capacity = 0;

    let chunks = mem::replace(&mut self.chunks, Vec::new());

    // SAFETY:
    //
    // - Because this method takes a mutable reference, every lifetime of a
    //   reference to a previously allocated slot has ended. It follows that it
    //   is safe to deallocate the chunks' memory.
    // - The `layout` is the same as in `alloc_chunk`, so it has a valid size
    //   and alignment.
    // - The `lo` pointer was returned from `std::alloc::alloc` in
    //   `alloc_chunk` and hasn't been deallocated yet.

    for Chunk { lo, hi } in chunks.into_iter() {
      let size = hi.addr() - lo.addr();
      let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

      unsafe { std::alloc::dealloc(lo, layout) }
    }
  }

  #[inline(never)]
  fn alloc_chunk<E: InternalError>(&mut self, min_size: usize) -> Result<Chunk, E> {
    // POSTCONDITION:
    //
    // - If `min_size <= MAX_OBJECT_SIZE`, then the returned `Chunk` has size
    //   `>= min_size`.

    let average = self.average;
    let capacity = self.capacity;

    // If we don't allocate any large individual objects, we get a sequence of
    // chunk sizes that looks like
    //
    //   1, 1, 1, 1, 2, 2, 4, 4, 8, 8, ...
    //
    // as multiples of the minimum chunk size.

    let target_0 = min_size;
    let target_1 = average / 4;
    let target_2 = capacity / 4 + 1;
    let target = max(max(target_0, target_1), target_2);

    let size_class = ChunkSizeClass::from_target(target);
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

    if lo.is_null() { return Err(E::from_global_alloc_error(layout)); }

    let hi = lo.wrapping_add(size);

    // We're past possible error conditions, so actually update self.

    // TODO: `push` might fail.

    self.capacity = capacity.saturating_add(size);
    self.chunks.push(Chunk { lo, hi });

    Ok(Chunk { lo, hi })
  }
}

impl Drop for ArenaStorage {
  #[inline]
  fn drop(&mut self) {
    self.reset()
  }
}

impl<'a> Arena<'a> {
  #[inline(always)]
  fn internal_alloc<T, E: InternalError>(&mut self) -> Result<ArenaSlot<'a, T>, E> {
    let align = mem::align_of::<T>();
    let size = mem::size_of::<T>();

    if /* const */ mem::needs_drop::<T>() {
      return Err(E::from_object_type_needs_drop());
    }

    if /* const */ align > MAX_OBJECT_ALIGN {
      return Err(E::from_object_align_too_large(align));
    }

    if /* const */ size > MAX_OBJECT_SIZE {
      return Err(E::from_object_size_too_large(size));
    }

    if unlikely(size > self.hi.addr() - self.lo.addr()) {
      let Chunk { lo, hi } = self.storage.alloc_chunk(size)?;
      self.lo = lo;
      self.hi = hi;
    }

    let hi = self.hi.wrapping_sub(size).mask(! (align - 1));

    // SAFETY:
    //
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    let slot: &'a mut MaybeUninit<T> = unsafe { &mut *hi.cast() };

    self.hi = hi;

    Ok(ArenaSlot(slot))
  }

  #[inline(always)]
  fn internal_alloc_slice<T, E: InternalError>(&mut self, len: usize) -> Result<ArenaSliceSlot<'a, T>, E> {
    let align = mem::align_of::<T>();
    let size_of_element = mem::size_of::<T>();
    let max_len = MAX_OBJECT_SIZE / size_of_element;

    if /* const */ mem::needs_drop::<T>() {
      return Err(E::from_object_type_needs_drop());
    }

    if /* const */ align > MAX_OBJECT_ALIGN {
      return Err(E::from_object_align_too_large(align));
    }

    if unlikely(len > max_len) {
      return Err(E::from_slice_too_long(len));
    }

    let size = size_of_element * len;

    if unlikely(size > self.hi.addr() - self.lo.addr()) {
      let Chunk { lo, hi } = self.storage.alloc_chunk(size)?;
      self.lo = lo;
      self.hi = hi;
    }

    let hi = self.hi.wrapping_sub(size).mask(! (align - 1));

    // SAFETY:
    //
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    let slot: &'a mut [MaybeUninit<T>] = unsafe { slice::from_raw_parts_mut(hi.cast(), len) };

    self.hi = hi;

    Ok(ArenaSliceSlot(slot))
  }

  #[inline]
  pub fn alloc<T>(&mut self) -> ArenaSlot<'a, T> {
    ok(self.internal_alloc())
  }

  #[inline]
  pub fn try_alloc<T>(&mut self) -> Result<ArenaSlot<'a, T>, ArenaError> {
    self.internal_alloc()
  }

  #[inline]
  pub fn alloc_slice<T>(&mut self, len: usize) -> ArenaSliceSlot<'a, T> {
    ok(self.internal_alloc_slice(len))
  }

  #[inline]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<ArenaSliceSlot<'a, T>, ArenaError> {
    self.internal_alloc_slice(len)
  }

  #[inline]
  pub fn with<F, A>(f: F) -> A where for<'b> F: FnOnce(Arena<'b>) -> A {
    let mut storage = ArenaStorage::new();
    f(storage.arena())
  }
}

impl<'a, T> ArenaSlot<'a, T> {
  #[inline]
  pub fn init(self, value: T) -> &'a mut T {
    self.0.write(value)
  }
}

impl<'a, T> ArenaSliceSlot<'a, T> {
  #[inline]
  pub fn init<F>(self, mut f: F) -> &'a mut [T] where F: FnMut(usize) -> T {
    for (i, a) in self.0.iter_mut().enumerate() {
      a.write(f(i));
    }

    // SAFETY:
    //
    // - Every slice element has been initialized.

    unsafe { &mut *(self.0 as *mut [MaybeUninit<T>] as *mut [T]) }
  }
}
