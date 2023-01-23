#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]

use core::alloc::Layout;
use core::cmp::max;
use core::mem::MaybeUninit;
use core::mem;
use core::slice;
use core::ptr;

const CHUNK_ALIGN: usize = 1 << CHUNK_ALIGN_LOG2;
const CHUNK_ALIGN_LOG2: u8 = 6;
const MAX_CHUNK_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;
const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;
const MAX_OBJECT_SIZE: usize = MAX_CHUNK_SIZE;
const MIN_CHUNK_SIZE: usize = 1 << MIN_CHUNK_SIZE_LOG2;
const MIN_CHUNK_SIZE_LOG2: u8 = 14;
const NULL: *mut u8 = ptr::null_mut();

pub struct Arena {
  lo: *mut u8,
  hi: *mut u8,
  total_allocated: usize,
}

pub struct ArenaAllocator<'a> {
  lo: *mut u8,
  hi: *mut u8,
  arena: &'a mut Arena,
}

// SAFETY:
//
// The `Arena` and `Arena` types conform to the usual shared xor mutable
// discipline.

unsafe impl Send for Arena {}

unsafe impl Sync for Arena {}

unsafe impl<'a> Send for ArenaAllocator<'a> {}

unsafe impl<'a> Sync for ArenaAllocator<'a> {}

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

struct Range {
  lo: *mut u8,
  hi: *mut u8,
}

struct ChunkSizeClass(u8);

#[inline(always)]
fn ok<T>(x: Result<T, Panicked>) -> T {
  match x { Ok(t) => t, Err(e) => match e {} }
}

#[inline(always)]
fn ptr_byte_diff<T>(p: *const T, q: *const T) -> usize {
  p as usize - q as usize
}

#[inline(always)]
fn ptr_mask_mut<T>(p: *mut T, m: usize) -> *mut T {
  // #![feature(ptr_mask)] => `p.mask(m)`
  p.cast::<u8>().wrapping_sub((p as usize) & ! m).cast::<T>()
}

#[inline(always)]
unsafe fn dealloc_chunk_list(lo: *mut u8, hi: *mut u8) {
  // SAFETY:
  //
  // - ???

  let mut lo = lo;
  let mut hi = hi;

  while ! hi.is_null() {
    let size = ptr_byte_diff(hi, lo) + mem::size_of::<Range>();
    let next = unsafe { hi.cast::<Range>().read() };

    let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

    unsafe { std::alloc::dealloc(lo, layout) }

    lo = next.lo;
    hi = next.hi;
  }
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
  #[cold]
  fn from_global_alloc_error(layout: Layout) -> Self {
    std::alloc::handle_alloc_error(layout)
  }

  #[inline(never)]
  #[cold]
  fn from_object_align_too_large(align: usize) -> Self {
    panic!("object align too large: {:?}", align)
  }

  #[inline(never)]
  #[cold]
  fn from_object_size_too_large(size: usize) -> Self {
    panic!("object size too large: {:?}", size)
  }

  #[inline(never)]
  #[cold]
  fn from_object_type_needs_drop() -> Self {
    panic!("object type needs drop")
  }

  #[inline(never)]
  #[cold]
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

impl Arena {
  #[inline(always)]
  pub fn new() -> Self {
    Self {
      lo: NULL,
      hi: NULL,
      total_allocated: 0,
    }
  }

  #[inline(always)]
  pub fn allocator(&mut self) -> ArenaAllocator<'_> {
    ArenaAllocator { lo: self.lo, hi: self.hi, arena: self, }
  }

  #[inline(always)]
  pub fn reset(&mut self) {
    // Retain the top of the stack, dealloc everything else.

    let hi = self.hi;

    if ! hi.is_null() {
      let next = unsafe { hi.cast::<Range>().replace(Range { lo: NULL, hi: NULL }) };

      unsafe { dealloc_chunk_list(next.lo, next.hi) };
    }
  }

  #[inline(never)]
  #[cold]
  fn alloc_chunk<E>(&mut self, min_size: usize) -> Result<Range, E>
    where E: InternalError
  {
    assert!(MIN_CHUNK_SIZE % CHUNK_ALIGN == 0);
    assert!(mem::align_of::<Range>() <= CHUNK_ALIGN);
    assert!(mem::size_of::<Range>() <= MIN_CHUNK_SIZE);

    let total_allocated = self.total_allocated;
    let target = max(min_size, total_allocated / 4 + 1);
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

    let hi = lo.wrapping_add(size).wrapping_sub(mem::size_of::<Range>());

    // SAFETY:
    //
    // - ???

    unsafe { hi.cast::<Range>().write(Range { lo: self.lo, hi: self.hi }) };

    // We're past possible error conditions, so actually update `self`.

    self.lo = lo;
    self.hi = hi;
    self.total_allocated = total_allocated.saturating_add(size);

    Ok(Range { lo, hi })
  }
}

impl Drop for Arena {
  #[inline(always)]
  fn drop(&mut self) {
    // SAFETY:
    //
    // - ???

    unsafe { dealloc_chunk_list(self.lo, self.hi) };
  }
}

impl<'a> ArenaAllocator<'a> {
  #[inline(always)]
  fn internal_alloc<T, E>(&mut self) -> Result<ArenaSlot<'a, T>, E>
    where E: InternalError
  {
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

    if size > ptr_byte_diff(self.hi, self.lo) {
      let Range { lo, hi } = self.arena.alloc_chunk(size)?;
      self.lo = lo;
      self.hi = hi;
    }

    let hi = ptr_mask_mut(self.hi.wrapping_sub(size), ! (align - 1));

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
  fn internal_alloc_slice<T, E>(&mut self, len: usize) -> Result<ArenaSliceSlot<'a, T>, E>
    where E: InternalError
  {
    let align = mem::align_of::<T>();
    let size_of_element = mem::size_of::<T>();
    let max_len = MAX_OBJECT_SIZE / size_of_element;

    if /* const */ mem::needs_drop::<T>() {
      return Err(E::from_object_type_needs_drop());
    }

    if /* const */ align > MAX_OBJECT_ALIGN {
      return Err(E::from_object_align_too_large(align));
    }

    if len > max_len {
      return Err(E::from_slice_too_long(len));
    }

    let size = size_of_element * len;

    if size > ptr_byte_diff(self.hi, self.lo) {
      let Range { lo, hi } = self.arena.alloc_chunk(size)?;
      self.lo = lo;
      self.hi = hi;
    }

    let hi = ptr_mask_mut(self.hi.wrapping_sub(size), ! (align - 1));

    // SAFETY:
    //
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    let slot: &'a mut [MaybeUninit<T>] = unsafe { slice::from_raw_parts_mut(hi.cast(), len) };

    self.hi = hi;

    Ok(ArenaSliceSlot(slot))
  }

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> ArenaSlot<'a, T> {
    ok(self.internal_alloc())
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<ArenaSlot<'a, T>, ArenaError> {
    self.internal_alloc()
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> ArenaSliceSlot<'a, T> {
    ok(self.internal_alloc_slice(len))
  }

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<ArenaSliceSlot<'a, T>, ArenaError> {
    self.internal_alloc_slice(len)
  }

  #[inline(always)]
  pub fn with<F, A>(f: F) -> A
    where F: for<'b> FnOnce(ArenaAllocator<'b>) -> A
  {
    let mut arena = Arena::new();
    f(arena.allocator())
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
  pub fn init<F>(self, mut f: F) -> &'a mut [T]
    where F: FnMut(usize) -> T
  {
    for (i, a) in self.0.iter_mut().enumerate() {
      a.write(f(i));
    }

    let slot: *mut [MaybeUninit<T>] = self.0;
    let slot: *mut [T] = slot as *mut [T];

    // SAFETY:
    //
    // - Every slice element has been initialized.

    unsafe { &mut *slot }
  }
}
