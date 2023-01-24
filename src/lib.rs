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

const CHUNK_ALIGN_LOG2: u8 = 6;
const CHUNK_ALIGN: usize = 1 << CHUNK_ALIGN_LOG2;

const MIN_CHUNK_SIZE_LOG2: u8 = 14;
const MIN_CHUNK_SIZE: usize = 1 << MIN_CHUNK_SIZE_LOG2;

const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_CHUNK_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;

const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;
const MAX_OBJECT_SIZE: usize = MAX_CHUNK_SIZE - mem::size_of::<Tail>();

const _: () = assert!(mem::align_of::<Tail>() <= CHUNK_ALIGN);
const _: () = assert!(mem::size_of::<Tail>() <= MIN_CHUNK_SIZE);

pub struct Arena {
  lo: *mut u8,
  hi: *mut Tail,
  total_allocated: usize,
}

pub struct Allocator<'a> {
  lo: *mut u8,
  hi: *mut u8,
  arena: &'a mut Arena,
}

// SAFETY:
//
// The `Arena` and `Allocator` types conform to the usual shared xor mutable
// discipline.

unsafe impl Send for Arena {}

unsafe impl Sync for Arena {}

unsafe impl<'a> Send for Allocator<'a> {}

unsafe impl<'a> Sync for Allocator<'a> {}

pub struct Slot<'a, T: 'a>(&'a mut MaybeUninit<T>);

pub struct SliceSlot<'a, T: 'a>(&'a mut [MaybeUninit<T>]);

#[derive(Clone, Debug)]
pub enum AllocError {
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

struct Tail(*mut u8, *mut Tail);

struct Span(*mut u8, *mut u8);

struct ChunkSizeClass(u8);

#[inline(always)]
fn ok<T>(x: Result<T, Panicked>) -> T {
  match x { Ok(t) => t, Err(e) => match e {} }
}

#[inline(always)]
fn ptr_byte_diff<T, U>(p: *const T, q: *const U) -> usize {
  p as usize - q as usize
}

#[inline(always)]
fn ptr_mask_mut<T>(p: *mut T, m: usize) -> *mut T {
  // NB: This expression preserves pointer provenance and should be optimized
  // into `p & m`.
  //
  // Once the `ptr_mask` feature is stabilized, we can just use `p.mask(m)`.

  (p as *mut u8).wrapping_sub((p as usize) & ! m) as *mut T
}

#[inline(always)]
unsafe fn dealloc_chunk_list(lo: *mut u8, hi: *mut Tail) {
  let mut lo = lo;
  let mut hi = hi;

  // SAFETY:
  //
  // - ???

  while ! hi.is_null() {
    let size = ptr_byte_diff(hi, lo) + mem::size_of::<Tail>();
    let next = unsafe { hi.read() };

    let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

    unsafe { std::alloc::dealloc(lo, layout) }

    lo = next.0;
    hi = next.1;
  }
}

impl InternalError for AllocError {
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
  fn from_target(n: usize) -> Self {
    if n <= MIN_CHUNK_SIZE {
      Self(MIN_CHUNK_SIZE_LOG2)
    } else if n > MAX_CHUNK_SIZE {
      Self(MAX_CHUNK_SIZE_LOG2)
    } else {
      Self((usize::BITS - (n - 1).leading_zeros()) as u8)
    }
  }

  // `1 <= size <= isize::MAX`

  fn size(self) -> usize {
    1 << self.0
  }
}

impl Arena {
  #[inline(always)]
  pub fn new() -> Self {
    Self {
      lo: ptr::null_mut(),
      hi: ptr::null_mut(),
      total_allocated: 0,
    }
  }

  #[inline(always)]
  pub fn allocator(&mut self) -> Allocator<'_> {
    Allocator {
      lo: self.lo,
      hi: self.hi as *mut u8,
      arena: self,
    }
  }

  #[inline(always)]
  pub fn reset(&mut self) {
    // Retain the top of the stack and dealloc every other chunk.

    let hi = self.hi;

    // SAFETY:
    //
    // - ???

    if ! hi.is_null() {
      let next = unsafe { hi.replace(Tail(ptr::null_mut(), ptr::null_mut())) };

      unsafe { dealloc_chunk_list(next.0, next.1) };
    }
  }

  #[inline(never)]
  #[cold]
  fn alloc_chunk<E>(&mut self, min_size: usize) -> Result<Span, E>
    where E: InternalError
  {
    // POSTCONDITION:
    //
    // - If `min_size <= MAX_OBJECT_SIZE`, then the returned `Span` has size
    //   at least `min_size`.

    let total_allocated = self.total_allocated;
    let target = max(min_size + mem::size_of::<Tail>(), total_allocated / 4 + 1);
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

    let hi = lo.wrapping_add(size).wrapping_sub(mem::size_of::<Tail>()) as *mut Tail;

    // SAFETY:
    //
    // - ???

    unsafe { hi.write(Tail(self.lo, self.hi)) };

    // We're past possible error conditions, so actually update `self`.

    self.lo = lo;
    self.hi = hi;
    self.total_allocated = total_allocated.saturating_add(size);

    Ok(Span(lo, hi as *mut u8))
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

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn internal_alloc<T, E>(&mut self) -> Result<Slot<'a, T>, E>
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
      let Span(lo, hi) = self.arena.alloc_chunk(size)?;
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

    Ok(Slot(slot))
  }

  #[inline(always)]
  fn internal_alloc_slice<T, E>(&mut self, len: usize) -> Result<SliceSlot<'a, T>, E>
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
      let Span(lo, hi) = self.arena.alloc_chunk(size)?;
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

    Ok(SliceSlot(slot))
  }

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    ok(self.internal_alloc())
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError> {
    self.internal_alloc()
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> SliceSlot<'a, T> {
    ok(self.internal_alloc_slice(len))
  }

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<SliceSlot<'a, T>, AllocError> {
    self.internal_alloc_slice(len)
  }

  #[inline(always)]
  pub fn with<F, A>(f: F) -> A
    where F: for<'b> FnOnce(Allocator<'b>) -> A
  {
    let mut arena = Arena::new();
    f(arena.allocator())
  }
}

impl<'a, T> Slot<'a, T> {
  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    self.0.write(value)
  }
}

impl<'a, T> SliceSlot<'a, T> {
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
