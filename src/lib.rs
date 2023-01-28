//! An arena allocator.
//!
//! # Example
//!
//! ```
//! let mut arena = oxcart::Arena::new();
//! let mut allocator = arena.allocator();
//! let x: &mut u64 = allocator.alloc().init(42);
//! *x += 1;
//! assert!(*x == 43);
//! arena.reset();
//! let mut allocator = arena.allocator();
//! let y: &mut [u64] = allocator.alloc_slice(100).init(|i| i as u64);
//! assert!(y.iter().sum::<u64>() == 4950);
//! ```

#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]

extern crate alloc;

use core::alloc::Layout;
use core::cmp::max;
use core::mem::MaybeUninit;
use core::mem::align_of;
use core::mem::needs_drop;
use core::mem::size_of;
use core::ptr::null_mut;
use core::slice;

const MIN_CHUNK_ALIGN_LOG2: u8 = 6;
const MIN_CHUNK_ALIGN: usize = 1 << MIN_CHUNK_ALIGN_LOG2;

const CHUNK_ALIGN_LOG2: u8 = 6;
const CHUNK_ALIGN: usize = 1 << CHUNK_ALIGN_LOG2;

const MIN_CHUNK_SIZE_LOG2: u8 = 14;
const MIN_CHUNK_SIZE: usize = 1 << MIN_CHUNK_SIZE_LOG2;

/// The maximum supported alignment for any object in the arena.

pub const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;

const _: () = assert!(align_of::<Tail>() <= CHUNK_ALIGN);
const _: () = assert!(size_of::<Tail>() <= MIN_CHUNK_SIZE);

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

/// A reference to an uninitialized slot in the arena.

pub struct Slot<'a, T: 'a + ?Sized>(pub &'a mut T);

/// A cause of an allocation failure.

#[derive(Clone, Debug)]
pub struct AllocError {}

enum Panicked {}

enum InternalError {
  GlobalAllocError(Layout),
  LayoutError,
  SliceTooLong(usize),
  TypeAlignTooLarge(usize),
  TypeNeedsDrop,
}

trait FromInternalError {
  fn from(_: InternalError) -> Self;
}

struct Tail(*mut u8, *mut Tail);

struct Span(*mut u8, *mut u8);

#[inline(always)]
const fn align_up(size: usize, align: usize) -> usize {
  // This assumes that `align` is a power of two.  In some cases, the result
  // will overflow to zero.

  size.wrapping_add(align).wrapping_sub(1) & ! (align - 1)
}

#[inline(always)]
fn unwrap<T>(x: Result<T, Panicked>) -> T {
  match x { Ok(t) => t, Err(e) => match e {} }
}

#[inline(always)]
fn ptr_addr<T>(p: *const T) -> usize {
  p as usize
}

#[inline(always)]
fn ptr_mask_mut<T>(p: *mut T, m: usize) -> *mut T {
  // This expression preserves pointer provenance and should be optimized into
  // `p & m`.
  //
  // Once the `ptr_mask` feature is stabilized, we can just use `p.mask(m)`.

  (p as *mut u8).wrapping_sub((p as usize) & ! m) as *mut T
}

unsafe fn dealloc_chunk_list(lo: *mut u8, hi: *mut Tail) {
  let mut lo = lo;
  let mut hi = hi;

  while ! hi.is_null() {
    let size = ptr_addr(hi) - ptr_addr(lo) + size_of::<Tail>();
    let next = unsafe { hi.read() };

    let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

    unsafe { alloc::alloc::dealloc(lo, layout) }

    lo = next.0;
    hi = next.1;
  }
}

impl FromInternalError for AllocError {
  #[inline(always)]
  fn from(_: InternalError) -> Self {
    Self {}
  }
}

impl FromInternalError for Panicked {
  #[inline(never)]
  #[cold]
  fn from(e: InternalError) -> Self {
    match e {
      InternalError::GlobalAllocError(layout) => alloc::alloc::handle_alloc_error(layout),
      InternalError::LayoutError => panic!("layout error"),
      InternalError::SliceTooLong(len) => panic!("slice too long: {len:?}"),
      InternalError::TypeAlignTooLarge(align) => panic!("type align too large: {align:?}"),
      InternalError::TypeNeedsDrop => panic!("type needs drop"),
    }
  }
}

impl Arena {
  /// Creates a new arena.

  #[inline(always)]
  pub fn new() -> Self {
    Self {
      lo: null_mut(),
      hi: null_mut(),
      total_allocated: 0,
    }
  }

  /// Creates a handle with which to allocate from the arena. Allocated objects
  /// are live for the lifetime of this mutable borrow.

  #[inline(always)]
  pub fn allocator(&mut self) -> Allocator<'_> {
    Allocator {
      lo: self.lo,
      hi: self.hi as *mut u8,
      arena: self,
    }
  }

  /// Deallocates all but one chunk of memory. Calling this method (or, indeed,
  /// any method) on the arena implies that the lifetime of any previously
  /// allocated object has ended.

  pub fn reset(&mut self) {
    // Retain the top of the stack and dealloc every other chunk.

    let hi = self.hi;

    if ! hi.is_null() {
      let next = unsafe { hi.replace(Tail(null_mut(), null_mut())) };

      unsafe { dealloc_chunk_list(next.0, next.1) };
    }
  }

  #[inline(never)]
  #[cold]
  fn alloc_chunk_for<E>(&mut self, object_layout: Layout) -> Result<Span, E>
    where E: FromInternalError
  {
    // POST-CONDITIONS:
    //
    // If this method is successful, then a new chunk has been allocated and
    //
    // - the chunk has been pushed onto the arena's stack,
    // - the chunk is aligned to at least `MIN_CHUNK_ALIGN`, and
    // - the chunk can accommodate a slot with layout `object_layout`.

    const _: () = assert!(align_of::<Tail>() <= MIN_CHUNK_ALIGN);
    const _: () = assert!(MIN_CHUNK_SIZE % MIN_CHUNK_ALIGN == 0);
    const _: () = assert!(MIN_CHUNK_SIZE <= isize::MAX as usize);

    let total_allocated = self.total_allocated;

    let object_size = object_layout.size();
    let object_align = object_layout.align();

    // The chunk size we'd like to allocate, if the object will fit in it.  It
    // is always a power of two `<= 0b0100...`.

    let size_0 = total_allocated / 4 + 1;
    let size_0 = 1 << (usize::BITS - (size_0 - 1).leading_zeros());
    let size_0 = max(size_0, MIN_CHUNK_SIZE);

    // The size of any `Layout` is guaranteed to be `<= isize::MAX`. It follows
    // that `size_1` does not overflow `usize`.

    let size_1 = align_up(object_size, align_of::<Tail>()) + size_of::<Tail>();

    let size = max(size_0, size_1);
    let align = max(object_align, MIN_CHUNK_ALIGN);

    // We can construct a valid `Layout` if and only if `size` rounded up to
    // `align` does not overflow and is `<= isize::MAX`.

    if size > isize::MAX as usize - (align - 1) {
      return Err(E::from(InternalError::LayoutError));
    }

    // SAFETY:
    //
    // - `align != 0`
    // - `align` is a power of two
    // - `size` rounded up to a multiple of `align` is `<= isize::MAX`

    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    // SAFETY:
    //
    // - `size != 0`

    let lo = unsafe { alloc::alloc::alloc(layout) };

    if lo.is_null() {
      return Err(E::from(InternalError::GlobalAllocError(layout)));
    }

    // The earlier computations of `size` and `align` guarantee both that the
    // chunk is aligned to at least `align_of::<Tail>()` and that the size is a
    // multiple of `align_of::<Tail>(), so we can place the tail at the very
    // end of the chunk.

    let hi = lo.wrapping_add(size).wrapping_sub(size_of::<Tail>()) as *mut Tail;

    // SAFETY:
    //
    // - `hi` is valid and aligned for writing a `Tail`.

    unsafe { hi.write(Tail(self.lo, self.hi)) };

    // We're past possible error conditions, so we should actually update
    // `self`.

    self.lo = lo;
    self.hi = hi;
    self.total_allocated = total_allocated.saturating_add(size);

    Ok(Span(lo, hi as *mut u8))
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe { dealloc_chunk_list(self.lo, self.hi) };
  }
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn internal_alloc<T, E>(&mut self) -> Result<Slot<'a, MaybeUninit<T>>, E>
    where E: FromInternalError
  {
    let layout = Layout::new::<T>();
    let size = layout.size();
    let align = layout.align();

    if /* const */ needs_drop::<T>() {
      return Err(E::from(InternalError::TypeNeedsDrop));
    }

    // TODO: find a more efficient sequence for the slow arbitrary alignment
    // case.

    if
      size > ptr_addr(self.hi) - ptr_addr(self.lo) || (
        align > MIN_CHUNK_ALIGN && (
          self.lo > ptr_mask_mut(self.hi.wrapping_sub(size), ! (align - 1))))
    {
      let Span(lo, hi) = self.arena.alloc_chunk_for::<E>(layout)?;
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
  fn internal_alloc_slice<T, E>(&mut self, len: usize) -> Result<Slot<'a, [MaybeUninit<T>]>, E>
    where E: FromInternalError
  {
    let size_of_element = size_of::<T>();
    let align = align_of::<T>();

    let max_len = isize::MAX as usize / size_of_element;

    if /* const */ needs_drop::<T>() {
      return Err(E::from(InternalError::TypeNeedsDrop));
    }

    if /* const */ align > MAX_OBJECT_ALIGN {
      return Err(E::from(InternalError::TypeAlignTooLarge(align)));
    }

    if len > max_len {
      return Err(E::from(InternalError::SliceTooLong(len)));
    }

    let size = size_of_element * len;

    if size > ptr_addr(self.hi) - ptr_addr(self.lo) {
      let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
      let Span(lo, hi) = self.arena.alloc_chunk_for::<E>(layout)?;
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

    Ok(Slot(slot))
  }

  /// Allocates a slot for a single object.
  ///
  /// # Panics
  ///
  /// - ???

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, MaybeUninit<T>> {
    unwrap(self.internal_alloc())
  }

  /// Allocates a slot for a single object.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc`](Self::alloc).

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, MaybeUninit<T>>, AllocError> {
    self.internal_alloc()
  }

  /// Allocates a slot for a slice of the given length.
  ///
  /// # Panics
  ///
  /// - ???

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [MaybeUninit<T>]> {
    unwrap(self.internal_alloc_slice(len))
  }

  /// Allocates a slot for a slice of the given length.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc_slice`](Self::alloc_slice).

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [MaybeUninit<T>]>, AllocError> {
    self.internal_alloc_slice(len)
  }
}

impl<'a, T> Slot<'a, MaybeUninit<T>> {
  /// Initializes the object with the given value.

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    self.0.write(value)
  }
}

impl<'a, T> Slot<'a, [MaybeUninit<T>]> {
  /// Initializes the slice with values produced by calling the given function
  /// with each index in order.

  #[inline(always)]
  pub fn init<F>(self, f: F) -> &'a mut [T]
    where F: FnMut(usize) -> T
  {
    let mut f = f;

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

#[repr(align(128))]
pub struct BigAlign([u64; 16]);

pub fn foo<'a>(allocator: &mut Allocator<'a>, count: usize) {
  for i in 0 .. count {
    allocator.alloc().init(i as u64);
  }
}

pub fn bar<'a>(allocator: &mut Allocator<'a>, count: usize) {
  for i in 0 .. count {
    allocator.alloc().init(BigAlign([i as u64; 16]));
  }
}
