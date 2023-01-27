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

const CHUNK_ALIGN_LOG2: u8 = 6;
const CHUNK_ALIGN: usize = 1 << CHUNK_ALIGN_LOG2;

const MIN_CHUNK_SIZE_LOG2: u8 = 14;
const MIN_CHUNK_SIZE: usize = 1 << MIN_CHUNK_SIZE_LOG2;

const MAX_CHUNK_SIZE_LOG2: u8 = usize::BITS as u8 - 2;
const MAX_CHUNK_SIZE: usize = 1 << MAX_CHUNK_SIZE_LOG2;

/// The maximum supported alignment for any object in the arena.

pub const MAX_OBJECT_ALIGN: usize = CHUNK_ALIGN;

/// The maximum supported size for any object in the arena.

pub const MAX_OBJECT_SIZE: usize = MAX_CHUNK_SIZE - size_of::<Tail>();

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
#[non_exhaustive]
pub enum AllocError {
  GlobalAllocError,
  SliceTooLong,
  TypeAlignTooLarge,
  TypeNeedsDrop,
  TypeSizeTooLarge,
}

enum Panicked {}

trait InternalError {
  fn from_global_alloc_error(layout: Layout) -> Self;
  fn from_type_align_too_large(align: usize) -> Self;
  fn from_type_size_too_large(size: usize) -> Self;
  fn from_type_needs_drop() -> Self;
  fn from_slice_too_long(len: usize) -> Self;
}

struct Tail(*mut u8, *mut Tail);

struct Span(*mut u8, *mut u8);

#[inline(always)]
fn unwrap<T>(x: Result<T, Panicked>) -> T {
  match x { Ok(t) => t, Err(e) => match e {} }
}

#[inline(always)]
fn ptr_byte_diff<T, U>(p: *const T, q: *const U) -> usize {
  p as usize - q as usize
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
    let size = ptr_byte_diff(hi, lo) + size_of::<Tail>();
    let next = unsafe { hi.read() };

    let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

    unsafe { alloc::alloc::dealloc(lo, layout) }

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
  fn from_slice_too_long(_: usize) -> Self {
    Self::SliceTooLong
  }

  #[inline(always)]
  fn from_type_align_too_large(_: usize) -> Self {
    Self::TypeAlignTooLarge
  }

  #[inline(always)]
  fn from_type_needs_drop() -> Self {
    Self::TypeNeedsDrop
  }

  #[inline(always)]
  fn from_type_size_too_large(_: usize) -> Self {
    Self::TypeSizeTooLarge
  }
}

impl InternalError for Panicked {
  #[inline(never)]
  #[cold]
  fn from_global_alloc_error(layout: Layout) -> Self {
    alloc::alloc::handle_alloc_error(layout)
  }

  #[inline(never)]
  #[cold]
  fn from_slice_too_long(len: usize) -> Self {
    panic!("slice too long: {:?}", len)
  }

  #[inline(never)]
  #[cold]
  fn from_type_align_too_large(align: usize) -> Self {
    panic!("type align too large: {:?}", align)
  }

  #[inline(never)]
  #[cold]
  fn from_type_needs_drop() -> Self {
    panic!("type needs drop")
  }

  #[inline(never)]
  #[cold]
  fn from_type_size_too_large(size: usize) -> Self {
    panic!("type size too large: {:?}", size)
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
  fn alloc_chunk_for<E>(&mut self, object_size: usize) -> Result<Span, E>
    where E: InternalError
  {
    // POSTCONDITION:
    //
    // - If `object_size <= MAX_OBJECT_SIZE`, then the returned `Span` has size
    //   at least `object_size`.

    let total_allocated = self.total_allocated;

    let target_0 = object_size + size_of::<Tail>();
    let target_1 = total_allocated / 4 + 1;
    let target = max(target_0, target_1);

    let size =
      if target <= MIN_CHUNK_SIZE {
        MIN_CHUNK_SIZE
      } else if target > MAX_CHUNK_SIZE {
        MAX_CHUNK_SIZE
      } else {
        1 << (usize::BITS - (target - 1).leading_zeros())
      };

    // SAFETY:
    //
    // - `CHUNK_ALIGN != 0`
    // - `CHUNK_ALIGN` is a power of two
    // - `size` rounded up to a multiple of `CHUNK_ALIGN` is `<= isize::MAX`

    let layout = unsafe { Layout::from_size_align_unchecked(size, CHUNK_ALIGN) };

    // SAFETY:
    //
    // - `size != 0`

    let lo = unsafe { alloc::alloc::alloc(layout) };

    if lo.is_null() { return Err(E::from_global_alloc_error(layout)); }

    let hi = lo.wrapping_add(size).wrapping_sub(size_of::<Tail>()) as *mut Tail;

    unsafe { hi.write(Tail(self.lo, self.hi)) };

    // We're past possible error conditions, so actually update `self`.

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
    where E: InternalError
  {
    let align = align_of::<T>();
    let size = size_of::<T>();

    if /* const */ needs_drop::<T>() {
      return Err(E::from_type_needs_drop());
    }

    if /* const */ align > MAX_OBJECT_ALIGN {
      return Err(E::from_type_align_too_large(align));
    }

    if /* const */ size > MAX_OBJECT_SIZE {
      return Err(E::from_type_size_too_large(size));
    }

    if size > ptr_byte_diff(self.hi, self.lo) {
      let Span(lo, hi) = self.arena.alloc_chunk_for(size)?;
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
    where E: InternalError
  {
    let align = align_of::<T>();
    let size_of_element = size_of::<T>();
    let max_len = MAX_OBJECT_SIZE / size_of_element;

    if /* const */ needs_drop::<T>() {
      return Err(E::from_type_needs_drop());
    }

    if /* const */ align > MAX_OBJECT_ALIGN {
      return Err(E::from_type_align_too_large(align));
    }

    if len > max_len {
      return Err(E::from_slice_too_long(len));
    }

    let size = size_of_element * len;

    if size > ptr_byte_diff(self.hi, self.lo) {
      let Span(lo, hi) = self.arena.alloc_chunk_for(size)?;
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
  /// - Panics if acquiring memory from the global allocator fails.
  /// - Panics if the type implements [`drop`](Drop).
  /// - Panics if the alignment of the type is greater than [`MAX_OBJECT_ALIGN`].
  /// - Panics if the size of the type is greater than [`MAX_OBJECT_SIZE`].

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
  /// - Panics if acquiring memory from the global allocator fails.
  /// - Panics if the element type implements [`drop`](Drop).
  /// - Panics if the alignment of the element type is greater than
  ///   [`MAX_OBJECT_ALIGN`].
  /// - Panics if the an array of the given element type and length would have
  ///   size greater than [`MAX_OBJECT_SIZE`].

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
