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
use core::mem;
use core::mem::MaybeUninit;
use core::mem::align_of;
use core::mem::needs_drop;
use core::mem::size_of;
use core::ptr::NonNull;
use core::ptr::null_mut;
use core::slice;

const MIN_CHUNK_SIZE: usize = 1 << 16; // 64kb
const MIN_CHUNK_ALIGN: usize = align_of::<Tail>();

const _: () = assert!(MIN_CHUNK_SIZE % MIN_CHUNK_ALIGN == 0);
const _: () = assert!(MIN_CHUNK_SIZE <= isize::MAX as usize);
const _: () = assert!(size_of::<Tail>() <= MIN_CHUNK_SIZE);
const _: () = assert!(align_of::<Tail>() <= MIN_CHUNK_ALIGN);

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

pub struct Uninit<'a, T: 'a>(pub &'a mut MaybeUninit<T>);

pub struct UninitSlice<'a, T: 'a>(pub &'a mut [MaybeUninit<T>]);

#[derive(Clone, Debug)]
pub struct AllocError {}

enum Panicked {}

enum InternalError {
  GlobalAllocError(Layout),
  LayoutError,
  SliceTooLong(usize),
  TypeNeedsDrop,
}

trait FromInternalError {
  fn from(_: InternalError) -> Self;
}

struct Tail {
  layout: Layout,
  next: *mut Tail,
}

struct Span(*mut u8, *mut u8);

#[inline(always)]
fn unwrap<T>(x: Result<T, Panicked>) -> T {
  match x { Ok(t) => t, Err(e) => match e {} }
}

#[inline(always)]
fn align_up(size: usize, align: usize) -> usize {
  size.wrapping_add(align - 1) & ! (align - 1)
}

#[inline(always)]
fn ptr_addr<T>(p: *const T) -> usize {
  p as usize
}

#[inline(always)]
fn ptr_mask(p: *mut u8, m: usize) -> *mut u8 {
  // This expression preserves pointer provenance and should be optimized into
  // `p & m`.
  //
  // Once the `ptr_mask` feature is stabilized, we can just use `p.mask(m)`.

  p.wrapping_sub((p as usize) & ! m)
}

#[inline(always)]
fn ptr_align_up(p: *mut u8, align: usize) -> *mut u8 {
  ptr_mask(p.wrapping_add(align - 1), ! (align - 1))
}

unsafe fn dealloc_chunk_list(p: *mut Tail) {
  // SAFETY:
  //
  // - `p` must be the head of a valid linked list of chunks.

  let mut p = p;

  while ! p.is_null() {
    let Tail { layout, next } = unsafe { p.read() };
    let lo = (p as *mut u8).wrapping_add(size_of::<Tail>()).wrapping_sub(layout.size());

    unsafe { alloc::alloc::dealloc(lo, layout) }

    p = next;
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

    let p = self.hi;

    if ! p.is_null() {
      let p = mem::replace(&mut unsafe { &mut *p }.next, null_mut());

      unsafe { dealloc_chunk_list(p) };
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
    // - the chunk has been pushed onto the arena's stack, and
    // - the chunk can accommodate `object_layout` at the start of the chunk.
    //
    // If this method is not successful, the allocator's state is unchanged.

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
    //
    // Note that a very large `object_size` is necessary for this to occur; the
    // exponential chunk growth alone will not cause this to overflow.

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

    // We have made sure that the chunk is aligned to at least
    // `align_of::<Tail>()` and that its size is a multiple of
    // `align_of::<Tail>(), so we can place the tail at the very end of the
    // chunk.

    let hi = lo.wrapping_add(size).wrapping_sub(size_of::<Tail>()) as *mut Tail;

    // SAFETY:
    //
    // - `hi` is valid and aligned for writing a `Tail`.

    unsafe { hi.write(Tail { layout, next: self.hi }) };

    // We're past possible error conditions, so we can actually update `self`.

    self.lo = lo;
    self.hi = hi;
    self.total_allocated = total_allocated.saturating_add(size);

    Ok(Span(lo, hi as *mut u8))
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe { dealloc_chunk_list(self.hi) };
  }
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn internal_alloc_memory<E>(&mut self, layout: Layout) -> Result<NonNull<u8>, E>
    where E: FromInternalError
  {
    let size = layout.size();
    let align = layout.align();

    let p = ptr_align_up(self.lo, align);

    // We shouldn't need to write this intermediate value to `self.lo`, but it
    // seems to help with loop optimizations.

    self.lo = p;

    if size as isize > ptr_addr(self.hi).wrapping_sub(ptr_addr(p)) as isize {
      let Span(lo, hi) = self.arena.alloc_chunk_for::<E>(layout)?;
      self.lo = lo;
      self.hi = hi;
    }

    let p = self.lo;

    self.lo = p.wrapping_add(size);

    Ok(unsafe { NonNull::new_unchecked(p) })
  }

  #[inline(always)]
  fn internal_alloc<T, E>(&mut self) -> Result<Uninit<'a, T>, E>
    where E: FromInternalError
  {
    if /* const */ needs_drop::<T>() {
      return Err(E::from(InternalError::TypeNeedsDrop));
    }

    let p = self.internal_alloc_memory::<E>(Layout::new::<T>())?;

    // SAFETY:
    //
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(Uninit(unsafe { p.cast().as_mut() }))
  }

  #[inline(always)]
  fn internal_alloc_slice<T, E>(&mut self, len: usize) -> Result<UninitSlice<'a, T>, E>
    where E: FromInternalError
  {
    let size_of_element = size_of::<T>();
    let align = align_of::<T>();

    if /* const */ needs_drop::<T>() {
      return Err(E::from(InternalError::TypeNeedsDrop));
    }

    // Because `size_of::<T>() % align_of::<T>() == 0` for all types `T`, we
    // don't need to consider the case where rounding the size up to the
    // alignment exceeds `isize::MAX`.

    if size_of_element != 0 && len > isize::MAX as usize / size_of_element {
      return Err(E::from(InternalError::SliceTooLong(len)));
    }

    let layout = unsafe { Layout::from_size_align_unchecked(size_of_element * len, align) };

    let p = self.internal_alloc_memory::<E>(layout)?;

    // SAFETY:
    //
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(UninitSlice(unsafe { slice::from_raw_parts_mut(p.cast().as_ptr(), len) }))
  }

  #[inline(always)]
  fn internal_alloc_layout<E>(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
    where E: FromInternalError
  {
    let p = self.internal_alloc_memory::<E>(layout)?;

    Ok(unsafe { slice::from_raw_parts_mut(p.cast().as_ptr(), layout.size()) })
  }

  /// Allocates memory for a single object.
  ///
  /// # Panics
  ///
  /// - `T` implements [`drop`](core::ops::Drop).
  /// - Appending metadata to the allocation would overflow [`Layout`].
  /// - The global allocator failed to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Uninit<'a, T> {
    unwrap(self.internal_alloc())
  }

  /// Allocates memory for a single object.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc`](Self::alloc).

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Uninit<'a, T>, AllocError> {
    self.internal_alloc()
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Panics
  ///
  /// - `T` implements [`drop`](core::ops::Drop).
  /// - An array of `T` of the given length would overflow [`Layout`].
  /// - Appending metadata to the allocation would overflow [`Layout`].
  /// - The global allocator failed to allocate memory.

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> UninitSlice<'a, T> {
    unwrap(self.internal_alloc_slice(len))
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc_slice`](Self::alloc_slice).

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<UninitSlice<'a, T>, AllocError> {
    self.internal_alloc_slice(len)
  }

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// - Appending metadata to the allocation would overflow [`Layout`].
  /// - The global allocator failed to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
    unwrap(self.internal_alloc_layout(layout))
  }

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc_layout`](Self::alloc_layout).

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError> {
    self.internal_alloc_layout(layout)
  }
}

impl<'a, T> Uninit<'a, T> {
  /// Initializes the object with the given value.

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    self.0.write(value)
  }
}

impl<'a, T> UninitSlice<'a, T> {
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

    let p: *mut [MaybeUninit<T>] = self.0;
    let p: *mut [T] = p as *mut [T];

    // SAFETY:
    //
    // - Every slice element has been initialized.

    unsafe { &mut *p }
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
