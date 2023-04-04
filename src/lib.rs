#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(missing_docs)]
#![warn(non_ascii_idents)]
#![warn(trivial_numeric_casts)]
#![warn(unreachable_pub)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]
#![warn(unused_results)]

extern crate alloc;

use core::alloc::Layout;
use core::cell::UnsafeCell;
use core::fmt;
use core::hint;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::align_of;
use core::mem::needs_drop;
use core::mem::size_of;
use core::panic::RefUnwindSafe;
use core::str;
use ptr_monotype::ptr;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

/// An arena allocator.

pub struct Arena {
  // SAFETY:
  //
  // We ensure if we are writing to a field, then it is not possible for a
  // reference to this struct to be live in a different thread.
  //
  // It follows that it is always sound to read from these fields.

  lo: UnsafeCell<ptr>,
  hi: UnsafeCell<ptr>,
}

/// A view of an arena for allocating objects with a particular lifetime.

#[repr(transparent)]
pub struct Allocator<'a>(
  Arena,
  PhantomData<InvariantLifetime<'a>>,
);

/// A shareable reference to an arena for allocating objects with a particular
/// lifetime.

#[derive(Clone, Copy)]
pub struct AllocatorRef<'a>(
  &'a Arena,
  PhantomData<InvariantLifetime<'a>>,
  PhantomData<NotSendNotSync>,
);

/// An uninitialized slot in the arena.
///
/// Typically you will initialize the slot with [`init`](Self::init) or
/// [`init_slice`](Self::init_slice).

pub struct Slot<'a, T: ?Sized + Pointee>(
  ptr,
  T::Metadata,
  PhantomData<Invariant<T>>,
  PhantomData<InvariantLifetime<'a>>,
);

/// A failed allocation from the arena.

#[derive(Debug)]
pub struct AllocError;

/// Polyfill for the unstable [`core::ptr::Pointee`] trait.

pub trait Pointee {
  #[allow(missing_docs)]
  type Metadata: Copy + Send + Sync + Unpin;
}

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

enum Void {}

struct Footer {
  next: ptr,
  total_allocated: usize,
  layout: Layout,
}

trait FromError {
  fn global_alloc_error(_: Layout) -> Self;
  fn layout_overflow() -> Self;
}

struct Invariant<T: ?Sized>(fn(T) -> T);

struct InvariantLifetime<'a>(fn(&'a ()) -> &'a ());

struct NotSendNotSync(*const ());

unsafe trait AllocMemory<'a> {
  fn alloc_memory<E>(self, layout: Layout) -> Result<ptr, E>
  where
    E: FromError;
}

impl<T> Pointee for T {
  type Metadata = ();
}

impl<T> Pointee for [T] {
  type Metadata = usize;
}

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

#[cfg(not(test))]
const MIN_CHUNK_SIZE_LOG2: usize = 12; // 4kb

#[cfg(test)]
const MIN_CHUNK_SIZE_LOG2: usize = 6; // 64b

const FOOTER_SIZE: usize = size_of::<Footer>();
const FOOTER_ALIGN: usize = align_of::<Footer>();
const MIN_CHUNK_SIZE: usize = 1 << MIN_CHUNK_SIZE_LOG2;
const MIN_CHUNK_ALIGN: usize = max(FOOTER_ALIGN, WORD_ALIGN);
const WORD_ALIGN: usize = align_of::<usize>();

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
const fn max(x: usize, y: usize) -> usize {
  if x >= y { x } else { y }
}

////////////////////////////////////////////////////////////////////////////////
//
// Void
//
////////////////////////////////////////////////////////////////////////////////

impl Void {
  #[inline(always)]
  fn unwrap<T>(x: Result<T, Void>) -> T {
    match x {
      Ok(x) => x,
      Err(e) => match e {}
    }
  }
}

impl FromError for Void {
  #[inline(never)]
  #[cold]
  fn global_alloc_error(layout: Layout) -> Self {
    alloc::alloc::handle_alloc_error(layout)
  }

  #[inline(never)]
  #[cold]
  fn layout_overflow() -> Self {
    panic!("layout overflow")
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// AllocError
//
////////////////////////////////////////////////////////////////////////////////

impl fmt::Display for AllocError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str("memory allocation failed")
  }
}

impl FromError for AllocError {
  #[inline(always)]
  fn global_alloc_error(_: Layout) -> Self { Self }

  #[inline(always)]
  fn layout_overflow() -> Self { Self }
}

////////////////////////////////////////////////////////////////////////////////
//
// Arena
//
////////////////////////////////////////////////////////////////////////////////

impl RefUnwindSafe for Arena {}

// SAFETY:
//
// See safety comment on the `struct Arena` type declaration.

unsafe impl Sync for Arena {}

unsafe fn dealloc_chunk_list(p: ptr) {
  // SAFETY:
  //
  // `p` must be the head of a valid linked list of chunks.

  // STACK SPACE:
  //
  // Chunk sizes grow exponentially, so stack usage is O(log(word size)) at
  // worst even without TCO.

  let f = unsafe { p.as_ref::<Footer>() };
  let q = f.next;
  let l = f.layout;
  let p = p + FOOTER_SIZE - l.size();

  unsafe { ptr::dealloc(p, l) }

  if ! q.is_null() {
    unsafe { dealloc_chunk_list(q) }
  }
}

#[inline(never)]
#[cold]
unsafe fn alloc_chunk_for<E>
  (
    lo: ptr,
    hi: ptr,
    object: Layout,
  )
  -> Result<(ptr, ptr), E>
where
  E: FromError
{
  // SAFETY:
  //
  // `hi` must either be null or point to a valid `Footer`.

  // POSTCONDITIONS:
  //
  // If this function returns `Ok(_)`, then it has allocated a new chunk and
  // placed it at the head of linked list whose previous head was `hi`.
  // Additionally, the first  pointer points to memory suitable for the start
  // of an object with layout `object`.
  //
  // If this function returns `Err(_)`, then the linked list of chunks is
  // unmodified.

  const _: () = assert!(MIN_CHUNK_SIZE % MIN_CHUNK_ALIGN == 0);
  const _: () = assert!(MIN_CHUNK_SIZE <= isize::MAX as usize);
  const _: () = assert!(FOOTER_SIZE <= MIN_CHUNK_SIZE);
  const _: () = assert!(FOOTER_ALIGN <= MIN_CHUNK_ALIGN);

  let _ = hint::black_box(lo);
  let chunks = hi;

  let total_allocated =
    if chunks.is_null() {
      0
    } else {
      unsafe { chunks.as_ref::<Footer>() }.total_allocated
    };

  let object_size = object.size();
  let object_align = object.align();

  // The chunk size we'd like to allocate, if the object will fit in it.  It
  // is always a power of two `<= 0b0100...`.

  let size_0 = total_allocated / 4 + 1;
  let size_0 = 1 << (usize::BITS - (size_0 - 1).leading_zeros());
  let size_0 = max(size_0, MIN_CHUNK_SIZE);

  // The size of any `Layout` is guaranteed to be `<= isize::MAX`. It follows
  // that `size_1` does not overflow `usize`.

  let size_1 = object_size.wrapping_add(FOOTER_ALIGN - 1) & ! (FOOTER_ALIGN - 1);
  let size_1 = size_1 + FOOTER_SIZE;

  let size = max(size_0, size_1);
  let align = max(object_align, MIN_CHUNK_ALIGN);

  // We can construct a valid `Layout` if and only if `size` rounded up to
  // `align` does not overflow and is `<= isize::MAX`.
  //
  // Note that a very large `object_size` is necessary for this to occur; the
  // exponential chunk growth alone will not cause this to overflow.

  if size > isize::MAX as usize - (align - 1) {
    return Err(E::layout_overflow());
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

  let lo = unsafe { ptr::alloc(layout) };

  if lo.is_null() {
    return Err(E::global_alloc_error(layout));
  }

  // We have made sure that the chunk is aligned to at least
  // `align_of::<Footer>()` and that its size is a multiple of
  // `align_of::<Footer>(), so we can place the tail at the very end of the
  // chunk.

  let hi = lo + size - FOOTER_SIZE;

  let total_allocated = total_allocated.saturating_add(size);

  let f = Footer { next: chunks, total_allocated, layout };

  // SAFETY:
  //
  // - `hi` is valid and aligned for writing a `Footer`.

  unsafe { hi.set(f) };

  Ok((lo, hi))
}

impl Arena {
  /// Creates a new arena. It does not yet request any memory from the global
  /// allocator.

  #[inline(always)]
  pub fn new() -> Self {
    // We initialize with `lo > hi` so there is no space for a zero-sized
    // allocation.
    //
    // Also, `hi - align_up(lo, MAX_ALIGN) == isize::MIN`, so we don't
    // underflow `isize` in the capacity calculation.

    Self {
      lo: UnsafeCell::new(ptr::invalid(1)),
      hi: UnsafeCell::new(ptr::invalid(0)),
    }
  }

  /// Gets a handle with which to allocate objects from the arena. The lifetime
  /// from this mutable borrow is propagated to those allocations.

  #[inline(always)]
  pub fn allocator_mut(&mut self) -> &mut Allocator<'_> {
    // The type `&'a mut Allocator<'b>` has two lifetimes, which, during usage,
    // can differ from each other due to reborrowing.

    let p = ptr::from(self);

    // SAFETY:
    //
    // Various allocation methods use unsafe code to create references from
    // pointers.  For that code to be sound, it is necessary for every user
    // accessible `Allocator` to have an appropriately restricted lifetime
    // parameter.

    // SAFETY:
    //
    // The soundness of this cast depends on the fact that `Allocator` is
    // `#[repr(transparent)]` with an `Arena` field.

    unsafe { p.as_mut_ref() }
  }

  /// Gets a handle with which to allocate objects from the arena. The lifetime
  /// from this mutable borrow is propagated to those allocations.
  ///
  /// In contrast with the handle returned by `allocator_mut`, this handle can
  /// be shared but can't be sent to a different thread.

  #[inline(always)]
  pub fn allocator_ref(&mut self) -> AllocatorRef<'_> {
    // Unlike with the handle returned by `allocator_mut`, we only need one
    // lifetime here because we don't need to deal with reborrowing.

    // SAFETY:
    //
    // There must be no other currently live reference to the `Arena`, because
    // an `AllocatorRef` can access the underying `Arena` with interior
    // mutability and `Arena` itself is `Sync`.  We ensure this by taking a
    // `&mut self` parameter here.
    //
    // The `AllocatorRef` itself can be safely duplicated because it (unlike a
    // `&Arena`) is neither `Send` nor `Sync`.

    AllocatorRef(self, PhantomData, PhantomData)
  }

  /// Deallocates all objects previously allocated from the arena. The arena
  /// may release some, but not necessarily all, of its memory back to the
  /// global allocator.

  pub fn reset(&mut self) {
    // SAFETY:
    //
    // Various allocation methods use unsafe code to create references from
    // pointers.  For that code to be sound, it is necessary for calling this
    // method to imply that any lifetime associated with an `Allocator` or
    // `AllocatorRef` has already ended.

    let lo = self.lo.get_mut();
    let hi = self.hi.get_mut();

    let p = *hi;

    if ! p.is_null() {
      let f = unsafe { p.as_mut_ref::<Footer>() };
      let q = f.next;
      let l = f.layout;
      let p = p + FOOTER_SIZE - l.size();

      *lo = p;

      if ! q.is_null() {
        f.next = ptr::NULL;
        unsafe { dealloc_chunk_list(q) }
      }
    }
  }

  #[inline(always)]
  fn alloc<E>(&mut self, layout: Layout) -> Result<ptr, E>
  where
    E: FromError
  {
    let size = layout.size();
    let align = layout.align();

    let lo = self.lo.get_mut();
    let hi = self.hi.get_mut();

    let p = *lo;
    let q = *hi;

    let p = (p + (align - 1)) & ! (align - 1);

    if size as isize > (q - p) as isize {
      let (p, q) = unsafe { alloc_chunk_for::<E>(p, q, layout) }?;
      *lo = p;
      *hi = q;
    } else {
      *lo = p;
    }

    let p = *lo;

    *lo = p + size;

    Ok(p)
  }

  #[inline(always)]
  unsafe fn alloc_shared<E>(&self, layout: Layout) -> Result<ptr, E>
  where
    E: FromError
  {
    // SAFETY:
    //
    // This must not be called when another `&self` reference is live in a
    // different thread.

    let size = layout.size();
    let align = layout.align();

    let lo = self.lo.get();
    let hi = self.hi.get();

    let p = unsafe { lo.read() };
    let q = unsafe { hi.read() };

    let p = (p + (align - 1)) & ! (align - 1);

    if size as isize > (q - p) as isize {
      let (p, q) = unsafe { alloc_chunk_for::<E>(p, q, layout) }?;
      unsafe { lo.write(p) };
      unsafe { hi.write(q) };
    } else {
      unsafe { lo.write(p) };
    }

    let p = unsafe { lo.read() };

    unsafe { lo.write(p + size) };

    Ok(p)
  }

  fn debug(&self, f: &mut fmt::Formatter<'_>, name: &str) -> fmt::Result {
    let lo = self.lo.get();
    let hi = self.hi.get();
    let p = unsafe { lo.read() };
    let q = unsafe { hi.read() };

    f.debug_struct(name).field("lo", &p).field("hi", &q).finish()
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    let p = *self.hi.get_mut();

    if ! p.is_null() {
      unsafe { dealloc_chunk_list(p) }
    }
  }
}

impl Default for Arena {
  #[inline(always)]
  fn default() -> Self {
    Self::new()
  }
}

impl fmt::Debug for Arena {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.debug(f, "Arena")
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// ALLOCATION FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
fn alloc<'a, S, T, E>(allocator: S) -> Result<Slot<'a, T>, E>
where
  S: AllocMemory<'a>,
  E: FromError
{
  let p = allocator.alloc_memory(Layout::new::<T>())?;

  // SAFETY:
  //
  // - The pointer is non-null and aligned, even if `size == 0`.
  // - The memory has the correct size.
  // - The memory is not aliased by any other reference.
  // - The memory is live for the duration of the assigned lifetime.

  Ok(unsafe { Slot::new(p, ()) })
}

#[inline(always)]
fn alloc_slice<'a, S, T, E>(allocator: S, len: usize) -> Result<Slot<'a, [T]>, E>
where
  S: AllocMemory<'a>,
  E: FromError
{
  let size_of_element = size_of::<T>();
  let align = align_of::<T>();

  // Because `size_of::<T>() % align_of::<T>() == 0` for all types `T`, we
  // don't need to consider the case where rounding the size up to the
  // alignment exceeds `isize::MAX`.

  if size_of_element != 0 && len > isize::MAX as usize / size_of_element {
    return Err(E::layout_overflow());
  }

  let size = size_of_element * len;
  let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

  let p = allocator.alloc_memory(layout)?;

  // SAFETY:
  //
  // - The pointer is non-null and aligned, even if `size == 0`.
  // - The memory has the correct size.
  // - The memory is not aliased by any other reference.
  // - The memory is live for the duration of the assigned lifetime.

  Ok(unsafe { Slot::new(p, len) })
}

#[inline(always)]
fn alloc_layout<'a, S, E>(allocator: S, layout: Layout) -> Result<Slot<'a, [u8]>, E>
where
  S: AllocMemory<'a>,
  E: FromError
{
  let p = allocator.alloc_memory(layout)?;

  // SAFETY:
  //
  // - The pointer is non-null and aligned, even if `size == 0`.
  // - The memory has the correct size.
  // - The memory is not aliased by any other reference.
  // - The memory is live for the duration of the assigned lifetime.

  Ok(unsafe { Slot::new(p, layout.size()) })
}

#[inline(always)]
fn copy_slice<'a, S, T, E>(allocator: S, src: &[T]) -> Result<&'a mut [T], E>
where
  S: AllocMemory<'a>,
  T: Copy,
  E: FromError
{
  // `Copy` implies `!Drop`.

  let size_of_element = size_of::<T>();
  let align = align_of::<T>();
  let n = src.len();
  let size = size_of_element * n;

  // SAFETY:
  //
  // The existence of `src` implies that we'll construct a valid layout.

  let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

  let p = allocator.alloc_memory(layout)?;
  let q = ptr::from(src);

  // SAFETY:
  //
  // - The `src` argument is valid for reading `T`s.
  // - The `dst` argument is valid for writing `T`s.
  // - The `src` and `dst` regions do not overlap.
  //
  // Note that the above holds, and in particular that the pointers are
  // non-null and aligned, even if we need to do a zero-byte read and write.

  unsafe { ptr::copy_nonoverlapping::<T>(q, p, n) };

  // SAFETY:
  //
  // - The pointer is non-null and aligned, even if `size == 0`.
  // - The memory has the correct size.
  // - The memory is not aliased by any other reference.
  // - The memory is live for the duration of the assigned lifetime.
  // - The memory is initialized.

  Ok(unsafe { p.as_slice_mut_ref(n) })
}

#[inline(always)]
fn copy_str<'a, S, E>(allocator: S, src: &str) -> Result<&'a mut str, E>
where
  S: AllocMemory<'a>,
  E: FromError
{
  let p = copy_slice(allocator, src.as_bytes())?;

  // SAFETY:
  //
  // The byte array is valid UTF-8 because `src` was valid UTF-8.

  Ok(unsafe { str::from_utf8_unchecked_mut(p) })
}

////////////////////////////////////////////////////////////////////////////////
//
// Allocator
//
////////////////////////////////////////////////////////////////////////////////

unsafe impl<'a> AllocMemory<'a> for &mut Allocator<'a> {
  #[inline(always)]
  fn alloc_memory<E>(self, layout: Layout) -> Result<ptr, E>
  where
    E: FromError
  {
    self.0.alloc(layout)
  }
}

impl<'a> Allocator<'a> {
  /// Allocates memory for a single object.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    Void::unwrap(alloc(self))
  }

  /// Allocates memory for a single object.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError> {
    alloc(self)
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    Void::unwrap(alloc_slice(self, len))
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, AllocError> {
    alloc_slice(self, len)
  }

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> Slot<'a, [u8]> {
    Void::unwrap(alloc_layout(self, layout))
  }

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, AllocError> {
    alloc_layout(self, layout)
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    Void::unwrap(copy_slice(self, src))
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_slice<T>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError>
  where
    T: Copy
  {
    copy_slice(self, src)
  }

  /// Copies the string into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    Void::unwrap(copy_str(self, src))
  }

  /// Copies the string into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    copy_str(self, src)
  }
}

impl fmt::Debug for Allocator<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.debug(f, "Allocator")
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// AllocatorRef
//
////////////////////////////////////////////////////////////////////////////////

unsafe impl<'a> AllocMemory<'a> for AllocatorRef<'a> {
  #[inline(always)]
  fn alloc_memory<E>(self, layout: Layout) -> Result<ptr, E>
  where
    E: FromError
  {
    // SAFETY:
    //
    // No other reference to the `Arena` is currently live in a different
    // thread.

    unsafe { self.0.alloc_shared(layout) }
  }
}

impl<'a> AllocatorRef<'a> {
  /// Allocates memory for a single object.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(self) -> Slot<'a, T> {
    Void::unwrap(alloc(self))
  }

  /// Allocates memory for a single object.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc<T>(self) -> Result<Slot<'a, T>, AllocError> {
    alloc(self)
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_slice<T>(self, len: usize) -> Slot<'a, [T]> {
    Void::unwrap(alloc_slice(self, len))
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_slice<T>(self, len: usize) -> Result<Slot<'a, [T]>, AllocError> {
    alloc_slice(self, len)
  }

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(self, layout: Layout) -> Slot<'a, [u8]> {
    Void::unwrap(alloc_layout(self, layout))
  }

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_layout(self, layout: Layout) -> Result<Slot<'a, [u8]>, AllocError> {
    alloc_layout(self, layout)
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_slice<T>(self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    Void::unwrap(copy_slice(self, src))
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_slice<T>(self, src: &[T]) -> Result<&'a mut [T], AllocError>
  where
    T: Copy
  {
    copy_slice(self, src)
  }

  /// Copies the string into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_str(self, src: &str) -> &'a mut str {
    Void::unwrap(copy_str(self, src))
  }

  /// Copies the string into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_str(self, src: &str) -> Result<&'a mut str, AllocError> {
    copy_str(self, src)
  }
}

impl fmt::Debug for AllocatorRef<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.debug(f, "Allocator")
  }
}

#[cfg(feature = "allocator_api")]
impl FromError for alloc::alloc::AllocError {
  #[inline(always)]
  fn global_alloc_error(_: Layout) -> Self { Self {} }

  #[inline(always)]
  fn layout_overflow() -> Self { Self {} }
}

#[cfg(feature = "allocator_api")]
unsafe impl<'a> alloc::alloc::Allocator for AllocatorRef<'a> {
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<core::ptr::NonNull<[u8]>, alloc::alloc::AllocError> {
    // SAFETY:
    //
    // No other reference to the `Arena` is currently live in a different
    // thread.

    let p = self.alloc_memory::<alloc::alloc::AllocError>(layout)?;
    let p = p.as_slice_mut_ptr(layout.size());

    Ok(unsafe { core::ptr::NonNull::new_unchecked(p) })
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: core::ptr::NonNull<u8>, layout: Layout) {
    let _ = self;
    let _ = ptr;
    let _ = layout;
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Slot
//
////////////////////////////////////////////////////////////////////////////////

#[inline(never)]
#[cold]
fn panic_type_needs_drop() -> ! {
  panic!("cannot initialize arena slot with a type that needs drop")
}

impl<'a, T> fmt::Debug for Slot<'a, T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Slot").field(&self.0).finish()
  }
}

impl<'a, T: ?Sized + Pointee> Slot<'a, T> {
  unsafe fn new(p: ptr, meta: T::Metadata) -> Self {
    // SAFETY:
    //
    // To satisfy invariants for `Slot`, we require that
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Self(p, meta, PhantomData, PhantomData)
  }
}

impl<'a, T> Slot<'a, T> {
  /// Converts the slot into a reference to an uninitialized value.

  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    let p = ptr::from(self.0);

    // SAFETY:
    //
    // The pointed-to memory is valid for `T`, though uninitialized.

    unsafe { p.as_mut_ref() }
  }

  /// Initializes the object with the given value.
  ///
  /// # Panics
  ///
  /// Panics if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    if needs_drop::<T>() {
      panic_type_needs_drop();
    }

    self.as_uninit().write(value)
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  /// Converts the slot into a reference to an array of uninitialized values.

  #[inline(always)]
  pub fn as_uninit_array(self) -> &'a mut [MaybeUninit<T>; N] {
    let p = ptr::from(self.0);

    // SAFETY:
    //
    // The pointed-to memory is valid for an array of `T`s, though
    // uninitialized.

    unsafe { p.as_mut_ref() }
  }

  /// Initializes the array with values produced by calling the given function
  /// with each index in order.
  ///
  /// # Panics
  ///
  /// Panics if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init_array<F>(self, f: F) -> &'a mut [T; N]
  where
    F: FnMut(usize) -> T
  {
    if needs_drop::<T>() {
      panic_type_needs_drop();
    }

    let mut f = f;

    let p = self.as_uninit_array();

    for (i, elt) in p.iter_mut().enumerate() {
      let _: _ = elt.write(f(i));
    }

    let p = ptr::from(p);

    // SAFETY:
    //
    // Every array element has been initialized.

    unsafe { p.as_mut_ref() }
  }
}

impl<'a, T> Slot<'a, [T]> {
  /// The length of the slice (in items, not bytes) occupying the slot.

  #[inline(always)]
  pub fn len(&self) -> usize {
    self.1
  }

  /// Converts the slot into a reference to a slice of uninitialized values.

  #[inline(always)]
  pub fn as_uninit_slice(self) -> &'a mut [MaybeUninit<T>] {
    let n = self.1;
    let p = ptr::from(self.0);

    // SAFETY:
    //
    // The pointed-to memory is valid for a slice of `T`s, though
    // uninitialized.

    unsafe { p.as_slice_mut_ref(n) }
  }

  /// Initializes the slice with values produced by calling the given function
  /// with each index in order.
  ///
  /// # Panics
  ///
  /// Panics if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init_slice<F>(self, f: F) -> &'a mut [T]
  where
    F: FnMut(usize) -> T
  {
    if needs_drop::<T>() {
      panic_type_needs_drop();
    }

    let mut f = f;

    let p = self.as_uninit_slice();

    for (i, elt) in p.iter_mut().enumerate() {
      let _: _ = elt.write(f(i));
    }

    let n = p.len();
    let p = ptr::from(p);

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { p.as_slice_mut_ref(n) }
  }
}
