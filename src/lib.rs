#![doc = include_str!("../README.md")]
#![no_std]

extern crate alloc;

use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::str;
use pop::Ptr;

pub mod two;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

/// An arena allocator.

pub struct Arena {
  lo: Ptr,
  hi: Ptr,
}

/// An uninitialized slot in the arena.
///
/// Typically you will initialize the slot with [`init`](Self::init) or
/// [`init_slice`](Self::init_slice).

pub struct Slot<'a, T>(
  Ptr,
  T::Metadata,
  PhantomData<(Invariant<T>, InvariantLifetime<'a>)>,
)
where
  T: Pointee + ?Sized;

/// A failed allocation from the arena.

#[derive(Debug)]
pub struct AllocError;

/// Methods for a `&'a mut Arena` that allocate a slot with the corresponding
/// lifetime.

pub trait ArenaRef<'a> {

  /// Allocates memory for a single object.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  fn alloc<T>(&mut self) -> Slot<'a, T>;

  /// Allocates memory for a single object.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError>;

  /// Allocates memory for a slice of the given length.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]>;

  /// Allocates memory for a slice of the given length.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, AllocError>;

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  fn alloc_layout(&mut self, layout: Layout) -> Slot<'a, [u8]>;

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  fn try_alloc_layout(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, AllocError>;

  /// Copies the slice into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy;

  /// Copies the slice into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  fn try_copy_slice<T>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError>
  where
    T: Copy;

  /// Copies the string into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  fn copy_str(&mut self, src: &str) -> &'a mut str;

  /// Copies the string into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError>;
}

/// Polyfill for the unstable [`core::ptr::Pointee`] trait.

pub trait Pointee {
  #[allow(missing_docs)]
  type Metadata: Copy + Send + Sync + Unpin;
}

impl<T> Pointee for T {
  type Metadata = ();
}

impl<T> Pointee for [T] {
  type Metadata = usize;
}

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

enum Void {}

struct Footer {
  next: Ptr,
  total_allocated: isize,
  layout: Layout,
}

trait FromError {
  fn global_alloc_error(_: Layout) -> Self;
  fn layout_overflow() -> Self;
}

struct Invariant<T>(fn(T) -> T) where T: ?Sized;

struct InvariantLifetime<'a>(fn(&'a ()) -> &'a ());

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

#[cfg(not(test))]
const MIN_CHUNK_SIZE_LOG2: u32 = 12; // 4kb

#[cfg(test)]
const MIN_CHUNK_SIZE_LOG2: u32 = 6; // 64b

const FOOTER_SIZE: isize = size_of::<Footer>();
const FOOTER_ALIGN: isize = align_of::<Footer>();
const MIN_CHUNK_SIZE: isize = 1 << MIN_CHUNK_SIZE_LOG2;
const MIN_CHUNK_ALIGN: isize = max(FOOTER_ALIGN, WORD_ALIGN);
const WORD_ALIGN: isize = align_of::<usize>();

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
const fn size_of<T>() -> isize {
  core::mem::size_of::<T>() as isize
}

#[inline(always)]
const fn align_of<T>() -> isize {
  core::mem::align_of::<T>() as isize
}

#[inline(always)]
const fn max(x: isize, y: isize) -> isize {
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

impl core::fmt::Display for AllocError {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

unsafe fn dealloc_chunk_list(p: Ptr) {
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
  let p = p + FOOTER_SIZE - l.size() as isize;

  unsafe { alloc::alloc::dealloc(p.as_mut_ptr(), l) };

  if ! q.is_null() {
    unsafe { dealloc_chunk_list(q) }
  }
}

#[inline(never)]
#[cold]
unsafe fn try_alloc_chunk_for<E>(_lo: Ptr, hi: Ptr, object: Layout) -> Result<(Ptr, Ptr), E>
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
  const _: () = assert!(FOOTER_SIZE <= MIN_CHUNK_SIZE);
  const _: () = assert!(FOOTER_ALIGN <= MIN_CHUNK_ALIGN);

  let chunks = hi;

  let total_allocated =
    if chunks.is_null() {
      0
    } else {
      unsafe { chunks.as_ref::<Footer>() }.total_allocated
    };

  let object_size = object.size() as isize;
  let object_align = object.align() as isize;

  // The chunk size we'd like to allocate, if the object will fit in it.  It
  // is always a power of two `<= 0b0100...`.

  let size_0 = total_allocated / 4 + 1;
  let size_0 = 1 << (usize::BITS - (size_0 - 1).leading_zeros());
  let size_0 = max(size_0, MIN_CHUNK_SIZE);

  // FIXME: we're using `isize` now, so we need to redo the overflow logic.

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

  if size > isize::MAX - (align - 1) {
    return Err(E::layout_overflow());
  }

  // SAFETY:
  //
  // - `align != 0`
  // - `align` is a power of two
  // - `size` rounded up to a multiple of `align` is `<= isize::MAX`

  let layout = unsafe { Layout::from_size_align_unchecked(size as usize, align as usize) };

  // SAFETY:
  //
  // - `size != 0`

  let lo = Ptr::from(unsafe { alloc::alloc::alloc(layout) });

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

  unsafe { hi.write(f) };

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
      lo: Ptr::invalid(1),
      hi: Ptr::invalid(0),
    }
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

    let p = self.hi;

    if ! p.is_null() {
      let f = unsafe { p.as_mut_ref::<Footer>() };
      let q = f.next;
      let l = f.layout;
      let p = p + FOOTER_SIZE - l.size() as isize;

      self.lo = p;

      if ! q.is_null() {
        f.next = Ptr::NULL;
        unsafe { dealloc_chunk_list(q) }
      }
    }
  }

  #[inline(always)]
  fn try_alloc<E>(&mut self, layout: Layout) -> Result<Ptr, E>
  where
    E: FromError
  {
    let size = layout.size() as isize;
    let align = layout.align() as isize;

    let p = self.lo;
    let q = self.hi;

    let p = (p + (align - 1)) & ! (align - 1) as usize;

    if size > q - p {
      let (p, q) = unsafe { try_alloc_chunk_for::<E>(p, q, layout) }?;
      self.lo = p;
      self.hi = q;
    } else {
      self.lo = p;
    }

    let p = self.lo;

    self.lo = p + size;

    Ok(p)
  }

  fn debug(&self, f: &mut core::fmt::Formatter<'_>, name: &str) -> core::fmt::Result {
    let p = self.lo;
    let q = self.hi;

    f.debug_struct(name).field("lo", &p).field("hi", &q).finish()
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    let p = self.hi;

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

impl core::fmt::Debug for Arena {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.debug(f, "Arena")
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// ALLOCATION FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
fn try_alloc<'a, T, E>(arena: &mut &'a mut Arena) -> Result<Slot<'a, T>, E>
where
  E: FromError
{
  let p = (*arena).try_alloc(Layout::new::<T>())?;

  // SAFETY:
  //
  // - The pointer is non-null and aligned, even if `size == 0`.
  // - The memory has the correct size.
  // - The memory is not aliased by any other reference.
  // - The memory is live for the duration of the assigned lifetime.

  Ok(unsafe { Slot::new(p, ()) })
}

#[inline(always)]
fn try_alloc_slice<'a, T, E>(arena: &mut &'a mut Arena, len: usize) -> Result<Slot<'a, [T]>, E>
where
  E: FromError
{
  let size_of_element = size_of::<T>();
  let align = align_of::<T>();

  // Because `size_of::<T>() % align_of::<T>() == 0` for all types `T`, we
  // don't need to consider the case where rounding the size up to the
  // alignment exceeds `isize::MAX`.

  if size_of_element != 0 && len > (isize::MAX / size_of_element) as usize {
    return Err(E::layout_overflow());
  }

  let size = size_of_element * len as isize;
  let layout = unsafe { Layout::from_size_align_unchecked(size as usize, align as usize) };

  let p = (*arena).try_alloc(layout)?;

  // SAFETY:
  //
  // - The pointer is non-null and aligned, even if `size == 0`.
  // - The memory has the correct size.
  // - The memory is not aliased by any other reference.
  // - The memory is live for the duration of the assigned lifetime.

  Ok(unsafe { Slot::new(p, len) })
}

#[inline(always)]
fn try_alloc_layout<'a, E>(arena: &mut &'a mut Arena, layout: Layout) -> Result<Slot<'a, [u8]>, E>
where
  E: FromError
{
  let p = (*arena).try_alloc(layout)?;

  // SAFETY:
  //
  // - The pointer is non-null and aligned, even if `size == 0`.
  // - The memory has the correct size.
  // - The memory is not aliased by any other reference.
  // - The memory is live for the duration of the assigned lifetime.

  Ok(unsafe { Slot::new(p, layout.size()) })
}

#[inline(always)]
fn try_copy_slice<'a, T, E>(arena: &mut &'a mut Arena, src: &[T]) -> Result<&'a mut [T], E>
where
  T: Copy,
  E: FromError
{
  // `Copy` implies `!Drop`.

  let size_of_element = size_of::<T>();
  let align = align_of::<T>();
  let n = src.len();
  let size = size_of_element * n as isize;

  // SAFETY:
  //
  // The existence of `src` implies that we'll construct a valid layout.

  let layout = unsafe { Layout::from_size_align_unchecked(size as usize, align as usize) };

  let p = (*arena).try_alloc(layout)?;
  let q = Ptr::from(src);

  // SAFETY:
  //
  // - The `src` argument is valid for reading `T`s.
  // - The `dst` argument is valid for writing `T`s.
  // - The `src` and `dst` regions do not overlap.
  //
  // Note that the above holds, and in particular that the pointers are
  // non-null and aligned, even if we need to do a zero-byte read and write.

  unsafe { Ptr::copy_nonoverlapping::<T>(q, p, n) };

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
fn try_copy_str<'a, E>(arena: &mut &'a mut Arena, src: &str) -> Result<&'a mut str, E>
where
  E: FromError
{
  let p = try_copy_slice(arena, src.as_bytes())?;

  // SAFETY:
  //
  // The byte array is valid UTF-8 because `src` was valid UTF-8.

  Ok(unsafe { str::from_utf8_unchecked_mut(p) })
}

impl<'a> ArenaRef<'a> for &'a mut Arena {
  #[inline(always)]
  fn alloc<T>(&mut self) -> Slot<'a, T> {
    Void::unwrap(try_alloc(self))
  }

  #[inline(always)]
  fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError> {
    try_alloc(self)
  }

  #[inline(always)]
  fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    Void::unwrap(try_alloc_slice(self, len))
  }

  #[inline(always)]
  fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, AllocError> {
    try_alloc_slice(self, len)
  }

  #[inline(always)]
  fn alloc_layout(&mut self, layout: Layout) -> Slot<'a, [u8]> {
    Void::unwrap(try_alloc_layout(self, layout))
  }

  #[inline(always)]
  fn try_alloc_layout(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, AllocError> {
    try_alloc_layout(self, layout)
  }

  #[inline(always)]
  fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    Void::unwrap(try_copy_slice(self, src))
  }

  #[inline(always)]
  fn try_copy_slice<T>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError>
  where
    T: Copy
  {
    try_copy_slice(self, src)
  }

  #[inline(always)]
  fn copy_str(&mut self, src: &str) -> &'a mut str {
    Void::unwrap(try_copy_str(self, src))
  }

  #[inline(always)]
  fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    try_copy_str(self, src)
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

impl<'a, T> core::fmt::Debug for Slot<'a, T> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("Slot").field(&self.0).finish()
  }
}

impl<'a, T> Slot<'a, T>
where
  T: Pointee + ?Sized
{
  unsafe fn new(p: Ptr, m: T::Metadata) -> Self {
    // SAFETY:
    //
    // To satisfy invariants for `Slot`, we require that
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Self(p, m, PhantomData)
  }
}

impl<'a, T> Slot<'a, T> {
  /// Converts the slot into a reference to an uninitialized value.

  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    let p = Ptr::from(self.0);

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
    let p = Ptr::from(self.0);

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

    let p = Ptr::from(p);

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
    let p = Ptr::from(self.0);

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
    let p = Ptr::from(p);

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { p.as_slice_mut_ref(n) }
  }
}
