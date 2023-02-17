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
use core::cell::Cell;
use core::cmp::max;
use core::fmt;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::align_of;
use core::mem::needs_drop;
use core::mem::size_of;
use core::ptr::NonNull;
use core::ptr;
use core::slice;
use core::str;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

/// An arena allocator.

pub struct Arena {
  lo: Cell<*mut u8>,
  hi: Cell<*mut Footer>,
}

/// A handle for allocating objects with a particular lifetime.

#[repr(transparent)]
pub struct Allocator<'a>(Arena, InvariantLifetime<'a>);

/// An uninitialized slot in the arena.
///
/// Typically you will initialize the slot with [`init`](Self::init) or
/// [`init_slice`](Self::init_slice).

#[repr(transparent)]
pub struct Slot<'a, T: 'a + ?Sized>(NonNull<T>, InvariantLifetime<'a>);

/// A failed allocation from the arena.

pub struct ArenaError;

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

type InvariantLifetime<'a> = PhantomData<fn(&'a ()) -> &'a ()>;

enum Void {}

struct Footer {
  layout: Layout,
  next: Option<NonNull<Footer>>,
  total_allocated: usize,
}

trait Error {
  fn global_alloc_error(_: Layout) -> Self;
  fn layout_overflow() -> Self;
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
const MIN_CHUNK_ALIGN: usize = FOOTER_ALIGN;

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
fn invalid_mut<T>(addr: usize) -> *mut T {
  unsafe { core::mem::transmute(addr) }
}

#[inline(always)]
fn addr<T: ?Sized>(p: *const T) -> usize {
  let p = p as *const ();
  unsafe { core::mem::transmute(p) }
}

#[inline(always)]
fn mask(p: *mut u8, mask: usize) -> *mut u8 {
  p.wrapping_sub(addr(p) & ! mask)
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

impl Error for Void {
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
// ArenaError
//
////////////////////////////////////////////////////////////////////////////////

impl Error for ArenaError {
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

// SAFETY:
//
// ???
//
// Note that `Arena` can use interior mutability, so it is not `Sync`.

unsafe impl Send for Arena {}

unsafe fn dealloc_chunk_list(p: NonNull<Footer>) {
  // SAFETY:
  //
  // `p` must be the head of a valid linked list of chunks.

  // STACK SPACE:
  //
  // Chunk sizes grow exponentially, so stack usage is O(log(word size)) at
  // worst even without TCO.

  let p = p.as_ptr();
  let f = unsafe { p.read() };
  let p = p as *mut u8;
  let p = p.wrapping_add(FOOTER_SIZE);
  let p = p.wrapping_sub(f.layout.size());

  unsafe { alloc::alloc::dealloc(p, f.layout) }

  if let Some(p) = f.next {
    unsafe { dealloc_chunk_list(p) }
  }
}

#[inline(never)]
#[cold]
unsafe fn alloc_chunk_for<E: Error>
  (
    object: Layout,
    chunks: *mut Footer
  )
  -> Result<(*mut u8, *mut Footer), E>
{
  // SAFETY:
  //
  // `chunks` must either be null or point to a valid `Footer`.

  // POSTCONDITIONS:
  //
  // If this function returns `Ok(_)`, then it has allocated a new chunk and
  // placed it at the head of linked list whose previous head was `chunks`.
  // Additionally, the first (`*mut u8`) pointer points to memory suitable for
  // the start of an object with layout `object`.
  //
  // If this function returns `Err(_)`, then the linked list of chunks is
  // unmodified.

  const _: () = assert!(MIN_CHUNK_SIZE % MIN_CHUNK_ALIGN == 0);
  const _: () = assert!(MIN_CHUNK_SIZE <= isize::MAX as usize);
  const _: () = assert!(FOOTER_SIZE <= MIN_CHUNK_SIZE);
  const _: () = assert!(FOOTER_ALIGN <= MIN_CHUNK_ALIGN);

  let chunks = NonNull::new(chunks);

  let total_allocated =
    match chunks {
      None => 0,
      Some(chunks) => unsafe { chunks.as_ref() }.total_allocated
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

  let lo = unsafe { alloc::alloc::alloc(layout) };

  if lo.is_null() {
    return Err(E::global_alloc_error(layout));
  }

  // We have made sure that the chunk is aligned to at least
  // `align_of::<Footer>()` and that its size is a multiple of
  // `align_of::<Footer>(), so we can place the tail at the very end of the
  // chunk.

  let hi = lo.wrapping_add(size).wrapping_sub(FOOTER_SIZE) as *mut Footer;

  let total_allocated = total_allocated.saturating_add(size);
  let f = Footer { layout, next: chunks, total_allocated };

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
      lo: Cell::new(invalid_mut(1)),
      hi: Cell::new(invalid_mut(0)),
    }
  }

  /// Gets a handle with which to allocate objects from the arena. The lifetime
  /// from this mutable borrow is propagated to those allocations.

  #[inline(always)]
  pub fn allocator(&mut self) -> &mut Allocator<'_> {
    // SAFETY:
    //
    // Various allocation methods use unsafe code to create references from
    // pointers.  For that code to be sound, it is necessary for every user
    // accessible `Allocator<_>` to have an appropriately restricted lifetime
    // parameter.

    let p = self as *mut _;
    let p = p as *mut _;

    // SAFETY:
    //
    // The soundness of this cast depends on the fact that `Allocator` is
    // `#[repr(transparent)]` with an `Arena` field.

    unsafe { &mut *p }
  }

  /// Deallocates all objects previously allocated from the arena. The arena
  /// may release some, but not necessarily all, of its memory back to the
  /// global allocator.

  pub fn reset(&mut self) {
    // SAFETY:
    //
    // Various allocation methods use unsafe code to create references from
    // pointers.  For that code to be sound, it is necessary for calling this
    // method to imply that any lifetime associated with an `Allocator<_>` has
    // already ended.

    let p = self.hi.get();

    if ! p.is_null() {
      let f = unsafe { &mut *p };
      let p = p as *mut u8;
      let p = p.wrapping_add(FOOTER_SIZE).wrapping_sub(f.layout.size());

      self.lo.set(p);

      if let Some(next) = f.next {
        f.next = None;
        unsafe { dealloc_chunk_list(next) }
      }
    }
  }

  #[inline(always)]
  fn alloc<E: Error>(&mut self, layout: Layout) -> Result<NonNull<u8>, E> {
    let size = layout.size();
    let align = layout.align();

    let lo = self.lo.get_mut();
    let hi = self.hi.get_mut();

    let p = *lo;
    let q = *hi;

    let p = mask(p.wrapping_add(align - 1), ! (align - 1));

    if size as isize > addr(q).wrapping_sub(addr(p)) as isize {
      let (p, q) = unsafe { alloc_chunk_for::<E>(layout, q) }?;
      *lo = p;
      *hi = q;
    } else {
      *lo = p;
    }

    let p = *lo;
    let r = unsafe { NonNull::new_unchecked(p) };
    let p = p.wrapping_add(size);

    *lo = p;

    Ok(r)
  }

  #[cfg(feature = "allocator_api")]
  #[inline(always)]
  fn alloc_shared<E: Error>(&self, layout: Layout) -> Result<NonNull<u8>, E> {
    let size = layout.size();
    let align = layout.align();

    let p = self.lo.get();
    let q = self.hi.get();

    let p = mask(p.wrapping_add(align - 1), ! (align - 1));

    if size as isize > addr(q).wrapping_sub(addr(p)) as isize {
      let (p, q) = unsafe { alloc_chunk_for::<E>(layout, q) }?;
      self.lo.set(p);
      self.hi.set(q);
    } else {
      self.lo.set(p);
    }

    let p = self.lo.get();
    let r = unsafe { NonNull::new_unchecked(p) };
    let p = p.wrapping_add(size);

    self.lo.set(p);

    Ok(r)
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    let p = self.hi.get();

    if let Some(p) = NonNull::new(p) {
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
    f.debug_struct("Arena")
      .field("lo", &self.lo.get())
      .field("hi", &self.hi.get())
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Allocator
//
////////////////////////////////////////////////////////////////////////////////

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn gen_alloc<T, E: Error>(&mut self) -> Result<Slot<'a, T>, E> {
    let p = self.0.alloc::<E>(Layout::new::<T>())?;
    let p = p.cast();

    // SAFETY:
    //
    // To satisfy invariants for `Slot`, we require that
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(Slot(p, PhantomData))
  }

  #[inline(always)]
  fn gen_alloc_slice<T, E: Error>(&mut self, len: usize) -> Result<Slot<'a, [T]>, E> {
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

    let p = self.0.alloc::<E>(layout)?;
    let p = p.as_ptr();
    let p = p as *mut _;
    let p = ptr::slice_from_raw_parts_mut(p, len);

    // SAFETY:
    //
    // To satisfy invariants for `Slot`, we require that
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(Slot(unsafe { NonNull::new_unchecked(p) }, PhantomData))
  }

  #[inline(always)]
  fn gen_alloc_layout<E: Error>(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, E> {
    let p = self.0.alloc::<E>(layout)?;
    let p = p.as_ptr();
    let p = ptr::slice_from_raw_parts_mut(p, layout.size());

    // SAFETY:
    //
    // To satisfy invariants for `Slot`, we require that
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(Slot(unsafe { NonNull::new_unchecked(p) }, PhantomData))
  }

  #[inline(always)]
  fn gen_copy_slice<T: Copy, E: Error>(&mut self, src: &[T]) -> Result<&'a mut [T], E> {
    // NB:
    //
    // - `Copy` implies `!Drop`.
    // - The existence of `src` implies that we'll construct a valid layout.

    let size_of_element = size_of::<T>();
    let align = align_of::<T>();
    let n = src.len();
    let size = size_of_element * n;
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let p = self.0.alloc::<E>(layout)?;
    let p = p.as_ptr();
    let p = p as *mut _;
    let q = src.as_ptr();

    // SAFETY:
    //
    // - The `src` argument is valid for reading `T`s.
    // - The `dst` argument is valid for writing `T`s.
    // - The `src` and `dst` regions do not overlap.
    //
    // Note that the above holds, and in particular that the pointers are
    // non-null and aligned, even if we need to do a zero-byte read and write.

    unsafe { ptr::copy_nonoverlapping(q, p, n) };

    // SAFETY:
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.
    // - The memory is initialized.

    Ok(unsafe { slice::from_raw_parts_mut(p, n) })
  }

  #[inline(always)]
  fn gen_copy_str<E: Error>(&mut self, src: &str) -> Result<&'a mut str, E> {
    let p = self.gen_copy_slice(src.as_bytes())?;

    // SAFETY:
    //
    // The byte array is valid UTF-8 because `src` was valid UTF-8.

    Ok(unsafe { str::from_utf8_unchecked_mut(p) })
  }

  /// Allocates memory for a single object.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    Void::unwrap(self.gen_alloc())
  }

  /// Allocates memory for a single object.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.


  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, ArenaError> {
    self.gen_alloc()
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    Void::unwrap(self.gen_alloc_slice(len))
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, ArenaError> {
    self.gen_alloc_slice(len)
  }

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> Slot<'a, [u8]> {
    Void::unwrap(self.gen_alloc_layout(layout))
  }

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, ArenaError> {
    self.gen_alloc_layout(layout)
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_slice<T: Copy>(&mut self, src: &[T]) -> &'a mut [T] {
    Void::unwrap(self.gen_copy_slice(src))
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_slice<T: Copy>(&mut self, src: &[T]) -> Result<&'a mut [T], ArenaError> {
    self.gen_copy_slice(src)
  }

  /// Copies the string into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    Void::unwrap(self.gen_copy_str(src))
  }

  /// Copies the string into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, ArenaError> {
    self.gen_copy_str(src)
  }
}

impl fmt::Debug for Allocator<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("Allocator")
      .field("lo", &self.0.lo.get())
      .field("hi", &self.0.hi.get())
      .finish()
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

// SAFETY:
//
// The `Slot` type conforms to the usual shared xor mutable discipline,
// despite containing a pointer.

unsafe impl<'a, T: ?Sized + Send> Send for Slot<'a, T> {}

unsafe impl<'a, T: ?Sized + Sync> Sync for Slot<'a, T> {}

impl<'a, T> fmt::Debug for Slot<'a, T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Slot")
      .field(&self.0)
      .finish()
  }
}

impl<'a, T: ?Sized> Slot<'a, T> {
  /// Converts the slot into a non-null pointer to its underlying memory.
  ///
  /// The pointer is properly aligned.

  pub fn as_non_null(self) -> NonNull<T> {
    self.0
  }

  /// Converts the slot into a pointer to its underlying memory.
  ///
  /// The pointer is non-null and properly aligned.

  pub fn as_ptr(self) -> *mut T {
    self.0.as_ptr()
  }
}

impl<'a, T> Slot<'a, T> {
  /// Converts the slot into a reference to an uninitialized value.

  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    let p = self.0.as_ptr();
    let p = p as *mut _;

    // SAFETY:
    //
    // The pointed-to memory is valid for `T`, though uninitialized.

    unsafe { &mut *p }
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
    let p = self.0.as_ptr();
    let p = p as *mut _;

    // SAFETY:
    //
    // The pointed-to memory is valid for an array of `T`s, though
    // uninitialized.

    unsafe { &mut *p }
  }

  /// Initializes the array with values produced by calling the given function
  /// with each index in order.
  ///
  /// # Panics
  ///
  /// Panics if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init_array<F: FnMut(usize) -> T>(self, f: F) -> &'a mut [T; N] {
    if needs_drop::<T>() {
      panic_type_needs_drop();
    }

    let mut f = f;

    let p = self.as_uninit_array();

    for (i, elt) in p.iter_mut().enumerate() {
      let _: _ = elt.write(f(i));
    }

    let p = p as *mut _;
    let p = p as *mut _;

    // SAFETY:
    //
    // Every array element has been initialized.

    unsafe { &mut *p }
  }
}

impl<'a, T> Slot<'a, [T]> {
  /// The length of the slice (in items, not bytes) occupying the slot.

  #[inline(always)]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  /// Converts the slot into a reference to a slice of uninitialized values.

  #[inline(always)]
  pub fn as_uninit_slice(self) -> &'a mut [MaybeUninit<T>] {
    let n = self.0.len();
    let p = self.0.as_ptr();
    let p = p as *mut _;

    // SAFETY:
    //
    // The pointed-to memory is valid for a slice of `T`s, though
    // uninitialized.

    unsafe { slice::from_raw_parts_mut(p, n) }
  }

  /// Initializes the slice with values produced by calling the given function
  /// with each index in order.
  ///
  /// # Panics
  ///
  /// Panics if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init_slice<F: FnMut(usize) -> T>(self, f: F) -> &'a mut [T] {
    if needs_drop::<T>() {
      panic_type_needs_drop();
    }

    let mut f = f;

    let p = self.as_uninit_slice();

    for (i, elt) in p.iter_mut().enumerate() {
      let _: _ = elt.write(f(i));
    }

    let p = p as *mut _;
    let p = p as *mut _;

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { &mut *p }
  }
}

#[cfg(feature = "allocator_api")]
impl Error for alloc::alloc::AllocError {
  #[inline(always)]
  fn global_alloc_error(_: Layout) -> Self { Self {} }

  #[inline(always)]
  fn layout_overflow() -> Self { Self {} }
}

#[cfg(feature = "allocator_api")]
unsafe impl<'a> alloc::alloc::Allocator for Allocator<'a> {
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, alloc::alloc::AllocError> {
    let p = self.0.alloc_shared::<alloc::alloc::AllocError>(layout)?;
    let p = p.as_ptr();
    let p = ptr::slice_from_raw_parts_mut(p, layout.size());

    Ok(unsafe { NonNull::new_unchecked(p) })
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    let _ = self;
    let _ = ptr;
    let _ = layout;
  }
}
