#![doc = include_str!("../README.md")]
#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(missing_docs)]
#![warn(non_ascii_idents)]
#![warn(trivial_numeric_casts)]
#![warn(unreachable_pub)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]
#![warn(unused_results)]

mod prelude;
mod raw;
use crate::prelude::*;

/// An arena allocator.

pub struct Arena(Allocator<'static>);

/// A handle for allocating objects from an arena with a particular lifetime.

pub struct Allocator<'a>(raw::Arena, InvariantLifetime<'a>);

/// An uninitialized slot in the arena.
///
/// Typically you will immediately call [`init`](Self::init) or
/// [`init_slice`](Self::init_slice) to initialize the slot.

pub struct Slot<'a, T: 'a + ?Sized>(NonNull<T>, InvariantLifetime<'a>);

// SAFETY:
//
// The `Slot` type conforms to the usual shared xor mutable discipline,
// despite containing a pointer.

unsafe impl<'a, T: ?Sized + Send> Send for Slot<'a, T> {}

unsafe impl<'a, T: ?Sized + Sync> Sync for Slot<'a, T> {}

// We make the `Allocator` and `Slot` types invariant with respect to their
// associated lifetime. It would be ok to make them covariant, but that
// shouldn't be necessary for any use case.

type InvariantLifetime<'a> = PhantomData<fn(&'a ()) -> &'a ()>;

/// A failed allocation from the arena.

#[derive(Debug)]
pub struct AllocError;

impl fmt::Display for AllocError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    f.write_str("AllocError")
  }
}

impl raw::Error for AllocError {
  #[inline(always)]
  fn global_alloc_error(_: Layout) -> Self { Self }

  #[inline(always)]
  fn layout_overflow() -> Self { Self }
}

enum Panicked {}

impl Panicked {
  #[inline(always)]
  fn unwrap<T>(x: Result<T, Panicked>) -> T {
    match x {
      Ok(x) => x,
      Err(e) => match e {}
    }
  }
}

impl raw::Error for Panicked {
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

#[inline(never)]
#[cold]
fn panic_type_needs_drop() -> ! {
  panic!("type needs drop")
}

impl Arena {
  /// Creates a new arena. This does not acquire any memory from the global
  /// allocator.

  #[inline(always)]
  pub fn new() -> Self {
    Self(Allocator(raw::Arena::new(), PhantomData))
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

    let p = &mut self.0;
    let p = p as *mut _;
    let p = p as *const _;
    let p = p as *mut _;
    unsafe { &mut *p }
  }

  /// Deallocates all objects previously allocated from the arena. The arena
  /// may release some, but not necessarily all, of its memory back to the
  /// global allocator.

  #[inline(always)]
  pub fn reset(&mut self) {
    // SAFETY:
    //
    // Various allocation methods use unsafe code to create references from
    // pointers.  For that code to be sound, it is necessary for calling this
    // method to imply that any lifetime associated with an `Allocator<_>` has
    // already ended.

    self.0.0.reset()
  }
}

impl Default for Arena {
  #[inline(always)]
  fn default() -> Self {
    Self::new()
  }
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn gen_alloc<T, E: raw::Error>(&mut self) -> Result<Slot<'a, T>, E> {
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
  fn gen_alloc_slice<T, E: raw::Error>(&mut self, len: usize) -> Result<Slot<'a, [T]>, E> {
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
    let p = p.as_ptr() as *mut _;
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
  fn gen_alloc_layout<E: raw::Error>(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, E> {
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
  fn gen_copy_slice<T: Copy, E: raw::Error>(&mut self, src: &[T]) -> Result<&'a mut [T], E> {
    // NB:
    //
    // - `Copy` implies `!Drop`.
    // - The existence of `src` implies that we'll construct a valid layout.

    let size_of_element = size_of::<T>();
    let align = align_of::<T>();
    let len = src.len();
    let size = size_of_element * len;
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let p = self.0.alloc::<E>(layout)?;
    let p = p.as_ptr() as *mut _;

    // SAFETY:
    //
    // - The `src` argument is valid for reading `T`s.
    // - The `dst` argument is valid for writing `T`s.
    // - The `src` and `dst` regions do not overlap.
    //
    // Note that the above holds, and in particular that the pointers are
    // non-null and aligned, even if we need to do a zero-byte read and write.

    unsafe { ptr::copy_nonoverlapping(src.as_ptr(), p, len) };

    // SAFETY:
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.
    // - The memory is initialized.

    Ok(unsafe { slice::from_raw_parts_mut(p, len) })
  }

  #[inline(always)]
  fn gen_copy_str<E: raw::Error>(&mut self, src: &str) -> Result<&'a mut str, E> {
    let t = self.gen_copy_slice(src.as_bytes())?;

    // SAFETY:
    //
    // The byte array is valid UTF-8 because `src` was valid UTF-8.

    Ok(unsafe { str::from_utf8_unchecked_mut(t) })
  }

  /// Allocates memory for a single object.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    Panicked::unwrap(self.gen_alloc())
  }

  /// Allocates memory for a single object.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.


  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError> {
    self.gen_alloc()
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    Panicked::unwrap(self.gen_alloc_slice(len))
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, AllocError> {
    self.gen_alloc_slice(len)
  }

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> Slot<'a, [u8]> {
    Panicked::unwrap(self.gen_alloc_layout(layout))
  }

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<Slot<'a, [u8]>, AllocError> {
    self.gen_alloc_layout(layout)
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_slice<T: Copy>(&mut self, src: &[T]) -> &'a mut [T] {
    Panicked::unwrap(self.gen_copy_slice(src))
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_slice<T: Copy>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError> {
    self.gen_copy_slice(src)
  }

  /// Copies the string into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    Panicked::unwrap(self.gen_copy_str(src))
  }

  /// Copies the string into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    self.gen_copy_str(src)
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
    let p = self.0.as_ptr() as *mut _;

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
    let p = self.0.as_ptr() as *mut _;

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

    // SAFETY:
    //
    // Every slice element has been initialized.

    unsafe { slice_assume_init_mut(p) }
  }
}
