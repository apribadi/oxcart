//! An arena allocator.
//!
//! # Example
//!
//! ```
//! let mut arena = oxcart::Arena::new();
//! let allocator = arena.allocator();
//!
//! let x: &mut u64 = allocator.alloc().init(13);
//! let y: &mut [u64] = allocator.alloc_slice(5).init(|i| i as u64);
//!
//! assert!(*x == 13);
//! assert!(y == &[0, 1, 2, 3, 4]);
//!
//! arena.reset();
//! ```

#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(elided_lifetimes_in_paths)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]

mod prelude;

mod raw;

use crate::prelude::*;

/// A fast arena allocator.

pub struct Arena(Allocator<'static>);

/// A handle for allocating objects from the arena with a particular lifetime.

pub struct Allocator<'a>(raw::Arena, PhantomData<&'a ()>);

/// An uninitialized object in the arena.

pub struct Uninit<'a, T: 'a>(pub &'a mut MaybeUninit<T>);

/// An uninitialized slice of objects in the arena.

pub struct UninitSlice<'a, T: 'a>(pub &'a mut [MaybeUninit<T>]);

/// A failed allocation from the arena.

#[derive(Clone, Debug)]
pub struct AllocError;

// SAFETY:
//
// The `Arena` and `Allocator` types conform to the usual shared xor mutable
// discipline so it is safe for them to be `Send` and `Sync`.

unsafe impl Send for Arena {}

unsafe impl Sync for Arena {}

unsafe impl<'a> Send for Allocator<'a> {}

unsafe impl<'a> Sync for Allocator<'a> {}

impl raw::Error for AllocError {
  #[inline(always)]
  fn global_alloc_error(_: Layout) -> Self { Self }

  #[inline(always)]
  fn layout_overflow() -> Self { Self }

  #[inline(always)]
  fn slice_too_long(_: usize) -> Self { Self }

  #[inline(always)]
  fn type_needs_drop() -> Self { Self }
}

impl raw::Error for Infallible {
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

  #[inline(never)]
  #[cold]
  fn slice_too_long(len: usize) -> Self {
    panic!("slice too long: {len}")
  }

  #[inline(never)]
  #[cold]
  fn type_needs_drop() -> Self {
    panic!("type needs drop")
  }
}

impl Arena {
  /// Creates a new arena.

  #[inline(always)]
  pub fn new() -> Self {
    Self(Allocator(raw::Arena::new(), PhantomData))
  }

  /// Gets a handle with which to allocate objects from the arena. The lifetime
  /// from this mutable borrow is propagated to those allocations.

  #[inline(always)]
  pub fn allocator<'a>(&'a mut self) -> &'a mut Allocator<'a> {
    // SAFETY:
    //
    // Various allocation methods on `Allocator<_>` use unsafe code to create
    // references from pointers.  For that code to be sound, it is necessary
    // for every user accessible `Allocator<_>` to have an appropriately
    // restricted lifetime parameter.
    //
    // Also, the lifetime parameter of `Allocator<_>` does not affect its
    // representation, so we end up with a reference to a well-formed value.

    let p: &'a mut Allocator<'static> = &mut self.0;
    let p: *mut Allocator<'static> = p;
    let p: *mut Allocator<'a> = p.cast();
    let p: &'a mut Allocator<'a> = unsafe { &mut *p };
    p
  }

  /// Deallocates all objects previously allocated from the arena. The arena
  /// may release some, but not necessarily all, of its memory back to the
  /// global allocator.

  #[inline(always)]
  pub fn reset(&mut self) {
    // SAFETY:
    //
    // Various allocation methods on `Allocator<_>` use unsafe code to create
    // references from pointers.  For that code to be sound, it is necessary
    // for this method to force the end of any lifetime associated with an
    // `Allocator<_>`.

    self.0.0.reset()
  }
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn gen_alloc<T, E>(&mut self) -> Result<Uninit<'a, T>, E>
    where E: raw::Error
  {
    if needs_drop::<T>() {
      return Err(E::type_needs_drop());
    }

    let p = self.0.alloc::<E>(Layout::new::<T>())?;
    let p = p.cast().as_ptr();

    // SAFETY:
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(Uninit(unsafe { &mut *p }))
  }

  #[inline(always)]
  fn gen_alloc_slice<T, E>(&mut self, len: usize) -> Result<UninitSlice<'a, T>, E>
    where E: raw::Error
  {
    let size_of_element = size_of::<T>();
    let align = align_of::<T>();

    if needs_drop::<T>() {
      return Err(E::type_needs_drop());
    }

    // Because `size_of::<T>() % align_of::<T>() == 0` for all types `T`, we
    // don't need to consider the case where rounding the size up to the
    // alignment exceeds `isize::MAX`.

    if size_of_element != 0 && len > isize::MAX as usize / size_of_element {
      return Err(E::slice_too_long(len));
    }

    let size = size_of_element * len;
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let p = self.0.alloc::<E>(layout)?;
    let p = p.cast().as_ptr();

    // SAFETY:
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(UninitSlice(unsafe { slice::from_raw_parts_mut(p, len) }))
  }

  #[inline(always)]
  fn gen_alloc_layout<E>(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
    where E: raw::Error
  {
    let p = self.0.alloc::<E>(layout)?;
    let p = p.cast().as_ptr();

    Ok(unsafe { slice::from_raw_parts_mut(p, layout.size()) })
  }

  #[inline(always)]
  fn gen_copy_slice<T: Copy, E>(&mut self, src: &[T]) -> Result<&'a mut [T], E>
    where E: raw::Error
  {
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
    let p = p.cast().as_ptr();

    // SAFETY:
    //
    // - The `src` argument is valid for reading `T`s.
    // - The `dst` argument is valid for writing `T`s.
    // - The `src` and `dst` regions do not overlap.
    //
    // Note that the above holds, and in particular the pointers are non-null
    // and aligned, even if we need to do zero-byte reads and writes.

    unsafe { copy_nonoverlapping(src.as_ptr(), p, len) };

    // SAFETY:
    //
    // - The pointer is non-null and aligned, even if `size == 0`.
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.
    // - The memory is initialized.

    Ok(unsafe { slice::from_raw_parts_mut(p, len) })
  }

  #[inline(always)]
  fn gen_copy_str<E>(&mut self, src: &str) -> Result<&'a mut str, E>
    where E: raw::Error
  {
    let a = self.gen_copy_slice(src.as_bytes())?;

    // SAFETY: The byte array is valid UTF-8.

    Ok(unsafe { str::from_utf8_unchecked_mut(a) })
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
    unwrap(self.gen_alloc())
  }

  /// Allocates memory for a single object.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc`](Self::alloc).

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Uninit<'a, T>, AllocError> {
    self.gen_alloc()
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
    unwrap(self.gen_alloc_slice(len))
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc_slice`](Self::alloc_slice).

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<UninitSlice<'a, T>, AllocError> {
    self.gen_alloc_slice(len)
  }

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// - Appending metadata to the allocation would overflow [`Layout`].
  /// - The global allocator failed to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
    unwrap(self.gen_alloc_layout(layout))
  }

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`alloc_layout`](Self::alloc_layout).

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError> {
    self.gen_alloc_layout(layout)
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Panics
  ///
  /// - Appending metadata to the allocation would overflow [`Layout`].
  /// - The global allocator failed to allocate memory.

  #[inline(always)]
  pub fn copy_slice<T: Copy>(&mut self, src: &[T]) -> &'a mut [T] {
    unwrap(self.gen_copy_slice(src))
  }

  /// Copies the slice into a new allocation.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`copy_slice`](Self::copy_slice).

  #[inline(always)]
  pub fn try_copy_slice<T: Copy>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError> {
    self.gen_copy_slice(src)
  }

  /// Copies the string into a new allocation.
  ///
  /// # Panics
  ///
  /// - Appending metadata to the allocation would overflow [`Layout`].
  /// - The global allocator failed to allocate memory.

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    unwrap(self.gen_copy_str(src))
  }

  /// Copies the string into a new allocation.
  ///
  /// # Errors
  ///
  /// See panic conditions for [`copy_str`](Self::copy_str).

  #[inline(always)]
  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    self.gen_copy_str(src)
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

    // SAFETY:
    //
    // - Every slice element has been initialized.

    unsafe { slice_assume_init_mut(self.0) }
  }
}

pub fn foo<'a>(allocator: &mut Allocator<'a>, s: &str) -> &'a mut str {
  allocator.copy_str(s)
}
