//! An arena allocator.
//!
//! # Example
//!
//! ```
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

pub struct Arena(Allocator<'static>);

pub struct Allocator<'a>(raw::Arena, PhantomData<&'a ()>);

pub struct Uninit<'a, T: 'a>(pub &'a mut MaybeUninit<T>);

pub struct UninitSlice<'a, T: 'a>(pub &'a mut [MaybeUninit<T>]);

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

  /// Deallocates objects previously allocated from the arena. The arena may
  /// release some, but not all, of its memory back to the global allocator.

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

    // SAFETY:
    //
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(Uninit(unsafe { p.cast().as_mut() }))
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

    // SAFETY:
    //
    // - The memory has the correct size and alignment.
    // - The memory is not aliased by any other reference.
    // - The memory is live for the duration of the assigned lifetime.

    Ok(UninitSlice(unsafe { slice::from_raw_parts_mut(p.cast().as_ptr(), len) }))
  }

  #[inline(always)]
  fn gen_alloc_layout<E>(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
    where E: raw::Error
  {
    let p = self.0.alloc::<E>(layout)?;

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
