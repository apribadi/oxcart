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
mod internal;

use crate::prelude::*;

pub struct Arena(Allocator<'static>);

pub struct Allocator<'a>(internal::Arena, PhantomData<&'a ()>);

pub struct Uninit<'a, T: 'a>(pub &'a mut MaybeUninit<T>);

pub struct UninitSlice<'a, T: 'a>(pub &'a mut [MaybeUninit<T>]);

#[derive(Clone, Debug)]
pub struct AllocError;

enum Panicked {}

// SAFETY:
//
// The `Arena` and `Allocator` types conform to the usual shared xor mutable
// discipline.

unsafe impl Send for Arena {}

unsafe impl Sync for Arena {}

unsafe impl<'a> Send for Allocator<'a> {}

unsafe impl<'a> Sync for Allocator<'a> {}

impl internal::FromError for AllocError {
  #[inline(always)]
  fn from_error(_: internal::Error) -> Self {
    Self
  }
}

impl internal::FromError for Panicked {
  #[inline(never)]
  fn from_error(_: internal::Error) -> Self {
    panic!()
  }
}

#[inline(always)]
fn ok_or_panicked<T>(x: Result<T, Panicked>) -> T {
  match x {
    Ok(x) => x,
    Err(e) => match e {}
  }
}

impl Arena {
  /// Creates a new arena.

  #[inline(always)]
  pub fn new() -> Self {
    Self(Allocator(internal::Arena::new(), PhantomData))
  }

  #[inline(always)]
  pub fn region<F, T>(&mut self, f: F) -> T
    where F: for<'a, 'b> FnOnce(&'a mut Allocator<'b>) -> T
  {
    let p: &'_ mut Allocator<'static> = &mut self.0;
    let p: *mut Allocator<'static> = p;
    let p: *mut Allocator<'_> = p.cast();
    let p: &'_ mut Allocator<'_> = unsafe { &mut *p };

    let t = f(p);

    self.0.0.reset();

    t
  }
}

impl<'a> Allocator<'a> {
  #[inline(always)]
  fn gen_alloc<T, E>(&mut self) -> Result<Uninit<'a, T>, E>
    where E: internal::FromError
  {
    if /* const */ needs_drop::<T>() {
      return Err(E::from_error(internal::Error::TypeNeedsDrop));
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
    where E: internal::FromError
  {
    let size_of_element = size_of::<T>();
    let align = align_of::<T>();

    if /* const */ needs_drop::<T>() {
      return Err(E::from_error(internal::Error::TypeNeedsDrop));
    }

    // Because `size_of::<T>() % align_of::<T>() == 0` for all types `T`, we
    // don't need to consider the case where rounding the size up to the
    // alignment exceeds `isize::MAX`.

    if size_of_element != 0 && len > isize::MAX as usize / size_of_element {
      return Err(E::from_error(internal::Error::SliceTooLong(len)));
    }

    let layout = unsafe { Layout::from_size_align_unchecked(size_of_element * len, align) };

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
    where E: internal::FromError
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
    ok_or_panicked(self.gen_alloc())
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
    ok_or_panicked(self.gen_alloc_slice(len))
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
    ok_or_panicked(self.gen_alloc_layout(layout))
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

    let p: *mut [MaybeUninit<T>] = self.0;
    let p: *mut [T] = p as *mut [T];

    // SAFETY:
    //
    // - Every slice element has been initialized.

    unsafe { &mut *p }
  }
}
