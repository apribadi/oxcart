#[derive(
  Clone,
  Copy,
  Eq,
  Hash,
  Ord,
  PartialEq,
  PartialOrd,
)]
#[repr(transparent)]
pub struct ptr(*mut u8);

unsafe impl Send for ptr { }

unsafe impl Sync for ptr { }

impl ptr {
  /// Creates a pointer with the given address and no provenance.

  #[inline(always)]
  pub const fn invalid(addr: usize) -> ptr {
    // Once the `strict_provenance` feature has been stabilized, this should
    // use the `core::ptr::invalid` function.

    ptr(unsafe { core::mem::transmute::<usize, *mut u8>(addr) })
  }

  /// An invalid pointer with address zero.

  pub const NULL: ptr = ptr::invalid(0);

  /// Gets the address of the pointer.

  #[inline(always)]
  pub fn addr(self) -> usize {
    // NB: This must not be a `const` function.
    //
    // Transmuting a pointer into an integer in a const context is undefined
    // behavior.

    // Once the `strict_provenance` feature has been stabilized, this should
    // use the `addr` method on the primitive pointer type.

    unsafe { core::mem::transmute::<*mut u8, usize>(self.0) }
  }

  /// Whether the pointer has address zero.

  #[inline(always)]
  pub fn is_null(self) -> bool {
    self.addr() == 0
  }

  #[inline(always)]
  pub const fn from_const_ptr<T: ?Sized>(x: *const T) -> ptr {
    ptr(x as *mut u8)
  }

  #[inline(always)]
  pub const fn from_mut_ptr<T: ?Sized>(x: *mut T) -> ptr {
    ptr(x as *mut u8)
  }

  #[inline(always)]
  pub const fn from_ref<T: ?Sized>(x: &T) -> ptr {
    Self::from_const_ptr(x)
  }

  #[inline(always)]
  pub fn from_mut_ref<T: ?Sized>(x: &mut T) -> ptr {
    Self::from_mut_ptr(x)
  }

  #[inline(always)]
  pub const fn from_non_null<T: ?Sized>(x: core::ptr::NonNull<T>) -> ptr {
    Self::from_mut_ptr(x.as_ptr())
  }

  /// Adds the given byte offset to the pointer's address with wrapping
  /// arithmetic.

  #[inline(always)]
  pub fn offset(self, n: isize) -> ptr {
    ptr(self.0.wrapping_offset(n))
  }

  /// Adds the given byte offset to the pointer's address with wrapping
  /// arithmetic.

  #[inline(always)]
  pub fn add(self, n: usize) -> ptr {
    ptr(self.0.wrapping_add(n))
  }

  /// Subtracts the given byte offset from the pointer's address with wrapping
  /// arithmetic.

  #[inline(always)]
  pub fn sub(self, n: usize) -> ptr {
    ptr(self.0.wrapping_sub(n))
  }

  /// Computes the difference in bytes between the two pointers' addresses with
  /// wrapping arithmetic.

  #[inline(always)]
  pub fn diff(self, other: Self) -> usize {
    self.addr().wrapping_sub(other.addr())
  }

  /// Computes the offset needed to add to `x` to align it to an address that
  /// is a multiple of `align`.
  ///
  /// If `align` is not a power of two, returns an unspecified value.

  #[inline(always)]
  pub fn align_offset(self, align: usize) -> usize {
    self.addr() & align.wrapping_neg()
  }

  #[inline(always)]
  pub fn gep<T>(self, index: isize) -> ptr {
    self.offset((core::mem::size_of::<T>() as isize).wrapping_mul(index))
  }

  /// # Safety:
  ///
  /// See `core::ptr::read`.

  #[inline(always)]
  pub unsafe fn read<T>(self) -> T {
    let x = self.as_const_ptr::<T>();
    unsafe { core::ptr::read(x) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::read_unaligned`.

  #[inline(always)]
  pub unsafe fn read_unaligned<T>(self) -> T {
    let x = self.as_const_ptr::<T>();
    unsafe { core::ptr::read_unaligned(x) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::read_volatile`.

  #[inline(always)]
  pub unsafe fn read_volatile<T>(self) -> T {
    let x = self.as_const_ptr::<T>();
    unsafe { core::ptr::read_volatile(x) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::write`.

  #[inline(always)]
  pub unsafe fn write<T>(self, value: T) {
    let x = self.as_mut_ptr::<T>();
    unsafe { core::ptr::write(x, value) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::write_unaligned`.

  #[inline(always)]
  pub unsafe fn write_unaligned<T>(self, value: T) {
    let x = self.as_mut_ptr::<T>();
    unsafe { core::ptr::write_unaligned(x, value) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::write_volatile`.

  #[inline(always)]
  pub unsafe fn write_volatile<T>(self, value: T) {
    let x = self.as_mut_ptr::<T>();
    unsafe { core::ptr::write_volatile(x, value) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::replace`.

  #[inline(always)]
  pub unsafe fn replace<T>(self, value: T) -> T {
    let x = self.as_mut_ptr::<T>();
    unsafe { core::ptr::replace(x, value) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::drop_in_place`.

  #[inline(always)]
  pub unsafe fn drop_in_place<T>(self) {
    let x = self.as_mut_ptr::<T>();
    unsafe { core::ptr::drop_in_place(x) }
  }

  /// # Safety:
  ///
  /// See `core::ptr::copy_nonoverlapping`.

  #[inline(always)]
  pub unsafe fn copy_nonoverlapping<T>(src: ptr, dst: ptr, count: usize) {
    let src = src.as_const_ptr();
    let dst = dst.as_mut_ptr();
    unsafe { core::ptr::copy_nonoverlapping::<T>(src, dst, count) };
  }

  /// # Safety:
  ///
  /// See `core::ptr::swap_nonoverlapping`.

  #[inline(always)]
  pub unsafe fn swap_nonoverlapping<T>(x: ptr, y: ptr, count: usize) {
    let x = x.as_mut_ptr();
    let y = y.as_mut_ptr();
    unsafe { core::ptr::swap_nonoverlapping::<T>(x, y, count) };
  }

  #[inline(always)]
  pub fn as_const_ptr<T>(self) -> *const T {
    self.0 as *const T
  }

  #[inline(always)]
  pub fn as_mut_ptr<T>(self) -> *mut T {
    self.0 as *mut T
  }

  #[inline(always)]
  pub fn as_slice_const_ptr<T>(self, len: usize) -> *const [T] {
    core::ptr::slice_from_raw_parts(self.as_const_ptr(), len)
  }

  #[inline(always)]
  pub fn as_slice_mut_ptr<T>(self, len: usize) -> *mut [T] {
    core::ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), len)
  }

  #[inline(always)]
  pub unsafe fn as_ref<'a, T>(self) -> &'a T {
    let x = self.as_const_ptr();
    unsafe { &*x }
  }

  #[inline(always)]
  pub unsafe fn as_mut_ref<'a, T>(self) -> &'a mut T {
    let x = self.as_mut_ptr();
    unsafe { &mut *x }
  }

  #[inline(always)]
  pub unsafe fn as_slice_ref<'a, T>(self, len: usize) -> &'a [T] {
    let x = self.as_slice_const_ptr(len);
    unsafe { &*x }
  }

  #[inline(always)]
  pub unsafe fn as_slice_mut_ref<'a, T>(self, len: usize) -> &'a mut [T] {
    let x = self.as_slice_mut_ptr(len);
    unsafe { &mut *x }
  }

  /// # Safety:
  ///
  /// The pointer must not have address zero.

  #[inline(always)]
  pub unsafe fn as_non_null<T>(self) -> core::ptr::NonNull<T> {
    unsafe { core::ptr::NonNull::new_unchecked(self.as_mut_ptr()) }
  }
}

pub trait ThinRef {
  unsafe fn cast(x: ptr) -> Self;
}

impl<T: ?Sized> From<*const T> for ptr {
  #[inline(always)]
  fn from(value: *const T) -> ptr {
    ptr::from_const_ptr(value)
  }
}

impl<T: ?Sized> From<*mut T> for ptr {
  #[inline(always)]
  fn from(value: *mut T) -> ptr {
    ptr::from_mut_ptr(value)
  }
}

impl<T: ?Sized> From<&T> for ptr {
  #[inline(always)]
  fn from(value: &T) -> ptr {
    ptr::from_ref(value)
  }
}

impl<T: ?Sized> From<&mut T> for ptr {
  #[inline(always)]
  fn from(value: &mut T) -> ptr {
    ptr::from_mut_ref(value)
  }
}

impl<T: ?Sized> From<core::ptr::NonNull<T>> for ptr {
  #[inline(always)]
  fn from(value: core::ptr::NonNull<T>) -> ptr {
    ptr::from_non_null(value)
  }
}

impl<T> From<ptr> for *const T {
  #[inline(always)]
  fn from(value: ptr) -> *const T {
    value.as_const_ptr()
  }
}

impl<T> From<ptr> for *mut T {
  #[inline(always)]
  fn from(value: ptr) -> *mut T {
    value.as_mut_ptr()
  }
}

impl core::ops::Add<isize> for ptr {
  type Output = ptr;

  #[inline(always)]
  fn add(self, rhs: isize) -> ptr {
    self.offset(rhs)
  }
}

impl core::ops::AddAssign<isize> for ptr {
  #[inline(always)]
  fn add_assign(&mut self, rhs: isize) {
    *self = *self + rhs;
  }
}

impl core::ops::Add<usize> for ptr {
  type Output = ptr;

  #[inline(always)]
  fn add(self, rhs: usize) -> ptr {
    self.add(rhs)
  }
}

impl core::ops::AddAssign<usize> for ptr {
  #[inline(always)]
  fn add_assign(&mut self, rhs: usize) {
    *self = *self + rhs;
  }
}

impl core::ops::Sub<isize> for ptr {
  type Output = ptr;

  #[inline(always)]
  fn sub(self, rhs: isize) -> ptr {
    self.offset(rhs.wrapping_neg())
  }
}

impl core::ops::SubAssign<isize> for ptr {
  #[inline(always)]
  fn sub_assign(&mut self, rhs: isize) {
    *self = *self - rhs;
  }
}

impl core::ops::Sub<usize> for ptr {
  type Output = ptr;

  #[inline(always)]
  fn sub(self, rhs: usize) -> ptr {
    self.sub(rhs)
  }
}

impl core::ops::SubAssign<usize> for ptr {
  #[inline(always)]
  fn sub_assign(&mut self, rhs: usize) {
    *self = *self - rhs;
  }
}

impl core::ops::Sub<ptr> for ptr {
  type Output = usize;

  #[inline(always)]
  fn sub(self, rhs: ptr) -> usize {
    self.diff(rhs)
  }
}

impl core::ops::Neg for ptr {
  type Output = usize;

  #[inline(always)]
  fn neg(self) -> usize {
    self.addr().wrapping_neg()
  }
}

impl core::fmt::Debug for ptr {
  fn fmt(&self, out: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(out, "0x{:01$x}", self.addr(), (usize::BITS / 4) as usize)
  }
}
