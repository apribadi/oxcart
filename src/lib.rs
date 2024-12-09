#![doc = include_str!("../README.md")]
#![no_std]

extern crate alloc;

use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr::NonNull;
use pop::ptr;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PUBLIC TYPES                                                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/// A `Store` owns the memory reserved for some arena allocators.
///
/// The memory is released back to the global allocator when the `Store` is
/// dropped.

pub struct Store {
  root: ptr
}

/// An `Arena<'a>` allocates memory regions live for the lifetime `'a`.

pub struct Arena<'a> {
  span: Span,
  _phantom_data: PhantomData<&'a ()>
}

/// A `Slot<'a, T>` refers to uninitialized memory with lifetime `'a` which can
/// contain a `T`.
///
/// Typically you will initialize a slot with [`init`](Self::init) or
/// [`init_slice`](Self::init_slice).

pub struct Slot<'a, T: ?Sized>(NonNull<T>, PhantomData<fn(T) -> &'a ()>);

unsafe impl<'a, T: ?Sized> Send for Slot<'a, T> { }

unsafe impl<'a, T: ?Sized> Sync for Slot<'a, T> { }

impl <'a, T: ?Sized> core::panic::UnwindSafe for Slot<'a, T> { }

impl <'a, T: ?Sized> core::panic::RefUnwindSafe for Slot<'a, T> { }

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PRIVATE TYPES                                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

struct Head {
  next: ptr,
  size: usize,
}

#[derive(Clone, Copy)]
struct Span {
  tail: ptr,
  size: usize,
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// CONSTANTS                                                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// We allocate from an arena in multiples of `QUANTUM`.
//
// We require both
//
// - align_of::<Head>() <= QUANTUM, and
// - size_of::<Head>() % QUANTUM == 0
//
// and this definition of QUANTUM guarantees those two conditions.

const QUANTUM: usize = align_of::<Head>();

// Number of bits in a word.

const BITS: u32 = usize::BITS;

// We limit the total capacity of an arena to `MAX_SIZE`. It is the largest
// power of two that is a valid layout size.

const MAX_SIZE: usize = 1 << BITS - 2;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// UTILITY FUNCTIONS                                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
fn ceil_pow2(x: usize) -> usize {
  debug_assert!(1 <= x && x <= 1 << BITS - 1);

  1 << BITS - (x - 1).leading_zeros()
}

#[inline(always)]
fn min(x: usize, y: usize) -> usize {
  if x <= y { x } else { y }
}

#[inline(always)]
fn max(x: usize, y: usize) -> usize {
  if x >= y { x } else { y }
}

// SAFETY
//
// - A `Layout` with this `size` and `align == QUANTUM` must be valid.
// - The `size` must be non-zero.

unsafe fn global_alloc(size: usize) -> ptr {
  debug_assert!(Layout::from_size_align(size, QUANTUM).is_ok());
  debug_assert!(size != 0);

  let layout = unsafe { Layout::from_size_align_unchecked(size, QUANTUM) };
  let p = unsafe { ptr::from(alloc::alloc::alloc(layout)) };

  if p.is_null() {
    panic!("oxcart: Allocating with the global allocator failed!")
  }

  p
}

// SAFETY
//
// - The pointer `p` must refer to a currently allocated region that was
//   allocated with this `size` and `align == QUANTUM`.

unsafe fn global_free(p: ptr, size: usize) {
  debug_assert!(Layout::from_size_align(size, QUANTUM).is_ok());
  debug_assert!(size != 0);

  let layout = unsafe { Layout::from_size_align_unchecked(size, QUANTUM) };
  unsafe { alloc::alloc::dealloc(p.as_mut_ptr(), layout) };
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Store                                                                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

impl Store {
  /// Creates a new empty store. This does not reserve any memory from the
  /// global allocator.
  ///
  /// ```
  /// # use oxcart::Store;
  /// let mut store = Store::new();
  /// ```

  pub const fn new() -> Self {
    Store { root: ptr::NULL }
  }

  /// Creates a new store and pre-allocates approximately `size` bytes of
  /// memory.
  ///
  /// The `size` parameter is purely advisory, and guarentees neither
  ///
  /// - a lower bound on a set of allocations that can be made without
  ///   requesting additional memory from the global allocator, nor
  ///
  /// - an upper bound on the amount of memory requested from the global
  ///   allocator.
  ///
  /// ```
  /// # use oxcart::Store;
  /// let mut store = Store::with_capacity(100);
  /// ```

  pub fn with_capacity(size: usize) -> Self {
    let size = ceil_pow2(min(max(size, size_of::<Head>() + 1), MAX_SIZE));
    let root = unsafe { global_alloc(size) };
    unsafe { ptr::write(root, Head { next: ptr::NULL, size }) };
    Store { root }
  }

  /// Prepares an arena.
  ///
  /// The allocations from this arena will have a lifetime bounded by the
  /// lifetime of the `&'a mut self` method receiver.
  ///
  /// # Panics
  ///
  /// Panics if the underlying global memory allocator fails to deallocate or
  /// allocate memory.
  ///
  /// ```
  /// # use oxcart::Store;
  /// let mut store = Store::new();
  /// let mut arena = store.arena();
  /// ```

  pub fn arena<'a>(&'a mut self) -> Arena<'a> {
    if self.root.is_null() {
      // CASE 1: Zero slabs.

      const SIZE: usize = 1 << 16;

      let root = unsafe { global_alloc(SIZE) };

      unsafe { ptr::write(root, Head { next: ptr::NULL, size: SIZE }) };

      self.root = root;

      return Arena {
        span: Span {
          tail: root + SIZE,
          size: SIZE - size_of::<Head>()
        },
        _phantom_data: PhantomData
      };
    }

    let head = unsafe { self.root.as_ref::<Head>() };
    let next = head.next;
    let size = head.size;

    if next.is_null () {
      // CASE 2: Exactly one slab.

      return Arena {
        span: Span {
          tail: self.root + size,
          size: size - size_of::<Head>()
        },
        _phantom_data: PhantomData
      };
    }

    // CASE 3: Two or more slabs.

    let mut curr_slab = self.root;
    let mut next_slab = next;
    let mut prev_size = 0;
    let mut curr_size = size;

    // Unlink.

    self.root = ptr::NULL;

    // Free slabs.

    loop {
      unsafe { global_free(curr_slab, curr_size - prev_size) };

      if next_slab.is_null() { break; }

      let head = unsafe { next_slab.as_ref::<Head>() };
      curr_slab = next_slab;
      next_slab = head.next;
      prev_size = curr_size;
      curr_size = head.size;
    }

    // Allocate new block.

    debug_assert!(curr_size <= MAX_SIZE);

    let size = ceil_pow2(curr_size);
    let root = unsafe { global_alloc(size) };

    unsafe { ptr::write(root, Head { next: ptr::NULL, size }) };

    self.root = root;

    return Arena {
      span: Span {
        tail: root + size,
        size: size - size_of::<Head>()
      },
      _phantom_data: PhantomData
    };
  }
}

impl Drop for Store {
  fn drop(&mut self) {
    let mut curr_slab;
    let mut next_slab = self.root;
    let mut prev_size;
    let mut curr_size = 0;

    // Unlink.

    self.root = ptr::NULL;

    // Free blocks.

    while ! next_slab.is_null() {
      let head = unsafe { next_slab.as_ref::<Head>() };
      curr_slab = next_slab;
      next_slab = head.next;
      prev_size = curr_size;
      curr_size = head.size;

      unsafe { global_free(curr_slab, curr_size - prev_size) };
    }
  }
}

impl Default for Store {
  fn default() -> Self {
    Store::new()
  }
}

impl core::fmt::Debug for Store {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let mut slab = self.root;
    let mut size = 0;
    let mut list = alloc::vec::Vec::new();

    while ! slab.is_null() {
      let head = unsafe { slab.as_ref::<Head>() };
      list.push(head.size - size);
      slab = head.next;
      size = head.size;
    }

    let list = list.into_boxed_slice();

    f.debug_tuple("Store").field(&list).finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Arena                                                                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast(span: Span, layout: Layout) -> (Span, bool) {
  let p = span.tail;
  let n = span.size;
  let a = layout.align();
  let s = layout.size();

  unsafe { core::hint::assert_unchecked(p.addr() & QUANTUM - 1 == 0) };

  let d = s + (p.addr().wrapping_sub(s) & (a - 1 | QUANTUM - 1));

  (Span { tail: p - d, size: n.wrapping_sub(d) }, d <= n)
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow(span: &mut Span, layout: Layout) {
  let head = unsafe { (span.tail - span.size - size_of::<Head>()).as_mut_ref::<Head>() };
  let span_out = span;

  // PROPOSITION
  //
  // The following expression does not overflow.
  //
  // PROOF
  //
  // ???

  let size =
    size_of::<Head>()
      + (! (QUANTUM - 1) & QUANTUM - 1 + layout.size())
      + (! (QUANTUM - 1) & layout.align() - 1);

  if ! (size <= MAX_SIZE) {
    panic!("oxcart: Arena capacity would exceed maximum size!");
  }

  let prev_size = head.size;

  debug_assert!(prev_size <= MAX_SIZE);

  let size = ceil_pow2(max(size, prev_size));

  if ! (size <= MAX_SIZE - prev_size) {
    panic!("oxcart: Arena capacity would exceed maximum size!");
  }

  let curr_size = prev_size + size;

  debug_assert!(curr_size <= MAX_SIZE);

  let p = unsafe { global_alloc(size) };

  unsafe { ptr::write(p, Head { next: ptr::NULL, size: curr_size }) };

  head.next = p;

  let span = Span { tail: p + size, size: size - size_of::<Head>() };
  let span = unsafe { alloc_fast(span, layout).0 }; // Must succeed.

  *span_out = span;
}

impl<'a> Arena<'a> {
  #[inline(always)]
  fn alloc_internal(&mut self, layout: Layout) -> ptr {
    let span =
      match unsafe { alloc_fast(self.span, layout) } {
        (span, true) => span,
        (span, false) => {
          let mut span = span;
          unsafe { alloc_slow(&mut span, layout) };
          span
        }
      };
    self.span = span;
    span.tail
  }

  /// Allocates memory for a single value.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc().init(1_u64);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    let x = self.alloc_internal(Layout::new::<T>());
    Slot(unsafe { x.as_non_null() }, PhantomData)
  }

  /// Allocates memory for a slice of the given length.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc_slice(5).init_slice(|i| i as u64);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    if size_of::<T>() != 0 && ! (len <= isize::MAX as usize / size_of::<T>()) {
      panic!("oxcart: Layout computation would overflow!");
    }

    let align = align_of::<T>();
    let size = len * size_of::<T>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    let x = self.alloc_internal(layout);
    Slot(unsafe { x.as_slice_non_null(len) }, PhantomData)
  }

  /// Copies the given slice into a new allocation.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.copy_slice(&[0_u64, 1, 2, 3, 4]);
  /// ```
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_slice<T: Copy>(&mut self, src: &[T]) -> &'a mut [T] {
    let x = self.alloc_internal(Layout::for_value(src));
    let n = src.len();
    unsafe { ptr::copy_nonoverlapping::<T>(ptr::from(src), x, n) };
    unsafe { x.as_slice_mut_ref(n) }
  }

  /// Copies the given string into a new allocation.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.copy_str("Hello!");
  /// ```
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    let x = self.copy_slice(src.as_bytes());
    unsafe { core::str::from_utf8_unchecked_mut(x) }
  }

  /// Allocates memory for the given layout. The memory is valid for the
  /// lifetime `'a` from `Arena<'a>`.
  ///
  /// ```
  /// # use std::alloc::Layout;
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc_layout(Layout::new::<u64>());
  /// ```
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> NonNull<u8> {
    let x = self.alloc_internal(layout);
    unsafe { x.as_non_null() }
  }
}

impl<'a> core::fmt::Debug for Arena<'a> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("Arena").field(&self.span.size).finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Slot                                                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

impl<'a, T: ?Sized> Slot<'a, T> {
  #[inline(always)]
  fn ptr(&self) -> ptr {
    ptr::from(self.0)
  }
}

impl<'a, T> Slot<'a, T> {
  /// Converts the slot into a reference to an uninitialized value.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc().as_uninit().write(1_u64);
  /// ```

  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    unsafe { self.ptr().as_mut_ref() }
  }

  /// Initializes the slot with the given value.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc().init(1_u64);
  /// ```
  ///
  /// # Static Panics
  ///
  /// Compilation fails if `T` implements [Drop].
  ///
  /// You can avoid this restriction by wrapping with
  /// [ManuallyDrop][core::mem::ManuallyDrop].
  ///
  /// ```
  /// # use core::mem::ManuallyDrop;
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let x = arena.alloc().init(ManuallyDrop::new(Vec::new()));
  /// x.push(1_u64);
  /// unsafe { ManuallyDrop::drop(x) };
  /// ```

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    const { assert!(! core::mem::needs_drop::<T>()) };

    unsafe { ptr::write(self.ptr(), value) };
    unsafe { self.ptr().as_mut_ref() }
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  /// Converts the slot into a reference to an array of uninitialized values.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc::<[u64; 5]>().as_uninit_array();
  /// ```

  #[inline(always)]
  pub fn as_uninit_array(self) -> &'a mut [MaybeUninit<T>; N] {
    unsafe { self.ptr().as_mut_ref() }
  }

  /// Initializes the array with values produced by calling the given function
  /// with each index in order.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc::<[_; 5]>().init_array(|i| i as u64);
  /// ```
  ///
  /// # Static Panics
  ///
  /// Compilation fails if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init_array<F>(self, f: F) -> &'a mut [T; N]
  where
    F: FnMut(usize) -> T
  {
    const { assert!(! core::mem::needs_drop::<T>()) };

    let mut p = self.ptr();
    let mut i = 0;
    let mut f = f;

    while i < N {
      unsafe { ptr::write(p, f(i)) };
      i = i + 1;
      p = p + size_of::<T>();
    }

    unsafe { self.ptr().as_mut_ref() }
  }
}

impl<'a, T> Slot<'a, [T]> {
  /// The length of the uninitialized slice.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc_slice::<u64>(5).len();
  /// ```

  #[inline(always)]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  /// Converts the slot into a reference to a slice of uninitialized values.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc_slice::<u64>(5).as_uninit_slice();
  /// ```

  #[inline(always)]
  pub fn as_uninit_slice(self) -> &'a mut [MaybeUninit<T>] {
    unsafe { self.ptr().as_slice_mut_ref(self.len()) }
  }

  /// Initializes the slice with values produced by calling the given function
  /// with each index in order.
  ///
  /// ```
  /// # let mut store = oxcart::Store::with_capacity(100);
  /// # let mut arena = store.arena();
  /// let _ = arena.alloc_slice(5).init_slice(|i| i as u64);
  /// ```
  ///
  /// # Static Panics
  ///
  /// Compilation fails if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init_slice<F>(self, f: F) -> &'a mut [T]
  where
    F: FnMut(usize) -> T
  {
    const { assert!(! core::mem::needs_drop::<T>()) };

    let mut p = self.ptr();
    let mut i = 0;
    let mut f = f;

    while i < self.len() {
      unsafe { ptr::write(p, f(i)) };
      i = i + 1;
      p = p + size_of::<T>();
    }

    unsafe { self.ptr().as_slice_mut_ref(self.len()) }
  }
}

impl<'a, T> core::fmt::Debug for Slot<'a, T> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("Slot").finish()
  }
}

impl<'a, T> core::fmt::Debug for Slot<'a, [T]> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("Slot").field(&self.len()).finish()
  }
}
