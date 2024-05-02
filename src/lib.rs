#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]

mod ptr;

use core::alloc::Layout;
use core::cell::UnsafeCell;
use core::fmt;
use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::align_of;
use core::mem::needs_drop;
use core::mem::size_of;
use core::ptr::NonNull;
use allocator_api2::alloc::AllocError;
use allocator_api2::alloc::Allocator;
use allocator_api2::alloc::Global;
use allocator_api2::alloc::handle_alloc_error;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PUBLIC TYPE AND TRAIT DEFINITIONS                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


/// TODO: writeme
///

pub struct Store<A = Global>(NonNull<Root<A>>) where A: Allocator;

unsafe impl<A> Send for Store<A> where A: Allocator + Send { }

unsafe impl<A> Sync for Store<A> where A: Allocator + Sync { }

impl<A> core::panic::RefUnwindSafe for Store<A> where A: Allocator { }

impl<A> core::panic::UnwindSafe for Store<A> where A: Allocator { }

/// TODO: writeme
///

pub struct Arena<'a, A = Global>(Span, PhantomData<(&'a (), A)>) where A: Allocator;

unsafe impl<'a, A> Send for Arena<'a, A> where A: Allocator + Send { }

unsafe impl<'a, A> Sync for Arena<'a, A> where A: Allocator + Sync { }

/// Uninitialized memory with lifetime `'a` which can hold a `T`.
///
/// Typically you will initialize a slot with [`init`](Self::init) or
/// [`init_slice`](Self::init_slice).

pub struct Slot<'a, T>(NonNull<T>, PhantomData<&'a ()>) where T: ?Sized;

unsafe impl<'a, T> Send for Slot<'a, T> where T: ?Sized { }

unsafe impl<'a, T> Sync for Slot<'a, T> where T: ?Sized { }

/// An `ArenaAllocator<'a>` is wrapper around an `Arena<'a>` that implements
/// the `Allocator` trait.
///
/// Notably, it uses interior mutability and is `!Sync`.

pub struct ArenaAllocator<'a, A = Global>(UnsafeCell<Arena<'a, A>>) where A: Allocator;

unsafe impl<'a, A> Send for ArenaAllocator<'a, A> where A: Allocator + Send { }

impl<'a, A> core::panic::RefUnwindSafe for ArenaAllocator<'a, A> where A: Allocator { }

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PRIVATE TYPE AND TRAIT DEFINITIONS                                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy)]
struct Span {
  tail: NonNull<u8>,
  size: usize,
}

struct Root<A>
where
  A: ?Sized
{
  head: NonNull<Head>,
  last: NonNull<Head>,
  used: usize,
  allocator: A,
}

struct Head {
  next: Span,
  root: NonNull<Root<dyn Allocator>>,
}

enum Error {
  ParentAllocatorFailed(Layout),
  TooLarge,
}

#[derive(Clone, Copy)]
enum Panicked { }

trait Fail: Copy + Sized {
  fn fail<T>(_: Error) -> Result<T, Self>;
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// CONSTANTS                                                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

const BITS: usize = usize::BITS as usize;
const WORD: usize = align_of::<usize>();

const DEFAULT_CAPACITY: usize = 1 << 16; // 65536

const MAX_CHUNK: usize = 1 << BITS - 2; // 0b01000...0
const MAX_ALLOC: usize = 1 << BITS - 3; // 0b00100...0
const MAX_ALIGN: usize = 1 << BITS - 4; // 0b00010...0

const ALIGN: usize = max(WORD, align_of::<Head>());

const HEAD_SIZE: usize = ! (WORD - 1) & WORD - 1 + size_of::<Head>();

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// UTILITY FUNCTIONS                                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
const fn max(x: usize, y: usize) -> usize {
  if x >= y { x } else { y }
}

#[inline(always)]
const fn min(x: usize, y: usize) -> usize {
  if x <= y { x } else { y }
}

#[inline(always)]
const fn clz(x: usize) -> usize {
  x.leading_zeros() as usize
}

#[inline(always)]
fn unwrap<T>(x: Result<T, Panicked>) -> T {
  match x { Err(e) => match e { }, Ok(x) => x }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Fail                                                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

impl Fail for Panicked {
  #[inline(never)]
  #[cold]
  fn fail<T>(e: Error) -> Result<T, Self> {
    match e {
      Error::ParentAllocatorFailed(layout) =>
        handle_alloc_error(layout),
      Error::TooLarge =>
        panic!("oxcart: attempted an allocation that is too large!"),
    }
  }
}

impl Fail for AllocError {
  #[inline(always)]
  fn fail<T>(_: Error) -> Result<T, Self> {
    Err(AllocError)
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Span                                                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

impl Span {
  #[inline(always)]
  fn new(tail: NonNull<u8>, size: usize) -> Self {
    Self { tail, size, }
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Store                                                                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

fn store<A, E>(n: usize, allocator: A) -> Result<Store<A>, E>
where
  A: Allocator,
  E: Fail
{
  let root_size = const { ! (WORD - 1) & WORD - 1 + size_of::<Root<A>>() };
  let root_slop = const { ! (WORD - 1) & align_of::<Root<A>>() - 1 };

  let n = ! (WORD - 1) & n;
  let n = max(n, HEAD_SIZE + root_size + root_slop);
  let n = min(n, MAX_CHUNK);
  let l = unsafe { Layout::from_size_align_unchecked(n, ALIGN) };

  let Ok(h) = allocator.allocate(l) else {
    return E::fail(Error::ParentAllocatorFailed(l));
  };

  let h = ptr::cast(h);
  let t = unsafe { ptr::add(h, n - (root_size + root_slop)) };
  let r = unsafe { ptr::align_up(t) };

  let root = Root {
    head: h,
    last: h,
    used: n,
    allocator,
  };

  let head = Head {
    next: Span::new(t, n - (HEAD_SIZE + root_size + root_slop)),
    root: unsafe { NonNull::new_unchecked(r.as_ptr() as *mut Root<dyn Allocator>) },
  };

  unsafe { ptr::write(h, head) };
  unsafe { ptr::write(r, root) };

  Ok(Store(r))
}

impl Store<Global> {
  /// Allocates a new store with a default capacity.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  pub fn new() -> Self {
    unwrap(store(DEFAULT_CAPACITY, Global))
  }

  /// Allocates a new store with a default capacity.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  pub fn try_new() -> Result<Self, AllocError> {
    store(DEFAULT_CAPACITY, Global)
  }

  /// TODO: writeme
  ///

  pub fn with_capacity(capacity: usize) -> Self {
    unwrap(store(capacity, Global))
  }

  /// TODO: writeme
  ///

  pub fn try_with_capacity(capacity: usize) -> Result<Self, AllocError> {
    store(capacity, Global)
  }
}

impl<A> Store<A>
where
  A: Allocator
{
  /// TODO: writeme
  ///

  pub fn arena(&mut self) -> Arena<'_, A> {
    let r = unsafe { ptr::as_mut_ref(self.0) };
    r.last = r.head;
    let h = unsafe { ptr::as_ref(r.head) };
    Arena(h.next, PhantomData)
  }

  /// TODO: writeme
  ///

  pub fn allocator(&self) -> &A {
    let r = unsafe { ptr::as_ref(self.0) };
    &r.allocator
  }
}

impl<A> Drop for Store<A>
where
  A: Allocator
{
  fn drop(&mut self) {
    let root_size = const { ! (WORD - 1) & WORD - 1 + size_of::<Root<A>>() };
    let root_slop = const { ! (WORD - 1) & align_of::<Root<A>>() - 1 };

    let root = unsafe { ptr::as_ref(self.0) };
    let last = root.head;
    let mut span = unsafe { ptr::as_ref(last) }.next;

    // NB: We will drop `allocator` exactly once.
    let allocator: A = unsafe { ptr::read(ptr::from_ref(&root.allocator)) };

    loop {
      let p = unsafe { ptr::sub(span.tail, span.size + HEAD_SIZE) };

      if p == last {
        let n = span.size + HEAD_SIZE + root_size + root_slop;
        let l = unsafe { Layout::from_size_align_unchecked(n, ALIGN) };
        unsafe { allocator.deallocate(ptr::cast(p), l) };
        break;
      }

      let n = span.size + HEAD_SIZE;
      span = unsafe { ptr::as_ref(p) }.next;
      let l = unsafe { Layout::from_size_align_unchecked(n, ALIGN) };
      unsafe { allocator.deallocate(ptr::cast(p), l) };
    }
  }
}

impl<A> fmt::Debug for Store<A>
where
  A: Allocator
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Store").finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Arena                                                                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast<E>(span: Span, layout: Layout) -> Result<Span, E>
where
  E: Fail
{
  if ! ptr::is_aligned_to(span.tail, WORD) { unreachable_unchecked(); }

  let m =
    layout.size() + (
      (WORD - 1 | layout.align() - 1) &
        ptr::addr(span.tail).wrapping_sub(layout.size()));

  let Some(n) = span.size.checked_sub(m) else {
    return alloc_slow(span, layout)[0];
  };

  Ok(Span::new(ptr::sub(span.tail, m), n))
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow<E>(span: Span, layout: Layout) -> [Result<Span, E>; 1]
where
  E: Fail
{
  let h: &Head = ptr::as_ref(ptr::sub(span.tail, span.size + HEAD_SIZE));
  let r = ptr::as_mut_ref(h.root);

  'grow: {
    if ptr::from_ref(h) == r.last {
      break 'grow;
    }

    let m =
      layout.size() + (
        (WORD - 1 | layout.align() - 1) &
          ptr::addr(h.next.tail).wrapping_sub(layout.size()));

    let Some(n) = h.next.size.checked_sub(m) else {
      break 'grow;
    };

    return [Ok(Span::new(ptr::sub(h.next.tail, m), n))];
  }

  if ! (layout.size() <= MAX_ALLOC && layout.align() <= MAX_ALIGN) {
    return [E::fail(Error::TooLarge)];
  }

  let h = ptr::as_mut_ref(r.head);

  let n =
    1 << BITS - clz(
      max(
        max(
          max(
            WORD,
            h.next.size + HEAD_SIZE,
          ),
          r.used / 4 + 1,
        ),
        HEAD_SIZE
          + (! (WORD - 1) & WORD - 1 + layout.size())
          + (! (WORD - 1) & layout.align() - 1)
      ) - 1
    );

  let l = unsafe { Layout::from_size_align_unchecked(n, ALIGN) };

  let Ok(p) = r.allocator.allocate(l) else {
    return [E::fail(Error::ParentAllocatorFailed(l))];
  };

  let p = ptr::cast(p);
  let t = ptr::add(p, n);

  let head = Head {
    next: h.next,
    root: h.root,
  };

  ptr::write(p, head);

  let span = Span::new(t, n - HEAD_SIZE);

  let m =
    layout.size() + (
      (WORD - 1 | layout.align() - 1) &
        ptr::addr(span.tail).wrapping_sub(layout.size()));

  debug_assert!(m <= span.size);

  h.next = span;
  r.last = p;
  r.used = r.used.saturating_add(n);

  [Ok(Span::new(ptr::sub(span.tail, m), span.size - m))]
}

#[inline(always)]
fn alloc_impl<'a, A, E>(arena: &mut Arena<'a, A>, layout: Layout) -> Result<NonNull<u8>, E>
where
  A: Allocator,
  E: Fail
{
  let s = arena.0;
  let s = unsafe { alloc_fast(s, layout) }?;
  arena.0 = s;
  Ok(s.tail)
}

#[inline(always)]
fn alloc<'a, A, E, T>(arena: &mut Arena<'a, A>) -> Result<Slot<'a, T>, E>
where
  A: Allocator,
  E: Fail
{
  let x = alloc_impl(arena, Layout::new::<T>())?;
  Ok(Slot(ptr::cast(x), PhantomData))
}

#[inline(always)]
fn alloc_slice<'a, A, E, T>(arena: &mut Arena<'a, A>, len: usize) -> Result<Slot<'a, [T]>, E>
where
  A: Allocator,
  E: Fail
{
  if ! (size_of::<T>() == 0 || len <= MAX_ALLOC / size_of::<T>()) {
    return E::fail(Error::TooLarge);
  }

  let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
  let x = alloc_impl(arena, l)?;
  Ok(Slot(ptr::as_slice(ptr::cast(x), len), PhantomData))
}

#[inline(always)]
fn copy_slice<'a, A, E, T>(arena: &mut Arena<'a, A>, src: &[T]) -> Result<&'a mut [T], E>
where
  A: Allocator,
  T: Copy,
  E: Fail
{
  let x = alloc_impl(arena, Layout::for_value(src))?;
  let x = ptr::cast(x);
  let y = ptr::cast(ptr::from_ref(src));
  let n = src.len();
  unsafe { ptr::copy_nonoverlapping::<T>(y, x, n) };
  Ok(unsafe { ptr::as_slice_mut_ref(x, n) })
}

#[inline(always)]
fn copy_str<'a, A, E>(arena: &mut Arena<'a, A>, src: &str) -> Result<&'a mut str, E>
where
  A: Allocator,
  E: Fail
{
  let x = copy_slice(arena, src.as_bytes())?;
  Ok(unsafe { core::str::from_utf8_unchecked_mut(x) })
}

#[inline(always)]
fn alloc_layout<'a, A, E>(arena: &mut Arena<'a, A>, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
where
  A: Allocator,
  E: Fail
{
  let x = alloc_impl(arena, layout)?;
  Ok(unsafe { ptr::as_slice_mut_ref(ptr::cast(x), layout.size()) })
}

impl<'a, A> Arena<'a, A>
where
  A: Allocator
{
  /// Allocates memory for a single object.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    unwrap(alloc(self))
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
    unwrap(alloc_slice(self, len))
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
    unwrap(copy_slice(self, src))
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
    unwrap(copy_str(self, src))
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

  /// Allocates memory for the given layout.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
    unwrap(alloc_layout(self, layout))
  }

  /// Allocates memory for the given layout.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError> {
    alloc_layout(self, layout)
  }

  /// TODO: writeme
  ///

  #[inline(always)]
  pub fn as_allocator(self) -> ArenaAllocator<'a, A> {
    ArenaAllocator(UnsafeCell::new(self))
  }
}

impl<'a, A> fmt::Debug for Arena<'a, A>
where
  A: Allocator
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Arena")
      .field(&self.0.tail)
      .field(&self.0.size)
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Slot                                                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

impl<'a, T> Slot<'a, T> {
  /// Converts the slot into a reference to an uninitialized value.

  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    unsafe { ptr::as_mut_ref(ptr::cast(self.0)) }
  }

  /// Initializes the slot with the given value.
  ///
  /// # Panics
  ///
  /// Panics if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    assert!(! needs_drop::<T>());

    unsafe { ptr::write(self.0, value) };
    unsafe { ptr::as_mut_ref(self.0) }
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  /// Converts the slot into a reference to an array of uninitialized values.

  #[inline(always)]
  pub fn as_uninit_array(self) -> &'a mut [MaybeUninit<T>; N] {
    unsafe { ptr::as_mut_ref(ptr::cast(self.0)) }
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
    assert!(! needs_drop::<T>());

    let mut x = ptr::cast(self.0);
    let mut i = 0;
    let mut f = f;

    while i < N {
      unsafe { ptr::write(x, f(i)) };
      i = i + 1;
      x = unsafe { ptr::inc(x) };
    }

    unsafe { ptr::as_mut_ref(self.0) }
  }
}

impl<'a, T> Slot<'a, [T]> {
  /// The length of the uninitialized slice.

  #[inline(always)]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  /// Converts the slot into a reference to a slice of uninitialized values.

  #[inline(always)]
  pub fn as_uninit_slice(self) -> &'a mut [MaybeUninit<T>] {
    unsafe { ptr::as_slice_mut_ref(ptr::cast(self.0), self.0.len()) }
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
    assert!(! needs_drop::<T>());

    let mut x = ptr::cast(self.0);
    let mut i = 0;
    let mut f = f;

    while i < self.0.len() {
      unsafe { ptr::write(x, f(i)) };
      i = i + 1;
      x = unsafe { ptr::inc(x) };
    }

    unsafe { ptr::as_mut_ref(self.0) }
  }
}

impl<'a, T> fmt::Debug for Slot<'a, T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Slot").field(&self.0).finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Allocator API                                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

unsafe impl<'a, A> Allocator for ArenaAllocator<'a, A>
where
  A: Allocator
{
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    // SAFETY:
    //
    // The lifetime of the `&mut Arena<'a>` does not overlap with the lifetime
    // of any other reference to the arena.
    //
    // In particular, it is not possible for the global allocator to access
    // this allocator.

    let x = unsafe { &mut *self.0.get() }.try_alloc_layout(layout)?;
    Ok(ptr::as_slice(ptr::cast(ptr::from_mut_ref(x)), x.len()))
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    let _ = self;
    let _ = ptr;
    let _ = layout;
  }
}
