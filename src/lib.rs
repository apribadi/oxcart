#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]

extern crate alloc;

mod ptr;

use alloc::alloc::Layout;
use core::cell::UnsafeCell;
use core::fmt;
use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::align_of;
use core::mem::needs_drop;
use core::mem::size_of;
use core::ptr::NonNull;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PUBLIC TYPE AND TRAIT DEFINITIONS                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[doc(no_inline)]
pub use allocator_api2::alloc::AllocError;

/// TODO: writeme
///

pub struct Store(NonNull<Node>);

unsafe impl Send for Store { }

unsafe impl Sync for Store { }

/// TODO: writeme
///

pub struct Arena<'a>(Span, PhantomData<&'a ()>);

unsafe impl<'a> Send for Arena<'a> { }

unsafe impl<'a> Sync for Arena<'a> { }

/// Uninitialized memory with lifetime `'a` which can hold a `T`.
///
/// Typically you will initialize a slot with [`init`](Self::init) or
/// [`init_slice`](Self::init_slice).

pub struct Slot<'a, T>(NonNull<T>, PhantomData<&'a ()>) where T: ?Sized;

unsafe impl<'a, T> Send for Slot<'a, T> where T: ?Sized { }

unsafe impl<'a, T> Sync for Slot<'a, T> where T: ?Sized { }

/// An `ArenaAllocator<'a>` is wrapper around an `Arena<'a>` that implements
/// the `Allocator` trait. Notably, it is `!Sync`.

pub struct ArenaAllocator<'a>(UnsafeCell<Arena<'a>>);

impl<'a> core::panic::RefUnwindSafe for ArenaAllocator<'a> { }

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

struct Node {
  next: Span,
  root: NonNull<Node>,
  flag: bool,
  used: usize,
}

enum Error {
  GlobalAllocatorFailed(Layout),
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
const WORD: usize = size_of::<usize>();

const CHUNK_ALIGN: usize = max(WORD, align_of::<Node>());

const INIT_SIZE: usize = 1 << 16; // 65536
const MAX_CHUNK: usize = 1 << BITS - 2; // 0b01000...0
const MAX_ALLOC: usize = 1 << BITS - 3; // 0b00100...0
const MAX_ALIGN: usize = 1 << BITS - 4; // 0b00010...0

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
      Error::GlobalAllocatorFailed(layout) =>
        alloc::alloc::handle_alloc_error(layout),
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

fn chunk<E>(n: usize) -> Result<NonNull<Node>, E>
where
  E: Fail
{
  debug_assert!(n >= size_of::<Node>());
  debug_assert!(n <= MAX_CHUNK);
  debug_assert!(n % WORD == 0);

  let layout = Layout::from_size_align(n, CHUNK_ALIGN).unwrap();

  let Ok(x) = ptr::alloc(layout) else {
    return E::fail(Error::GlobalAllocatorFailed(layout));
  };

  Ok(x)
}

fn store<E>(n: usize) -> Result<Store, E>
where
  E: Fail
{
  let n = min(! (WORD - 1) & WORD - 1 + max(n, size_of::<Node>()), MAX_CHUNK);
  let p = chunk(n)?;
  let t = unsafe { ptr::add(ptr::cast::<_, u8>(p), n) };

  let node = Node {
    next: Span::new(t, n - size_of::<Node>()),
    root: p,
    flag: false,
    used: n,
  };

  unsafe { ptr::write(p, node) };

  Ok(Store(p))
}

impl Store {
  /// Allocates a new store with a default capacity.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  pub fn new() -> Self {
    unwrap(store(INIT_SIZE))
  }

  /// Allocates a new store with a default capacity.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  pub fn try_new() -> Result<Self, AllocError> {
    store(INIT_SIZE)
  }

  pub fn with_capacity(capacity: usize) -> Self {
    unwrap(store(capacity))
  }

  pub fn try_with_capacity(capacity: usize) -> Result<Self, AllocError> {
    store(capacity)
  }

  /// TODO: writeme
  ///

  pub fn arena(&mut self) -> Arena<'_> {
    let r = unsafe { ptr::as_mut_ref(self.0) };
    r.flag = false;
    Arena(r.next, PhantomData)
  }
}

impl Drop for Store {
  fn drop(&mut self) {
    let root = self.0;
    let mut span = unsafe { ptr::as_ref(self.0) }.next;

    loop {
      let n = span.size + size_of::<Node>();
      let p = ptr::cast::<_, Node>(unsafe { ptr::sub(span.tail, n) });
      span = unsafe { ptr::as_ref(p) }.next;
      unsafe { ptr::dealloc(p, Layout::from_size_align_unchecked(n, CHUNK_ALIGN)) };
      if p == root { break; }
    }
  }
}

impl fmt::Debug for Store {
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
  let a: &Node = ptr::as_ref(ptr::cast(ptr::sub(span.tail, span.size + size_of::<Node>())));
  let r: &Node = ptr::as_ref(a.root);

  'grow: {
    if ptr::from_ref(a) == ptr::from_ref(r) || r.flag {
      break 'grow;
    }

    let m =
      layout.size() + (
        (WORD - 1 | layout.align() - 1) &
          ptr::addr(a.next.tail).wrapping_sub(layout.size()));

    let Some(n) = a.next.size.checked_sub(m) else {
      break 'grow;
    };

    return [Ok(Span::new(ptr::sub(a.next.tail, m), n))];
  }

  let r: &mut Node = ptr::as_mut_ref(r.root);

  if ! (layout.size() <= MAX_ALLOC && layout.align() <= MAX_ALIGN) {
    return [E::fail(Error::TooLarge)];
  }

  let n =
    1 << BITS - clz(
      max(
        max(
          r.next.size + size_of::<Node>(),
          r.used / 4 + 1,
        ),
        size_of::<Node>()
          + (! (WORD - 1) & layout.align() - 1)
          + (! (WORD - 1) & WORD - 1 + layout.size())
      ) - 1
    );

  let p = match chunk(n) { Err(e) => return [Err(e)], Ok(p) => p };
  let t = ptr::add(ptr::cast::<_, u8>(p), n);

  let node = Node {
    next: r.next,
    root: r.root,
    flag: /* dummy */ false,
    used: /* dummy */ 0,
  };

  ptr::write(p, node);

  let span = Span::new(t, n - size_of::<Node>());

  let m =
    layout.size() + (
      (WORD - 1 | layout.align() - 1) &
        ptr::addr(span.tail).wrapping_sub(layout.size()));

  debug_assert!(m <= span.size);

  r.next = span;
  r.flag = true;
  r.used = r.used.saturating_add(n);

  [Ok(Span::new(ptr::sub(span.tail, m), span.size - m))]
}

#[inline(always)]
fn alloc_impl<'a, E>(arena: &mut Arena<'a>, layout: Layout) -> Result<NonNull<u8>, E>
where
  E: Fail
{
  let s = arena.0;
  let s = unsafe { alloc_fast(s, layout) }?;
  arena.0 = s;
  Ok(s.tail)
}

#[inline(always)]
fn alloc<'a, T, E>(arena: &mut Arena<'a>) -> Result<Slot<'a, T>, E>
where
  E: Fail
{
  let x = alloc_impl(arena, Layout::new::<T>())?;
  Ok(Slot(ptr::cast(x), PhantomData))
}

#[inline(always)]
fn alloc_slice<'a, T, E>(arena: &mut Arena<'a>, len: usize) -> Result<Slot<'a, [T]>, E>
where
  E: Fail
{
  if ! (size_of::<T>() == 0 || len <= MAX_ALLOC / size_of::<T>()) {
    return E::fail(Error::TooLarge);
  }

  let layout = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
  let x = alloc_impl(arena, layout)?;
  Ok(Slot(ptr::as_slice(ptr::cast(x), len), PhantomData))
}

#[inline(always)]
fn copy_slice<'a, T, E>(arena: &mut Arena<'a>, src: &[T]) -> Result<&'a mut [T], E>
where
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
fn copy_str<'a, E>(arena: &mut Arena<'a>, src: &str) -> Result<&'a mut str, E>
where
  E: Fail
{
  let x = copy_slice(arena, src.as_bytes())?;
  Ok(unsafe { core::str::from_utf8_unchecked_mut(x) })
}

#[inline(always)]
fn alloc_layout<'a, E>(arena: &mut Arena<'a>, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
where
  E: Fail
{
  let x = alloc_impl(arena, layout)?;
  Ok(unsafe { ptr::as_slice_mut_ref(ptr::cast(x), layout.size()) })
}

impl<'a> Arena<'a> {
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
  pub fn as_allocator(self) -> ArenaAllocator<'a> {
    ArenaAllocator(UnsafeCell::new(self))
  }
}

impl<'a> fmt::Debug for Arena<'a> {
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
      x = unsafe { ptr::add(x, 1) };
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
      x = unsafe { ptr::add(x, 1) };
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

unsafe impl<'a> allocator_api2::alloc::Allocator for ArenaAllocator<'a> {
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
    Ok(ptr::as_slice(ptr::cast(ptr::from_ref(x)), x.len()))
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    let _ = self;
    let _ = ptr;
    let _ = layout;
  }
}
