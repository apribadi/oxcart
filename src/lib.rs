#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]

extern crate alloc;

use allocator_api::Allocator;
use allocator_api::Global;
use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr::NonNull;
use pop::ptr;

/// TODO

#[derive(Clone, Copy)]
pub struct AllocError;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// SUBMODULES                                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

pub mod allocator_api;

mod foo;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PUBLIC TYPE AND TRAIT DEFINITIONS                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/// TODO: writeme
///

pub struct Store<A: Allocator = Global>(ptr, PhantomData<A>);

/// TODO: writeme
///

pub struct Arena<'a, A: Allocator = Global>(Span, PhantomData<(&'a (), A)>);

/// Uninitialized memory with lifetime `'a` which can hold a `T`.
///
/// Typically you will initialize a slot with [`init`](Self::init) or
/// [`init_slice`](Self::init_slice).

pub struct Slot<'a, T: ?Sized>(NonNull<T>, PhantomData<&'a ()>);

unsafe impl<'a, T: ?Sized> Send for Slot<'a, T> { }

unsafe impl<'a, T: ?Sized> Sync for Slot<'a, T> { }

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PRIVATE TYPE AND TRAIT DEFINITIONS                                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy)]
struct Span {
  tail: ptr,
  size: usize,
}

struct Root<A> {
  head: NonNull<Head>,
  last: NonNull<Head>,
  used: usize,
  allocator: A,
}

struct Head {
  next: Span,
  root: ptr,
}

enum Error {
  ParentAllocatorFailed(Layout),
  TooLarge,
}

enum Panicked { }

trait Fail: Sized {
  fn fail<T>(_: Error) -> Result<T, Self>;
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// CONSTANTS                                                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

const BITS: usize = usize::BITS as usize;
const WORD: usize = size_of::<usize>();

const DEFAULT_CAPACITY: usize = 1 << 16; // 65536

const MAX_CHUNK: usize = 1 << BITS - 2; // 0b01000...0
const MAX_ALLOC: usize = 1 << BITS - 3; // 0b00100...0
const MAX_ALIGN: usize = 1 << BITS - 4; // 0b00010...0

const _: () = assert!(WORD.is_power_of_two());

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
  match x { Ok(x) => x, Err(e) => match e { } }
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
        alloc::alloc::handle_alloc_error(layout),
      Error::TooLarge =>
        // The requested allocation is too large for the arena allocator to
        // handle, even in the absence of physical constraints.
        //
        // In some (but not all) cases, it is not possible to construct a valid
        // `Layout` representing the requested allocation.
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
  fn new(tail: ptr, size: usize) -> Self {
    Self { tail, size, }
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Store                                                                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

fn store<A, E>(capacity: usize, allocator: A) -> Result<Store<A>, E>
where
  A: Allocator,
  E: Fail,
{
  let CHUNK_ALIGN = const { max(WORD, align_of::<Head>()) };
  let HEAD_SIZE = const { ! (WORD - 1) & WORD - 1 + size_of::<Head>() };
  let ROOT_SIZE = const { ! (WORD - 1) & WORD - 1 + size_of::<Root<A>>() };
  let ROOT_SLOP = const { ! (WORD - 1) & align_of::<Root<A>>() - 1 };

  let mut allocator = allocator;

  let n = ! (WORD - 1) & capacity;
  let n = max(n, HEAD_SIZE + ROOT_SIZE + ROOT_SLOP);
  let n = min(n, MAX_CHUNK);
  let l = unsafe { Layout::from_size_align_unchecked(n, CHUNK_ALIGN) };

  let Some(h) = allocator.alloc(l) else {
    return E::fail(Error::ParentAllocatorFailed(l));
  };

  let h = foo::cast(h);
  let t = unsafe { foo::add::<_, u8>(h, n - (ROOT_SIZE + ROOT_SLOP)) };
  let r = unsafe { foo::align_up(t) };

  let root = Root {
    head: h,
    last: h,
    used: n,
    allocator,
  };

  let head = Head {
    next: Span::new(ptr::from(t), n - (HEAD_SIZE + ROOT_SIZE + ROOT_SLOP)),
    root: ptr::from(r),
  };

  unsafe { foo::write(h, head) };
  unsafe { foo::write(r, root) };

  Ok(Store(ptr::from(r), PhantomData))
}

impl Store<Global> {
  /// Allocates a new store with the default capacity backed by the global
  /// allocator.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  pub fn new() -> Self {
    unwrap(store(DEFAULT_CAPACITY, Global))
  }

  /// Allocates a new store with the default capacity backed by the global
  /// allocator.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  pub fn try_new() -> Result<Self, AllocError> {
    store(DEFAULT_CAPACITY, Global)
  }

  /// Allocates a new store with the given capacity backed by the global
  /// allocator.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  pub fn with_capacity(capacity: usize) -> Self {
    unwrap(store(capacity, Global))
  }

  /// Allocates a new store with the given capacity backed by the global
  /// allocator.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  pub fn try_with_capacity(capacity: usize) -> Result<Self, AllocError> {
    store(capacity, Global)
  }
}

impl<A: Allocator> Store<A> {
  /// TODO: writeme
  ///

  pub fn new_in(allocator: A) -> Self {
    unwrap(store(DEFAULT_CAPACITY, allocator))
  }

  /// TODO: writeme
  ///

  pub fn try_new_in(allocator: A) -> Result<Self, AllocError> {
    store(DEFAULT_CAPACITY, allocator)
  }

  /// TODO: writeme
  ///

  pub fn with_capacity_in(capacity: usize, allocator: A) -> Self {
    unwrap(store(capacity, allocator))
  }

  /// TODO: writeme
  ///

  pub fn try_with_capacity_in(capacity: usize, allocator: A) -> Result<Self, AllocError> {
    store(capacity, allocator)
  }

  /// TODO: writeme
  ///

  pub fn arena(&mut self) -> Arena<'_, A> {
    let r = unsafe { self.0.as_mut_ref::<Root<A>>() };
    r.last = r.head;
    let h = unsafe { foo::as_ref(r.head) };
    Arena(h.next, PhantomData)
  }

  /// A reference to the parent allocator.

  pub fn allocator(&self) -> &A {
    let r = unsafe { self.0.as_ref::<Root<A>>() };
    &r.allocator
  }
}

impl<A: Allocator> Drop for Store<A> {
  fn drop(&mut self) {
    let CHUNK_ALIGN = const { max(WORD, align_of::<Head>()) };
    let HEAD_SIZE = const { ! (WORD - 1) & WORD - 1 + size_of::<Head>() };
    let ROOT_SIZE = const { ! (WORD - 1) & WORD - 1 + size_of::<Root<A>>() };
    let ROOT_SLOP = const { ! (WORD - 1) & align_of::<Root<A>>() - 1 };

    let root = unsafe { self.0.as_ref::<Root<A>>() };
    let last = root.head;
    let mut span = unsafe { foo::as_ref(last) }.next;

    let mut allocator = unsafe { foo::read(foo::from_ref(&root.allocator)) };

    loop {
      let p = span.tail - (span.size + HEAD_SIZE);

      if p == ptr::from(last) {
        let n = span.size + HEAD_SIZE + ROOT_SIZE + ROOT_SLOP;
        let l = unsafe { Layout::from_size_align_unchecked(n, CHUNK_ALIGN) };
        unsafe { allocator.free(p.as_non_null(), l) };
        break;
      }

      let n = span.size + HEAD_SIZE;
      let l = unsafe { Layout::from_size_align_unchecked(n, CHUNK_ALIGN) };
      span = unsafe { p.as_ref::<Head>() }.next;
      unsafe { allocator.free(p.as_non_null(), l) };
    }

    // NB: We will drop `allocator` exactly once. This call to `drop` is not
    // necessary, but serves as a reminder of this fact.
    drop::<A>(allocator)
  }
}

impl<A: Allocator> core::fmt::Debug for Store<A> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("Store").finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Arena                                                                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast(span: Span, layout: Layout) -> Option<Span> {
  let p = span.tail;
  let n = span.size;
  let a = layout.align();
  let s = layout.size();

  core::hint::assert_unchecked(p.addr() & WORD - 1 == 0);

  let d = s + ((WORD - 1 | a - 1) & p.addr().wrapping_sub(s));
  let k = n.checked_sub(d)?;

  Some(Span::new(p - d, k))
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow<A, E>(span: Span, layout: Layout) -> [Result<Span, E>; 1]
where
  A: Allocator,
  E: Fail,
{
  let ALIGN_CHUNK = const { max(WORD, align_of::<Head>()) };
  let HEAD_SIZE = const { ! (WORD - 1) & WORD - 1 + size_of::<Head>() };

  let h = (span.tail - (span.size + HEAD_SIZE)).as_ref::<Head>();
  let r = h.root.as_mut_ref::<Root<A>>();

  if foo::from_ref(h) != r.last {
    if let Some(s) = alloc_fast(h.next, layout) {
      return [Ok(s)];
    }
  }

  if ! (layout.size() <= MAX_ALLOC && layout.align() <= MAX_ALIGN) {
    return [E::fail(Error::TooLarge)];
  }

  let h = foo::as_mut_ref(r.head);

  let n =
    1 << BITS - clz(
      max(
        max(
          h.next.size + HEAD_SIZE,
          r.used / 4 + 1,
        ),
        HEAD_SIZE
          + (! (WORD - 1) & WORD - 1 + layout.size())
          + (! (WORD - 1) & layout.align() - 1)
      ) - 1
    );

  let l = Layout::from_size_align_unchecked(n, ALIGN_CHUNK);

  let Some(p) = r.allocator.alloc(l) else {
    return [E::fail(Error::ParentAllocatorFailed(l))];
  };

  let p = foo::cast(p);
  let t = foo::add::<_, u8>(p, n);

  let head = Head {
    next: h.next,
    root: h.root,
  };

  foo::write(p, head);

  let span = Span::new(ptr::from(t), n - HEAD_SIZE);

  h.next = span;
  r.last = p;
  r.used = r.used.saturating_add(n);

  [Ok(alloc_fast(span, layout).unwrap_unchecked())]
}

#[inline(always)]
fn alloc_layout<'a, A, E>(arena: &mut Arena<'a, A>, layout: Layout) -> Result<NonNull<u8>, E>
where
  A: Allocator,
  E: Fail,
{
  let s = arena.0;
  let s =
    match unsafe { alloc_fast(s, layout) } {
      Some(s) => s,
      None =>
        match unsafe { alloc_slow::<A, E>(s, layout) } {
          [Ok(s)] => s,
          [Err(e)] => return Err(e),
        },
    };
  arena.0 = s;
  Ok(unsafe { s.tail.as_non_null() })
}

#[inline(always)]
fn alloc<'a, A, E, T>(arena: &mut Arena<'a, A>) -> Result<Slot<'a, T>, E>
where
  A: Allocator,
  E: Fail,
{
  let x = alloc_layout(arena, Layout::new::<T>())?;
  Ok(Slot(foo::cast(x), PhantomData))
}

#[inline(always)]
fn alloc_slice<'a, A, E, T>(arena: &mut Arena<'a, A>, len: usize) -> Result<Slot<'a, [T]>, E>
where
  A: Allocator,
  E: Fail,
{
  if ! (size_of::<T>() == 0 || len <= MAX_ALLOC / size_of::<T>()) {
    return E::fail(Error::TooLarge);
  }

  let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
  let x = alloc_layout(arena, l)?;
  Ok(Slot(foo::as_slice(foo::cast(x), len), PhantomData))
}

#[inline(always)]
fn copy_slice<'a, A, E, T>(arena: &mut Arena<'a, A>, src: &[T]) -> Result<&'a mut [T], E>
where
  A: Allocator,
  E: Fail,
  T: Copy,
{
  let x = alloc_layout(arena, Layout::for_value(src))?;
  let x = foo::cast(x);
  let y = foo::cast(foo::from_ref(src));
  let n = src.len();
  unsafe { foo::copy_nonoverlapping::<T>(y, x, n) };
  Ok(unsafe { foo::as_slice_mut_ref(x, n) })
}

#[inline(always)]
fn copy_str<'a, A, E>(arena: &mut Arena<'a, A>, src: &str) -> Result<&'a mut str, E>
where
  A: Allocator,
  E: Fail,
{
  let x = copy_slice(arena, src.as_bytes())?;
  Ok(unsafe { core::str::from_utf8_unchecked_mut(x) })
}

impl<'a, A: Allocator> Arena<'a, A> {
  /// Allocates memory for a single value.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    unwrap(alloc(self))
  }

  /// Allocates memory for a single value.
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

  /// Copies the given slice into a new allocation.
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

  /// Copies the given slice into a new allocation.
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

  /// Copies the given string into a new allocation.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    unwrap(copy_str(self, src))
  }

  /// Copies the given string into a new allocation.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    copy_str(self, src)
  }

  /// Allocates memory for the given layout. The memory is valid for the
  /// lifetime `'a` from `Arena<'a>`.
  ///
  /// # Panics
  ///
  /// Panics on failure to allocate memory.

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> NonNull<u8> {
    unwrap(alloc_layout(self, layout))
  }

  /// Allocates memory for the given layout. The memory is valid for the
  /// lifetime `'a` from `Arena<'a>`.
  ///
  /// # Errors
  ///
  /// An error is returned on failure to allocate memory.

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
    alloc_layout(self, layout)
  }
}

impl<'a, A: Allocator> core::fmt::Debug for Arena<'a, A> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

impl<'a, T: ?Sized> Slot<'a, T> {
  #[inline(always)]
  fn ptr(&self) -> ptr {
    ptr::from(self.0)
  }
}

impl<'a, T> Slot<'a, T> {
  /// Converts the slot into a reference to an uninitialized value.

  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    unsafe { self.ptr().as_mut_ref() }
  }

  /// Initializes the slot with the given value.
  ///
  /// # Panics
  ///
  /// Panics if `T` implements [`Drop`].

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    assert!(! core::mem::needs_drop::<T>());

    unsafe { self.ptr().write(value) };
    unsafe { self.ptr().as_mut_ref() }
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  /// Converts the slot into a reference to an array of uninitialized values.

  #[inline(always)]
  pub fn as_uninit_array(self) -> &'a mut [MaybeUninit<T>; N] {
    unsafe { self.ptr().as_mut_ref() }
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
    assert!(! core::mem::needs_drop::<T>());

    let mut p = self.ptr();
    let mut i = 0;
    let mut f = f;

    while i < N {
      unsafe { p.write(f(i)) };
      i = i + 1;
      p = p + size_of::<T>();
    }

    unsafe { self.ptr().as_mut_ref() }
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
    unsafe { self.ptr().as_slice_mut_ref(self.len()) }
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
    assert!(! core::mem::needs_drop::<T>());

    let mut p = self.ptr();
    let mut i = 0;
    let mut f = f;

    while i < self.len() {
      unsafe { p.write(f(i)) };
      i = i + 1;
      p = p + size_of::<T>();
    }

    unsafe { self.ptr().as_slice_mut_ref(self.len()) }
  }
}

impl<'a, T> core::fmt::Debug for Slot<'a, T> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("Slot").field(&self.0).finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Allocator API                                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

unsafe impl<'a, A: Allocator> Allocator for Arena<'a, A> {
  #[inline(always)]
  fn alloc(&mut self, layout: Layout) -> Option<NonNull<u8>> {
    match alloc_layout::<_, AllocError>(self, layout) {
      Ok(p) => Some(p),
      Err(_) => None,
    }
  }

  #[inline(always)]
  unsafe fn free(&mut self, ptr: NonNull<u8>, layout: Layout) {
    let _ = ptr;
    let _ = layout;
  }
}
