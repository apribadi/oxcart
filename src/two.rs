use std::alloc::Layout;
use std::alloc;
use std::cell::Cell;
use std::cmp::max;
use std::cmp::min;
use std::fmt;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::mem::align_of;
use std::mem::size_of;
use std::panic::RefUnwindSafe;
use std::ptr::NonNull;
use std::str;

////////////////////////////////////////////////////////////////////////////////
//
// PUBLIC TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

pub use allocator_api2::alloc::AllocError;

pub struct Store(NonNull<Header>);

pub struct Arena<'a>(Cell<Span>, PhantomData<&'a ()>);

pub struct Slot<'a, T>(NonNull<T>, PhantomData<&'a ()>)
where
  T: ?Sized;

unsafe impl Send for Store { }

unsafe impl Sync for Store { }

unsafe impl<'a> Send for Arena<'a> { }

impl<'a> RefUnwindSafe for Arena<'a> { }

unsafe impl<'a, T> Send for Slot<'a, T> where T: ?Sized { }

unsafe impl<'a, T> Sync for Slot<'a, T> where T: ?Sized { }

////////////////////////////////////////////////////////////////////////////////
//
// PRIVATE TYPE AND TRAIT DEFINITIONS
//
////////////////////////////////////////////////////////////////////////////////

#[derive(Eq, PartialEq)]
enum Kind {
  NonRoot,
  Growing,
  Ready,
}

#[derive(Clone, Copy)]
struct Span {
  tail: NonNull<u8>,
  size: usize,
}

struct Header {
  next: Span,
  root: NonNull<Header>,
  kind: Kind,
}

const _: () = assert!(size_of::<Header>() % WORD == 0 && align_of::<Header>() == WORD);

enum Error {
  SystemAllocatorFailed(Layout),
  TooLarge,
}

enum Panicked { }

trait Fail: Sized {
  fn fail<T>(_: Error) -> Result<T, Self>;
}

////////////////////////////////////////////////////////////////////////////////
//
// CONSTANTS
//
////////////////////////////////////////////////////////////////////////////////

const BITS: usize = usize::BITS as usize;
const WORD: usize = size_of::<usize>();  // 0b00...001000 (for 64-bit)
const MASK: usize = WORD.wrapping_neg(); // 0b11...111000

const INITIAL_CHUNK: usize = 1 << 14; // 16384

const MAX_CHUNK: usize = 1 << BITS - 2; // 0b01000...0
const MAX_ALLOC: usize = 1 << BITS - 3; // 0b00100...0
const MAX_ALIGN: usize = 1 << BITS - 4; // 0b00010...0

////////////////////////////////////////////////////////////////////////////////
//
// UTILITY FUNCTIONS
//
////////////////////////////////////////////////////////////////////////////////

mod ptr {
  use std::alloc::Layout;
  use std::ptr::NonNull;

  #[inline(always)]
  pub(crate) unsafe fn from_ref<T: ?Sized>(x: &T) -> NonNull<T> {
    NonNull::from(x)
  }

  #[inline(always)]
  pub(crate) fn addr<T>(x: NonNull<T>) -> usize {
    // NB: This must not be a `const` function.
    //
    // Transmuting a pointer into an integer in a const context is undefined
    // behavior.

    // Once the `strict_provenance` feature has been stabilized, this should
    // use the `addr` method on the primitive pointer type.

    unsafe { core::mem::transmute::<*mut T, usize>(x.as_ptr()) }
  }

  #[inline(always)]
  pub(crate) fn is_aligned_to<T>(x: NonNull<T>, y: usize) -> bool {
    addr(x) & y - 1 == 0
  }

  #[inline(always)]
  pub(crate) const fn cast<T: ?Sized, U>(x: NonNull<T>) -> NonNull<U> {
    x.cast()
  }

  #[inline(always)]
  pub(crate) const unsafe fn add<T>(x: NonNull<T>, y: usize) -> NonNull<T> {
    NonNull::new_unchecked(x.as_ptr().add(y))
  }

  #[inline(always)]
  pub(crate) const unsafe fn sub<T>(x: NonNull<T>, y: usize) -> NonNull<T> {
    NonNull::new_unchecked(x.as_ptr().sub(y))
  }

  #[inline(always)]
  pub(crate) unsafe fn write<T>(x: NonNull<T>, y: T) {
    x.as_ptr().write(y)
  }

  #[inline(always)]
  pub(crate) fn as_slice<T>(x: NonNull<T>, y: usize) -> NonNull<[T]> {
    let x = std::ptr::slice_from_raw_parts_mut(x.as_ptr(), y);
    unsafe { NonNull::new_unchecked(x) }
  }

  #[inline(always)]
  pub(crate) unsafe fn as_ref<'a, T: ?Sized>(x: NonNull<T>) -> &'a T {
    &*x.as_ptr()
  }

  #[inline(always)]
  pub(crate) unsafe fn as_mut_ref<'a, T: ?Sized>(x: NonNull<T>) -> &'a mut T {
    &mut *x.as_ptr()
  }

  #[inline(always)]
  pub(crate) unsafe fn as_slice_mut_ref<'a, T>(x: NonNull<T>, y: usize) -> &'a mut [T] {
    &mut *std::ptr::slice_from_raw_parts_mut(x.as_ptr(), y)
  }

  #[inline(always)]
  pub(crate) unsafe fn copy_nonoverlapping<T>(src: NonNull<T>, dst: NonNull<T>, len: usize) {
    std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_ptr(), len)
  }

  #[inline(always)]
  pub(crate) unsafe fn alloc(layout: Layout) -> Option<NonNull<u8>> {
    NonNull::new(std::alloc::alloc(layout))
  }
}

#[inline(always)]
fn clz(x: usize) -> usize {
  x.leading_zeros() as usize
}

#[inline(always)]
fn unwrap<T>(x: Result<T, Panicked>) -> T {
  match x {
    Ok(x) => x,
    Err(e) => match e { }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Panicked
//
////////////////////////////////////////////////////////////////////////////////

impl Fail for Panicked {
  #[inline(never)]
  #[cold]
  fn fail<T>(e: Error) -> Result<T, Self> {
    match e {
      Error::SystemAllocatorFailed(layout) => alloc::handle_alloc_error(layout),
      Error::TooLarge => panic!("oxcart: attempted a too large allocation!"),
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// AllocError
//
////////////////////////////////////////////////////////////////////////////////

impl Fail for AllocError {
  #[inline(always)]
  fn fail<T>(_: Error) -> Result<T, Self> {
    Err(AllocError)
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Span
//
////////////////////////////////////////////////////////////////////////////////

impl Span {
  #[inline(always)]
  fn new(tail: NonNull<u8>, size: usize) -> Self {
    Self { tail, size, }
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Store
//
////////////////////////////////////////////////////////////////////////////////

fn chunk<E>(n: usize) -> Result<NonNull<u8>, E>
where
  E: Fail
{
  assert!(n >= 1);
  assert!(n <= MAX_CHUNK);
  assert!(n % WORD == 0);

  let l = Layout::from_size_align(n, WORD).unwrap();
  let x = unsafe { ptr::alloc(l) };
  let Some(x) = x else { return E::fail(Error::SystemAllocatorFailed(l)); };
  Ok(x)
}

fn store<E>(n: usize) -> Result<Store, E>
where
  E: Fail
{
  let n = min(max(n & MASK, size_of::<Header>()), MAX_CHUNK);
  let a = chunk(n)?;

  unsafe {
    ptr::write(
      ptr::cast(a),
      Header {
        next: Span { tail: ptr::add(a, n), size: n - size_of::<Header>() },
        root: ptr::cast(a),
        kind: Kind::Ready,
      }
    )
  };

  Ok(Store(ptr::cast(a)))
}

impl Store {
  pub fn new() -> Self {
    unwrap(store(INITIAL_CHUNK))
  }

  pub fn try_new() -> Result<Self, AllocError> {
    store(INITIAL_CHUNK)
  }

  pub fn arena(&mut self) -> Arena<'_> {
    Arena(Cell::new(unsafe { ptr::as_mut_ref(self.0) }.next), PhantomData)
  }
}

impl Drop for Store {
  fn drop(&mut self) {
    let _ = self;
    // TODO
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Arena
//
////////////////////////////////////////////////////////////////////////////////

#[inline(always)]
unsafe fn alloc_fast<E>(span: Span, layout: Layout) -> Result<Span, E>
where
  E: Fail
{
  if ! ptr::is_aligned_to(span.tail, WORD) { unsafe { unreachable_unchecked() }; }

  let m =
    layout.size() + (
      (WORD - 1 | layout.align() - 1) &
        ptr::addr(span.tail).wrapping_sub(layout.size()));

  let Some(n) = span.size.checked_sub(m) else { return alloc_slow(span, layout); };

  Ok(Span::new(ptr::sub(span.tail, m), n))
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow<E>(span: Span, layout: Layout) -> Result<Span, E>
where
  E: Fail
{
  let a: &Header = ptr::as_ref(ptr::cast(ptr::sub(span.tail, span.size + size_of::<Header>())));
  let b: &Header = ptr::as_ref(a.root);

  'grow: {
    if ptr::from_ref(a) == ptr::from_ref(b) || a.kind == Kind::Growing { break 'grow; }

    let m =
      layout.size() + (
        (WORD - 1 | layout.align() - 1) &
          ptr::addr(a.next.tail).wrapping_sub(layout.size()));

    let Some(n) = a.next.size.checked_sub(m) else { break 'grow; };

    return Ok(Span::new(ptr::sub(a.next.tail, m), n));
  }

  if std::hint::black_box(true) {
    std::hint::black_box(E::fail(Error::TooLarge))
  } else {
    std::hint::black_box(E::fail(Error::TooLarge))
  }
}

#[inline(always)]
fn alloc_internal<'a, E>(arena: &mut Arena<'a>, layout: Layout) -> Result<NonNull<u8>, E>
where
  E: Fail
{
  let a = arena.0.get_mut();
  let s = unsafe { alloc_fast(*a, layout) }?;
  *a = s;
  Ok(s.tail)
}

#[inline(always)]
fn alloc<'a, T, E>(arena: &mut Arena<'a>) -> Result<Slot<'a, T>, E>
where
  E: Fail
{
  let x = alloc_internal(arena, Layout::new::<T>())?;
  Ok(Slot(ptr::cast(x), PhantomData))
}

#[inline(always)]
fn alloc_slice<'a, T, E>(arena: &mut Arena<'a>, len: usize) -> Result<Slot<'a, [T]>, E>
where
  E: Fail
{
  if size_of::<T>() != 0 && len > MAX_ALLOC / size_of::<T>() {
    return E::fail(Error::TooLarge);
  }

  let l = unsafe { Layout::from_size_align_unchecked(size_of::<T>() * len, align_of::<T>()) };
  let x = alloc_internal(arena, l)?;
  Ok(Slot(ptr::as_slice(ptr::cast(x), len), PhantomData))
}

#[inline(always)]
fn copy_slice<'a, T, E>(arena: &mut Arena<'a>, src: &[T]) -> Result<&'a mut [T], E>
where
  T: Copy,
  E: Fail
{
  let x = alloc_internal(arena, Layout::for_value(src))?;
  unsafe { ptr::copy_nonoverlapping::<T>(ptr::cast(ptr::from_ref(src)), ptr::cast(x), src.len()) };
  Ok(unsafe { ptr::as_slice_mut_ref(ptr::cast(x), src.len()) })
}

#[inline(always)]
fn copy_str<'a, E>(arena: &mut Arena<'a>, src: &str) -> Result<&'a mut str, E>
where
  E: Fail
{
  let x = copy_slice(arena, src.as_bytes())?;
  Ok(unsafe { str::from_utf8_unchecked_mut(x) })
}

#[inline(always)]
fn alloc_layout<'a, E>(arena: &mut Arena<'a>, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], E>
where
  E: Fail
{
  let x = alloc_internal(arena, layout)?;
  Ok(unsafe { ptr::as_slice_mut_ref(ptr::cast(x), layout.size()) })
}

impl<'a> Arena<'a> {
  #[inline(always)]
  pub fn alloc<T>(&mut self) -> Slot<'a, T> {
    unwrap(alloc(self))
  }

  #[inline(always)]
  pub fn try_alloc<T>(&mut self) -> Result<Slot<'a, T>, AllocError> {
    alloc(self)
  }

  #[inline(always)]
  pub fn alloc_slice<T>(&mut self, len: usize) -> Slot<'a, [T]> {
    unwrap(alloc_slice(self, len))
  }

  #[inline(always)]
  pub fn try_alloc_slice<T>(&mut self, len: usize) -> Result<Slot<'a, [T]>, AllocError> {
    alloc_slice(self, len)
  }

  #[inline(always)]
  pub fn copy_slice<T>(&mut self, src: &[T]) -> &'a mut [T]
  where
    T: Copy
  {
    unwrap(copy_slice(self, src))
  }

  #[inline(always)]
  pub fn try_copy_slice<T>(&mut self, src: &[T]) -> Result<&'a mut [T], AllocError>
  where
    T: Copy
  {
    copy_slice(self, src)
  }

  #[inline(always)]
  pub fn copy_str(&mut self, src: &str) -> &'a mut str {
    unwrap(copy_str(self, src))
  }

  #[inline(always)]
  pub fn try_copy_str(&mut self, src: &str) -> Result<&'a mut str, AllocError> {
    copy_str(self, src)
  }

  #[inline(always)]
  pub fn alloc_layout(&mut self, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
    unwrap(alloc_layout(self, layout))
  }

  #[inline(always)]
  pub fn try_alloc_layout(&mut self, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError> {
    alloc_layout(self, layout)
  }
}

impl<'a> fmt::Debug for Arena<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Arena").field(&self.0.get().tail).field(&self.0.get().size).finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//
// Slot
//
////////////////////////////////////////////////////////////////////////////////

impl<'a, T> Slot<'a, T> {
  #[inline(always)]
  pub fn as_uninit(self) -> &'a mut MaybeUninit<T> {
    unsafe { ptr::as_mut_ref(ptr::cast(self.0)) }
  }

  #[inline(always)]
  pub fn init(self, value: T) -> &'a mut T {
    unsafe { ptr::write(self.0, value) };
    unsafe { ptr::as_mut_ref(self.0) }
  }
}

impl<'a, T, const N: usize> Slot<'a, [T; N]> {
  #[inline(always)]
  pub fn as_uninit_array(self) -> &'a mut [MaybeUninit<T>; N] {
    unsafe { ptr::as_mut_ref(ptr::cast(self.0)) }
  }

  #[inline(always)]
  pub fn init_array<F>(self, f: F) -> &'a mut [T; N]
  where
    F: FnMut(usize) -> T
  {
    let mut x = ptr::cast(self.0);
    let mut i = 0;
    let mut f = f;

    while i < N {
      unsafe { ptr::write(x, f(i)) };
      i = i + 1;
      x = unsafe { ptr::add(x, 1) };
    }

    unsafe { ptr::as_mut_ref(ptr::cast(self.0)) }
  }
}

impl<'a, T> Slot<'a, [T]> {
  #[inline(always)]
  pub fn as_uninit_slice(self) -> &'a mut [MaybeUninit<T>] {
    unsafe { ptr::as_slice_mut_ref(ptr::cast(self.0), self.0.len()) }
  }

  #[inline(always)]
  pub fn init_slice<F>(self, f: F) -> &'a mut [T]
  where
    F: FnMut(usize) -> T
  {
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
//
// Allocator API
//
////////////////////////////////////////////////////////////////////////////////

unsafe impl<'a> allocator_api2::alloc::Allocator for Arena<'a> {
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    let s = self.0.get();
    let s = unsafe { alloc_fast(s, layout) }?;
    self.0.set(s);
    Ok(ptr::as_slice(s.tail, layout.size()))
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    let _ = self;
    let _ = ptr;
    let _ = layout;
  }
}

////////////////////////////////////////////////////////////////////////////////

pub fn foo<'a>(a: &mut Arena<'a>) -> &'a mut u64 {
  a.alloc().init(1_u64)
}

pub fn bar<'a>(a: &mut Arena<'a>, n: usize) -> &'a mut [u64] {
  a.alloc_slice(n).init_slice(|_| 1_u64)
}

pub fn baz<'a>(a: &mut Arena<'a>, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
  a.alloc_layout(layout)
}

pub fn qux<'a>(a: &mut Arena<'a>) -> Result<&'a mut u64, AllocError> {
  a.try_alloc().map(|x| x.init(1_u64))
}

pub fn qqq<'a>(a: &mut Arena<'a>, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError> {
  a.try_alloc_layout(layout)
}
