#![doc = include_str!("../README.md")]

use std::alloc::Layout;
use std::alloc;
use std::cell::Cell;
use std::fmt;
use std::hint::unreachable_unchecked;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::mem::align_of;
use std::mem::size_of;
use std::panic::RefUnwindSafe;
use std::ptr::NonNull;
use std::str;

mod ptr;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// PUBLIC TYPE AND TRAIT DEFINITIONS                                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

pub struct Store(NonNull<Node>);

pub struct Arena<'a>(Cell<Span>, PhantomData<&'a ()>);

pub struct Slot<'a, T>(NonNull<T>, PhantomData<&'a ()>) where T: ?Sized;

pub use allocator_api2::alloc::AllocError;

unsafe impl Send for Store { }

unsafe impl Sync for Store { }

impl<'a> RefUnwindSafe for Arena<'a> { }

unsafe impl<'a> Send for Arena<'a> { }

unsafe impl<'a, T> Send for Slot<'a, T> where T: ?Sized { }

unsafe impl<'a, T> Sync for Slot<'a, T> where T: ?Sized { }

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
// Panicked                                                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

impl Fail for Panicked {
  #[inline(never)]
  #[cold]
  fn fail<T>(e: Error) -> Result<T, Self> {
    match e {
      Error::GlobalAllocatorFailed(layout) =>
        alloc::handle_alloc_error(layout),
      Error::TooLarge =>
        panic!("oxcart: attempted a too large allocation!"),
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// AllocError                                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

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
  pub fn new() -> Self {
    unwrap(store(INIT_SIZE))
  }

  pub fn try_new() -> Result<Self, AllocError> {
    store(INIT_SIZE)
  }

  pub fn with_capacity(capacity: usize) -> Self {
    unwrap(store(capacity))
  }

  pub fn try_with_capacity(capacity: usize) -> Result<Self, AllocError> {
    store(capacity)
  }

  pub fn arena(&mut self) -> Arena<'_> {
    let r = unsafe { ptr::as_mut_ref(self.0) };
    r.flag = false;
    Arena(Cell::new(r.next), PhantomData)
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
    return alloc_slow(span, layout);
  };

  Ok(Span::new(ptr::sub(span.tail, m), n))
}

#[inline(never)]
#[cold]
unsafe fn alloc_slow<E>(span: Span, layout: Layout) -> Result<Span, E>
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

    return Ok(Span::new(ptr::sub(a.next.tail, m), n));
  }

  let r: &mut Node = ptr::as_mut_ref(r.root);

  if ! (layout.size() <= MAX_ALLOC && layout.align() <= MAX_ALIGN) {
    return E::fail(Error::TooLarge);
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

  let p = chunk(n)?;
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

  Ok(Span::new(ptr::sub(span.tail, m), span.size - m))
}

#[inline(always)]
fn alloc_impl<'a, E>(arena: &mut Arena<'a>, layout: Layout) -> Result<NonNull<u8>, E>
where
  E: Fail
{
  let a = arena.0.get_mut();
  let s = *a;
  let s = unsafe { alloc_fast(s, layout) }?;
  *a = s;
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
  Ok(unsafe { str::from_utf8_unchecked_mut(x) })
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
    f.debug_tuple("Arena")
      .field(&self.0.get().tail)
      .field(&self.0.get().size)
      .finish()
  }
}

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Slot                                                                       //
//                                                                            //
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

    unsafe { ptr::as_mut_ref(self.0) }
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
//                                                                            //
// Allocator API                                                              //
//                                                                            //
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

pub fn foo<'a>(a: &mut Arena<'a>) -> [&'a mut u64; 4] {
  [
    a.alloc().init(1_u64),
    a.alloc().init(1_u64),
    a.alloc().init(1_u64),
    a.alloc().init(1_u64),
  ]
}

pub fn example_alloc_init<'a>(a: &mut Arena<'a>) -> &'a mut u64 {
  a.alloc().init(1_u64)
}

pub fn example_try_alloc_init<'a>(a: &mut Arena<'a>) -> Result<&'a mut u64, AllocError> {
  a.try_alloc().map(|x| x.init(1_u64))
}

pub fn example_alloc_slice<'a>(a: &mut Arena<'a>, n: usize) -> &'a mut [u64] {
  let mut i = 0_u64;
  a.alloc_slice(n).init_slice(|_| { i = i.wrapping_mul(5).wrapping_add(1); i })
}

pub fn example_try_alloc_slice<'a>(a: &mut Arena<'a>, n: usize) -> Result<&'a mut [u64], AllocError> {
  let mut i = 0_u64;
  a.try_alloc_slice(n).map(|x| x.init_slice(|_| { i = i.wrapping_mul(5).wrapping_add(1); i }))
}

pub fn example_alloc_layout<'a>(a: &mut Arena<'a>, layout: Layout) -> &'a mut [MaybeUninit<u8>] {
  a.alloc_layout(layout)
}

pub fn example_try_alloc_layout<'a>(a: &mut Arena<'a>, layout: Layout) -> Result<&'a mut [MaybeUninit<u8>], AllocError> {
  a.try_alloc_layout(layout)
}

pub fn example_loop_mut_ref_alloc_init<'a>(a: &mut Arena<'a>, x: &mut [Option<&'a mut u64>]) {
  for i in 0 .. x.len() {
    x[i] = Some(a.alloc().init(1_u64));
  }
}

pub fn example_loop_value_alloc_init<'a>(a: Arena<'a>, x: &mut [Option<&'a mut u64>]) {
  let mut a = a;
  for i in 0 .. x.len() {
    x[i] = Some(a.alloc().init(1_u64))
  }
}

pub fn example_loop_mut_ref_try_alloc_init<'a>(a: &mut Arena<'a>, x: &mut [Option<&'a mut u64>]) {
  for i in 0 .. x.len() {
    x[i] = match a.try_alloc() { Err(_) => None, Ok(x) => Some(x.init(1_u64)) };
  }
}
