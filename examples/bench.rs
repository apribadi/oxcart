use std::alloc::Layout;
use std::mem::MaybeUninit;
use std::time::Instant;
use std::hint::black_box;

const OUTER: usize = 10_000;
const INNER: usize = 1000;
const COUNT: usize = OUTER * INNER;

struct Rng {
  x: u64
}

impl Rng {
  fn new() -> Self {
    Rng { x: 0x93c4_67e3_7db0_c7a5 }
  }

  #[inline(always)]
  fn next(&mut self) -> u64 {
    let x = self.x;
    let y = x;
    let x = x ^ x << 7;
    let x = x ^ x >> 9;
    self.x = x;
    y
  }
}

#[allow(dead_code)]
enum List<'a, T> {
  Nil,
  Cons(&'a Node<'a, T>),
}

#[allow(dead_code)]
struct Node<'a, T> {
  car: T,
  cdr: List<'a, T>,
}

impl<'a, T> bump_scope::NoDrop for Node<'a, T> where T: bump_scope::NoDrop { }

#[inline(never)]
fn go_a_0<'a>(arena: &mut oxcart::Arena<'a>, buf: &mut [Option<&'a MaybeUninit<u64>>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc().as_uninit());
  }
}

#[inline(never)]
fn go_a_1<'a>(arena: &mut oxcart::Arena<'a>, len: &[usize; INNER], buf: &mut [Option<&'a [MaybeUninit<u64>]>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_slice(len[i]).as_uninit_slice());
  }
}

#[inline(never)]
fn go_a_2<'a>(arena: &mut oxcart::Arena<'a>, layout: &[Layout; INNER], buf: &mut [Option<&'a [MaybeUninit<u8>]>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_layout(layout[i]));
  }
}

#[inline(never)]
fn go_a_3<'a>(arena: &mut oxcart::Arena<'a>) -> List<'a, u64> {
  let mut x = List::Nil;
  for i in 0 .. INNER {
    x = List::Cons(arena.alloc().init(Node { car: i as u64, cdr: x }));
  }
  x
}

#[inline(never)]
fn go_b_0<'a>(arena: oxcart::Arena<'a>, buf: &mut [Option<&'a MaybeUninit<u64>>; INNER]) {
  let mut arena = arena;
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc().as_uninit());
  }
}

#[inline(never)]
fn go_b_1<'a>(arena: oxcart::Arena<'a>, len: &[usize; INNER], buf: &mut [Option<&'a [MaybeUninit<u64>]>; INNER]) {
  let mut arena = arena;
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_slice(len[i]).as_uninit_slice());
  }
}

#[inline(never)]
fn go_b_2<'a>(arena: oxcart::Arena<'a>, layout: &[Layout; INNER], buf: &mut [Option<&'a [MaybeUninit<u8>]>; INNER]) {
  let mut arena = arena;
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_layout(layout[i]));
  }
}

#[inline(never)]
fn go_b_3<'a>(arena: oxcart::Arena<'a>) -> List<'a, u64> {
  let mut arena = arena;
  let mut x = List::Nil;
  for i in 0 .. INNER {
    x = List::Cons(arena.alloc().init(Node { car: i as u64, cdr: x }));
  }
  x
}

#[inline(never)]
fn go_c_0<'a>(arena: &'a bumpalo::Bump, buf: &mut [Option<&'a MaybeUninit<u64>>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc(MaybeUninit::uninit()));
  }
}

#[inline(never)]
fn go_c_1<'a>(arena: &'a bumpalo::Bump, len: &[usize; INNER], buf: &mut [Option<&'a [MaybeUninit<u64>]>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_slice_fill_copy(len[i], MaybeUninit::uninit()));
  }
}

#[inline(never)]
fn go_c_2<'a>(arena: &'a bumpalo::Bump, layout: &[Layout; INNER], buf: &mut [Option<&'a [MaybeUninit<u8>]>; INNER]) {
  for i in 0 .. INNER {
    let layout = layout[i];
    let p = arena.alloc_layout(layout).as_ptr().cast();
    let p = unsafe { &*std::ptr::slice_from_raw_parts(p, layout.size()) };
    buf[i] = Some(p);
  }
}

#[inline(never)]
fn go_c_3<'a>(arena: &'a bumpalo::Bump) -> List<'a, u64> {
  let mut x = List::Nil;
  for i in 0 .. INNER {
    x = List::Cons(arena.alloc(Node { car: i as u64, cdr: x }));
  }
  x
}

#[inline(never)]
fn go_d_0<'a>(arena: &'a bump_scope::Bump, buf: &mut [Option<&'a MaybeUninit<u64>>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_uninit().into_mut());
  }
}

#[inline(never)]
fn go_d_1<'a>(arena: &'a bump_scope::Bump, len: &[usize; INNER], buf: &mut [Option<&'a [MaybeUninit<u64>]>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_uninit_slice(len[i]).into_mut());
  }
}

#[inline(never)]
fn go_d_2<'a>(arena: &'a bump_scope::Bump, layout: &[Layout; INNER], buf: &mut [Option<&'a [MaybeUninit<u8>]>; INNER]) {
  for i in 0 .. INNER {
    let layout = layout[i];
    let p = arena.alloc_layout(layout).as_ptr().cast();
    let p = unsafe { &*std::ptr::slice_from_raw_parts(p, layout.size()) };
    buf[i] = Some(p);
  }
}

#[inline(never)]
fn go_d_3<'a>(arena: &'a bump_scope::Bump) -> List<'a, u64> {
  let mut x = List::Nil;
  for i in 0 .. INNER {
    x = List::Cons(arena.alloc(Node { car: i as u64, cdr: x }).into_mut());
  }
  x
}

type BumpScopeDownAlign8 = bump_scope::Bump<allocator_api2::alloc::Global, 8, false>;

#[inline(never)]
fn go_e_0<'a>(arena: &'a BumpScopeDownAlign8, buf: &mut [Option<&'a MaybeUninit<u64>>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_uninit().into_mut());
  }
}

#[inline(never)]
fn go_e_1<'a>(arena: &'a BumpScopeDownAlign8, len: &[usize; INNER], buf: &mut [Option<&'a [MaybeUninit<u64>]>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_uninit_slice(len[i]).into_mut());
  }
}

#[inline(never)]
fn go_e_2<'a>(arena: &'a BumpScopeDownAlign8, layout: &[Layout; INNER], buf: &mut [Option<&'a [MaybeUninit<u8>]>; INNER]) {
  for i in 0 .. INNER {
    let layout = layout[i];
    let p = arena.alloc_layout(layout).as_ptr().cast();
    let p = unsafe { &*std::ptr::slice_from_raw_parts(p, layout.size()) };
    buf[i] = Some(p);
  }
}

#[inline(never)]
fn go_e_3<'a>(arena: &'a BumpScopeDownAlign8) -> List<'a, u64> {
  let mut x = List::Nil;
  for i in 0 .. INNER {
    x = List::Cons(arena.alloc(Node { car: i as u64, cdr: x }).into_mut());
  }
  x
}

#[inline(never)]
fn warmup() {
  let mut s = 1u64;
  for i in 0 .. 1_000_000_000 { s = s.wrapping_mul(i); }
  let _: u64 = black_box(s);
}

#[inline(never)]
fn timeit<F: FnMut()>(name: &str, f: F) {
  let mut f = f;
  let start = Instant::now();
  for _ in 0 .. OUTER { f() }
  let stop = Instant::now();
  let elapsed = stop.saturating_duration_since(start).as_nanos() as f64;
  println!("{} {:.3} ns", name, elapsed / COUNT as f64);
}

fn main() {
  warmup();

  let mut rng = Rng::new();

  let len = &mut [0_usize; INNER];
  len.fill_with(|| 1 + rng.next().trailing_zeros() as usize);

  let layout = &mut [Layout::new::<()>(); INNER];
  layout.fill_with(||
    Layout::from_size_align(
      [0, 4, 8, 12][(rng.next() & 3) as usize],
      [1, 4, 8, 32][(rng.next() & 3) as usize]
    ).unwrap()
  );

  let mut store = oxcart::Store::with_capacity(1 << 17);
  timeit("A.0", || go_a_0(&mut store.arena(), &mut [None; INNER]));
  timeit("A.1", || go_a_1(&mut store.arena(), len, &mut [None; INNER]));
  timeit("A.2", || go_a_2(&mut store.arena(), layout, &mut [None; INNER]));
  timeit("A.3", || { let _ = black_box(go_a_3(&mut store.arena())); });

  let mut store = oxcart::Store::with_capacity(1 << 17);
  timeit("B.0", || go_b_0(store.arena(), &mut [None; INNER]));
  timeit("B.1", || go_b_1(store.arena(), len, &mut [None; INNER]));
  timeit("B.2", || go_b_2(store.arena(), layout, &mut [None; INNER]));
  timeit("B.3", || { let _ = black_box(go_b_3(store.arena())); });

  let mut arena = bumpalo::Bump::with_capacity(1 << 17);
  timeit("C.0", || { arena.reset(); go_c_0(&arena, &mut [None; INNER]); });
  timeit("C.1", || { arena.reset(); go_c_1(&arena, len, &mut [None; INNER]); });
  timeit("C.2", || { arena.reset(); go_c_2(&arena, layout, &mut [None; INNER]); });
  timeit("C.3", || { arena.reset(); let _ = black_box(go_c_3(&arena)); });

  let mut arena = bump_scope::Bump::with_size(1 << 17);
  timeit("D.0", || { arena.reset(); go_d_0(&arena, &mut [None; INNER]); });
  timeit("D.1", || { arena.reset(); go_d_1(&arena, len, &mut [None; INNER]); });
  timeit("D.2", || { arena.reset(); go_d_2(&arena, layout, &mut [None; INNER]); });
  timeit("D.3", || { arena.reset(); let _ = black_box(go_d_3(&arena)); });

  let mut arena = BumpScopeDownAlign8::with_size(1 << 17);
  timeit("E.0", || { arena.reset(); go_e_0(&arena, &mut [None; INNER]); });
  timeit("E.1", || { arena.reset(); go_e_1(&arena, len, &mut [None; INNER]); });
  timeit("E.2", || { arena.reset(); go_e_2(&arena, layout, &mut [None; INNER]); });
  timeit("E.3", || { arena.reset(); let _ = black_box(go_e_3(&arena)); });
}
