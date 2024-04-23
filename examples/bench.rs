use std::time::Instant;
use std::mem::MaybeUninit;

const OUTER: usize = 1024 * 16;
const INNER: usize = 1024;
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

#[inline(never)]
fn go_a_0<'a>(arena: &mut oxcart::Arena<'a>, buf: &mut [Option<&'a MaybeUninit<u64>>; INNER]) {
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc().as_uninit());
  }
}

#[inline(never)]
fn go_a_1<'a>(arena: &mut oxcart::Arena<'a>, len: &[usize; INNER], buf: &mut [Option<&'a [MaybeUninit<u64>]>; INNER])
{
  for i in 0 .. INNER {
    buf[i] = Some(arena.alloc_slice(len[i]).as_uninit_slice());
  }
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
fn warmup() {
  let mut s = 1u64;
  for i in 0 .. 1_000_000_000 { s = s.wrapping_mul(i); }
  let _: u64 = std::hint::black_box(s);
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

  let mut store = oxcart::Store::new();
  timeit("A.0", || go_a_0(&mut store.arena(), &mut [None; INNER]));
  timeit("A.1", || go_a_1(&mut store.arena(), len, &mut [None; INNER]));

  let mut store = oxcart::Store::new();
  timeit("B.0", || go_b_0(store.arena(), &mut [None; INNER]));
  timeit("B.1", || go_b_1(store.arena(), len, &mut [None; INNER]));

  let mut arena = bumpalo::Bump::new();
  timeit("C.0", || { arena.reset(); go_c_0(&arena, &mut [None; INNER]); });
  timeit("C.1", || { arena.reset(); go_c_1(&arena, len, &mut [None; INNER]); });
}
