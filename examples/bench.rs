use std::time::Instant;
use std::hint;
use oxcart::Arena;
use oxcart::ArenaStorage;

const COUNT: usize = 100_000_000;

enum List<'a, A> {
  Nil,
  Cons(&'a Node<'a, A>),
}

#[allow(dead_code)]
struct Node<'a, A> {
  car: A,
  cdr: List<'a, A>
}

fn warmup() {
  let mut s = 1u64;
  for i in 0 .. 100_000_000 { s = s.wrapping_mul(i); }
  let _: u64 = hint::black_box(s);
}

fn timeit<A, F>(f: F) -> f64 where F: FnOnce() -> A {
  let start = Instant::now();
  let _: A = hint::black_box(f());
  let stop = Instant::now();
  stop.saturating_duration_since(start).as_nanos() as f64
}

fn run_bench<F, A, B>(name: &str, t: A, f: F) where F: Fn(A, usize) -> B {
  let elapsed = timeit(|| f(t, COUNT));
  print!("{:25} {:.3} ns\n", name, elapsed / (COUNT as f64));
}

#[inline(never)]
fn bench_oxcart<'a>(arena: Arena<'a>, count: usize) -> List<'a, u64> {
  let mut arena = arena;
  let mut r = List::Nil;
  for i in 0 .. count {
    r = List::Cons(arena.alloc().init(Node { car: i as u64, cdr: r }));
  }
  r
}

#[inline(never)]
fn bench_bumpalo<'a>(bump: &'a bumpalo::Bump, count: usize) -> List<'a, u64> {
  let mut r = List::Nil;
  for i in 0 .. count {
    r = List::Cons(bump.alloc(Node { car: i as u64, cdr: r }));
  }
  r
}

fn main() {
  warmup();

  let mut storage = ArenaStorage::new();
  let bump = &bumpalo::Bump::new();

  run_bench("oxcart", storage.arena(), bench_oxcart);
  run_bench("bumpalo", bump, bench_bumpalo);
}
