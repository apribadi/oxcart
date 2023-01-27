use std::time::Instant;
use std::hint;

const COUNT_0: usize = 10_000;
const COUNT_1: usize = 10_000;

#[derive(Clone, Copy)]
enum List<'a, A> {
  Nil,
  Cons(&'a Node<'a, A>),
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
struct Node<'a, A> {
  car: A,
  cdr: List<'a, A>
}

#[allow(dead_code)]
enum KeyedList<K> {
  Nil,
  Cons(K),
}

#[allow(dead_code)]
struct KeyedNode<K, A> {
  car: A,
  cdr: K,
}

fn warmup() {
  let mut s = 1u64;
  for i in 0 .. 2_000_000_000 { s = s.wrapping_mul(i); }
  let _: u64 = hint::black_box(s);
}

fn timeit<A, F>(f: F) -> f64 where F: FnOnce() -> A {
  let start = Instant::now();
  let _: A = hint::black_box(f());
  let stop = Instant::now();
  stop.saturating_duration_since(start).as_nanos() as f64
}

fn run_bench<F>(name: &str, f: F) where F: Fn(usize, usize) -> () {
  let count_0 = hint::black_box(COUNT_0);
  let count_1 = hint::black_box(COUNT_1);
  let elapsed = timeit(|| f(count_0, count_1));
  print!("{:25} {:.3} ns\n", name, elapsed / ((COUNT_0 * COUNT_1) as f64));
}

#[inline(never)]
fn bench_oxcart<'a>(count_0: usize, count_1: usize) {
  let mut arena = oxcart::Arena::new();
  for _ in 0 .. count_0 {
    let mut allocator = arena.allocator();
    let mut r = List::Nil;
    for i in 0 .. count_1 {
      r = List::Cons(allocator.alloc().init(Node { car: i as u64, cdr: r }));
    }
    let _: List<_> = hint::black_box(r);
    arena.reset();
  }
}

#[inline(never)]
fn bench_bumpalo<'a>(count_0: usize, count_1: usize) {
  let mut arena = bumpalo::Bump::new();
  for _ in 0 .. count_0 {
    let mut r = List::Nil;
    for i in 0 .. count_1 {
      r = List::Cons(arena.alloc(Node { car: i as u64, cdr: r }));
    }
    let _: List<_> = hint::black_box(r);
    arena.reset();
  }
}

#[inline(never)]
fn bench_toolshed<'a>(count_0: usize, count_1: usize) {
  for _ in 0 .. count_0 {
    let arena = toolshed::Arena::new();
    let mut r = List::Nil;
    for i in 0 .. count_1 {
      r = List::Cons(arena.alloc(Node { car: i as u64, cdr: r }));
    }
    let _: List<_> = hint::black_box(r);
  }
}

#[inline(never)]
fn bench_typed_arena<'a>(count_0: usize, count_1: usize) {
  for _ in 0 .. count_0 {
    let arena = typed_arena::Arena::new();
    let mut r = List::Nil;
    for i in 0 .. count_1 {
      r = List::Cons(arena.alloc(Node { car: i as u64, cdr: r }));
    }
    let _: List<_> = hint::black_box(r);
  }
}

#[inline(never)]
fn bench_copy_arena<'a>(count_0: usize, count_1: usize) {
  for _ in 0 .. count_0 {
    let mut arena = copy_arena::Arena::new();
    let mut allocator = arena.allocator();
    let mut r = List::Nil;
    for i in 0 .. count_1 {
      r = List::Cons(allocator.alloc(Node { car: i as u64, cdr: r }));
    }
    let _: List<_> = hint::black_box(r);
  }
}

#[inline(never)]
fn bench_slotmap<'a>(count_0: usize, count_1: usize) {
  let mut slotmap = slotmap::basic::SlotMap::new();
  for _ in 0 .. count_0 {
    let mut r = KeyedList::Nil;
    for i in 0 .. count_1 {
      r = KeyedList::Cons(slotmap.insert(KeyedNode { car: i as u64, cdr: r }));
    }
    let _: KeyedList<_> = hint::black_box(r);
    slotmap.clear();
  }
}

#[inline(never)]
fn bench_generational_arena<'a>(count_0: usize, count_1: usize) {
  let mut arena = generational_arena::Arena::new();
  for _ in 0 .. count_0 {
    let mut r = KeyedList::Nil;
    for i in 0 .. count_1 {
      r = KeyedList::Cons(arena.insert(KeyedNode { car: i as u64, cdr: r }));
    }
    let _: KeyedList<_> = hint::black_box(r);
    arena.clear();
  }
}

fn main() {
  warmup();

  run_bench("oxcart", bench_oxcart);
  run_bench("bumpalo", bench_bumpalo);
  run_bench("toolshed", bench_toolshed);
  run_bench("typed-arena", bench_typed_arena);
  run_bench("copy_arena", bench_copy_arena);
  run_bench("slotmap", bench_slotmap);
  run_bench("generational_arena", bench_generational_arena);
}
