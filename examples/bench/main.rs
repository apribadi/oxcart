use std::time::Instant;
use std::hint;

// mod intmap;

const ITERS: usize = 10_000;
const LEN: usize = 10_000;
// const LEN: usize = 1_000;

type List<'a, T> = Option<&'a Node<'a, T>>;

#[derive(Clone, Copy)]
struct Node<'a, T> {
  #[allow(dead_code)]
  car: T,
  #[allow(dead_code)]
  cdr: Option<&'a Node<'a, T>>,
}

struct NodeWithKey<K, T> {
  #[allow(dead_code)]
  car: T,
  #[allow(dead_code)]
  cdr: Option<K>,
}

fn warmup() {
  let mut s = 1u64;
  for i in 0 .. 2_000_000_000 { s = s.wrapping_mul(i); }
  let _: u64 = hint::black_box(s);
}

fn timeit<F: FnOnce()>(f: F) -> f64 {
  let start = Instant::now();
  f();
  let stop = Instant::now();
  stop.saturating_duration_since(start).as_nanos() as f64
}

fn run_bench<F: FnOnce(usize, usize)>(name: &str, f: F) {
  let duration = timeit(|| f(hint::black_box(ITERS), hint::black_box(LEN)));
  let duration = duration / ((ITERS * LEN) as f64);
  print!("{:25} {:.3} ns\n", name, duration);
}

#[inline(never)]
fn bench_oxcart(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list<'a>(allocator: &mut oxcart::Allocator<'a>, len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(allocator.alloc().init(Node { car: i as u64, cdr: r }));
    }
    r
  }

  let mut arena = oxcart::Arena::new();

  for _ in 0 .. iters {
    let allocator = arena.allocator();
    let _: _ = hint::black_box(make_list(allocator, len));
    arena.reset();
  }
}

#[inline(never)]
fn bench_oxcart_noinline(iters: usize, len: usize) {
  #[inline(never)]
  fn make_node<'a>
    (
      allocator: &mut oxcart::Allocator<'a>,
      car: u64,
      cdr: Option<&'a Node<'a, u64>>
    ) -> &'a mut Node<'a, u64>
  {
    allocator.alloc().init(Node { car, cdr })
  }

  #[inline(never)]
  fn make_list<'a>(allocator: &mut oxcart::Allocator<'a>, len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(make_node(allocator, i as u64, r));
    }
    r
  }

  let mut arena = oxcart::Arena::new();

  for _ in 0 .. iters {
    let allocator = arena.allocator();
    let _: _ = hint::black_box(make_list(allocator, len));
    arena.reset();
  }
}

#[inline(never)]
fn bench_bumpalo(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list<'a>(arena: &'a bumpalo::Bump, len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(arena.alloc(Node { car: i as u64, cdr: r }));
    }
    r
  }

  let mut arena = bumpalo::Bump::new();

  for _ in 0 .. iters {
    let _: List<_> = hint::black_box(make_list(&arena, len));
    arena.reset();
  }
}

#[inline(never)]
fn bench_bumpalo_noinline(iters: usize, len: usize) {
  #[inline(never)]
  fn make_node<'a>
    (
      arena: &'a bumpalo::Bump,
      car: u64,
      cdr: Option<&'a Node<'a, u64>>
    ) -> &'a mut Node<'a, u64>
  {
    arena.alloc(Node { car, cdr })
  }

  #[inline(never)]
  fn make_list<'a>(arena: &'a bumpalo::Bump, len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(make_node(arena, i as u64, r));
    }
    r
  }

  let mut arena = bumpalo::Bump::new();

  for _ in 0 .. iters {
    let _: _ = hint::black_box(make_list(&arena, len));
    arena.reset();
  }
}

#[inline(never)]
fn bench_typed_arena(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list<'a>(arena: &'a typed_arena::Arena<Node<'a, u64>>, len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(arena.alloc(Node { car: i as u64, cdr: r }));
    }
    r
  }

  for _ in 0 .. iters {
    let arena = typed_arena::Arena::new();
    let _: List<_> = hint::black_box(make_list(&arena, len));
  }
}

#[inline(never)]
fn bench_copy_arena(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list<'a>(allocator: &'a mut copy_arena::Allocator<'a>, len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(allocator.alloc(Node { car: i as u64, cdr: r }));
    }
    r
  }

  for _ in 0 .. iters {
    let mut arena = copy_arena::Arena::new();
    let mut allocator = arena.allocator();
    let _: List<_> = hint::black_box(make_list(&mut allocator, len));
  }
}

#[inline(never)]
fn bench_slotmap(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list
    (
      slotmap: &mut slotmap::SlotMap<slotmap::DefaultKey, NodeWithKey<slotmap::DefaultKey, u64>>,
      len: usize
    ) -> Option<slotmap::DefaultKey>
  {
    let mut r = None;
    for i in (0 .. len).rev() {
      r = Some(slotmap.insert(NodeWithKey { car: i as u64, cdr: r }));
    }
    r
  }

  let mut slotmap = slotmap::SlotMap::new();

  for _ in 0 .. iters {
    let _: _ = hint::black_box(make_list(&mut slotmap, len));
    slotmap.clear();
  }
}

#[inline(never)]
fn bench_generational_arena(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list
    (
      arena: &mut generational_arena::Arena<NodeWithKey<generational_arena::Index, u64>>,
      len: usize
    ) -> Option<generational_arena::Index>
  {
    let mut r = None;
    for i in (0 .. len).rev() {
      r = Some(arena.insert(NodeWithKey { car: i as u64, cdr: r }));
    }
    r
  }

  let mut arena = generational_arena::Arena::new();

  for _ in 0 .. iters {
    let _: _ = hint::black_box(make_list(&mut arena, len));
    arena.clear();
  }
}

#[inline(never)]
fn bench_slab(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list
    (
      slab: &mut slab::Slab<NodeWithKey<usize, u64>>,
      len: usize
    ) -> Option<usize>
  {
    let mut r = None;
    for i in (0 .. len).rev() {
      r = Some(slab.insert(NodeWithKey { car: i as u64, cdr: r }));
    }
    r
  }

  let mut slab = slab::Slab::new();

  for _ in 0 .. iters {
    let _: _ = hint::black_box(make_list(&mut slab, len));
    slab.clear();
  }
}

#[inline(never)]
fn bench_box_leak(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list<'a>(len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(Box::leak(Box::new(Node { car: i as u64, cdr: r })));
    }
    r
  }

  for _ in 0 .. iters {
    let _: List<_> = hint::black_box(make_list(len));
  }
}

#[cfg(feature = "allocator_api")]
#[inline(never)]
fn bench_allocator_api(iters: usize, len: usize) {
  #[inline(never)]
  fn make_list<'a>(allocator: &oxcart::Allocator<'a>, len: usize) -> List<'a, u64> {
    let mut r: List<'a, u64> = None;
    for i in (0 .. len).rev() {
      r = Some(Box::leak(Box::new_in(Node { car: i as u64, cdr: r }, allocator)));
    }
    r
  }

  let mut arena = oxcart::Arena::new();

  for _ in 0 .. iters {
    let allocator = arena.allocator();
    let _: List<_> = hint::black_box(make_list(len), allocator);
    arena.reset();
  }
}

/*
#[inline(never)]
fn bench_intmap_oxcart(iters: usize, len: usize) {
  #[inline(never)]
  fn make_intmap<'a>
    (
      allocator: &mut oxcart::Allocator<'a>,
      len: usize
    ) -> intmap::IntMap<'a, u64>
  {
    let mut t = intmap::new();

    for i in 0 .. len {
      let i = i as u64;
      t = intmap::with_oxcart::insert(allocator, i, i, t)
    }

    t
  }

  let mut arena = oxcart::Arena::new();

  for _ in 0 .. iters {
    let allocator = arena.allocator();
    let _: _ = hint::black_box(make_intmap(allocator, len));
    arena.reset();
  }
}

#[inline(never)]
fn bench_intmap_bumpalo(iters: usize, len: usize) {
  #[inline(never)]
  fn make_intmap<'a>
    (
      arena: &'a bumpalo::Bump,
      len: usize
    ) -> intmap::IntMap<'a, u64>
  {
    let mut t = intmap::new();

    for i in 0 .. len {
      let i = i as u64;
      t = intmap::with_bumpalo::insert(arena, i, i, t)
    }

    t
  }

  let mut arena = bumpalo::Bump::new();

  for _ in 0 .. iters {
    let _: _ = hint::black_box(make_intmap(&arena, len));
    arena.reset();
  }
}
*/


fn main() {
  /*
  warmup();

  run_bench("intmap-oxcart", bench_intmap_oxcart);
  run_bench("intmap-bumpalo", bench_intmap_bumpalo);
  */
  warmup();

  run_bench("oxcart", bench_oxcart);
  run_bench("oxcart-noinline", bench_oxcart_noinline);
  run_bench("bumpalo", bench_bumpalo);
  run_bench("bumpalo-noinline", bench_bumpalo_noinline);
  run_bench("typed-arena", bench_typed_arena);
  run_bench("copy_arena", bench_copy_arena);
  run_bench("slotmap", bench_slotmap);
  run_bench("generational_arena", bench_generational_arena);
  run_bench("slab", bench_slab);
  run_bench("box-leak", bench_box_leak);

  #[cfg(feature = "allocator_api")]
  run_bench("allocator_api", bench_allocator_api);
}
