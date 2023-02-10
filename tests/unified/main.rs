use core::alloc::Layout;
use core::fmt;
use oxcart::Arena;

#[test]
fn test_arena() {
  let mut arena = Arena::new();

  let allocator = arena.allocator();

  let x = allocator.alloc().init(0);
  let y = allocator.alloc().init(0);
  let z = allocator.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);

  arena.reset();

  let allocator = arena.allocator();

  let _ = allocator.alloc::<[u64; 100000]>();
  let _ = allocator.alloc::<[u64; 0]>();
  let _ = allocator.alloc::<[u64; 1]>();

  arena.reset();

  let allocator = arena.allocator();

  let x = allocator.alloc_slice(3).init_slice(|i| (i as u64) + 1);
  let y = allocator.alloc_layout(Layout::new::<[u64; 10]>());
  let z: &mut dyn fmt::Display = allocator.alloc().init(13u64);

  assert!(x[0] + x[1] + x[2] == 6);
  assert!(y.len() == 80);
  assert!(&format!("{z}") == "13");

  arena.reset();
}

#[test]
fn test_zst() {
  let mut arena = Arena::new();
  let allocator = arena.allocator();
  let x = allocator.alloc().init(());
  assert!(*x == ());
}

#[test]
fn test_send_sync() {
  fn send_sync<T: Send + Sync>(_ : &T) {}

  let mut arena = Arena::new();

  send_sync::<Arena>(&arena);

  let allocator = arena.allocator();
  let x = allocator.alloc::<i64>();
  let y = allocator.alloc_slice::<i64>(2);

  send_sync::<oxcart::Allocator>(allocator);
  send_sync::<oxcart::Slot<_>>(&x);
  send_sync::<oxcart::Slot<_>>(&y);
}

#[test]
fn test_list() {
  enum List<'a, T> {
    Nil,
    Cons(&'a Node<'a, T>),
  }

  #[allow(dead_code)]
  struct Node<'a, T> {
    car: T,
    cdr: List<'a, T>
  }

  let mut arena = Arena::new();
  let allocator = arena.allocator();

  let mut a = List::Nil;
  for i in 0 .. 100 {
    a = List::Cons(allocator.alloc().init(Node { car: i as u64, cdr: a }));
  }
}
