use core::alloc::Layout;
use core::fmt;
use oxcart::Allocator;
use oxcart::Arena;
use oxcart::Slot;

#[test]
fn test_basic() {
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
  let z: &mut dyn fmt::Display = allocator.alloc().init(42u64);

  assert!(x[0] + x[1] + x[2] == 6);
  assert!(y.len() == 80);
  assert!(&format!("{z}") == "42");

  arena.reset();
}

#[test]
fn test_zero_size() {
  let mut arena = Arena::new();
  let allocator = arena.allocator();
  let x = allocator.alloc().init(());
  let y = allocator.alloc_slice(0).init_slice(|_| 0u64);
  let z = allocator.alloc_slice(0).init_slice(|_| ());
  assert!(*x == ());
  assert!(y.len() == 0);
  assert!(z.len() == 0);
}

#[test]
fn test_no_reset() {
  let mut arena = Arena::new();
  let allocator = arena.allocator();
  let x = allocator.alloc().init(1);
  let allocator = arena.allocator();
  let y = allocator.alloc().init(2);
  let allocator = arena.allocator();
  let z = allocator.alloc().init(3);
  let _ = x;
  let _ = y;
  let _ = z;
}

#[test]
fn test_send_sync() {
  fn send_sync<T: Send + Sync>(_ : &T) {}

  let mut arena = Arena::new();
  send_sync::<Arena>(&arena);

  let allocator = arena.allocator();
  send_sync::<Allocator>(allocator);

  let x = allocator.alloc::<u64>();
  let y = allocator.alloc_slice::<u64>(2);
  send_sync::<Slot<_>>(&x);
  send_sync::<Slot<_>>(&y);
}

#[test]
fn test_list() {
  #[allow(dead_code)]
  struct Node<'a, T> {
    car: T,
    cdr: Option<&'a Node<'a, T>>
  }

  let mut arena = Arena::new();
  let allocator = arena.allocator();
  let mut head: Option<&Node<u64>> = None;
  for i in 0 .. 100 {
    head = Some(allocator.alloc().init(Node { car: i as u64, cdr: head }));
  }
}
