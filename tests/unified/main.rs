pub use expect_test::expect;
pub use oxcart::Arena;

#[test]
fn test_arena() {
  let mut arena = Arena::new();

  arena.region(|allocator| {
    let x = allocator.alloc().init(0);
    let y = allocator.alloc().init(0);
    let z = allocator.alloc().init(0);

    *x = 1;
    *y = 2;
    *z = 3;

    assert!(*x + *y + *z == 6);
  });

  arena.region(|allocator| {
    let x = allocator.alloc_slice(3).init(|i| (i as u64) + 1);

    assert!(x[0] + x[1] + x[2] == 6);
  });
}

#[test]
fn test_send_sync() {
  fn send_sync<T: Send + Sync>(_ : &T) {}

  let mut arena = Arena::new();

  send_sync::<Arena>(&arena);

  arena.region(|allocator| {
    let x = allocator.alloc::<i64>();
    let y = allocator.alloc_slice::<i64>(2);
    send_sync::<oxcart::Allocator>(&allocator);
    send_sync::<oxcart::Uninit<_>>(&x);
    send_sync::<oxcart::UninitSlice<_>>(&y);
  })
}

#[test]
fn test_list() {
  enum List<'a, A> {
    Nil,
    Cons(&'a Node<'a, A>),
  }

  #[allow(dead_code)]
  struct Node<'a, A> {
    car: A,
    cdr: List<'a, A>
  }

  let mut arena = Arena::new();

  arena.region(|allocator| {
    let mut x = List::Nil;
    for i in 0 .. 100 {
      x = List::Cons(allocator.alloc().init(Node { car: i as u64, cdr: x }));
    }
  });
}
