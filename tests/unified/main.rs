pub use expect_test::expect;
pub use oxcart::Arena;

enum List<'a, A> {
  Nil,
  Cons(&'a mut Node<'a, A>),
}

#[allow(dead_code)]
struct Node<'a, A> {
  car: A,
  cdr: List<'a, A>
}

#[test]
fn test_arena() {
  let mut arena = Arena::new();
  let mut aa = arena.allocator();

  let x = aa.alloc().init(0);
  let y = aa.alloc().init(0);
  let z = aa.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);

  arena.reset();

  let mut aa = arena.allocator();

  let x = aa.alloc().init(0);
  let y = aa.alloc().init(0);
  let z = aa.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);
}

#[test]
fn test_send_sync() {
  fn drop_send_sync<T: Send + Sync>(_ : T) {}
  let mut arena = Arena::new();
  let mut aa = arena.allocator();
  let x = aa.alloc::<i64>();
  let y = aa.alloc_slice::<i64>(2);
  drop_send_sync(aa);
  drop_send_sync(x);
  drop_send_sync(y);
  drop_send_sync(arena);
}

#[test]
fn test_list() {
  let mut arena = Arena::new();
  let mut aa = arena.allocator();
  let mut x = List::Nil;
  for i in 0 .. 100 {
    x = List::Cons(aa.alloc().init(Node { car: i as u64, cdr: x }));
  }
}
