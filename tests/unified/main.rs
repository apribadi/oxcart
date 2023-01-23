pub use expect_test::expect;
pub use oxcart::Arena;
pub use oxcart::ArenaAllocator;

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
