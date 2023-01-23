pub use expect_test::expect;
pub use oxcart::Arena;
pub use oxcart::ArenaStorage;

fn foo<'a>(x: &mut &'a mut u64) {
  let _ = x;
}

#[test]
fn test_arena() {
  let mut storage = ArenaStorage::new();
  let mut arena = storage.arena();

  let x = arena.alloc().init(0);
  let y = arena.alloc().init(0);
  let z = arena.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);

  storage.reset();
}

#[test]
fn test_send_sync() {
  fn drop_send_sync<T: Send + Sync>(_ : T) {}
  let mut storage = ArenaStorage::new();
  let mut arena = storage.arena();
  let x = arena.alloc::<i64>();
  let y = arena.alloc_slice::<i64>(2);
  drop_send_sync(arena);
  drop_send_sync(x);
  drop_send_sync(y);
  drop_send_sync(storage);
}
