use crate::prelude::*;

#[test]
fn test_arena() {
  let arena = Arena::new();

  let x: &i64 = arena.allocate().write(1);
  let y: &i64 = arena.allocate().write(2);
  let z: &i64 = arena.allocate().write(3);

  assert!(x + y + z == 6);

  core::mem::drop(arena);
}
