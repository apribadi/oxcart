use crate::prelude::*;

#[test]
fn test_arena() {
  let mut arena = Arena::new();
  let x: &i64 = arena.allocate().write(42i64);
  let _ = x;
}
