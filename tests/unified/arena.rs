use crate::prelude::*;

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

  drop(aa);

  assert!(*x + *y + *z == 6);

  let mut aa = arena.allocator();

  let x = aa.alloc().init(0);
  let y = aa.alloc().init(0);
  let z = aa.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);

  drop(aa);
}
