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
