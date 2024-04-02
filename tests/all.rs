// use expect_test::expect;
use oxcart::Arena;
// use oxcart::Slot;
use oxcart::pop::ptr;
use std::alloc::Layout;

#[test]
fn test_api() {
  let mut arena = Arena::new();
  let _ = Arena::try_new();
  // let _ = format!("{:?}", Arena::new());
  let mut allocator = arena.allocator();
  let _ = format!("{:?}", Arena::new().allocator());
  let _ = allocator.alloc_layout(Layout::new::<u64>());
  let _ = allocator.try_alloc_layout(Layout::new::<u64>());
  let _ = allocator.alloc::<u64>();
  let _ = allocator.try_alloc::<u64>();
  let _ = allocator.alloc_slice::<u64>(3);
  let _ = allocator.try_alloc_slice::<u64>(3);
  let _ = allocator.copy_slice::<u64>(&[0, 1, 2]);
  let _ = allocator.try_copy_slice::<u64>(&[0, 1, 2]);
  let _ = allocator.copy_str("hello");
  let _ = allocator.try_copy_str("hello");
  let _ = allocator.alloc::<u64>().as_uninit();
  let _ = allocator.alloc::<u64>().init(13);
  let _ = allocator.alloc::<[u64; 3]>().as_uninit_array();
  let _ = allocator.alloc::<[u64; 3]>().init_array(|i| i as u64);
  let _ = allocator.alloc_slice::<u64>(3).as_uninit_slice();
  let _ = allocator.alloc_slice::<u64>(3).init_slice(|i| i as u64);
  // let _ = format!("{:?}", Arena::new().allocator().alloc::<u64>());
}

#[test]
fn test_alloc_small() {
  let mut arena = Arena::new();
  let mut allocator = arena.allocator();
  let a = allocator.alloc().init(1_u8);
  let b = allocator.alloc().init(1_u16);
  let c = allocator.alloc().init(1_u32);
  let d = allocator.alloc().init(1_u64);
  let e = allocator.alloc().init(1_u128);
  let f = allocator.alloc().init(1_f32);
  let g = allocator.alloc().init(1_f64);
  let h = allocator.alloc().init(());
  let i = allocator.alloc().init(true);
  let j = allocator.alloc().init([1_u8; 0]);
  let k = allocator.alloc().init([1_u8; 1]);
  let l = allocator.alloc().init([1_u8; 3]);
  let m = allocator.alloc().init([1_u8; 5]);
  let n = allocator.alloc().init([1_u8; 7]);
  let o = allocator.alloc().init([1_u8; 9]);
  *a = 0_u8;
  *b = 0_u16;
  *c = 0_u32;
  *d = 0_u64;
  *e = 0_u128;
  *f = 0_f32;
  *g = 0_f64;
  *h = ();
  *i = false;
  *j = [0_u8; 0];
  *k = [0_u8; 1];
  *l = [0_u8; 3];
  *m = [0_u8; 5];
  *n = [0_u8; 7];
  *o = [0_u8; 9];
}

#[test]
fn test_alloc_zero_sized() {
  let mut arena = Arena::new();
  let mut allocator = arena.allocator();
  let _ = allocator.alloc_layout(Layout::new::<()>());
  let _ = allocator.alloc().init(());
  let _ = allocator.alloc().init([1_u64; 0]);
  let _ = allocator.alloc_slice(0).init_slice(|_| 0_u64);
  let _ = allocator.alloc_slice(5).init_slice(|_| ());
}


#[test]
fn test_alloc_aligned() {
  let mut arena = Arena::new();
  let mut allocator = arena.allocator();
  for &align in &[1, 2, 4, 8, 16, 32, 64] {
    let p = allocator.alloc_layout(Layout::from_size_align(1, align).unwrap());
    assert!(ptr::from(p).addr() & (align - 1) == 0);
  }
}

#[test]
fn test_linked_list() {
  struct Node<'a, T> {
    car: T,
    cdr: Option<&'a Node<'a, T>>
  }

  let mut arena = Arena::new();
  let mut allocator = arena.allocator();

  let mut x: Option<&Node<'_, u64>> = None;

  for i in 0 .. 10 {
    x = Some(allocator.alloc().init(Node { car: i, cdr: x }));
  }

  let mut y = 0;

  while let Some(z) = x {
    y = y + z.car;
    x = z.cdr;
  }

  assert!(y == 45);
}

/*
#[test]
fn test_too_big_allocation() {
  let too_big_nbytes = (isize::MAX as usize + 1) - (3 * size_of::<usize>());
  let too_big_nwords = too_big_nbytes / size_of::<usize>();
  let too_big_layout = Layout::from_size_align(too_big_nbytes, 1).unwrap();
  let mut arena = Arena::new();
  let mut arena_ref = &mut arena;
  assert!(arena_ref.try_alloc_slice::<usize>(too_big_nwords).is_err());
  assert!(arena_ref.try_alloc_layout(too_big_layout).is_err());
}
*/

/*
#[test]
fn test_debug() {
  expect!["Arena { lo: 0x0000000000000001, hi: 0x0000000000000000 }"].assert_eq(&format!("{:?}", Arena::new()));
}


#[test]
fn test_multiple_arena_refs_without_reset() {
  let mut arena = Arena::new();
  let mut arena_ref = &mut arena;
  let _ = arena_ref.alloc().init(1);
  let mut arena_ref = &mut arena;
  let _ = arena_ref.alloc().init(2);
  let mut arena_ref = &mut arena;
  let _ = arena_ref.alloc().init(3);
}

*/

/*
#[test]
fn test_demo() {
  let mut arena = Arena::new();

  let mut arena_ref = &mut arena;

  let x = arena_ref.alloc().init(0);
  let y = arena_ref.alloc().init(0);
  let z = arena_ref.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);

  arena.reset();

  let mut arena_ref = &mut arena;

  let _ = arena_ref.alloc::<[u64; 100000]>();
  let _ = arena_ref.alloc::<[u64; 0]>();
  let _ = arena_ref.alloc::<[u64; 1]>();

  arena.reset();

  let mut arena_ref = &mut arena;

  let x = arena_ref.alloc_slice(3).init_slice(|i| (i as u64) + 1);
  let y = arena_ref.alloc_layout(Layout::new::<[u64; 10]>());
  let z: &mut dyn fmt::Debug = arena_ref.alloc().init(13u64);

  assert!(x[0] + x[1] + x[2] == 6);
  assert!(y.len() == 80);
  assert!(&format!("{z:?}") == "13");

  arena.reset();
}
*/
