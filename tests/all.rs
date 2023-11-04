use expect_test::expect;
use core::alloc::Layout;
use core::fmt;
use core::mem::size_of;
use oxcart::Arena;
use oxcart::ArenaRef;
use oxcart::Slot;

#[inline(always)]
fn addr<T: ?Sized>(p: *const T) -> usize {
  let p = p as *const();
  unsafe { core::mem::transmute(p) }
}

#[test]
fn test_api() {
  let mut arena = Arena::new();
  arena.reset();
  let mut arena_ref = &mut arena;
  let _ = arena_ref.alloc::<u64>();
  let _ = arena_ref.try_alloc::<u64>();
  let _ = arena_ref.alloc_slice::<u64>(5);
  let _ = arena_ref.try_alloc_slice::<u64>(5);
  let _ = arena_ref.alloc_layout(Layout::new::<u64>());
  let _ = arena_ref.try_alloc_layout(Layout::new::<u64>());
  let _ = arena_ref.copy_slice::<u64>(&[0, 1, 2, 3, 4]);
  let _ = arena_ref.try_copy_slice::<u64>(&[0, 1, 2, 3, 4]);
  let _ = arena_ref.copy_str("hello");
  let _ = arena_ref.try_copy_str("hello");
  let _ = arena_ref.alloc::<u64>().as_uninit();
  let _ = arena_ref.alloc::<u64>().init(13);
  let _ = arena_ref.alloc::<[u64; 5]>().as_uninit_array();
  let _ = arena_ref.alloc::<[u64; 5]>().init_array(|i| i as u64);
  let _ = arena_ref.alloc_slice::<u64>(5).len();
  let _ = arena_ref.alloc_slice::<u64>(5).as_uninit_slice();
  let _ = arena_ref.alloc_slice::<u64>(5).init_slice(|i| i as u64);
  let _ = Arena::default();
  let _ = format!("{:?}", Arena::new());
  let _ = format!("{:?}", (&mut Arena::new()).alloc::<u64>());
}

#[test]
fn test_debug() {
  expect!["Arena { lo: 0x0000000000000001, hi: 0x0000000000000000 }"].assert_eq(&format!("{:?}", Arena::new()));
}

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

#[test]
fn test_zero_size_allocation() {
  let mut arena = Arena::new();
  let mut arena_ref = &mut arena;
  let a = arena_ref.alloc().init(());
  let b = arena_ref.alloc_slice(0).init_slice(|_| 0u64);
  let c = arena_ref.alloc_slice(5).init_slice(|_| ());
  let d = arena_ref.alloc_layout(Layout::new::<()>());
  assert!(*a == ());
  assert!(b.len() == 0);
  assert!(c.len() == 5);
  assert!(d.len() == 0);
}

#[test]
fn test_alignment() {
  let mut arena = Arena::new();
  let mut arena_ref = &mut arena;
  for align in [1, 2, 4, 8, 16, 32, 64] {
    let layout = Layout::from_size_align(1, align).unwrap();
    let p = arena_ref.alloc_layout(layout).as_uninit_slice();
    assert!(addr(p) & (align - 1) == 0);
  }
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

#[test]
fn test_types_are_send_and_sync() {
  fn is_send<T: Send>(_ : &T) {}
  fn is_sync<T: Sync>(_ : &T) {}
  let mut arena = Arena::new();
  is_send::<Arena>(&arena);
  is_sync::<Arena>(&arena);
  let mut arena_ref = &mut arena;
  let x = arena_ref.alloc::<u64>();
  let y = arena_ref.alloc_slice::<u64>(5);
  is_send::<Slot<'_, _>>(&x);
  is_sync::<Slot<'_, _>>(&x);
  is_send::<Slot<'_, _>>(&y);
  is_sync::<Slot<'_, _>>(&y);
}

#[test]
fn test_linked_list() {
  struct Node<'a, T> {
    car: T,
    cdr: Option<&'a Node<'a, T>>
  }

  let mut arena = Arena::new();
  let mut arena_ref = &mut arena;
  let mut head: Option<&Node<'_, u64>> = None;
  for i in 0 .. 10 {
    head = Some(arena_ref.alloc().init(Node { car: i as u64, cdr: head }));
  }
  let mut sum = 0;
  while let Some(node) = head {
    sum += node.car;
    head = node.cdr;
  }
  assert!(sum == 45);
}

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
