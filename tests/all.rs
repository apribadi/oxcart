#![cfg_attr(feature = "allocator_api", feature(allocator_api))]

use expect_test::expect;
use core::alloc::Layout;
use core::fmt;
use core::mem::size_of;
use oxcart::Allocator;
use oxcart::Arena;
use oxcart::Slot;

#[inline(always)]
fn addr<T: ?Sized>(p: *const T) -> usize {
  let p = p as *const();
  unsafe { core::mem::transmute(p) }
}

#[test]
fn test_api() {
  let mut arena = Arena::new();
  let _ = arena.allocator_mut();
  arena.reset();
  let allocator = arena.allocator_mut();
  let _ = allocator.alloc::<u64>();
  let _ = allocator.try_alloc::<u64>();
  let _ = allocator.alloc_slice::<u64>(5);
  let _ = allocator.try_alloc_slice::<u64>(5);
  let _ = allocator.alloc_layout(Layout::new::<u64>());
  let _ = allocator.try_alloc_layout(Layout::new::<u64>());
  let _ = allocator.copy_slice::<u64>(&[0, 1, 2, 3, 4]);
  let _ = allocator.try_copy_slice::<u64>(&[0, 1, 2, 3, 4]);
  let _ = allocator.copy_str("hello");
  let _ = allocator.try_copy_str("hello");
  let _ = allocator.alloc::<u64>().as_non_null();
  let _ = allocator.alloc::<u64>().as_ptr();
  let _ = allocator.alloc::<u64>().as_uninit();
  let _ = allocator.alloc::<u64>().init(13);
  let _ = allocator.alloc::<[u64; 5]>().as_uninit_array();
  let _ = allocator.alloc::<[u64; 5]>().init_array(|i| i as u64);
  let _ = allocator.alloc_slice::<u64>(5).len();
  let _ = allocator.alloc_slice::<u64>(5).as_uninit_slice();
  let _ = allocator.alloc_slice::<u64>(5).init_slice(|i| i as u64);
  let _ = Arena::default();
  let _ = format!("{:?}", Arena::new());
  let _ = format!("{:?}", Arena::new().allocator_mut());
  let _ = format!("{:?}", Arena::new().allocator_mut().alloc::<u64>());
}

#[test]
#[cfg(feature = "allocator_api")]
fn test_allocator_api() {
  let mut arena = Arena::new();
  let allocator = arena.allocator_ref();
  let mut x = Box::new_in(0u64, allocator);
  let mut y = Vec::new_in(allocator);
  *x += 13;
  y.extend([0, 1, 2, 3, 4]);
  assert!(*x == 13);
  assert!(y == &[0, 1, 2, 3, 4]);
}

#[test]
fn test_debug() {
  expect!["Arena { lo: 0x1, hi: 0x0 }"].assert_eq(&format!("{:?}", Arena::new()));
  expect!["Allocator { lo: 0x1, hi: 0x0 }"].assert_eq(&format!("{:?}", Arena::new().allocator_mut()));
}

#[test]
fn test_too_big_allocation() {
  let too_big_nbytes = (isize::MAX as usize + 1) - (3 * size_of::<usize>());
  let too_big_nwords = too_big_nbytes / size_of::<usize>();
  let too_big_layout = Layout::from_size_align(too_big_nbytes, 1).unwrap();
  let mut arena = Arena::new();
  let allocator = arena.allocator_mut();
  assert!(allocator.try_alloc_slice::<usize>(too_big_nwords).is_err());
  assert!(allocator.try_alloc_layout(too_big_layout).is_err());
}

#[test]
fn test_zero_size_allocation() {
  let mut arena = Arena::new();
  let allocator = arena.allocator_mut();
  let a = allocator.alloc().init(());
  let b = allocator.alloc_slice(0).init_slice(|_| 0u64);
  let c = allocator.alloc_slice(5).init_slice(|_| ());
  let d = allocator.alloc_layout(Layout::new::<()>());
  assert!(*a == ());
  assert!(b.len() == 0);
  assert!(c.len() == 5);
  assert!(d.len() == 0);
}

#[test]
fn test_alignment() {
  let mut arena = Arena::new();
  let allocator = arena.allocator_mut();
  for align in [1, 2, 4, 8, 16, 32, 64] {
    let layout = Layout::from_size_align(1, align).unwrap();
    let p = allocator.alloc_layout(layout).as_ptr();
    assert!(addr(p) & (align - 1) == 0);
  }
}

#[test]
fn test_multiple_allocators_without_reset() {
  let mut arena = Arena::new();
  let allocator = arena.allocator_mut();
  let _ = allocator.alloc().init(1);
  let allocator = arena.allocator_mut();
  let _ = allocator.alloc().init(2);
  let allocator = arena.allocator_mut();
  let _ = allocator.alloc().init(3);
}

#[test]
fn test_types_are_send_and_sync() {
  fn is_send<T: Send>(_ : &T) {}
  fn is_sync<T: Sync>(_ : &T) {}
  let mut arena = Arena::new();
  is_send::<Arena>(&arena);
  let allocator = arena.allocator_mut();
  is_send::<Allocator>(allocator);
  let x = allocator.alloc::<u64>();
  let y = allocator.alloc_slice::<u64>(5);
  is_send::<Slot<_>>(&x);
  is_sync::<Slot<_>>(&x);
  is_send::<Slot<_>>(&y);
  is_sync::<Slot<_>>(&y);
}

#[test]
fn test_linked_list() {
  struct Node<'a, T> {
    car: T,
    cdr: Option<&'a Node<'a, T>>
  }

  let mut arena = Arena::new();
  let allocator = arena.allocator_mut();
  let mut head: Option<&Node<u64>> = None;
  for i in 0 .. 10 {
    head = Some(allocator.alloc().init(Node { car: i as u64, cdr: head }));
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

  let allocator = arena.allocator_mut();

  let x = allocator.alloc().init(0);
  let y = allocator.alloc().init(0);
  let z = allocator.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);

  arena.reset();

  let allocator = arena.allocator_mut();

  let _ = allocator.alloc::<[u64; 100000]>();
  let _ = allocator.alloc::<[u64; 0]>();
  let _ = allocator.alloc::<[u64; 1]>();

  arena.reset();

  let allocator = arena.allocator_mut();

  let x = allocator.alloc_slice(3).init_slice(|i| (i as u64) + 1);
  let y = allocator.alloc_layout(Layout::new::<[u64; 10]>());
  let z: &mut dyn fmt::Debug = allocator.alloc().init(13u64);

  assert!(x[0] + x[1] + x[2] == 6);
  assert!(y.len() == 80);
  assert!(&format!("{z:?}") == "13");

  arena.reset();
}
