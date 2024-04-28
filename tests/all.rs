#![cfg_attr(feature = "allocator_api", feature(allocator_api))]

use std::alloc::Layout;
use std::mem::size_of;
use allocator_api2::vec::Vec;
use expect_test::expect;
use oxcart::Arena;
use oxcart::ArenaAllocator;
use oxcart::Slot;
use oxcart::Store;

#[test]
fn test_api() {
  let mut store = Store::new();
  let _ = Store::try_new();
  let _ = Store::with_capacity(0);
  let _ = Store::try_with_capacity(0);
  let _ = format!("{:?}", store);
  let mut arena = store.arena();
  let _ = arena.alloc::<u64>();
  let _ = arena.try_alloc::<u64>();
  let _ = arena.alloc_slice::<u64>(3);
  let _ = arena.try_alloc_slice::<u64>(3);
  let _ = arena.copy_slice::<u64>(&[0, 1, 2]);
  let _ = arena.try_copy_slice::<u64>(&[0, 1, 2]);
  let _ = arena.copy_str("hello");
  let _ = arena.try_copy_str("hello");
  let _ = arena.alloc_layout(Layout::new::<u64>());
  let _ = arena.try_alloc_layout(Layout::new::<u64>());
  let _ = arena.alloc::<u64>().as_uninit();
  let _ = arena.alloc::<u64>().init(13);
  let _ = arena.alloc::<[u64; 3]>().as_uninit_array();
  let _ = arena.alloc::<[u64; 3]>().init_array(|i| i as u64);
  let _ = arena.alloc_slice::<u64>(3).as_uninit_slice();
  let _ = arena.alloc_slice::<u64>(3).init_slice(|i| i as u64);
  let _ = format!("{:?}", arena);
  let _ = format!("{:?}", arena.alloc::<u64>());
  let _ = arena.as_allocator();
}

#[test]
fn test_special_traits() {
  fn is_ref_unwind_safe<T: std::panic::RefUnwindSafe>() {}
  fn is_send<T: Send>() {}
  fn is_sync<T: Sync>() {}
  fn is_unwind_safe<T: std::panic::UnwindSafe>() {}

  is_ref_unwind_safe::<Store>();
  is_send::<Store>();
  is_sync::<Store>();
  is_unwind_safe::<Store>();

  is_ref_unwind_safe::<Arena<'static>>();
  is_send::<Arena<'static>>();
  is_sync::<Arena<'static>>();
  is_unwind_safe::<Arena<'static>>();

  is_send::<Slot<'static, u64>>();
  is_sync::<Slot<'static, u64>>();
  is_unwind_safe::<Slot<'static, u64>>();
  is_ref_unwind_safe::<Slot<'static, u64>>();

  is_ref_unwind_safe::<ArenaAllocator<'static>>();
  is_send::<ArenaAllocator<'static>>();
  is_unwind_safe::<ArenaAllocator<'static>>();
}

#[test]
fn test_alloc_small() {
  let mut store = Store::new();
  let mut arena = store.arena();
  let a = arena.alloc().init(1_u8);
  let b = arena.alloc().init(1_u16);
  let c = arena.alloc().init(1_u32);
  let d = arena.alloc().init(1_u64);
  let e = arena.alloc().init(1_u128);
  let f = arena.alloc().init(1_f32);
  let g = arena.alloc().init(1_f64);
  let h = arena.alloc().init(());
  let i = arena.alloc().init(true);
  let j = arena.alloc().init((1_u8, 1_u128));
  let k = arena.alloc().init([1_u8; 0]);
  let l = arena.alloc().init([1_u8; 1]);
  let m = arena.alloc().init([1_u8; 3]);
  let n = arena.alloc().init([1_u8; 5]);
  let o = arena.alloc().init([1_u8; 7]);
  let p = arena.alloc().init([1_u8; 9]);
  *a = 0_u8;
  *b = 0_u16;
  *c = 0_u32;
  *d = 0_u64;
  *e = 0_u128;
  *f = 0_f32;
  *g = 0_f64;
  *h = ();
  *i = false;
  *j = (0_u8, 0_u128);
  *k = [0_u8; 0];
  *l = [0_u8; 1];
  *m = [0_u8; 3];
  *n = [0_u8; 5];
  *o = [0_u8; 7];
  *p = [0_u8; 9];
}

#[test]
fn test_alloc_zero_sized() {
  let mut store = Store::new();
  let mut arena = store.arena();
  let _ = arena.alloc_layout(Layout::new::<()>());
  let _ = arena.alloc().init(());
  let _ = arena.alloc().init([1_u64; 0]);
  let _ = arena.alloc_slice(0).init_slice(|_| 0_u64);
  let _ = arena.alloc_slice(5).init_slice(|_| ());
}

#[test]
fn test_too_large_allocation() {
  let too_large_nbytes = isize::MAX as usize - 1;
  let too_large_layout = Layout::from_size_align(too_large_nbytes, 1).unwrap();
  let too_large_nwords = too_large_nbytes / size_of::<usize>();
  let mut store = Store::new();
  let mut arena = store.arena();
  assert!(arena.try_alloc_layout(too_large_layout).is_err());
  assert!(arena.try_alloc_slice::<usize>(too_large_nwords).is_err());
}

#[test]
fn test_growth() {
  let mut store = Store::with_capacity(0);
  let mut arena = store.arena();
  let _ = arena.alloc().init(1_u8);
  let _ = arena.alloc().init(1_u16);
  let _ = arena.alloc().init(1_u32);
  let _ = arena.alloc().init(1_u64);
  let _ = arena.alloc().init(1_u128);
  let _ = arena.alloc().init(1_f32);
  let _ = arena.alloc().init(1_f64);
  let _ = arena.alloc().init(());
  let _ = arena.alloc().init(true);
  let _ = arena.alloc().init((1_u8, 1_u128));
  let _ = arena.alloc().init([1_u8; 0]);
  let _ = arena.alloc().init([1_u8; 1]);
  let _ = arena.alloc().init([1_u8; 3]);
  let _ = arena.alloc().init([1_u8; 5]);
  let _ = arena.alloc().init([1_u8; 7]);
  let _ = arena.alloc().init([1_u8; 9]);
}

#[test]
fn test_allocator_api() {
  let mut store = Store::new();
  let allocator = store.arena().as_allocator();
  let mut x = Vec::new_in(&allocator);
  let mut y = Vec::new_in(&allocator);
  x.push(0);
  y.push(0);
  x.push(1);
  y.push(1);
}

/*
#[test]
fn test_alloc_aligned() {
  let mut store = Store::new();
  let mut arena = store.arena();
  for &align in &[1, 2, 4, 8, 16, 32, 64] {
    let p = arena.alloc_layout(Layout::from_size_align(1, align).unwrap());
    assert!(ptr::from(p).addr() & (align - 1) == 0);
  }
}
*/

/*
#[test]
fn test_format() {
  let mut store = Store::new();
  expect!["Store { total_allocated: 16384 }"].assert_eq(&format!("{:?}", store));
  let mut arena = store.arena();
  expect!["Allocator(0x000000015b808200, 16344)"].assert_eq(&format!("{:?}", arena));
  let a = arena.alloc::<u64>();
  expect!["Slot(0x000000015b808200)"].assert_eq(&format!("{:?}", a));
  let b = arena.alloc::<u64>();
  expect!["Slot(0x000000015b808208)"].assert_eq(&format!("{:?}", b));
}
*/

#[test]
fn test_linked_list() {
  struct Node<'a, T> {
    car: T,
    cdr: Option<&'a Node<'a, T>>
  }

  let mut store = Store::with_capacity(50);

  for _ in 0 .. 3 {
    let mut arena = store.arena();
    let mut x: Option<&Node<'_, u64>> = None;
    for i in 0 .. 100 {
      x = Some(arena.alloc().init(Node { car: i, cdr: x }));
    }
    let mut y = 0;
    while let Some(z) = x {
      y = y + z.car;
      x = z.cdr;
    }
    expect!["4950"].assert_eq(&format!("{:?}", y));
  }
}

#[test]
fn test_demo() {
  let mut store = Store::new();
  let mut arena = store.arena();

  let x = arena.alloc().init(0);
  let y = arena.alloc().init(0);
  let z = arena.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  expect!["6"].assert_eq(&format!("{:?}", *x + *y + *z));

  let mut arena = store.arena();

  let _ = arena.alloc::<[u64; 100_000]>();
  let _ = arena.alloc::<[u64; 0]>();
  let _ = arena.alloc::<[u64; 1]>();

  let mut arena = store.arena();

  let x = arena.alloc_slice(3).init_slice(|i| (i as u64) + 1);
  let y = arena.alloc_layout(Layout::new::<[u64; 10]>());
  let z: &mut dyn std::fmt::Debug = arena.alloc().init(13u64);

  expect!["6"].assert_eq(&format!("{:?}", x[0] + x[1] + x[2]));
  expect!["80"].assert_eq(&format!("{:?}", y.len()));
  expect!["13"].assert_eq(&format!("{:?}", z));
}
