//! tests for oxcart

use std::alloc::Layout;
use oxcart::Arena;
use oxcart::Slot;
use oxcart::Store;
use expect_test::expect;

fn is_panic<F: FnOnce()>(f: F) -> bool {
  std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).is_err()
}

#[test]
fn test_api() {
  let mut store = Store::new();
  let _ = Store::with_capacity(0);
  let _ = format!("{:?}", store);
  let mut arena = store.arena();
  let x = arena.alloc::<u64>();
  let y = arena.alloc_slice::<u64>(3);
  let _ = arena.copy_slice::<u64>(&[0, 1, 2]);
  let _ = arena.copy_str("hello");
  let _ = arena.alloc_layout(Layout::new::<u64>());
  let _ = arena.alloc::<u64>().as_uninit();
  let _ = arena.alloc::<u64>().init(13);
  let _ = arena.alloc::<[u64; 3]>().as_uninit_array();
  let _ = arena.alloc::<[u64; 3]>().init_array(|i| i as u64);
  let _ = arena.alloc_slice::<u64>(3).as_uninit_slice();
  let _ = arena.alloc_slice::<u64>(3).init_slice(|i| i as u64);
  let _ = format!("{:?}", arena);
  let _ = format!("{:?}", arena.alloc::<u64>());

  expect!["Arena(65328)"].assert_eq(&format!("{:?}", arena)); // NB: arch dependent
  expect!["Slot"].assert_eq(&format!("{:?}", x));
  expect!["Slot(3)"].assert_eq(&format!("{:?}", y));
  expect!["Store([65536])"].assert_eq(&format!("{:?}", store));
}

#[test]
fn test_special_traits() {
  fn is_ref_unwind_safe<T: std::panic::RefUnwindSafe>() { }
  fn is_send<T: Send>() { }
  fn is_sync<T: Sync>() { }
  fn is_unpin<T: Unpin>() { }
  fn is_unwind_safe<T: std::panic::UnwindSafe>() { }

  is_ref_unwind_safe::<Store>();
  is_send::<Store>();
  is_sync::<Store>();
  is_unpin::<Store>();
  is_unwind_safe::<Store>();

  is_ref_unwind_safe::<Arena<'static>>();
  is_send::<Arena<'static>>();
  is_sync::<Arena<'static>>();
  is_unpin::<Arena<'static>>();
  is_unwind_safe::<Arena<'static>>();

  is_ref_unwind_safe::<Slot<'static, *mut std::cell::UnsafeCell<u64>>>();
  is_send::<Slot<'static, *mut std::cell::UnsafeCell<u64>>>();
  is_sync::<Slot<'static, *mut std::cell::UnsafeCell<u64>>>();
  is_unpin::<Slot<'static, *mut std::cell::UnsafeCell<u64>>>();
  is_unwind_safe::<Slot<'static, *mut std::cell::UnsafeCell<u64>>>();
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
  let too_large_nbytes = isize::MAX as usize;
  let too_large_layout = Layout::from_size_align(too_large_nbytes, 1).unwrap();
  let too_large_nwords = too_large_nbytes / size_of::<usize>();
  let mut store = Store::new();
  let mut arena = store.arena();

  assert!(is_panic(|| { let _: _ = arena.alloc_layout(too_large_layout); }));
  assert!(is_panic(|| { let _: _ = arena.alloc_slice::<usize>(too_large_nwords); }));
}

#[test]
fn test_growth() {
  let mut store = Store::with_capacity(64);
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
  let _ = arena.alloc().init([1_u8; 1000]);

  expect!["Arena(8)"].assert_eq(&format!("{:?}", arena));
  expect!["Store([64, 64, 128, 1024])"].assert_eq(&format!("{:?}", store));

  let arena = store.arena();

  expect!["Arena(2032)"].assert_eq(&format!("{:?}", arena));
  expect!["Store([2048])"].assert_eq(&format!("{:?}", store));
}

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
  let y: &mut dyn std::fmt::Debug = arena.alloc().init(13u64);

  expect!["6"].assert_eq(&format!("{:?}", x[0] + x[1] + x[2]));
  expect!["13"].assert_eq(&format!("{:?}", y));
}
