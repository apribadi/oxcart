# oxcart

A high performance arena allocator.

## Example

```
let mut store = oxcart::Store::new();
let mut arena = store.arena();

let a: &mut u16 = arena.alloc().init(1);
let b: &mut u32 = arena.alloc().init(1);
let c: &mut u64 = arena.alloc().init(1);

assert!(*a == 1);
assert!(*b == 1);
assert!(*c == 1);

let mut arena = store.arena();

let a: &mut [u64; 5] = arena.alloc().init_array(|i| i as u64);
let b: &mut [u64] = arena.alloc_slice(5).init_slice(|i| i as u64);
let c: &mut str = arena.copy_str("Hello!");
let d: &mut dyn std::fmt::Debug = arena.alloc().init(1_u64);

assert!(a == &[0, 1, 2, 3, 4]);
assert!(b == &[0, 1, 2, 3, 4]);
assert!(c == "Hello!");
assert!(format!("{:?}", d) == "1");
```
