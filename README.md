# oxcart

a fast arena allocator

## Example

```rust
let mut arena = oxcart::Arena::new();
let allocator = arena.allocator();

let x: &mut u64 = allocator.alloc().init(13);
let y: &mut [u64] = allocator.alloc_slice(5).init(|i| i as u64);

assert!(*x == 13);
assert!(y == &[0, 1, 2, 3, 4]);

arena.reset();
```

## Features

- fast
- allocates single objects, slices, or arbitrary layouts
- sound
- compatible with strict provenance

## Non-Features

- no `drop` calls on deallocation
- no `allocator_api` integration

## License
 
Artistic License 2.0
