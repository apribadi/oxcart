# oxcart

A fast arena allocator - efficiently allocate a large number of objects and
then deallocate all of them at once.

## Example

```rust
let mut arena = oxcart::Arena::new();
let allocator = arena.allocator();

let x: &mut u64 = allocator.alloc().init(13);
let y: &mut [u64] = allocator.alloc_slice(5).init_slice(|i| i as u64);

assert!(*x == 13);
assert!(y == &[0, 1, 2, 3, 4]);

arena.reset();
```

## Features

- fast
- allocates objects of multiple types
- allocates slices, strings, and arbitrary layouts
- supports `reset`-ing and reusing an arena
- separates allocation from initialization to avoid stack spills
- sound
- compatible with strict provenance
- zero-dependency

## Non-Features

- no allocation through an immutable reference
- no nested stack of regions
- no `drop` calls for objects upon arena `reset` or `drop`
- no `allocator_api` integration

## License
 
Artistic License 2.0
