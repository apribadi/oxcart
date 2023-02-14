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

- speed
- allocation of objects with multiple types
- allocation of slices, strings, and arbitrary layouts
- allocation separated from initialization to avoid stack spills
- reuse of memory after `reset`-ing an arena
- soundness
- compatibility with strict provenance
- zero dependencies

## Non-Features

- no allocation through an immutable reference
- no `drop` calls for objects upon arena `reset` or `drop`
- no `allocator_api` integration
- no nested stack of regions
- no support for custom DSTs

## License
 
Artistic License 2.0
