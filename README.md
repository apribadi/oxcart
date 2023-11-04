# oxcart

A fast arena allocator - supports efficiently allocating a large number of
objects and then deallocating all of them at once.

## Example

```rust
use oxcart::Arena;
use oxcart::ArenaRef;

let mut arena = Arena::new();
let mut arena_ref = &mut arena;

let x: &mut u64 = arena_ref.alloc().init(13);
let y: &mut [u64] = arena_ref.alloc_slice(5).init_slice(|i| i as u64);

assert!(*x == 13);
assert!(y == &[0, 1, 2, 3, 4]);

arena.reset();
```

## Features

- speed
- allocation of multiple types in a single arena
- allocation of slices, strings, and arbitrary layouts
- allocation separated from initialization to avoid stack spills
- reuse of memory after `reset`-ing an arena
- soundness
- compatibility with strict provenance
- zero dependencies

## Non-Features

- no `drop` calls for objects upon arena `reset` or `drop`
- no nested stack of regions
- no support for custom DSTs

## The Allocation Fast Path

Below is aarch64 assembly taken from the inner loop of a function that
allocates a singly linked list.

```text
LBB33_2:
	add x9, x8, #16                     // increment lower bound
	str x9, [x19]                       // store lower bound
	stp x20, x21, [x8]                  // initialize list node
	sub x20, x20, #1                    // decrement loop index
	mov x21, x8                         //
	cmn x20, #1                         // check loop termination
	b.eq LBB33_6                        // check loop termination
LBB33_3:
	add x8, x9, #7                      // align up
	and x8, x8, #0xfffffffffffffff8     // align up
	sub x9, x0, x8                      // compute remaining space
	cmp x9, #15                         // check if sufficient space
	b.gt LBB33_2                        // check if sufficient space
	bl oxcart::alloc_chunk_for          // call slow path
	mov x8, x0                          //
	mov x0, x1                          //
	str x1, [x19, #8]                   // store upper bound
	b LBB33_2                           //
```

In this particular example, the compiler was able to see that the reference to
the allocator state is not aliased. As result it did a store-to-load-forwarding
optimization and hoisted the load of the allocator state out of the loop (this
optimization is a little delicate and does not always occur).

Because the allocator has been passed by reference, the compiler isn't able to
do a scalar-replacement-of-aggregates optimization and therefore needs to
retain the stores that update the allocator state.

After aligning the pointer to the lower bound up, the capacity of the arena
might be negative. In fact, the capacity is in the range `isize::MIN ..=
isize::MAX` and the allocation size is in the range `0 ..= isize::MAX`, so we
can simply do a single signed comparison to determine whether the requested
allocation fits inside the current chunk.

## License

Artistic License 2.0
