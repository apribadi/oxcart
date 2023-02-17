# oxcart

A fast arena allocator - supports efficiently allocating a large number of
objects and then deallocating all of them at once.

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

## The Allocation Fast Path

Below is aarch64 assembly from the inner loop of a function that allocates a
singly linked list.

```text
LBB33_2:
	add x9, x8, #16                     // update low pointer
	str x9, [x19]                       // 
	stp x20, x21, [x8]                  // write to slot
	sub x20, x20, #1                    // decrement loop index
	mov x21, x8                         //
	cmn x20, #1                         // check loop termination
	b.eq LBB33_6                        //
LBB33_3:
	add x8, x9, #7                      // align up
	and x8, x8, #0xfffffffffffffff8     //
	sub x9, x0, x8                      // remaining space, signed
	cmp x9, #15                         // compare size with space
	b.gt LBB33_2                        // branch if enough space
	bl oxcart::alloc_chunk_for          // call slow path
	mov x8, x0                          //
	mov x0, x1                          //
	str x1, [x19, #8]                   // store upper bound
	b LBB33_2                           //
```

```text
LBB35_2:
	mov x0, x19
	mov w1, #16
	mov w2, #8
	bl bumpalo::Bump::alloc_layout_slow
	cbz x0, LBB35_9
	stp x20, x21, [x0]
	sub x20, x20, #1
	mov x21, x0
	cmn x20, #1
	b.eq LBB35_8
LBB35_4:
	ldr x8, [x19, #16]
	ldr x9, [x8, #32]
	subs x9, x9, #16
	b.lo LBB35_2
	ldr x10, [x8]
	and x0, x9, #0xfffffffffffffff8
	cmp x0, x10
	b.lo LBB35_2
	str x0, [x8, #32]
	stp x20, x21, [x0]
	sub x20, x20, #1
	mov x21, x0
	cmn x20, #1
	b.ne LBB35_4
	b LBB35_8
```

## License

Artistic License 2.0
