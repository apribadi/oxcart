use crate::prelude::*;

const FOOTER_SIZE: usize = size_of::<Footer>();
const FOOTER_ALIGN: usize = align_of::<Footer>();
const MIN_CHUNK_SIZE: usize = 1 << 16; // 64kb
const MIN_CHUNK_ALIGN: usize = FOOTER_ALIGN;

pub(crate) struct Arena {
  lo: *mut u8,
  hi: *mut Footer,
}

// SAFETY:
//
// The `Arena` type conforms to the usual shared xor mutable discipline,
// despite containing pointers.

unsafe impl Send for Arena {}

unsafe impl Sync for Arena {}

struct Footer {
  layout: Layout,
  next: Option<NonNull<Footer>>,
  total_allocated: usize,
}

pub(crate) trait Error {
  fn global_alloc_error(_: Layout) -> Self;
  fn layout_overflow() -> Self;
}

unsafe fn dealloc_chunk_list(p: NonNull<Footer>) {
  // SAFETY:
  //
  // `p` must be the head of a valid linked list of chunks.

  // STACK SPACE:
  //
  // Chunk sizes grow exponentially, so stack usage is O(log(word size)) at
  // worst even without TCO.

  let p = p.as_ptr();
  let t = unsafe { p.read() };
  let p = p as *mut u8;
  let p = p.wrapping_add(FOOTER_SIZE);
  let p = p.wrapping_sub(t.layout.size());

  unsafe { alloc::alloc::dealloc(p, t.layout) }

  if let Some(p) = t.next {
    unsafe { dealloc_chunk_list(p) }
  }
}

#[inline(never)]
#[cold]
unsafe fn alloc_chunk_for<E: Error>
  (
    object: Layout,
    chunks: *mut Footer
  )
  -> Result<(*mut u8, *mut Footer), E>
{
  // SAFETY:
  //
  // ???

  // POSTCONDITIONS:
  //
  // ???

  const _: () = assert!(MIN_CHUNK_SIZE % MIN_CHUNK_ALIGN == 0);
  const _: () = assert!(MIN_CHUNK_SIZE <= isize::MAX as usize);
  const _: () = assert!(FOOTER_SIZE <= MIN_CHUNK_SIZE);
  const _: () = assert!(FOOTER_ALIGN <= MIN_CHUNK_ALIGN);

  let chunks = NonNull::new(chunks);

  let total_allocated =
    match chunks {
      None => 0,
      Some(chunks) => unsafe { chunks.as_ref() }.total_allocated
    };

  let object_size = object.size();
  let object_align = object.align();

  // The chunk size we'd like to allocate, if the object will fit in it.  It
  // is always a power of two `<= 0b0100...`.

  let size_0 = total_allocated / 4 + 1;
  let size_0 = 1 << (usize::BITS - (size_0 - 1).leading_zeros());
  let size_0 = max(size_0, MIN_CHUNK_SIZE);

  // The size of any `Layout` is guaranteed to be `<= isize::MAX`. It follows
  // that `size_1` does not overflow `usize`.

  let size_1 = object_size.wrapping_add(FOOTER_ALIGN - 1) & ! (FOOTER_ALIGN - 1);
  let size_1 = size_1 + FOOTER_SIZE;

  let size = max(size_0, size_1);
  let align = max(object_align, MIN_CHUNK_ALIGN);

  // We can construct a valid `Layout` if and only if `size` rounded up to
  // `align` does not overflow and is `<= isize::MAX`.
  //
  // Note that a very large `object_size` is necessary for this to occur; the
  // exponential chunk growth alone will not cause this to overflow.

  if size > isize::MAX as usize - (align - 1) {
    return Err(E::layout_overflow());
  }

  // SAFETY:
  //
  // - `align != 0`
  // - `align` is a power of two
  // - `size` rounded up to a multiple of `align` is `<= isize::MAX`

  let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

  // SAFETY:
  //
  // - `size != 0`

  let lo = unsafe { alloc::alloc::alloc(layout) };

  if lo.is_null() {
    return Err(E::global_alloc_error(layout));
  }

  // We have made sure that the chunk is aligned to at least
  // `align_of::<Footer>()` and that its size is a multiple of
  // `align_of::<Footer>(), so we can place the tail at the very end of the
  // chunk.

  let hi = lo.wrapping_add(size).wrapping_sub(FOOTER_SIZE) as *mut Footer;

  let total_allocated = total_allocated.saturating_add(size);

  // SAFETY:
  //
  // - `hi` is valid and aligned for writing a `Footer`.

  unsafe { hi.write(Footer { layout, next: chunks, total_allocated }) };

  Ok((lo, hi))
}

impl Arena {
  #[inline(always)]
  pub(crate) fn new() -> Self {
    // NB:
    //
    // - `lo > hi` so there is no space for ZSTs.
    // - `hi - align_up(lo, MAX_ALIGN) == isize::MIN`.

    Self {
      lo: invalid_mut(1),
      hi: invalid_mut(0),
    }
  }

  pub(crate) fn reset(&mut self) {
    let hi = self.hi;

    if ! hi.is_null() {
      let f = unsafe { &mut *hi };

      self.lo = (hi as *mut u8).wrapping_add(FOOTER_SIZE).wrapping_sub(f.layout.size());

      if let Some(next) = f.next {
        f.next = None;
        unsafe { dealloc_chunk_list(next) }
      }
    }
  }

  #[inline(always)]
  pub(crate) fn alloc<E: Error>(&mut self, layout: Layout) -> Result<NonNull<u8>, E> {
    let size = layout.size();
    let align = layout.align();

    let lo = mask(self.lo.wrapping_add(align - 1), ! (align - 1));

    if size as isize > addr(self.hi).wrapping_sub(addr(lo)) as isize {
      let (lo, hi) = unsafe { alloc_chunk_for::<E>(layout, self.hi) }?;
      self.lo = lo;
      self.hi = hi;
    } else {
      self.lo = lo;
    }

    let p = unsafe { NonNull::new_unchecked(self.lo) };

    self.lo = self.lo.wrapping_add(size);

    Ok(p)
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    if let Some(p) = NonNull::new(self.hi) {
      unsafe { dealloc_chunk_list(p) }
    }
  }
}
