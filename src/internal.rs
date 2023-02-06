use crate::prelude::*;

const FOOTER_SIZE: usize = size_of::<Footer>();
const FOOTER_ALIGN: usize = align_of::<Footer>();
const MIN_CHUNK_SIZE: usize = 1 << 16; // 64kb
const MIN_CHUNK_ALIGN: usize = FOOTER_ALIGN;

pub(crate) struct Arena {
  lo: *mut u8,
  hi: *mut Footer,
}

struct Footer {
  layout: Layout,
  next: *mut Footer,
  total_allocated: usize,
}

pub(crate) enum Error {
  GlobalAllocError(Layout),
  LayoutOverflow,
  SliceTooLong(usize),
  TypeNeedsDrop,
}

pub(crate) trait FromError {
  fn from_error(_: Error) -> Self;
}

trait AlignUp {
  fn align_up(self, align: usize) -> Self;
}

impl AlignUp for usize {
  #[inline(always)]
  fn align_up(self, align: usize) -> Self {
    self.wrapping_add(align - 1) & ! (align - 1)
  }
}

impl AlignUp for *mut u8 {
  #[inline(always)]
  fn align_up(self, align: usize) -> Self {
    mask(self.wrapping_add(align - 1), ! (align - 1))
  }
}

unsafe fn dealloc_chunk_list(p: NonNull<Footer>) {
  // SAFETY:
  //
  // - `p` must be the head of a valid linked list of chunks.

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

  if let Some(p) = NonNull::new(t.next) {
    unsafe { dealloc_chunk_list(p) }
  }
}

#[inline(never)]
#[cold]
unsafe fn alloc_chunk_for<E: FromError>
  (
    object: Layout,
    chunks: *mut Footer
  )
  -> Result<(*mut u8, *mut Footer), E>
{
  // SAFETY:
  //
  // -

  // POSTCONDITIONS:
  //
  // -

  const _: () = assert!(MIN_CHUNK_SIZE % MIN_CHUNK_ALIGN == 0);
  const _: () = assert!(MIN_CHUNK_SIZE <= isize::MAX as usize);
  const _: () = assert!(FOOTER_SIZE <= MIN_CHUNK_SIZE);
  const _: () = assert!(FOOTER_ALIGN <= MIN_CHUNK_ALIGN);

  let total_allocated =
    if chunks.is_null() {
      0
    } else {
      unsafe { &*chunks }.total_allocated
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

  let size_1 = object_size.align_up(FOOTER_ALIGN) + FOOTER_SIZE;

  let size = max(size_0, size_1);
  let align = max(object_align, MIN_CHUNK_ALIGN);

  // We can construct a valid `Layout` if and only if `size` rounded up to
  // `align` does not overflow and is `<= isize::MAX`.
  //
  // Note that a very large `object_size` is necessary for this to occur; the
  // exponential chunk growth alone will not cause this to overflow.

  if size > isize::MAX as usize - (align - 1) {
    return Err(E::from_error(Error::LayoutOverflow));
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
    return Err(E::from_error(Error::GlobalAllocError(layout)));
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

  #[inline(always)]
  pub(crate) fn reset(&mut self) {
    let hi = self.hi;

    if ! hi.is_null() {
      let f = unsafe { &mut *hi };

      self.lo = (hi as *mut u8).wrapping_add(FOOTER_SIZE).wrapping_sub(f.layout.size());

      if let Some(next) = NonNull::new(f.next) {
        f.next = invalid_mut(0);
        unsafe { dealloc_chunk_list(next) }
      }
    }
  }

  #[inline(always)]
  pub(crate) fn alloc<E: FromError>(&mut self, layout: Layout) -> Result<NonNull<u8>, E> {
    let size = layout.size();
    let align = layout.align();

    let lo = self.lo.align_up(align);

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
