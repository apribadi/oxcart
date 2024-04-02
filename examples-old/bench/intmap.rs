use core::mem::MaybeUninit;

#[derive(Debug)]
pub enum IntMap<'a, T> {
  Empty,
  NonEmpty(NonEmpty<'a, T>),
}

#[derive(Debug)]
pub enum NonEmpty<'a, T> {
  Leaf(&'a Leaf<T>),
  Branch(&'a Branch<'a, T>),
}

#[derive(Debug)]
pub struct Leaf<T>(u64, T);

#[derive(Debug)]
pub struct Branch<'a, T>(u64, u64, NonEmpty<'a, T>, NonEmpty<'a, T>);

impl<'a, T> Clone for NonEmpty<'a, T> { fn clone(&self) -> Self { *self } }

impl<'a, T> Copy for NonEmpty<'a, T> {}

pub fn new<'a, T>() -> IntMap<'a, T> {
  IntMap::Empty
}

#[inline(always)]
fn zero_bit(k: u64, m: u64) -> bool {
  k & m == 0
}

#[inline(always)]
fn mask(k: u64, m: u64) -> u64 {
  k & (m - 1)
}

#[inline(always)]
fn match_prefix(k: u64, p: u64, m: u64) -> bool {
  mask(k, m) == p
}

#[inline(always)]
fn lowest_bit(x: u64) -> u64 {
  x & x.wrapping_neg()
}

#[inline(always)]
fn branching_bit(p0: u64, p1: u64) -> u64 {
  lowest_bit(p0 ^ p1)
}

pub mod with_oxcart {
  use super::*;

  #[inline(always)]
  fn join<'a, T>
    (
      ox: &mut oxcart::Allocator<'a>,
      p0: u64,
      t0: NonEmpty<'a, T>,
      p1: u64,
      t1: NonEmpty<'a, T>,
    ) -> NonEmpty<'a, T>
  {
    let m = branching_bit(p0, p1);
    if zero_bit(p0, m) {
      NonEmpty::Branch(ox.alloc().init(Branch(mask(p0, m), m, t0, t1)))
    } else {
      NonEmpty::Branch(ox.alloc().init(Branch(mask(p0, m), m, t1, t0)))
    }
  }

  fn insert_nonempty2<'a, T>
    (
      ox: &mut oxcart::Allocator<'a>,
      k: u64,
      x: T,
      t: NonEmpty<'a, T>
    ) -> NonEmpty<'a, T>
  {
    let mut t = t;
    let mut i = 0;
    let mut stack: [MaybeUninit<(bool, u64, u64, NonEmpty<'a, T>)>; 64] = [ MaybeUninit::uninit(); 64];
    let mut s =
      loop {
        match t {
          NonEmpty::Leaf(&Leaf(j, _)) => {
            if j == k {
              break NonEmpty::Leaf(ox.alloc().init(Leaf(k, x)));
            } else {
              let u = NonEmpty::Leaf(ox.alloc().init(Leaf(k, x)));
              break join(ox, k, u, j, t);
            }
          }
          NonEmpty::Branch(&Branch(p, m, t0, t1)) => {
            if match_prefix(k, p, m) {
              if zero_bit(k, m) {
                unsafe { *stack.get_unchecked_mut(i) = MaybeUninit::new((false, p, m, t1)) };
                i += 1;
                t = t0;
                continue;
              } else {
                unsafe { *stack.get_unchecked_mut(i) = MaybeUninit::new((true, p, m, t0)) };
                i += 1;
                t = t1;
                continue;
              }
            } else {
              let u = NonEmpty::Leaf(ox.alloc().init(Leaf(k, x)));
              break join(ox, k, u, p, t);
            }
          }
        }
      };

    while i > 0 {
      i -= 1;
      let (w, p, m, tx) = unsafe { stack.get_unchecked(i).assume_init() };

      if ! w {
        s = NonEmpty::Branch(ox.alloc().init(Branch(p, m, s, tx)))
      } else {
        s = NonEmpty::Branch(ox.alloc().init(Branch(p, m, tx, s)))
      }
    }

    s
  }

  /*
  fn insert_nonempty<'a, T>
    (
      ox: &mut oxcart::Allocator<'a>,
      k: u64,
      x: T,
      t: NonEmpty<'a, T>
    ) -> NonEmpty<'a, T>
  {
    match t {
      NonEmpty::Leaf(&Leaf(j, _)) => {
        if j == k {
          NonEmpty::Leaf(ox.alloc().init(Leaf(k, x)))
        } else {
          let u = NonEmpty::Leaf(ox.alloc().init(Leaf(k, x)));
          join(ox, k, u, j, t)
        }
      }
      NonEmpty::Branch(&Branch(p, m, t0, t1)) => {
        if match_prefix(k, p, m) {
          if zero_bit(k, m) {
            let t0 = insert_nonempty(ox, k, x, t0);
            NonEmpty::Branch(ox.alloc().init(Branch(p, m, t0, t1)))
          } else {
            let t1 = insert_nonempty(ox, k, x, t1);
            NonEmpty::Branch(ox.alloc().init(Branch(p, m, t0, t1)))
          }
        } else {
          let u = NonEmpty::Leaf(ox.alloc().init(Leaf(k, x)));
          join(ox, k, u, p, t)
        }
      }
    }
  }
  */

  pub fn insert<'a, T>
    (
      ox: &mut oxcart::Allocator<'a>,
      k: u64,
      x: T,
      t: IntMap<'a, T>
    ) -> IntMap<'a, T>
  {
    match t {
      IntMap::Empty => {
        IntMap::NonEmpty(NonEmpty::Leaf(ox.alloc().init(Leaf(k, x))))
      }
      IntMap::NonEmpty(t) => {
        IntMap::NonEmpty(insert_nonempty2(ox, k, x, t))
      }
    }
  }
}

pub mod with_bumpalo {
  use super::*;

  #[inline(always)]
  fn join<'a, T>
    (
      bp: &'a bumpalo::Bump,
      p0: u64,
      t0: NonEmpty<'a, T>,
      p1: u64,
      t1: NonEmpty<'a, T>,
    ) -> NonEmpty<'a, T>
  {
    let m = branching_bit(p0, p1);
    if zero_bit(p0, m) {
      NonEmpty::Branch(bp.alloc(Branch(mask(p0, m), m, t0, t1)))
    } else {
      NonEmpty::Branch(bp.alloc(Branch(mask(p0, m), m, t1, t0)))
    }
  }

  fn insert_nonempty<'a, T>
    (
      bp: &'a bumpalo::Bump,
      k: u64,
      x: T,
      t: NonEmpty<'a, T>
    ) -> NonEmpty<'a, T>
  {
    match t {
      NonEmpty::Leaf(&Leaf(j, _)) => {
        if j == k {
          NonEmpty::Leaf(bp.alloc(Leaf(k, x)))
        } else {
          let u = NonEmpty::Leaf(bp.alloc(Leaf(k, x)));
          join(bp, k, u, j, t)
        }
      }
      NonEmpty::Branch(&Branch(p, m, t0, t1)) => {
        if match_prefix(k, p, m) {
          if zero_bit(k, m) {
            let t0 = insert_nonempty(bp, k, x, t0);
            NonEmpty::Branch(bp.alloc(Branch(p, m, t0, t1)))
          } else {
            let t1 = insert_nonempty(bp, k, x, t1);
            NonEmpty::Branch(bp.alloc(Branch(p, m, t0, t1)))
          }
        } else {
          let u = NonEmpty::Leaf(bp.alloc(Leaf(k, x)));
          join(bp, k, u, p, t)
        }
      }
    }
  }

  pub fn insert<'a, T>
    (
      bp: &'a bumpalo::Bump,
      k: u64,
      x: T,
      t: IntMap<'a, T>
    ) -> IntMap<'a, T>
  {
    match t {
      IntMap::Empty => {
        IntMap::NonEmpty(NonEmpty::Leaf(bp.alloc(Leaf(k, x))))
      }
      IntMap::NonEmpty(t) => {
        IntMap::NonEmpty(insert_nonempty(bp, k, x, t))
      }
    }
  }
}
