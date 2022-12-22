use crate::prelude::*;

#[test]
fn test_arena() {
  let mut arena = Arena::new();

  let x = arena.alloc().init(0);
  let y = arena.alloc().init(0);
  let z = arena.alloc().init(0);

  *x = 1;
  *y = 2;
  *z = 3;

  assert!(*x + *y + *z == 6);

  arena.reset();
}

struct List<'a, A> {
  arena: &'a Arena,
  head: Option<&'a ListNode<'a, A>>,
}

struct ListNode<'a, A> {
  value: A,
  next: Option<&'a ListNode<'a, A>>,
}

impl<'a, A: Copy> List<'a, A> {
  fn new(arena: &'a Arena) -> Self {
    Self { arena, head: None }
  }

  fn push(&mut self, value: A) {
    self.head = Some(self.arena.alloc().init(ListNode { value, next: self.head }));
  }

  fn pop(&mut self) -> Option<A> {
    match self.head {
      None => { None }
      Some(node) => {
        self.head = node.next;
        Some(node.value)
      }
    }
  }
}

#[test]
fn test_list() {
  let arena = Arena::new();
  let mut t = List::new(&arena);
  t.push(0);
  t.push(1);
  t.push(2);
  assert!(t.pop() == Some(2));
  assert!(t.pop() == Some(1));
  assert!(t.pop() == Some(0));
  assert!(t.pop() == None);
}
