#[derive(Clone, Copy)]
pub enum List<'a, T> {
  Nil,
  Cons(&'a Node<'a, T>),
}

#[derive(Clone, Copy)]
pub struct Node<'a, T> {
  pub car: T,
  pub cdr: List<'a, T>,
}
