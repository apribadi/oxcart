use crate::prelude::*;

#[test]
fn hello() {
  expect!["Hello!"].assert_eq(&format!("Hello!"));
}
