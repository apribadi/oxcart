use crate::prelude::*;

#[test]
fn test_hello() {
  expect!["Hello!"].assert_eq(&format!("Hello!"));
}
