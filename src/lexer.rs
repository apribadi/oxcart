use crate::prelude::*;

#[repr(u8)]
pub enum Token {
  EOF,
  ERROR,
  Symbol,
  Number,
  Colon,
  Comma,
  Dot,
  DotDot,
  DotDotDot,
  Semicolon,
  LParen,
  LParenNoSpace,
  LBracket,
  LBracketNoSpace,
  LBrace,
  RParen,
  RBracket,
  RBrace,
  Assignment,
  Equal,
  NotEqual,
  GreaterThan,
  GreaterThanOrEqual,
  LessThan,
  LessThanOrEqual,
  Plus,
  Minus,
  Star,
  Slash,
  Ampersand,
  At,
  Bang,
  Caret,
  Dollar,
  Percent,
  Pipe,
  Query,
  Tilde,
  And,
  Break,
  Elif,
  Else,
  End,
  For,
  Fun,
  If,
  Let,
  Loop,
  Or,
  Return,
  While,
}

pub struct Lexer<'a> {
  token_start: *const u8,
  token_stop: *const u8,
  stop: *const u8,
  _marker: PhantomData<&'a u8>,
}

unsafe impl<'a> Send for Lexer<'a> {}

unsafe impl<'a> Sync for Lexer<'a> {}

impl<'a> Lexer<'a> {
  pub fn new(source: &'a [u8]) -> Self {
    let _ = source;

    unimplemented!()
  }

  pub fn next(&mut self) -> Token {
    unimplemented!()
  }

  pub fn current(&self) -> &'a [u8] {
    unimplemented!()
  }
}
