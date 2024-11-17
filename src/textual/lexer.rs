use std::str::FromStr;

use logos::{Lexer, Logos};

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token {
    #[token(".")]
    Period,

    #[token(",")]
    Comma,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token(":-")]
    ImpliedBy,

    #[regex("[a-z][a-zA-Z_0-9]*")]
    Symbol,

    #[regex(r"\$[0-9]+", lex_variable)]
    Variable(usize),

    #[regex(r"[\+-]?[0-9]+", lex_from_str)]
    Int(i64),

    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
}

fn lex_variable(lex: &mut Lexer<Token>) -> Option<usize> {
    let slice = lex.slice();
    let n = slice[1..].parse().ok()?; // skip '$'
    Some(n)
}

fn lex_from_str<T: FromStr>(lex: &mut Lexer<Token>) -> Option<T> {
    let slice = lex.slice();
    let n = slice.parse().ok()?; // skip '$'
    Some(n)
}
