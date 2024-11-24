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

    #[regex("[A-Z][a-zA-Z_0-9]*")]
    Variable,

    /// NOTE: each wild-card will be a different variable, even when the name is the same.
    #[regex("_[a-zA-Z_0-9]*")]
    Wildcard,

    #[regex("[+-]?[0-9]+", parse_int)]
    Int(i64),

    #[token("!")]
    Cut,

    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
}

fn parse_int(lex: &mut Lexer<Token>) -> Option<i64> {
    lex.slice().parse().ok()
}
