use logos::Logos;

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

    #[regex(r"[A-Z][a-zA-Z_0-9]*")]
    Variable,

    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
}
