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

    #[regex("[A-Z][a-zA-Z_0-9]*")]
    Variable,

    /// NOTE: each wild-card will be a different variable, even when the name is the same.
    #[regex("_[a-zA-Z_0-9]*")]
    Wildcard,

    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
}
