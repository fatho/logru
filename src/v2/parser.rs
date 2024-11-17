use std::collections::HashSet;
use std::iter::Peekable;
use std::sync::Arc;

use logos::{Logos, Span, SpannedIter};

use super::ast::{CompoundTerm, Query, Rule, Term};
use super::lexer::Token;

struct TokenStream<'a> {
    source: &'a str,
    lexer: Peekable<SpannedIter<'a, Token>>,
}

impl<'a> TokenStream<'a> {
    pub fn new(source: &'a str) -> Self {
        let lexer = Token::lexer(source).spanned().peekable();

        Self { source, lexer }
    }

    #[allow(unused)]
    pub fn peek(&mut self) -> Option<(Result<Token, ()>, Span)> {
        self.lexer.peek().cloned()
    }

    pub fn next(&mut self) -> Option<(Result<Token, ()>, Span)> {
        self.lexer.next()
    }

    pub fn advance(&mut self) {
        self.lexer.next();
    }

    pub fn peek_token(&mut self) -> Option<Result<Token, ()>> {
        self.lexer.peek().map(|(tok, _)| tok).cloned()
    }

    #[allow(unused)]
    pub fn next_token(&mut self) -> Option<Result<Token, ()>> {
        self.lexer.next().map(|(tok, _)| tok)
    }

    pub fn slice(&self, span: Span) -> &str {
        &self.source[span]
    }

    pub fn eof(&self) -> Span {
        self.source.len()..self.source.len()
    }
}

/// A parse error originating from [`Parser`].
#[derive(Debug)]
pub struct ParseError {
    /// The range in the source text where the error occurred.
    pub span: Span,
    /// The type of error that occurred.
    pub kind: ParseErrorKind,
}

impl ParseError {
    pub fn new(span: Span, kind: ParseErrorKind) -> Self {
        Self { span, kind }
    }
}

/// The various types of parse errors reported by [`Parser`].
#[derive(Debug)]
pub enum ParseErrorKind {
    /// The parser reached the end of the input, but expected more tokens to follow.
    UnexpectedEof,
    /// The parser encountered a token that doesn't belong in that place.
    UnexpectedToken,
    /// The parser encountered more tokens after the input should have ended.
    ExpectedEof,
}

/// A parser for terms using the Prolog-like syntax of the
/// [TextualUniverse](super::TextualUniverse).
pub struct Parser {
    interned_strings: HashSet<Arc<str>>,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            interned_strings: HashSet::new(),
        }
    }

    // //////////////////////////////// PUBLIC PARSER ////////////////////////////////

    pub fn parse_query_str(&mut self, query: &str) -> Result<Query, ParseError> {
        let mut tokens = TokenStream::new(query);
        let result = self.parse_conjunction1(&mut tokens).map(Query::new)?;
        self.expect_eof(&mut tokens)?;
        Ok(result)
    }

    pub fn parse_rule_str(&mut self, rule: &str) -> Result<Rule, ParseError> {
        let mut tokens = TokenStream::new(rule);
        let result = self.parse_rule(&mut tokens)?;
        self.expect_eof(&mut tokens)?;
        Ok(result)
    }

    pub fn parse_rules_str(&mut self, rules: &str) -> Result<Vec<Rule>, ParseError> {
        let mut tokens = TokenStream::new(rules);
        let mut result = vec![];
        while tokens.peek_token().is_some() {
            result.push(self.parse_rule(&mut tokens)?);
        }
        self.expect_eof(&mut tokens)?;
        Ok(result)
    }

    // //////////////////////////////// PARSER INTERNALS ////////////////////////////////

    fn parse_rule(&mut self, tokens: &mut TokenStream) -> Result<Rule, ParseError> {
        let head = self.parse_compound(tokens)?;
        let tail = match tokens.peek_token() {
            Some(Ok(Token::ImpliedBy)) => {
                tokens.advance();
                self.parse_conjunction1(tokens)?
            }
            Some(Ok(Token::Period)) => {
                tokens.advance();
                Vec::new()
            }
            Some(_) => {
                let (_, span) = tokens.next().unwrap();
                return Err(ParseError::new(span, ParseErrorKind::UnexpectedToken));
            }
            None => return Err(ParseError::new(tokens.eof(), ParseErrorKind::UnexpectedEof)),
        };
        Ok(Rule { head, tail })
    }

    fn parse_conjunction1(&mut self, tokens: &mut TokenStream) -> Result<Vec<Term>, ParseError> {
        let mut goals = vec![self.parse_term(tokens)?];
        loop {
            match tokens.peek_token() {
                Some(Ok(Token::Comma)) => {
                    tokens.advance();
                    goals.push(self.parse_term(tokens)?);
                }
                Some(Ok(Token::Period)) => {
                    tokens.advance();
                    break;
                }
                Some(_) => {
                    let (_, span) = tokens.next().unwrap();
                    return Err(ParseError::new(span, ParseErrorKind::UnexpectedToken));
                }
                None => return Err(ParseError::new(tokens.eof(), ParseErrorKind::UnexpectedEof)),
            }
        }
        Ok(goals)
    }

    fn expect_eof(&mut self, tokens: &mut TokenStream) -> Result<(), ParseError> {
        if let Some((_, span)) = tokens.next() {
            Err(ParseError::new(span, ParseErrorKind::UnexpectedToken))
        } else {
            Ok(())
        }
    }

    fn expect_token(
        &mut self,
        tokens: &mut TokenStream,
        expected: Token,
    ) -> Result<Span, ParseError> {
        if let Some((actual, span)) = tokens.next() {
            if actual == Ok(expected) {
                Ok(span)
            } else {
                Err(ParseError::new(span, ParseErrorKind::UnexpectedToken))
            }
        } else {
            Err(ParseError::new(tokens.eof(), ParseErrorKind::UnexpectedEof))
        }
    }

    fn parse_compound(&mut self, tokens: &mut TokenStream) -> Result<CompoundTerm, ParseError> {
        let functor = self.parse_symbol(tokens)?;
        let mut args = vec![];
        if let Some(Ok(Token::LParen)) = tokens.peek_token() {
            tokens.advance();
            loop {
                args.push(self.parse_term(tokens)?);
                match tokens.peek_token() {
                    Some(Ok(Token::Comma)) => {
                        tokens.advance();
                    }
                    Some(Ok(Token::RParen)) => {
                        tokens.advance();
                        break;
                    }
                    Some(_) => {
                        let (_, span) = tokens.next().unwrap();
                        return Err(ParseError::new(span, ParseErrorKind::UnexpectedToken));
                    }
                    None => {
                        return Err(ParseError::new(tokens.eof(), ParseErrorKind::UnexpectedEof))
                    }
                }
            }
        }
        Ok(CompoundTerm::new(functor, args))
    }

    fn parse_term(&mut self, tokens: &mut TokenStream) -> Result<Term, ParseError> {
        match tokens.peek_token() {
            Some(Ok(Token::Variable)) => {
                let var = self.parse_named_variable(tokens)?;
                Ok(Term::var(var))
            }
            Some(Ok(Token::AnonVariable)) => {
                tokens.advance();
                Ok(Term::var_anon())
            }
            _ => self.parse_compound(tokens).map(Term::Compound),
        }
    }

    fn parse_symbol(&mut self, tokens: &mut TokenStream) -> Result<Arc<str>, ParseError> {
        let span = self.expect_token(tokens, Token::Symbol)?;
        let sym = self.intern(tokens.slice(span));
        Ok(sym)
    }

    fn parse_named_variable(&mut self, tokens: &mut TokenStream) -> Result<Arc<str>, ParseError> {
        let span = self.expect_token(tokens, Token::Variable)?;
        let sym = self.intern(tokens.slice(span));
        Ok(sym)
    }

    fn intern(&mut self, value: &str) -> Arc<str> {
        if let Some(arc) = self.interned_strings.get(value) {
            arc.clone()
        } else {
            let new: Arc<str> = value.into();
            self.interned_strings.insert(new.clone());
            new
        }
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

#[test]
fn test_query_parsing() {
    #[track_caller]
    fn assert_query_roundtrip(input: &str) {
        let mut p = Parser::new();

        let q = p.parse_query_str(input).unwrap();
        assert_eq!(q.to_string(), input);
    }

    assert_query_roundtrip("grandparent(bob, X).");
    assert_query_roundtrip("grandparent(bob, X), female(X).");

    assert_query_roundtrip("add(s(s(s(s(z)))), s(s(z)), Y).");
}

#[test]
fn test_rule_parsing() {
    #[track_caller]
    fn assert_rule_roundtrip(input: &str) {
        let mut p = Parser::new();
        let r = p.parse_rule_str(input).unwrap();

        assert_eq!(r.to_string(), input);
    }

    assert_rule_roundtrip("anything(_).");
    assert_rule_roundtrip("is_natural(z).");
    assert_rule_roundtrip("is_natural(s(X)) :- is_natural(X).");
    assert_rule_roundtrip("grandparent(X, Y) :- parent(X, Z), parent(Z, Y).");
}