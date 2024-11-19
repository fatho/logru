use std::iter::Peekable;

use logos::{Logos, Span, SpannedIter};

use crate::ast::{AppTerm, Query, Rule, Sym, Term, Var, VarScope};
use crate::universe::SymbolStore;

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
pub struct Parser<'u> {
    symbols: &'u mut SymbolStore,
}

impl<'a> Parser<'a> {
    pub fn new(symbols: &'a mut SymbolStore) -> Self {
        Self { symbols }
    }

    // //////////////////////////////// PUBLIC PARSER ////////////////////////////////

    pub fn parse_query_str(&mut self, query: &str) -> Result<Query, ParseError> {
        let mut tokens = TokenStream::new(query);
        let mut scope = VarScope::new();
        let goals = self.parse_conjunction1(&mut tokens, &mut scope)?;
        self.expect_eof(&mut tokens)?;
        Ok(Query::new(goals, Some(scope)))
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
        Ok(result)
    }

    // //////////////////////////////// PARSER INTERNALS ////////////////////////////////

    fn parse_rule(&mut self, tokens: &mut TokenStream) -> Result<Rule, ParseError> {
        let mut scope = VarScope::new();
        let head = self.parse_appterm(tokens, &mut scope)?;
        let tail = match tokens.peek_token() {
            Some(Ok(Token::ImpliedBy)) => {
                tokens.advance();
                self.parse_conjunction1(tokens, &mut scope)?
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
        Ok(Rule {
            head,
            tail,
            scope: Some(scope),
        })
    }

    fn parse_conjunction1(
        &mut self,
        tokens: &mut TokenStream,
        scope: &mut VarScope,
    ) -> Result<Vec<AppTerm>, ParseError> {
        let mut goals = vec![self.parse_appterm(tokens, scope)?];
        loop {
            match tokens.peek_token() {
                Some(Ok(Token::Comma)) => {
                    tokens.advance();
                    goals.push(self.parse_appterm(tokens, scope)?);
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

    fn parse_appterm(
        &mut self,
        tokens: &mut TokenStream,
        scope: &mut VarScope,
    ) -> Result<AppTerm, ParseError> {
        let functor = self.parse_symbol(tokens)?;
        let mut args = vec![];
        if let Some(Ok(Token::LParen)) = tokens.peek_token() {
            tokens.advance();
            loop {
                args.push(self.parse_term(tokens, scope)?);
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
        Ok(AppTerm::new(functor, args))
    }

    fn parse_term(
        &mut self,
        tokens: &mut TokenStream,
        scope: &mut VarScope,
    ) -> Result<Term, ParseError> {
        match tokens.peek_token() {
            Some(Ok(Token::Variable)) => self.parse_variable(tokens, scope).map(Term::Var),
            Some(Ok(Token::Wildcard)) => {
                tokens.advance();
                Ok(Term::Var(scope.insert_wildcard()))
            }
            Some(Ok(Token::Int(i))) => {
                tokens.advance();
                Ok(Term::Int(i))
            }
            _ => self.parse_appterm(tokens, scope).map(Term::App),
        }
    }

    fn parse_symbol(&mut self, tokens: &mut TokenStream) -> Result<Sym, ParseError> {
        let span = self.expect_token(tokens, Token::Symbol)?;
        let sym = self.symbols.get_or_insert_named(tokens.slice(span));
        Ok(sym)
    }

    fn parse_variable(
        &mut self,
        tokens: &mut TokenStream,
        scope: &mut VarScope,
    ) -> Result<Var, ParseError> {
        let span = self.expect_token(tokens, Token::Variable)?;
        let var = scope.get_or_insert(tokens.slice(span));
        Ok(var)
    }
}

#[cfg(test)]
fn query_roundtrip_test(input: &str) {
    let mut nu = SymbolStore::new();
    let mut p = Parser::new(&mut nu);

    let q = p.parse_query_str(input).unwrap();

    let pretty = super::pretty::Prettifier::new(&nu);
    let qs = pretty.query_to_string(&q);
    assert_eq!(qs, input);
}

#[test]
fn test_query_parsing() {
    query_roundtrip_test("grandparent(bob, X).");
    query_roundtrip_test("grandparent(bob, X), female(X).");

    query_roundtrip_test("add(s(s(s(s(z)))), s(s(z)), X).");
}

#[cfg(test)]
fn rule_roundtrip_test(input: &str) {
    let mut nu = SymbolStore::new();
    let mut p = Parser::new(&mut nu);
    let q = p.parse_rule_str(input).unwrap();

    let pretty = super::pretty::Prettifier::new(&nu);
    let qs = pretty.rule_to_string(&q);
    assert_eq!(qs, input);
}

#[test]
fn test_rule_parsing() {
    rule_roundtrip_test("is_natural(z).");
    rule_roundtrip_test("is_natural(s(X)) :- is_natural(X).");
    rule_roundtrip_test("grandparent(X, Y) :- parent(X, Z), parent(Z, Y).");
}
