use crate::{
    ast::{AppTerm, Query, Rule, Term, VarScope},
    universe::Symbols,
};
use std::ops::Deref;

/// A pretty-printer for terms using the Prolog-like syntax of the
/// [TextualUniverse](super::TextualUniverse).
///
/// This type takes an explicit scope in many methods, making it possible to use the wrong variable scope for the given universe. A version where mixups are impossible is ScopedPrettifier.
pub struct Prettifier<'u, T: Symbols> {
    universe: &'u T,
}

impl<'a, T: Symbols> Prettifier<'a, T> {
    pub fn new(universe: &'a T) -> Self {
        Self { universe }
    }

    pub fn query_to_string(&self, query: &Query) -> String {
        let mut out = String::new();
        self.pretty_query(&mut out, query).unwrap();
        out
    }

    pub fn rule_to_string(&self, rule: &Rule) -> String {
        let mut out = String::new();
        self.pretty_rule(&mut out, rule).unwrap();
        out
    }

    pub fn term_to_string(&self, term: &Term, scope: Option<&VarScope>) -> String {
        let mut out = String::new();
        self.pretty(&mut out, term, scope).unwrap();
        out
    }

    pub fn pretty<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        term: &Term,
        scope: Option<&VarScope>,
    ) -> std::fmt::Result {
        match term {
            Term::Var(v) => {
                if let Some(name) = scope.and_then(|scope| scope.get_name(*v)) {
                    write!(writer, "{name}")
                } else {
                    write!(writer, "_{}", v.ord())
                }
            }
            Term::App(app) => self.pretty_app(writer, app, scope),
            Term::Int(int) => write!(writer, "{int}"),
            Term::Cut => write!(writer, "!"),
            Term::Constraint(int) => write!(writer, "#<{int}"),
        }
    }

    pub fn pretty_app<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        term: &AppTerm,
        scope: Option<&VarScope>,
    ) -> std::fmt::Result {
        if let Some(name) = &self.universe.get_symbol_name(term.functor) {
            write!(writer, "{}", name)?;
        } else {
            write!(writer, "<unk:{}>", term.functor.ord())?;
        }

        if let Some((first, rest)) = term.args.split_first() {
            write!(writer, "(")?;

            self.pretty(writer, first, scope)?;
            for arg in rest {
                write!(writer, ", ")?;
                self.pretty(writer, arg, scope)?;
            }

            write!(writer, ")")?;
        }

        Ok(())
    }

    pub fn pretty_query<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        query: &Query,
    ) -> std::fmt::Result {
        self.pretty_conjunction(writer, &query.goals, query.scope.as_ref())
    }

    pub fn pretty_conjunction<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        goals: &[Term],
        scope: Option<&VarScope>,
    ) -> std::fmt::Result {
        if let Some((first, rest)) = goals.split_first() {
            self.pretty(writer, first, scope)?;
            for arg in rest {
                write!(writer, ", ")?;
                self.pretty(writer, arg, scope)?;
            }
        }
        write!(writer, ".")?;

        Ok(())
    }

    pub fn pretty_rule<W: std::fmt::Write>(&self, writer: &mut W, rule: &Rule) -> std::fmt::Result {
        self.pretty_app(writer, &rule.head, rule.scope.as_ref())?;
        if rule.tail.is_empty() {
            write!(writer, ".")?;
        } else {
            write!(writer, " :- ")?;
            self.pretty_conjunction(writer, &rule.tail, rule.scope.as_ref())?;
        }
        Ok(())
    }
}

/// A prettifier for showing terms relating to a query.
pub struct ScopedPrettifier<'u, T: Symbols> {
    pretty: Prettifier<'u, T>,
    // The scope is meant to reference the same query as the symbols in the base prettifier, so it shares the lifetime
    scope: Option<&'u VarScope>,
}

impl<'u, T: Symbols> ScopedPrettifier<'u, T> {
    pub fn new(universe: &'u T, scope: Option<&'u VarScope>) -> Self {
        Self {
            pretty: Prettifier::new(universe),
            scope,
        }
    }

    pub fn term_to_string(&self, term: &Term) -> String {
        self.pretty.term_to_string(term, self.scope)
    }

    pub fn pretty<W: std::fmt::Write>(&self, writer: &mut W, term: &Term) -> std::fmt::Result {
        self.pretty.pretty(writer, term, self.scope)
    }

    pub fn pretty_app<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        term: &AppTerm,
    ) -> std::fmt::Result {
        self.pretty.pretty_app(writer, term, self.scope)
    }

    pub fn pretty_conjunction<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        goals: &[Term],
    ) -> std::fmt::Result {
        self.pretty.pretty_conjunction(writer, goals, self.scope)
    }
}

impl<'u, T: Symbols> Deref for ScopedPrettifier<'u, T> {
    type Target = Prettifier<'u, T>;
    fn deref(&self) -> &Self::Target {
        &self.pretty
    }
}
