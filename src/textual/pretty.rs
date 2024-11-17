use crate::ast::{AppTerm, Query, Rule, Term, VarScope};

use super::SymbolStore;

/// A pretty-printer for terms using the Prolog-like syntax of the
/// [TextualUniverse](super::TextualUniverse).
pub struct Prettifier<'u> {
    universe: &'u SymbolStore,
}

impl<'a> Prettifier<'a> {
    pub fn new(universe: &'a SymbolStore) -> Self {
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
        goals: &[AppTerm],
        scope: Option<&VarScope>,
    ) -> std::fmt::Result {
        if let Some((first, rest)) = goals.split_first() {
            self.pretty_app(writer, first, scope)?;
            for arg in rest {
                write!(writer, ", ")?;
                self.pretty_app(writer, arg, scope)?;
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
