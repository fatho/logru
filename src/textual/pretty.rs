use crate::ast::{AppTerm, Query, Rule, Term};

use super::NamedUniverse;

/// A pretty-printer for terms using the Prolog-like syntax of the
/// [TextualUniverse](super::TextualUniverse).
pub struct Prettifier<'u> {
    universe: &'u NamedUniverse,
}

impl<'a> Prettifier<'a> {
    pub fn new(universe: &'a NamedUniverse) -> Self {
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

    pub fn term_to_string(&self, term: &Term) -> String {
        let mut out = String::new();
        self.pretty(&mut out, term).unwrap();
        out
    }

    pub fn pretty<W: std::fmt::Write>(&self, writer: &mut W, term: &Term) -> std::fmt::Result {
        match term {
            Term::Var(v) => write!(writer, "${}", v.ord()),
            Term::App(app) => self.pretty_app(writer, app),
        }
    }

    pub fn pretty_app<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        term: &AppTerm,
    ) -> std::fmt::Result {
        if let Some(name) = &self.universe.symbol_name(term.functor) {
            write!(writer, "{}", name)?;
        } else {
            write!(writer, "<unk:{}>", term.functor.ord())?;
        }

        if let Some((first, rest)) = term.args.split_first() {
            write!(writer, "(")?;

            self.pretty(writer, first)?;
            for arg in rest {
                write!(writer, ", ")?;
                self.pretty(writer, arg)?;
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
        self.pretty_conjunction(writer, &query.goals)
    }

    pub fn pretty_conjunction<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        goals: &[AppTerm],
    ) -> std::fmt::Result {
        if let Some((first, rest)) = goals.split_first() {
            self.pretty_app(writer, first)?;
            for arg in rest {
                write!(writer, ", ")?;
                self.pretty_app(writer, arg)?;
            }
        }
        write!(writer, ".")?;

        Ok(())
    }

    pub fn pretty_rule<W: std::fmt::Write>(&self, writer: &mut W, rule: &Rule) -> std::fmt::Result {
        self.pretty_app(writer, &rule.head)?;
        if rule.tail.is_empty() {
            write!(writer, ".")?;
        } else {
            write!(writer, " :- ")?;
            self.pretty_conjunction(writer, &rule.tail)?;
        }
        Ok(())
    }
}
