//! # A Prolog-like syntax
//!
//! This module provides a textual, Prolog-like syntax for the solver core. See [`TextualUniverse`]
//! for an example.

mod lexer;
mod parser;
mod pretty;

pub use parser::{ParseError, ParseErrorKind};
use pretty::ScopedPrettifier;

use crate::{
    ast::Query,
    resolve::RuleResolver,
    search::{self, SolutionIter},
    universe::{RuleSet, SymbolOverlay, SymbolStore},
};

pub use self::{parser::Parser, pretty::Prettifier};

/// A universe that can be interacted with using a Prolog like syntax.
///
/// It builds on the [`SymbolStore`] and [`RuleSet`] abstractions and additionally provides a
/// fully textual syntax for defining rules and queries, looking very similar to Prolog.
///
/// Syntactic elements:
/// - **Variables**: An identifier starting with a upper case ASCII latter followed by zero or more
///   ASCII letters, digits or underscores, e.g. `X`, `Person`, `FooBar`.
/// - **Symbols**: An identifier starting with a lower case ASCII latter followed by zero or more
///   ASCII letters, digits or underscores, e.g. `foo`, `rightOf`, `is_natural`.
/// - **Application Terms**: An application of a functor to arguments, e.g. `is_natural(X)` or
///   `add(X, z, Y)`.
/// - **Facts**: An application term followed by a dot, e.g. `is_natural(z).`.
/// - **Rules**: An application term followed by `:-` (a reverse implication arrow) and a comma
///   separated list of one or more conjunctive conditions, followed by a dot, e.g. `grandparent(A,
///   B) :- parent(A, C), parent(C, B).`.
/// - **Queries**: A comma separated list of one or more conjunctive conditions, followed by a dot,
///   e.g. `grandparent(bob, A), female(A).`.
///
/// It doesn't support comments and the moment, so that is probably a good idea for the future.
///
/// Besides functions for parsing, the textual universe also provides pretty-printing facilities.
///
/// # Example
///
/// Definitions of facts and rules can be loaded from a string that contains zero or more facts or
/// rules as described above. In the following example, we define a set of Peano arithmetic rules
/// and compute the first 5 square numbers.
///
/// ```
/// # use logru::textual::*;
/// # use logru::query_dfs;
/// let mut u = TextualUniverse::new();
/// u.load_str(
///     r#"
/// is_natural(z).
/// is_natural(s(A)) :- is_natural(A).
/// add(A, z, A) :- is_natural(A).
/// add(A, s(B), s(C)) :- add(A, B, C).
/// mul(A, z, z) :- is_natural(A).
/// mul(A, s(B), C) :- mul(A, B, D), add(A, D, C).
/// "#,
/// )
/// .unwrap();
///
/// let query = u.prepare_query("mul(X,X,Y).").unwrap();
/// let solutions = query_dfs(u.resolver(), query.query());
/// for solution in solutions.take(5) {
///     println!("SOLUTION:");
///     for (var, term) in solution.iter_vars() {
///         if let Some(term) = term {
///             println!("  ${} = {}", var.ord(), query.pretty().term_to_string(&term));
///         } else {
///             println!("<bug: no solution>");
///         }
///     }
/// }
/// ```
///
pub struct TextualUniverse {
    pub symbols: SymbolStore,
    pub rules: RuleSet,
}

impl TextualUniverse {
    pub fn new() -> Self {
        Self {
            symbols: SymbolStore::new(),
            rules: RuleSet::new(),
        }
    }

    /// Load a set of rules from a string.
    pub fn load_str(&mut self, rules: &str) -> Result<(), ParseError> {
        let rules = Parser::new(&mut self.symbols).parse_rules_str(rules)?;
        for rule in rules {
            self.rules.insert(rule);
        }
        Ok(())
    }

    /// Parse a query, but do not run it.
    pub fn prepare_query(&self, query: &str) -> Result<UniverseQuery<'_>, ParseError> {
        let symbols = SymbolOverlay::new(&self.symbols);
        let mut parser = Parser::new(symbols);
        let query = parser.parse_query_str(query)?;
        Ok(UniverseQuery::new(parser.into_symbols(), query))
    }

    /// Run a query against the universe using the DFS solver.
    ///
    /// # Notes
    ///
    /// When you need access to the pretty printer while the solution iterator is still live, use
    /// [`Self::prepare_query`] instead. This method needs to take a mutable reference of the
    /// universe because parsing can discover new symbols that need to be added to the universe
    /// before running the query. Running a query by itself only requires a shared reference, and
    /// thus the pretty-printer is still accessible.
    pub fn query_dfs(&mut self, query: &str) -> Result<SolutionIter<RuleResolver>, ParseError> {
        let query = self.prepare_query(query)?;
        Ok(search::query_dfs(
            RuleResolver::new(&self.rules),
            query.query(),
        ))
    }

    // //////////////////////////////// OTHER ACCESSORS ////////////////////////////////

    /// Return a pretty-printer using the symbols defined in this universe.
    pub fn pretty(&self) -> Prettifier<SymbolStore> {
        Prettifier::new(&self.symbols)
    }

    /// Return a term parser that uses the name mapping of this universe for parsing terms.
    pub fn parse(&mut self) -> Parser<&mut SymbolStore> {
        Parser::new(&mut self.symbols)
    }

    /// Return a resolver for the internal rule database.
    pub fn resolver(&self) -> RuleResolver {
        RuleResolver::new(&self.rules)
    }
}

impl Default for TextualUniverse {
    fn default() -> Self {
        Self::new()
    }
}

/// A query tied to a particular universe through symbols
pub struct UniverseQuery<'a> {
    symbols: SymbolOverlay<'a>,
    query: Query,
}

impl<'a> UniverseQuery<'a> {
    pub fn new(symbols: SymbolOverlay<'a>, query: Query) -> Self {
        Self { symbols, query }
    }

    pub fn query(&self) -> &Query {
        &self.query
    }

    pub fn symbols(&self) -> &SymbolOverlay<'a> {
        &self.symbols
    }

    pub fn symbols_mut(&mut self) -> &mut SymbolOverlay<'a> {
        &mut self.symbols
    }

    /// Return a pretty-printer using the symbols defined in this query.
    /// As opposed to TextualUniverse::pretty, this one won't allow any mixups between the sources of the universe and the variables.
    pub fn pretty(&self) -> ScopedPrettifier<SymbolOverlay> {
        ScopedPrettifier::new(&self.symbols, self.query().scope.as_ref())
    }
}
