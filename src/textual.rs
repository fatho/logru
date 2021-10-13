//! # A Prolog-like syntax
//!
//! This module provides a textual, Prolog-like syntax for the solver core. See [`TextualUniverse`]
//! for an example.
//!
//! As a lower-level abstraction, this module also provides [`NamedUniverse`] which doesn't come
//! with a full-blown parse, but does provide a name mapping for symbols.

mod lexer;
mod parser;
mod pretty;

use std::collections::HashMap;

pub use parser::{ParseError, ParseErrorKind};

use crate::{
    ast::{Query, Sym},
    solver::{self, SolutionIter},
    universe::Universe,
};

pub use self::{parser::Parser, pretty::Prettifier};

/// A universe where symbols have literal names.
///
/// It wraps an underlying [`Universe`] and maintains a mapping between names and symbols so that
/// for each symbol created via this wrapper, the name can be looked up, and each symbol is created
/// by name.
///
/// # Example
///
/// ```
/// # use logru::textual::*;
/// let mut nu = NamedUniverse::new();
/// let foo = nu.symbol("foo");
/// let bar = nu.symbol("bar");
/// assert_ne!(foo, bar);
///
/// let foo_again = nu.symbol("foo");
/// assert_eq!(foo, foo_again);
///
/// let bar_name = nu.symbol_name(bar);
/// assert_eq!(bar_name, Some("bar"));
///
/// // Creating an unnamed symbol
/// let unknown = nu.inner_mut().alloc_symbol();
/// let unknown_name = nu.symbol_name(unknown);
/// assert_eq!(unknown_name, None);
/// ```
///
pub struct NamedUniverse {
    names: HashMap<String, Sym>,
    syms: HashMap<Sym, String>,
    universe: Universe,
}

impl NamedUniverse {
    /// Create a new empty universe.
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            syms: HashMap::new(),
            universe: Universe::new(),
        }
    }

    /// Create a new symbol or return an existing symbol with that name
    ///
    /// Each symbol with a given name can exist only once. When an existing name is passed to this
    /// function, the existing symbol identifier is returned.
    pub fn symbol(&mut self, name: &str) -> Sym {
        if let Some(sym) = self.names.get(name) {
            *sym
        } else {
            let sym = self.universe.alloc_symbol();
            self.names.insert(name.to_owned(), sym);
            self.syms.insert(sym, name.to_owned());
            sym
        }
    }

    /// Look up the name of a symbol.
    ///
    /// A symbol may have no name if it was created directly via the underlying universe using
    /// [`NamedUniverse::inner_mut`].
    pub fn symbol_name(&self, sym: Sym) -> Option<&str> {
        self.syms.get(&sym).map(|s| s.as_str())
    }

    /// Get mutable access to the underlying universe.
    pub fn inner_mut(&mut self) -> &mut Universe {
        &mut self.universe
    }

    /// Get shared access to the underlying universe.
    pub fn inner(&self) -> &Universe {
        &self.universe
    }
}

impl Default for NamedUniverse {
    fn default() -> Self {
        Self::new()
    }
}

/// A universe that can be interacted with using a Prolog like syntax.
///
/// It builds on the [`NamedUniverse`] abstraction and additionally provides a fully textual syntax
/// for defining rules and queries, looking very similar to Prolog. Variables are still referenced
/// by numeric IDs though, but this is subject to change in future versions.
///
/// Syntactic elements:
/// - **Variables**: A numeric identifier prefixed by `$`, e.g. `$0`, `$1`, ... .
/// - **Symbols**: An identifier starting with a lower case ASCII latter followed by zero or more
///   ASCII letters, digits or underscores, e.g. `foo`, `rightOf`, `is_natural`.
/// - **Application Terms**: An application of a functor to arguments, e.g. `is_natural($0)` or
///   `add($0, z, $0)`.
/// - **Facts**: An application term followed by a dot, e.g. `is_natural(Z).`.
/// - **Rules**: An application term followed by `:-` (a reverse implication arrow) and a comma
///   separated list of one or more conjunctive conditions, followed by a dot, e.g. `grandparent($0,
///   $1) :- parent($0, $2), parent($2, $0).`.
/// - **Queries**: A comma separated list of one or more conjunctive conditions, followed by a dot,
///   e.g. `grandparent(bob, $0), female($0).`.
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
/// is_natural(s($0)) :- is_natural($0).
/// add($0, z, $0) :- is_natural($0).
/// add($0, s($1), s($2)) :- add($0, $1, $2).
/// mul($0, z, z) :- is_natural($0).
/// mul($0, s($1), $2) :- mul($0,$1,$3), add($0,$3,$2).
/// "#,
/// )
/// .unwrap();
///
/// let query = u.prepare_query("mul($0,$0,$1).").unwrap();
/// let solutions = query_dfs(u.inner(), &query);
/// for solution in solutions.take(5) {
///     println!("SOLUTION:");
///     for (index, var) in solution.into_iter().enumerate() {
///         if let Some(term) = var {
///             println!("  ${} = {}", index, u.pretty().term_to_string(&term));
///         } else {
///             println!("<bug: no solution>");
///         }
///     }
/// }
/// ```
///
pub struct TextualUniverse {
    universe: NamedUniverse,
}

impl TextualUniverse {
    pub fn new() -> Self {
        Self {
            universe: NamedUniverse::new(),
        }
    }

    /// Load a set of rules from a string.
    pub fn load_str(&mut self, rules: &str) -> Result<(), ParseError> {
        let rules = Parser::new(&mut self.universe).parse_rules_str(rules)?;
        for rule in rules {
            self.universe.inner_mut().add_rule(rule);
        }
        Ok(())
    }

    /// Parse a query, but do not run it.
    pub fn prepare_query(&mut self, query: &str) -> Result<Query, ParseError> {
        Parser::new(&mut self.universe).parse_query_str(query)
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
    pub fn query_dfs(&mut self, query: &str) -> Result<SolutionIter, ParseError> {
        let query = self.prepare_query(query)?;
        Ok(solver::query_dfs(self.universe.inner(), &query))
    }

    // //////////////////////////////// OTHER ACCESSORS ////////////////////////////////

    /// Return a pretty-printer using the symbols defined in this universe.
    pub fn pretty(&self) -> Prettifier {
        Prettifier::new(&self.universe)
    }

    /// Return a term parser that uses the name mapping of this universe for parsing terms.
    pub fn parse(&mut self) -> Parser {
        Parser::new(&mut self.universe)
    }

    pub fn inner_mut(&mut self) -> &mut Universe {
        self.universe.inner_mut()
    }

    pub fn inner(&self) -> &Universe {
        self.universe.inner()
    }
}

impl Default for TextualUniverse {
    fn default() -> Self {
        Self::new()
    }
}
