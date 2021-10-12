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

use self::{parser::Parser, pretty::Prettifier};

/// A `Universe` where symbols have literal names.
pub struct NamedUniverse {
    names: HashMap<String, Sym>,
    syms: HashMap<Sym, String>,
    universe: Universe,
}

impl NamedUniverse {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            syms: HashMap::new(),
            universe: Universe::new(),
        }
    }

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

    pub fn symbol_name(&self, sym: Sym) -> Option<&str> {
        self.syms.get(&sym).map(|s| s.as_str())
    }

    pub fn inner_mut(&mut self) -> &mut Universe {
        &mut self.universe
    }

    pub fn inner(&self) -> &Universe {
        &self.universe
    }
}

impl Default for NamedUniverse {
    fn default() -> Self {
        Self::new()
    }
}

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
    pub fn query_dfs(&mut self, query: &str) -> Result<SolutionIter, ParseError> {
        let query = self.prepare_query(query)?;
        Ok(solver::query_dfs(self.universe.inner(), &query))
    }

    // //////////////////////////////// OTHER ACCESSORS ////////////////////////////////

    pub fn pretty(&self) -> Prettifier {
        Prettifier::new(&self.universe)
    }

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
