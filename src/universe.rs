use crate::ast::*;

/// The Universe is a collection of symbols, facts and rules. A solver can be used for running
/// queries against the universe.
#[derive(Debug)]
pub struct Universe {
    /// next unallocated symbol ID
    fresh_symbol: usize,
    rules: Vec<Rule>,
}

impl Universe {
    /// Create a new empty universe.
    pub fn new() -> Self {
        Self {
            fresh_symbol: 0,
            rules: vec![],
        }
    }

    /// Generate a fresh symbol ID in this universe.
    pub fn alloc_symbol(&mut self) -> Sym {
        let sym = Sym::from_ord(self.fresh_symbol);
        self.fresh_symbol += 1;
        sym
    }

    /// Generate a range of fresh symbol IDs in this universe.
    pub fn alloc_symbols(&mut self, count: usize) -> impl Iterator<Item = Sym> {
        let fresh_start = self.fresh_symbol;
        self.fresh_symbol += count;
        (fresh_start..fresh_start + count).map(Sym::from_ord)
    }

    /// Add a new rule to this universe for deriving facts.
    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    /// Returns the rules that have been added to this universe.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Returns the number of symbols that have been allocated in this universe.
    pub fn num_symbols(&self) -> usize {
        self.fresh_symbol
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}
