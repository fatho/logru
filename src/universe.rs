use crate::ast::*;

#[derive(Debug)]
pub struct Universe {
    fresh_symbol: usize,
    rules: Vec<Rule>,
}

impl Universe {
    pub fn alloc_symbol(&mut self) -> Sym {
        let sym = Sym::from_ord(self.fresh_symbol);
        self.fresh_symbol += 1;
        sym
    }

    pub fn alloc_symbols(&mut self, count: usize) -> impl Iterator<Item = Sym> {
        let fresh_start = self.fresh_symbol;
        self.fresh_symbol += count;
        (fresh_start..fresh_start + count).map(Sym::from_ord)
    }

    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    pub fn new() -> Self {
        Self {
            fresh_symbol: 0,
            rules: vec![],
        }
    }

    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    pub fn num_symbols(&self) -> usize {
        self.fresh_symbol
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}
