use std::collections::HashMap;

use super::stack::{Addr, Arity, Atom, Stack};

pub struct RulesDb {
    store: Stack,
    rules: Vec<Rule>,
    index: HashMap<RuleHead, (usize, usize)>,
}

impl RulesDb {
    pub fn lookup(&self, head: RuleHead) -> &[Rule] {
        self.index
            .get(&head)
            .map_or(&[], |(from, to)| &self.rules[*from..*to])
    }
}

pub struct Rule {
    head: Addr,
    tail: Addr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RuleHead(pub Atom, pub Arity);
