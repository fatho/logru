//! The universe holds the current knowledge in the form of facts and rules.

use std::collections::HashMap;

use super::stack::{Addr, Arity, Atom, Stack};

pub struct Universe {
    store: Stack,
    rules: Vec<Addr>,
    free_atom: Atom,
}

impl Universe {
    pub fn lookup(&self, head: RuleHead) -> &[Addr] {
        // self.index
        //     .get(&head)
        //     .map_or(&[], |(from, to)| &self.rules[*from..*to])
        todo!()
    }
}

pub mod builtin_atoms {
    use crate::v2::stack::Atom;

    /// Rule compound: holds pointers to the head and tail of the stored rule
    pub const RULE: Atom = Atom::new(1);
    /// Conjunction compound: proving this requires proving all arguments
    pub const CONJ: Atom = Atom::new(2);
}

// pub struct Rule {
//     head: Addr,
//     tail: Addr,
// }

// impl Rule {
//     pub const ATOM: Atom = builtin_atoms::RULE;

//     pub fn from_stack(stack: &Stack, base: Addr) -> Rule
// }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RuleHead(pub Atom, pub Arity);
