//! The universe holds the current knowledge in the form of facts and rules.

use super::stack::{Addr, Arity, Atom, DecodedWord, FrozenStack, Stack};

#[derive(Debug, Clone)]
pub struct Universe {
    store: Stack,
    rules: Vec<Rule>,
    free_atom: Atom,
}

impl Universe {
    pub fn new() -> Self {
        Self {
            store: Stack::new(),
            rules: Vec::new(),
            free_atom: Atom::new(0),
        }
    }

    pub fn freeze_for_query(&mut self) -> (RulesQuery<'_>, FrozenStack<'_>) {
        (RulesQuery { rules: &self.rules }, self.store.freeze())
    }

    /// Reserve a new unused atom
    pub fn reserve_atom(&mut self) -> Atom {
        assert!(
            self.free_atom < builtin_atoms::RESERVED_LIMIT,
            "atom overflow"
        );
        let ret = self.free_atom;
        self.free_atom = Atom::new(self.free_atom.into_raw() + 1);
        ret
    }

    pub fn add_rule(&mut self, build: impl FnOnce(&mut Stack) -> (Addr, Option<Addr>)) {
        // Allocate head and tail
        let (head, tail) = build(&mut self.store);
        let top = self.store.top();

        // Validate pointers stay within bounds
        #[cfg(debug_assertions)]
        {
            let head_end = tail.unwrap_or(top);
            for p in head.range_iter(head_end) {
                if let DecodedWord::Ptr(Some(addr)) = DecodedWord::from(self.store[p]) {
                    assert!(
                        addr >= head && addr < head_end,
                        "variables in head must only point inside head"
                    );
                }
            }
            if let Some(tail) = tail {
                for p in tail.range_iter(top) {
                    if let DecodedWord::Ptr(Some(addr)) = DecodedWord::from(self.store[p]) {
                        assert!(
                            addr >= head && addr < top,
                            "variables in tail must only point inside rule"
                        );
                    }
                }
            }
        }

        self.rules.push(Rule {
            head,
            tail,
            end: top,
        });
    }

    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            stack_pos: self.store.top(),
            rules_pos: self.rules.len(),
            free_atom: self.free_atom,
        }
    }

    pub fn restore(&mut self, checkpoint: Checkpoint) {
        self.store.free(checkpoint.stack_pos);
        self.rules.truncate(checkpoint.rules_pos);
        self.free_atom = checkpoint.free_atom;
    }
}

pub struct RulesQuery<'u> {
    rules: &'u [Rule],
}

impl<'u> RulesQuery<'u> {
    pub fn lookup<'a>(
        &'a self,
        store: &'a FrozenStack<'u>,
        head: RuleHead,
    ) -> impl DoubleEndedIterator<Item = Rule> + 'a {
        self.rules.iter().copied().filter(move |rule| {
            let DecodedWord::App(atom, arity) = store[rule.head].into() else {
                panic!("rule head is not compound term")
            };
            RuleHead(atom, arity) == head
        })
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Checkpoint {
    stack_pos: Addr,
    rules_pos: usize,
    free_atom: Atom,
}

pub mod builtin_atoms {
    use crate::v2::stack::Atom;

    /// Lowest reserved Atom, atoms above this may not be used by user definitions.
    pub const RESERVED_LIMIT: Atom = FACT;

    /// Rule compound: holds pointers to the head and tail of the stored rule
    pub const FACT: Atom = Atom::new(0xFFFF_FFF0);
    /// Fact compound: holds one pointer to the fact
    pub const RULE: Atom = Atom::new(0xFFFF_FFF1);
    /// Conjunction compound: proving this requires proving all arguments
    pub const CONJ: Atom = Atom::new(0xFFFF_FFF2);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rule {
    /// Address of the rule compound, which also must be the starting address of all rule data in
    /// memory.
    pub head: Addr,
    pub tail: Option<Addr>,
    /// Address one past the last rule word.
    pub end: Addr,
}

impl Rule {
    pub fn head_end(&self) -> Addr {
        self.tail.unwrap_or(self.end)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RuleHead(pub Atom, pub Arity);

#[cfg(test)]
mod tests {
    use crate::v2::solver::query_dfs;
    use crate::v2::stack::{Arity, DecodedWord};

    use super::{builtin_atoms, Universe};

    #[test]
    fn simple_rules() {
        tracing_subscriber::fmt::init();

        let mut u = Universe::new();

        let parent = u.reserve_atom();
        let grandparent = u.reserve_atom();
        let alice = u.reserve_atom();
        let bob = u.reserve_atom();
        let clive = u.reserve_atom();
        let eve = u.reserve_atom();

        u.add_rule(|stack| {
            let p = stack.alloc_zeroed_range(3);
            stack[p] = DecodedWord::App(parent, Arity::new(2)).into();
            stack[p.offset(1)] = DecodedWord::App(alice, Arity::new(0)).into();
            stack[p.offset(2)] = DecodedWord::App(bob, Arity::new(0)).into();
            (p, None)
        });
        u.add_rule(|stack| {
            let p = stack.alloc_zeroed_range(3);
            stack[p] = DecodedWord::App(parent, Arity::new(2)).into();
            stack[p.offset(1)] = DecodedWord::App(eve, Arity::new(0)).into();
            stack[p.offset(2)] = DecodedWord::App(alice, Arity::new(0)).into();
            (p, None)
        });
        u.add_rule(|stack| {
            let p = stack.alloc_zeroed_range(3);
            stack[p] = DecodedWord::App(parent, Arity::new(2)).into();
            stack[p.offset(1)] = DecodedWord::App(clive, Arity::new(0)).into();
            stack[p.offset(2)] = DecodedWord::App(alice, Arity::new(0)).into();
            (p, None)
        });
        u.add_rule(|stack| {
            let head = stack.alloc_zeroed_range(3);
            stack[head] = DecodedWord::App(grandparent, Arity::new(2)).into();

            let tail = stack.alloc_zeroed_range(3);
            stack[tail] = DecodedWord::App(builtin_atoms::CONJ, Arity::new(2)).into();

            let p1 = stack.alloc_zeroed_range(3);
            stack[p1] = DecodedWord::App(parent, Arity::new(2)).into();
            stack[p1.offset(1)] = DecodedWord::Ptr(Some(head.offset(1))).into();
            // offset 2 is unbound

            let p2 = stack.alloc_zeroed_range(3);
            stack[p2] = DecodedWord::App(parent, Arity::new(2)).into();
            stack[p2.offset(1)] = DecodedWord::Ptr(Some(p1.offset(2))).into();
            stack[p2.offset(2)] = DecodedWord::Ptr(Some(head.offset(2))).into();

            stack[tail.offset(1)] = DecodedWord::Ptr(Some(p1)).into();
            stack[tail.offset(2)] = DecodedWord::Ptr(Some(p2)).into();

            (head, Some(tail))
        });

        let mut s = query_dfs(&mut u, |stack| {
            let head = stack.alloc_zeroed_range(3);
            stack[head] = DecodedWord::App(grandparent, Arity::new(2)).into();
            stack[head.offset(2)] = DecodedWord::App(bob, Arity::new(0)).into();
            head
        });

        let mut solutions = 0;
        loop {
            if s.is_solution() {
                solutions += 1;
            }
            if !s.next_state() {
                break;
            }
        }
        // TODO: actually make sure we can extract and check solution terms
        assert_eq!(solutions, 2);
    }
}
