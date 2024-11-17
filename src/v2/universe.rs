//! The universe holds the current knowledge in the form of facts and rules.

use super::stack::{Addr, Arity, Atom, DecodedWord, FrozenStack, Stack};

/// The universe holds the facts and rules that are defined.
///
/// Atoms are represented as [`Atom`] values, i.e. integers that can be uniquely allocated in a
/// given universe via [`Universe::reserve_atom`]. If textual atoms are desired, the user has to
/// keep the mapping between strings and [`Atom`]s elsewhere.
///
/// TODO: implement higher-level interface for this.
#[derive(Debug, Clone)]
pub struct Universe {
    store: Stack,
    rules: Vec<Rule>,
    free_atom: Atom,
}

impl Universe {
    /// Create a new empty universe.
    pub fn new() -> Self {
        Self {
            store: Stack::new(),
            rules: Vec::new(),
            free_atom: Atom::new(0),
        }
    }

    /// Freeze the stack of this universe in its current state, and provide it for manipulation
    /// through a query engine.
    ///
    /// This allows the query engine to reuse the stack, and thus reference data in it, without
    /// having to make a copy, because the original data will be untouched.
    ///
    /// TODO: investigate if just copying is maybe cheaper after all
    pub fn freeze_for_query(&mut self) -> (RulesQuery<'_>, FrozenStack<'_>) {
        (RulesQuery { rules: &self.rules }, self.store.freeze())
    }

    /// Reserve a new unused atom.
    ///
    /// # Panics
    ///
    /// This panics if more than [`builtin_atoms::RESERVED_LIMIT`] atoms have been reserved.
    pub fn reserve_atom(&mut self) -> Atom {
        assert!(
            self.free_atom < builtin_atoms::RESERVED_LIMIT,
            "atom overflow"
        );
        let ret = self.free_atom;
        self.free_atom = Atom::new(self.free_atom.into_raw() + 1);
        ret
    }

    /// Add a rule or fact (i.e. a rule without tail that is thus always true) to the universe.
    ///
    /// The provided closure receives the stack on which it needs to construct the term, and needs
    /// to return the address where the rule head is allocated, and optionally the address where the
    /// rule tail is allocated.
    ///
    /// The allocations need to fulfill the following creteria:
    /// 1. The head of the rule must be the first allocation.
    /// 2. Pointers in the head may only point to other stack cells of the head.
    /// 3. The tail allocation must immediately follow the head allocation.
    /// 4. Pointers in the tail may only point to other stack cells in the head or tail.
    ///
    /// TODO: the first address should always be the current top of the stack
    ///
    pub fn add_rule(&mut self, build: impl FnOnce(&mut FrozenStack<'_>) -> (Addr, Option<Addr>)) {
        // Allocate head and tail on a temporarily frozen stack, so that existing data is protected
        // against manipulation.
        let mut builder_stack = self.store.freeze();
        let (head, tail) = build(&mut builder_stack);
        builder_stack.refreeze();
        drop(builder_stack);

        let top = self.store.top();

        // Validate pointers stay within bounds
        // #[cfg(debug_assertions)]
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

    /// Remember the current state of the universe, so that it can later be reverted to.
    ///
    /// Since a universe can only ever be added to with [`Universe::add_rule`] and
    /// [`Universe::reserve_atom`], checkpoints follow a stack semantic: Restoring a checkpoint
    /// discards all data added after the checkpoint.
    ///
    /// That means, restoring a later checkpoint after an earlier checkpoint will have no effect.
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            stack_pos: self.store.top(),
            rules_pos: self.rules.len(),
            free_atom: self.free_atom,
        }
    }

    /// Discard all data added to the universe since the creation of the checkpoint.
    ///
    /// Restoring a later checkpoint after already restoring an earlier one has no effect.
    pub fn restore(&mut self, checkpoint: Checkpoint) {
        self.store.free(checkpoint.stack_pos);
        self.rules.truncate(checkpoint.rules_pos);
        self.free_atom = checkpoint.free_atom;
    }
}

/// Lookup data structure for finding rules matching a certain head (defined by atom and arity).
///
/// TODO: investigate performance impact of linear search vs building a lookup data structure
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

/// Marker capturing the state of the universe at a certain point, so that it can later be reverted
/// back to that state.
///
/// This captures:
/// - The definitions on the stack.
/// - The defined rules.
/// - The next free atom value that can be reserved.
///
/// This can be useful for varying parts of the universe for different queries, while keeping the
/// base definitions shared.
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
