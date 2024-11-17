//! The universe holds the current knowledge in the form of facts and rules.

use super::stack::{Addr, Arity, Atom, FrozenStack, Stack, Word};

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
                if let Word::Ptr(Some(addr)) = self.store[p] {
                    assert!(
                        addr >= head && addr < head_end,
                        "variables in head must only point inside head"
                    );
                }
            }
            if let Some(tail) = tail {
                for p in tail.range_iter(top) {
                    if let Word::Ptr(Some(addr)) = self.store[p] {
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
            let Word::App(atom, arity) = store[rule.head] else {
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

/// Hold constants for built-in atoms that are available in every universe.
pub mod builtin_atoms {
    use crate::v2::stack::Atom;

    /// Lowest reserved Atom, atoms above this may not be used by user definitions.
    pub const RESERVED_LIMIT: Atom = CONJ;

    /// This atom designates a conjunction compound term of arbitrary arity.
    ///
    /// A conjunction term is proven by proving all of its argument terms.
    /// The empty conjunction is vacuously true.
    pub const CONJ: Atom = Atom::new(0xFFFF_FFFF);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rule {
    /// Address of the rule compound, which also must be the starting address of all rule data in
    /// memory.
    pub head: Addr,
    /// Start of the rule tail within the rule allocation.
    pub tail: Option<Addr>,
    /// Address one past the last rule word.
    pub end: Addr,
}

impl Rule {
    /// The end of the head allocation in this rule. It is either the start of the tail, if there is
    /// one, or the end of the entire allocation.
    pub fn head_end(&self) -> Addr {
        self.tail.unwrap_or(self.end)
    }
}

/// Type identifying the head of a rule, represented by the corresponding atom and arity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RuleHead(pub Atom, pub Arity);

#[cfg(test)]
mod tests {
    use crate::v2::solver::query_dfs;
    use crate::v2::stack::{Arity, Word};

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
            stack[p] = Word::App(parent, Arity::new(2));
            stack[p.offset(1)] = Word::App(alice, Arity::new(0));
            stack[p.offset(2)] = Word::App(bob, Arity::new(0));
            (p, None)
        });
        u.add_rule(|stack| {
            let p = stack.alloc_zeroed_range(3);
            stack[p] = Word::App(parent, Arity::new(2));
            stack[p.offset(1)] = Word::App(eve, Arity::new(0));
            stack[p.offset(2)] = Word::App(alice, Arity::new(0));
            (p, None)
        });
        u.add_rule(|stack| {
            let p = stack.alloc_zeroed_range(3);
            stack[p] = Word::App(parent, Arity::new(2));
            stack[p.offset(1)] = Word::App(clive, Arity::new(0));
            stack[p.offset(2)] = Word::App(alice, Arity::new(0));
            (p, None)
        });
        u.add_rule(|stack| {
            let head = stack.alloc_zeroed_range(3);
            stack[head] = Word::App(grandparent, Arity::new(2));

            let tail = stack.alloc_zeroed_range(3);
            stack[tail] = Word::App(builtin_atoms::CONJ, Arity::new(2));

            let p1 = stack.alloc_zeroed_range(3);
            stack[p1] = Word::App(parent, Arity::new(2));
            stack[p1.offset(1)] = Word::Ptr(Some(head.offset(1)));
            // offset 2 is unbound

            let p2 = stack.alloc_zeroed_range(3);
            stack[p2] = Word::App(parent, Arity::new(2));
            stack[p2.offset(1)] = Word::Ptr(Some(p1.offset(2)));
            stack[p2.offset(2)] = Word::Ptr(Some(head.offset(2)));

            stack[tail.offset(1)] = Word::Ptr(Some(p1));
            stack[tail.offset(2)] = Word::Ptr(Some(p2));

            (head, Some(tail))
        });

        let mut s = query_dfs(&mut u, |stack| {
            let head = stack.alloc_zeroed_range(3);
            stack[head] = Word::App(grandparent, Arity::new(2));
            stack[head.offset(2)] = Word::App(bob, Arity::new(0));
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
