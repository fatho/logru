use tracing::trace;

use crate::v2::universe::RuleHead;

use super::stack::{Addr, Arity, Atom, DecodedWord, FrozenStack, Word};
use super::universe::{builtin_atoms, Rule, RulesQuery, Universe};

pub fn query_dfs<'u>(
    universe: &'u mut Universe,
    build_query: impl FnOnce(&mut FrozenStack<'u>) -> Addr,
) -> Solver<'u> {
    let (rules, mut stack) = universe.freeze_for_query();
    let query = build_query(&mut stack);
    let initial_state = SearchState {
        unresolved_goals: vec![query],
        stack,
        assignments: vec![],
    };
    Solver {
        state: initial_state,
        rules,
        alternatives: vec![],
        checkpoints: vec![],
    }
}

pub struct Solver<'u> {
    /// Currently visited search state
    state: SearchState<'u>,
    /// Currently defined rules used for reasoning
    rules: RulesQuery<'u>,
    /// Alternatives we have yet to try
    ///
    /// NOTE: In the future, these could be an enum type with different kinds of alternatives for
    /// custom predicates
    alternatives: Vec<Rule>,
    /// Checkpoints used for backtracking the search
    checkpoints: Vec<SolveCheckpoint>,
}

struct SolveCheckpoint {
    alternative_len: usize,
    state_checkpoint: StateCheckpoint,
}

impl<'u> Solver<'u> {
    pub fn is_solution(&self) -> bool {
        self.state.unresolved_goals.is_empty()
    }

    /// Advance to the next state.
    ///
    /// Returns whether more states can be explored after that.
    pub fn next_state(&mut self) -> bool {
        if let Some((goal, checkpoint)) = self.state.pop_goal() {
            self.checkpoints.push(SolveCheckpoint {
                alternative_len: self.alternatives.len(),
                state_checkpoint: checkpoint,
            });

            let (goal_addr, goal_term) = self.state.deref_follow(goal);

            trace!("trying goal: {goal:?} => {goal_term:?}@{goal_addr:?}");

            match goal_term {
                DerefTerm::Free => {
                    // Free variables are vacuously fulfilled
                    return true;
                }
                DerefTerm::App(atom, arity) => {
                    match atom {
                        // Expand conjunction terms into individual goals
                        builtin_atoms::CONJ => {
                            trace!("decomposed cojunction");
                            // The next `arity` terms on the stack become goals
                            self.state
                                .unresolved_goals
                                .extend(goal.arg_iter(arity).rev());
                            return true;
                        }
                        _ => {
                            trace!("decomposed user rule");
                            // TODO: look up rule definitions by `atom/arity` and append them to
                            // `alternatives` in reverse order (so that the first definition is on
                            // top of the stack, and thus picked first)
                            self.alternatives.extend(
                                self.rules
                                    .lookup(&self.state.stack, RuleHead(atom, arity))
                                    .rev(),
                            );

                            if self.resume(Resume::First) {
                                return true;
                            }
                        }
                    }
                }
            }
        } else {
            // If there are no more goals, try next alternative of top-most goal
            if self.resume(Resume::Retry) {
                return true;
            }
        }

        // If nothing matches, backtrack, until we can
        while let Some(current) = self.checkpoints.pop() {
            // At this point, we should have already exhausted all the alternatives at the current
            // checkpoint, otherwise we wouldn't be here
            assert_eq!(self.alternatives.len(), current.alternative_len);
            self.state.backtrack(current.state_checkpoint);

            if self.resume(Resume::Retry) {
                return true;
            }
        }

        // No satisfiable goals left and nothing to back track
        false
    }

    fn resume(&mut self, mut mode: Resume) -> bool {
        let Some(current_checkpoint) = self.checkpoints.last() else {
            trace!("no more checkpoints");
            return false;
        };
        while self.alternatives.len() > current_checkpoint.alternative_len {
            match mode {
                Resume::First => mode = Resume::Retry,
                Resume::Retry => {
                    // Reset state for all but the first iterations
                    self.state.retry(&current_checkpoint.state_checkpoint);
                }
            }
            let goal = current_checkpoint.state_checkpoint.goal;
            let rule = self.alternatives.pop().expect("existence asserted above");
            trace!("trying rule {rule:?} for goal {goal:?}");
            let result = self.state.unify_rule(goal, rule);
            trace!(
                "unification done with outcome {result:?} and stack {:?}",
                self.state.stack.debug_decoded()
            );

            match result {
                UnifyRule::Fail => {
                    // try next
                }
                UnifyRule::Fact => {
                    return true;
                }
                UnifyRule::Rule(addr) => {
                    self.state.unresolved_goals.push(addr);
                    return true;
                }
            }
        }
        // No more alternatives left
        false
    }
}

/// From what state we are resuming a checkpoint.
#[derive(Debug, Clone, Copy)]
enum Resume {
    /// The checkpoint is resumed for the first time
    First,
    /// The checkpoint is resumed as a retry
    Retry,
}

struct SearchState<'u> {
    /// Goals not yet solved
    unresolved_goals: Vec<Addr>,
    /// Stack holding data and variables
    stack: FrozenStack<'u>,
    /// Variables assigned so far (used for undoing assignments)
    assignments: Vec<Addr>,
}

#[derive(Debug)]
struct StateCheckpoint {
    goal: Addr,
    unresolved_len: usize,
    assignment_len: usize,
    stack: Addr,
}

impl<'u> SearchState<'u> {
    fn pop_goal(&mut self) -> Option<(Addr, StateCheckpoint)> {
        let goal = self.unresolved_goals.pop()?;
        let checkpoint = StateCheckpoint {
            goal,
            unresolved_len: self.unresolved_goals.len(),
            assignment_len: self.assignments.len(),
            stack: self.stack.top(),
        };
        Some((goal, checkpoint))
    }

    fn deref_follow(&mut self, addr: Addr) -> (Addr, DerefTerm) {
        let mut prev = addr;
        let mut cur = addr;
        loop {
            match DecodedWord::from(self.stack[cur]) {
                DecodedWord::Ptr(Some(next)) => {
                    // TODO: is there a better way for path compression?
                    self.stack[prev] = self.stack[cur];
                    prev = cur;
                    cur = next;
                }
                DecodedWord::Ptr(None) => return (cur, DerefTerm::Free),
                DecodedWord::App(atom, arity) => return (cur, DerefTerm::App(atom, arity)),
            }
        }
    }

    /// Reset state to the start of the goal, so that we are ready to try another alternative.
    fn retry(&mut self, checkpoint: &StateCheckpoint) {
        self.unresolved_goals.truncate(checkpoint.unresolved_len);
        for addr in self.assignments.drain(checkpoint.assignment_len..) {
            self.stack[addr] = Word::null_ptr();
        }
        self.stack.free(checkpoint.stack);
    }

    /// Backtrack on the last goal, so that we can try earlier alternatives.
    fn backtrack(&mut self, checkpoint: StateCheckpoint) {
        // Same as retrying, but we also push the goal itself back
        self.retry(&checkpoint);
        self.unresolved_goals.push(checkpoint.goal);
    }

    fn unify(&mut self, left: Addr, right: Addr) -> bool {
        let (left_addr, left_term) = self.deref_follow(left);
        let (right_addr, right_term) = self.deref_follow(right);

        trace!("unifying {left:?}=>{left_term:?}@{left_addr:?} with {right:?}=>{right_term:?}@{right_addr:?}");

        match (left_term, right_term) {
            (DerefTerm::Free, DerefTerm::Free) => match left_addr.cmp(&right_addr) {
                // Point from higher to lower variable
                std::cmp::Ordering::Less => self.set_var(right_addr, left_addr),
                std::cmp::Ordering::Greater => self.set_var(left_addr, right_addr),
                std::cmp::Ordering::Equal => {
                    // Same variable, nothing to do
                    true
                }
            },
            // Set free variable to term
            (DerefTerm::Free, DerefTerm::App(_, _)) => self.set_var(left_addr, right_addr),
            (DerefTerm::App(_, _), DerefTerm::Free) => self.set_var(right_addr, left_addr),
            // Compare heads and args
            (DerefTerm::App(lat, lar), DerefTerm::App(rat, rar)) => {
                if lat == rat && lar == rar {
                    // check arguments
                    left_addr
                        .arg_iter(lar)
                        .zip(right_addr.arg_iter(rar))
                        .all(|(left_arg, right_arg)| self.unify(left_arg, right_arg))
                } else {
                    false
                }
            }
        }
    }

    /// Assign a value to a variable and record this operation in the undo log. A variable may only
    /// be assigned once, and the value may not contain the variable in question in order to guard
    /// against infinite terms.
    fn set_var(&mut self, var: Addr, target: Addr) -> bool {
        debug_assert_eq!(self.stack[var], Word::null_ptr());

        if self.occurs(var, target) {
            return false;
        }

        self.stack[var] = DecodedWord::Ptr(Some(target)).into();
        self.assignments.push(var);

        true
    }

    /// Check whether the variable represented by address `var` is referenced from within the term
    /// rooted at address `term`.
    fn occurs(&mut self, var: Addr, term: Addr) -> bool {
        // TODO: keep allocation around for next time
        let mut todo = vec![term];
        while let Some(term) = todo.pop() {
            if term == var {
                return true;
            }
            match DecodedWord::from(self.stack[term]) {
                DecodedWord::Ptr(addr) => todo.extend(addr),
                DecodedWord::App(_, arity) => todo.extend(term.arg_iter(arity)),
            }
        }
        false
    }

    fn unify_rule(&mut self, goal: Addr, rule: Rule) -> UnifyRule {
        // Instantiate rule head
        let new_head = self.instantiate(rule.head, rule.head_end());
        // try unifying head
        if self.unify(goal, new_head) {
            if let Some(tail) = rule.tail {
                let new_tail = self.instantiate(tail, rule.end);
                UnifyRule::Rule(new_tail)
            } else {
                UnifyRule::Fact
            }
        } else {
            UnifyRule::Fail
        }
    }

    fn instantiate(&mut self, start: Addr, end: Addr) -> Addr {
        // Instantiate rule head
        let new_start = self.stack.copy_range(start, end);
        // Adjust pointers
        let offset = new_start.into_raw() - start.into_raw();
        let new_end = end.offset(offset);
        for i in new_start.range_iter(new_end) {
            match DecodedWord::from(self.stack[i]) {
                DecodedWord::Ptr(addr) => {
                    if let Some(ptr) = addr {
                        // adjust pointer
                        self.stack[i] = DecodedWord::Ptr(Some(ptr.offset(offset))).into();
                    }
                }
                DecodedWord::App(_, _) => {
                    // nothing to fix
                }
            }
        }
        new_start
    }
}

/// The result of dereferencing an [`Addr`] to a term.
#[derive(Debug, Clone, Copy)]
enum DerefTerm {
    Free,
    App(Atom, Arity),
}

#[derive(Debug, Clone, Copy)]
enum UnifyRule {
    /// Unification failed
    Fail,
    /// Unification succeeded without new goal term,
    Fact,
    /// Unification succeeded with a new replacement goal term
    Rule(Addr),
}
