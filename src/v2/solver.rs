use super::stack::{Addr, DecodedWord, Stack, Word};
use super::universe::builtin_atoms;

pub struct Solver {
    /// Currently visited search state
    state: SearchState,
    /// Alternatives we have yet to try
    alternatives: Vec<Addr>,
    /// Checkpoints used for backtracking the search
    past_checkpoints: Vec<SolveCheckpoint>,
    current_checkpoint: SolveCheckpoint,
}

struct SolveCheckpoint {
    alternative_len: usize,
    state_checkpoint: StateCheckpoint,
}

impl Solver {
    pub fn is_solution(&self) -> bool {
        self.state.unresolved_goals.is_empty()
    }

    /// Advance to the next state.
    ///
    /// Returns whether more states can be explored after that.
    pub fn next_state(&mut self) -> bool {
        if let Some((goal, checkpoint)) = self.state.pop_goal() {
            // Make new checkpoint current:
            let previous = std::mem::replace(
                &mut self.current_checkpoint,
                SolveCheckpoint {
                    alternative_len: self.alternatives.len(),
                    state_checkpoint: checkpoint,
                },
            );
            self.past_checkpoints.push(previous);

            match DecodedWord::from(self.state.stack[goal]) {
                // TODO: theoretically, we could just follow the variable here until we find a
                // non-variable or a unbound variable
                DecodedWord::Ptr(_) => panic!("variable goals not supported"),
                DecodedWord::App(atom, arity) => {
                    match atom {
                        // Expand conjunction terms into individual goals
                        builtin_atoms::CONJ => {
                            // The next `arity` terms on the stack become goals
                            self.state
                                .unresolved_goals
                                .extend(goal.arg_iter(arity).rev());
                            return true;
                        }
                        _ => {
                            todo!("look up as rule");
                            // TODO: look up rule definitions by `atom/arity` and append them to
                            // `alternatives`
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
        while let Some(previous) = self.past_checkpoints.pop() {
            let old_current = std::mem::replace(&mut self.current_checkpoint, previous);
            // At this point, we should have already exhausted all the alternatives at the current
            // checkpoint, otherwise we wouldn't be here
            assert_eq!(self.alternatives.len(), old_current.alternative_len);
            self.state.backtrack(old_current.state_checkpoint);

            if self.resume(Resume::Retry) {
                return true;
            }
        }

        // No satisfiable goals left and nothing to back track
        false
    }

    fn resume(&mut self, mut mode: Resume) -> bool {
        while self.alternatives.len() > self.current_checkpoint.alternative_len {
            match mode {
                Resume::First => mode = Resume::Retry,
                Resume::Retry => {
                    // Reset state for all but the first iterations
                    self.state.retry(&self.current_checkpoint.state_checkpoint);
                }
            }
            let alt = self.alternatives.pop().expect("existence asserted above");
            // TODO: instantiate rule head
            // TODO: unify rule head
            // TODO: instantiate rule tail
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

struct SearchState {
    /// Goals not yet solved
    unresolved_goals: Vec<Addr>,
    /// Stack holding data and variables
    stack: Stack,
    /// Variables assigned so far (used for undoing assignments)
    assignments: Vec<Addr>,
}

#[derive(Debug)]
struct StateCheckpoint {
    goal: Addr,
    unresolved_len: usize,
    assignment_len: usize,
    stack_limit: Addr,
}

impl SearchState {
    fn pop_goal(&mut self) -> Option<(Addr, StateCheckpoint)> {
        let goal = self.unresolved_goals.pop()?;
        let checkpoint = StateCheckpoint {
            goal,
            unresolved_len: self.unresolved_goals.len(),
            assignment_len: self.assignments.len(),
            stack_limit: self.stack.top(),
        };
        Some((goal, checkpoint))
    }

    /// Reset state to the start of the goal, so that we are ready to try another alternative.
    fn retry(&mut self, checkpoint: &StateCheckpoint) {
        self.unresolved_goals.truncate(checkpoint.unresolved_len);
        for addr in self.assignments.drain(checkpoint.assignment_len..) {
            self.stack[addr] = Word::null_ptr();
        }
        self.stack.free(checkpoint.stack_limit);
    }

    /// Backtrack on the last goal, so that we can try earlier alternatives.
    fn backtrack(&mut self, checkpoint: StateCheckpoint) {
        // Same as retrying, but we also push the goal itself back
        self.retry(&checkpoint);
        self.unresolved_goals.push(checkpoint.goal);
    }
}