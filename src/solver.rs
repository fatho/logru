//! # A DFS solver for queries
//!
//! This module contains the bits and pieces necessary for proving queries in a [crate::Universe].
//! For now, Logru only supports a single solving strategy, [query_dfs].

#[cfg(test)]
mod test;

use crate::{
    ast::{self, Query, Sym, Var},
    term_arena::{self, TermArena},
    universe::{CompiledRule, CompiledRuleDb, Universe},
};

/// Solve queries against the universe using a depth-first-search.
///
/// A depth-first search is very efficient for finite search spaces. The caveat is that this
/// approach is not complete, i.e. it might recurse endlessly in infinite search spaces where the
/// rules are left-recursive.
///
/// For a usage example, see the [top-level example](crate#example).
pub fn query_dfs<'a, B>(universe: &'a Universe, builtins: B, query: &Query) -> SolutionIter<'a, B>
where
    B: BuiltinHandler,
{
    // determine how many goal variables we need to allocate
    let max_var = query.count_var_slots();

    let mut solution = SolutionState::new(max_var);

    let mut scratch = Vec::new();

    // initialize solver
    SolutionIter {
        rules: universe.compiled_rules(),
        unresolved_goals: query
            .goals
            .iter()
            .rev() // reverse so that the leftmost goal ends up on the top of the stack
            .map(|app| solution.terms.insert_ast_appterm(&mut scratch, app))
            .collect(),
        checkpoints: vec![],
        solution,
        builtin_state: builtins,
    }
}

pub trait BuiltinHandler {
    type Choice;

    fn lookup_predicate(&mut self, head: Sym) -> Option<Self::Choice>;

    fn next_choice(
        &mut self,
        choice: &mut Self::Choice,
        solution: &mut SolutionState,
        goal: term_arena::TermId,
    ) -> bool;
}

pub struct Plain;

impl BuiltinHandler for Plain {
    type Choice = NoChoice;

    fn next_choice(
        &mut self,
        choice: &mut Self::Choice,
        _: &mut SolutionState,
        _: term_arena::TermId,
    ) -> bool {
        match *choice {}
    }

    fn lookup_predicate(&mut self, _: Sym) -> Option<Self::Choice> {
        None
    }
}

impl<B: BuiltinHandler> BuiltinHandler for &mut B {
    type Choice = B::Choice;

    fn lookup_predicate(&mut self, head: Sym) -> Option<Self::Choice> {
        (*self).lookup_predicate(head)
    }

    fn next_choice(
        &mut self,
        choice: &mut Self::Choice,
        solution: &mut SolutionState,
        goal: term_arena::TermId,
    ) -> bool {
        (*self).next_choice(choice, solution, goal)
    }
}

/// Used for the [`Plain`] builtin to indicate that it does not provide extra types of choices.
pub enum NoChoice {}

/// Iterator over all solutions for a given query.
///
/// There are two ways of using this type to explore the solution space:
/// 1. Via the provided iterator implementation which returns all valid solutions to the query.
/// 2. Using the [SolutionIter::step] method which returns after each intermediate step as well.
///    This can be useful for implementing cancellation.
pub struct SolutionIter<'s, B: BuiltinHandler> {
    /// The rule database that can be used for resolving queries.
    rules: &'s CompiledRuleDb,
    /// Goals that still need to be solved
    unresolved_goals: Vec<term_arena::TermId>,
    /// Checkpoints created for past decisions, used for backtracking
    checkpoints: Vec<Checkpoint<'s, B>>,
    /// Current (partial) solution
    solution: SolutionState,
    /// State needed for evaluating builtins
    builtin_state: B,
}

/// A solver checkpoint that can be used for backtracking to an earlier choice point.
struct Checkpoint<'s, B: BuiltinHandler> {
    /// The goal for which we needed to make the choice.
    goal: term_arena::TermId,
    /// The symbol of the rule we're matching with.
    choice: ChoicePoint<'s, B>,
    /// The number of unresolved goals at the time of the choice. Used for popping goals from the
    /// stack that were added by a matching rule.
    goals_checkpoint: usize,
    /// Checkpoint of the partial solution to undo any assignments that have been made since this
    /// choice point.
    solution_checkpoint: SolutionCheckpoint,
}

/// Representation of the choices we have at a given checkpoint.
enum ChoicePoint<'s, B: BuiltinHandler> {
    /// Exactly one choice, proceeding
    True,
    /// No choice, failing
    False,
    /// Zero or more rule heads to match against
    Rule(RuleChoice<'s>),
    /// Builtin-defined choice
    Builtin(B::Choice),
}

/// Represents a choice between multiple rule definitions with a matching head.
struct RuleChoice<'s> {
    remaining: &'s [CompiledRule],
}

/// Status of the solution iterator after performing a step.
///
/// See [SolutionIter::step] for a usage example.
pub enum Step {
    /// The solver found a solution. Call [SolutionIter::get_solution] for obtaining the actual
    /// variable assignment.
    Yield,
    /// The solver made progress but there is no solution yet. Call [SolutionIter::step] again.
    Continue,
    /// The solver exhausted the solution space.
    Done,
}

impl<'s, B: BuiltinHandler> SolutionIter<'s, B> {
    /// Perform a single solver step.
    ///
    /// This method can be used as more fine-grained means for traversing the solution space as
    /// opposed to using the iterator interface, as the process could be cancelled at any choice
    /// point, not just when a solution was finally found.
    ///
    /// # Example
    ///
    /// The following snippet using the definitions from the [top-level Example][crate#example]
    /// section will enumerate all natural numbers (and thus never finish).
    ///
    /// ```
    /// # use logru::ast::{self, Rule};
    /// # use logru::solver::{Step, Plain};
    /// # let mut u = logru::Universe::new();
    /// # let s = u.alloc_symbol();
    /// # let z = u.alloc_symbol();
    /// # let is_natural = u.alloc_symbol();
    /// # let add = u.alloc_symbol();
    /// #
    /// # u.add_rule(Rule::fact(is_natural, vec![z.into()]));
    /// # u.add_rule(ast::forall(|[p]| {
    /// #     Rule::fact(is_natural, vec![ast::app(s, vec![p.into()])])
    /// #     .when(is_natural, vec![p.into()])
    /// # }));
    /// # let query = ast::exists(|[x]| {
    /// #     ast::Query::new(
    /// #         add,
    /// #         vec![
    /// #             x.into(),
    /// #             ast::app(s, vec![ast::app(s, vec![z.into()])]),
    /// #             ast::app(s, vec![ast::app(s, vec![ast::app(s, vec![z.into()])])]),
    /// #         ],
    /// #     )
    /// # });
    /// # use std::sync::Arc;
    /// # use std::sync::atomic::{self, AtomicBool};
    /// let interrupted = Arc::new(AtomicBool::new(false));
    /// // Pass `interrupted` off to somewhere else where it can be set when the search is cancelled
    /// # interrupted.store(true, atomic::Ordering::SeqCst);
    /// let mut solutions = logru::query_dfs(&u, Plain, &query);
    /// while ! interrupted.load(atomic::Ordering::SeqCst) {
    ///     match solutions.step() {
    ///         Step::Yield => println!("{:?}", solutions.get_solution()),
    ///         Step::Continue => continue,
    ///         Step::Done => break,
    ///     }
    /// }
    /// ```
    pub fn step(&mut self) -> Step {
        // When there are still unresolved goals left, we create a choice checkpoint for the
        // top-most one.
        if let Some(goal) = self.unresolved_goals.pop() {
            // resolve goal
            let (goal, goal_term) = self.solution.follow_vars(goal);
            let choice = match goal_term {
                term_arena::Term::Var(_) => {
                    // Free variable is vacuously true
                    ChoicePoint::True
                }
                term_arena::Term::App(functor, _) => self
                    .builtin_state
                    .lookup_predicate(functor)
                    .map(ChoicePoint::Builtin)
                    .unwrap_or_else(|| {
                        let rules = self.rules.rules_by_head(functor);
                        ChoicePoint::Rule(RuleChoice { remaining: rules })
                    }),
                term_arena::Term::Int(_) => {
                    // Integers cannot be resolved as goals
                    // TODO: we should probably log errors like this somewhere
                    ChoicePoint::False
                }
            };

            self.checkpoints.push(Checkpoint {
                goal,
                choice,
                solution_checkpoint: self.solution.checkpoint(),
                goals_checkpoint: self.unresolved_goals.len(),
            });
        }
        // Then we backtrack to the topmost checkpoint (which, in case we just added one above,
        // means that we likely don't actually need to backtrack at all) that still has a matching
        // alternative left to try.
        if self.resume_or_backtrack() {
            // Found a choice to commit to
            if self.unresolved_goals.is_empty() {
                // If no goals remain, we are done
                Step::Yield
            } else {
                // Otherwise, rinse & repeat with remaining goals
                Step::Continue
            }
        } else {
            // couldn't backtrack to any possible choice, we're done
            Step::Done
        }
    }

    /// Obtain a copy of the current assignment of the goal variables.
    ///
    /// Usually, this function should be called right after `step` returned `Step::Yield`. In taht
    /// case, it will return a valid solution to the query. It may be called at any point though,
    /// but the assignment will be incomplete and might not even be a part of a valid solution.
    ///
    /// The indexes in the resulting vector correspond to the [ordinals](crate::ast::Var::ord) of
    /// the goal variables, i.e. the assignment for a variable `x: Var` is stored at index
    /// `x.ord()`.
    ///
    /// Note that even in valid solutions, not all variables need to have an assignment. For
    /// example, given the rule
    ///
    /// ```prolog
    /// anything(X).
    /// ```
    ///
    /// the query `anything(X)` will be true for any `X`, hence even a valid solution won't have an
    /// assignment for this variable.
    pub fn get_solution(&self) -> Vec<Option<ast::Term>> {
        self.solution.get_solution()
    }

    /// Try the next alternative of the top-most checkpoint and return whether we committed to a
    /// choice.
    ///
    /// If no remaining alternative matched, this function returns `false`, discards the checkpoint
    /// and puts the goal back onto the stack of unresolved goals. This allows us to continue our
    /// search from earlier checkpoints and potentially revisit this goal in a different context.
    fn resume_checkpoint(&mut self) -> bool {
        let checkpoint = self
            .checkpoints
            .last_mut()
            .expect("invariant: there is always a checkpoint when this is called");
        match &mut checkpoint.choice {
            ChoicePoint::True => {
                // True has just one alternative
                checkpoint.choice = ChoicePoint::False;
            }
            ChoicePoint::False => {}
            ChoicePoint::Rule(rule_choice) => {
                while let Some((first, rest)) = rule_choice.remaining.split_first() {
                    rule_choice.remaining = rest;
                    let result = self.solution.unify_rule(checkpoint.goal, first);
                    if let Some(goals) = result {
                        self.unresolved_goals.extend(goals);
                        return true;
                    } else {
                        drop(result);
                        self.solution.restore(&checkpoint.solution_checkpoint);
                    }
                }
            }
            ChoicePoint::Builtin(choice) => {
                // TODO: allow builtins to produce new goals
                if self
                    .builtin_state
                    .next_choice(choice, &mut self.solution, checkpoint.goal)
                {
                    return true;
                } else {
                    self.solution.restore(&checkpoint.solution_checkpoint);
                }
            }
        }
        // checkpoint exhausted, put goal back and discard
        let discarded = self.checkpoints.pop().expect("we know there is one here");
        self.unresolved_goals.push(discarded.goal);
        false
    }

    /// Backtrack to the first checkpoint that allows making a choice
    fn resume_or_backtrack(&mut self) -> bool {
        while let Some(checkpoint) = self.checkpoints.last() {
            // restore to topmost checkpoint
            self.solution.restore(&checkpoint.solution_checkpoint);
            self.unresolved_goals.truncate(checkpoint.goals_checkpoint);
            // then try to resume it
            if self.resume_checkpoint() {
                // Success, continue search
                return true;
            }
            // couldn't resume, the checkpoint was discarded, so we can simply loop to the next
        }
        false
    }
}

impl<'s, B: BuiltinHandler> Iterator for SolutionIter<'s, B> {
    type Item = Vec<Option<ast::Term>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                Step::Yield => break Some(self.get_solution()),
                Step::Continue => continue,
                Step::Done => break None,
            }
        }
    }
}

/// Auxilliary data structure holding a (partial) solution.
pub struct SolutionState {
    /// The current map of goal variables to their values, if any.
    variables: Vec<Option<term_arena::TermId>>,
    /// A log of assignment operations. Everytime a variable is assigned, it is recorded here.
    assignments: Vec<Var>,
    /// The number of initial goal variables that were present in the query.
    goal_vars: usize,
    /// Arena from which solution terms are allocated.
    terms: TermArena,
    // Temporary scratch memory used for computing the occurs check.
    occurs_stack: Vec<term_arena::TermId>,
}

struct SolutionCheckpoint {
    operations_checkpoint: usize,
    variables_checkpoint: usize,
    terms_checkpoint: term_arena::Checkpoint,
}

impl SolutionState {
    /// Create an initial solution state with just the (still) unassigned goal variables.
    fn new(goal_vars: usize) -> Self {
        Self {
            assignments: vec![],
            variables: vec![None; goal_vars],
            goal_vars,
            terms: TermArena::new(),
            occurs_stack: Vec::new(),
        }
    }

    /// Allocate more goal variables (which needs to be done when rules are instantiated).
    fn allocate_vars(&mut self, num_vars: usize) {
        self.variables.resize(self.variables.len() + num_vars, None);
    }

    /// Assign a value to a variable and record this operation in the undo log. A variable may only
    /// be assigned once, and the value may not contain the variable in question in order to guard
    /// against infinite terms.
    fn set_var(&mut self, var: Var, value: term_arena::TermId) -> bool {
        debug_assert!(self.variables[var.ord()].is_none());

        if self.occurs(var, value) {
            return false;
        }

        self.variables[var.ord()] = Some(value);
        self.assignments.push(var);

        true
    }

    /// Check whether the variable occurs inside the given term.
    fn occurs(&mut self, var: Var, mut term: term_arena::TermId) -> bool {
        loop {
            match self.terms.get_term(term) {
                term_arena::Term::Var(v) => {
                    if v == var {
                        // Found the variable, we clear the stack for an early exit
                        self.occurs_stack.clear();
                        return true;
                    }
                }
                term_arena::Term::App(_, args) => {
                    let terms = &self.terms;
                    self.occurs_stack
                        .extend(args.map(|arg_id| terms.get_arg(arg_id)))
                }
                term_arena::Term::Int(_) => {}
            }
            match self.occurs_stack.pop() {
                // More terms to check
                Some(next) => term = next,
                // No more terms to check, variable does not occur
                None => return false,
            }
        }
    }

    /// Create a checkpoint for undoing all operations that happened after the checkpoint.
    fn checkpoint(&self) -> SolutionCheckpoint {
        SolutionCheckpoint {
            operations_checkpoint: self.assignments.len(),
            variables_checkpoint: self.variables.len(),
            terms_checkpoint: self.terms.checkpoint(),
        }
    }

    /// Undo all operations that have been applied to the solution since the checkpoint was created.
    fn restore(&mut self, checkpoint: &SolutionCheckpoint) {
        // NOTE: we also potentially undo assignments of variables that would be truncated in the
        // next step, but profiling showed that it doesn't make a difference if we were to omit
        // those variables from the undo log.
        for var in self.assignments.drain(checkpoint.operations_checkpoint..) {
            self.variables[var.ord()] = None;
        }
        self.variables.truncate(checkpoint.variables_checkpoint);
        self.terms.release(&checkpoint.terms_checkpoint);
    }

    /// Convert a term from the internal arena to the AST representation.
    fn get_solution_term(&self, term: term_arena::TermId) -> ast::Term {
        match self.terms.get_term(term) {
            term_arena::Term::Var(v) => {
                if let Some(value) = &self.variables[v.ord()] {
                    self.get_solution_term(*value)
                } else {
                    ast::Term::Var(v)
                }
            }
            term_arena::Term::App(functor, args) => ast::Term::App(ast::AppTerm {
                functor,
                args: args
                    .map(|arg_id| self.get_solution_term(self.terms.get_arg(arg_id)))
                    .collect(),
            }),
            term_arena::Term::Int(val) => ast::Term::Int(val),
        }
    }

    /// Obtain a copy of the current assignment of the original goal variables.
    fn get_solution(&self) -> Vec<Option<ast::Term>> {
        self.variables
            .iter()
            .take(self.goal_vars)
            .map(|val| val.as_ref().map(|t| self.get_solution_term(*t)))
            .collect()
    }

    /// Follow the assignment of variables until reaching either an unassigned variable or an
    /// application term. Used by unification for applying substitution on-the-fly rather than
    /// needing to create a bunch of copies of terms.
    pub fn follow_vars(
        &self,
        mut id: term_arena::TermId,
    ) -> (term_arena::TermId, term_arena::Term) {
        loop {
            match self.terms.get_term(id) {
                term_arena::Term::Var(var) => {
                    if let Some(value) = &self.variables[var.ord()] {
                        id = *value;
                    } else {
                        return (id, term_arena::Term::Var(var));
                    }
                }
                term => return (id, term),
            }
        }
    }

    pub fn terms(&self) -> &TermArena {
        &self.terms
    }

    pub fn terms_mut(&mut self) -> &mut TermArena {
        &mut self.terms
    }

    /// Unify the given goal (sub) term with a rule (sub) term.
    ///
    /// # Returns
    ///
    /// When unification was succesul, `true` is returned, otherwise `false`. In case of a
    /// unification failure, the solution is in an undefined state, so a checkpoint must be used for
    /// restoring it to its pre-unification state if desired.
    pub fn unify(&mut self, goal_term: term_arena::TermId, rule_term: term_arena::TermId) -> bool {
        // Step 1: transitively dereference variable terms.
        // This is important so that substitutions become visible here.
        let (goal_term_id, goal_term) = self.follow_vars(goal_term);
        let (rule_term_id, rule_term) = self.follow_vars(rule_term);

        // Step 2: the actual unification
        match (goal_term, rule_term) {
            // variable with variable
            (term_arena::Term::Var(goal_var), term_arena::Term::Var(rule_var)) => {
                if goal_var != rule_var {
                    // Make one variable point to the other. This kind of chain is what
                    // `follow_vars` handles.
                    self.set_var(rule_var, goal_term_id)
                } else {
                    // The two variables are the same, nothing to be done here
                    true
                }
            }
            // variable with another term
            (term_arena::Term::Var(goal_var), _) => self.set_var(goal_var, rule_term_id),
            (_, term_arena::Term::Var(rule_var)) => self.set_var(rule_var, goal_term_id),
            // two application terms
            (
                term_arena::Term::App(goal_func, goal_args),
                term_arena::Term::App(rule_func, rule_args),
            ) => {
                // the terms must have the same functor symbol and the same arity
                if goal_func != rule_func {
                    return false;
                }
                if goal_args.len() != rule_args.len() {
                    return false;
                }

                // and all the arguments must unify as well
                goal_args.zip(rule_args).all(|(goal_arg, rule_arg)| {
                    self.unify(self.terms.get_arg(goal_arg), self.terms.get_arg(rule_arg))
                })
            }
            // two integer terms
            (term_arena::Term::Int(i1), term_arena::Term::Int(i2)) => i1 == i2,
            // incompatible types
            // TODO: we should probably log a type error
            (_, _) => false,
        }
    }

    /// Unify a goal term with a rule and return the new sub goals if the unification was
    /// successful.
    fn unify_rule<'a>(
        &mut self,
        goal_term: term_arena::TermId,
        rule: &'a CompiledRule,
    ) -> Option<impl Iterator<Item = term_arena::TermId> + 'a> {
        // add uninstantiated variables for the rule
        let var_offset = self.variables.len();
        self.allocate_vars(rule.var_slots());

        // instantiate head for now
        let (head, head_blueprint) = rule.head();
        let conv_rule_head = self.terms.instantiate_blueprint(head_blueprint, var_offset);
        let instantiated_rule_head = conv_rule_head(head);

        if self.unify(goal_term, instantiated_rule_head) {
            // instantiate tail terms
            let (tail, tail_blueprint) = rule.tail();
            let conv_rule_tail = self.terms.instantiate_blueprint(tail_blueprint, var_offset);
            // and return the updated term IDs (in reverse order) so that the originally leftmost
            // goal ends up on the top of the goal stack, and hence is processed next.
            Some(tail.iter().rev().map(move |tail| conv_rule_tail(*tail)))
        } else {
            None
        }
    }
}
