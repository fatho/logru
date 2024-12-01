//! # A DFS search through the solution space of a query.
//!
//! This module contains the bits and pieces necessary for solving queries by searching through the
//! solution space that is expanded using the given [`Resolver`].
//!
//!  For now, Logru only supports a single solving strategy, [query_dfs].

#[cfg(test)]
mod test;

use crate::{
    ast::{self, Query, Var},
    term_arena::{self, TermArena, TermId},
};

/// Solve queries against the universe using a depth-first-search.
///
/// A depth-first search is very efficient for finite search spaces. The caveat is that this
/// approach is not complete, i.e. it might recurse endlessly in infinite search spaces where the
/// rules are left-recursive.
///
/// For a usage example, see the [top-level example](crate#example).
pub fn query_dfs<R: Resolver>(resolver: R, query: &Query) -> SolutionIter<R> {
    // determine how many goal variables we need to allocate
    let max_var = query.count_var_slots();

    let mut solution = SolutionState::new(max_var);

    let mut scratch = Vec::new();

    // initialize solver
    SolutionIter {
        resolver,
        unresolved_goals: query
            .goals
            .iter()
            .rev() // reverse so that the leftmost goal ends up on the top of the stack
            .map(|app| solution.terms.insert_ast_term(&mut scratch, app))
            .map(|goal| GoalFrame { goal, cut_level: 0 })
            .collect(),
        checkpoints: vec![],
        solution,
    }
}

/// The resolver is responsible for solving goals, e.g. through unification of variables or
/// decomposing them into smaller goals.
pub trait Resolver {
    type Choice: std::fmt::Debug;

    fn resolve(
        &mut self,
        goal_id: term_arena::TermId,
        goal_term: term_arena::AppTerm,
        context: &mut ResolveContext,
    ) -> Option<Resolved<Self::Choice>>;

    fn resume(
        &mut self,
        choice: &mut Self::Choice,
        goal_id: term_arena::TermId,
        context: &mut ResolveContext,
    ) -> bool;
}

/// The interface into the search state that is provided to a [`Resolver`] for resolving goals.
pub struct ResolveContext<'c> {
    solution: &'c mut SolutionState,
    goal_stack: &'c mut Vec<GoalFrame>,
    checkpoint: &'c SolutionCheckpoint,
    goal_len: usize,
    cut_level: usize,
}

impl<'c> ResolveContext<'c> {
    /// Provides mutable access to the solution state.
    #[inline(always)]
    pub fn solution_mut(&mut self) -> &mut SolutionState {
        self.solution
    }

    /// Provides access to the solution state.
    #[inline(always)]
    pub fn solution(&self) -> &SolutionState {
        self.solution
    }

    /// Push an additional goal to the stack, to be resolved later.
    #[inline(always)]
    pub fn push_goal(&mut self, goal: term_arena::TermId) {
        self.goal_stack.push(GoalFrame {
            goal,
            cut_level: self.cut_level,
        });
    }

    /// Extend the goal stack from the provided iterator. The last item will end up on top of the
    /// stack, and thus the next goal to be resolved.
    #[inline(always)]
    pub fn extend_goals(&mut self, new_goals: impl Iterator<Item = term_arena::TermId>) {
        let level = self.cut_level;
        self.goal_stack.extend(new_goals.map(|goal| GoalFrame {
            goal,
            cut_level: level,
        }));
    }

    /// Reset the solution state to the current choice point.
    #[inline(always)]
    pub fn reset(&mut self) {
        self.goal_stack.truncate(self.goal_len);
        self.solution.restore(self.checkpoint);
    }
}

#[derive(Debug)]
pub enum Resolved<C> {
    /// The goal resolved to a single choice that was successfully applied to the state.
    Success,
    /// The goal resolved to multiple alternatives. The first was already applied to the state,
    /// while the remaining choice is captured in the type `C`.
    SuccessRetry(C),
}

impl<C> Resolved<C> {
    pub fn map_choice<C2>(self, f: impl FnOnce(C) -> C2) -> Resolved<C2> {
        match self {
            Resolved::Success => Resolved::Success,
            Resolved::SuccessRetry(c) => Resolved::SuccessRetry(f(c)),
        }
    }
}

impl<R: Resolver> Resolver for &mut R {
    type Choice = R::Choice;

    #[inline(always)]
    fn resolve(
        &mut self,
        goal_id: term_arena::TermId,
        goal_term: term_arena::AppTerm,
        context: &mut ResolveContext,
    ) -> Option<Resolved<Self::Choice>> {
        (*self).resolve(goal_id, goal_term, context)
    }

    #[inline(always)]
    fn resume(
        &mut self,
        choice: &mut Self::Choice,
        goal_id: term_arena::TermId,
        context: &mut ResolveContext,
    ) -> bool {
        (*self).resume(choice, goal_id, context)
    }
}

/// Iterator over all solutions for a given query.
///
/// There are two ways of using this type to explore the solution space:
/// 1. Via the provided iterator implementation which returns all valid solutions to the query.
/// 2. Using the [SolutionIter::step] method which returns after each intermediate step as well.
///    This can be useful for implementing cancellation.
#[derive(Debug)]
pub struct SolutionIter<R: Resolver> {
    /// The rule database that can be used for resolving queries.
    resolver: R,
    /// Goals that still need to be solved
    unresolved_goals: Vec<GoalFrame>,
    /// Checkpoints created for past decisions, used for backtracking
    checkpoints: Vec<Checkpoint<R>>,
    /// Current (partial) solution
    solution: SolutionState,
}

/// A solver checkpoint that can be used for backtracking to an earlier choice point.
#[derive(Debug)]
struct Checkpoint<R: Resolver> {
    /// The goal for which we needed to make the choice.
    goal: term_arena::TermId,
    /// The choice state of the resolver at this checkpoint. If there is no choice, the checkpoint
    /// cannot resume and the search will backtrack immediately.
    choice: Option<R::Choice>,
    /// The number of unresolved goals at the time of the choice. Used for popping goals from the
    /// stack that were added by a matching rule.
    goals_checkpoint: usize,
    /// Checkpoint of the partial solution to undo any assignments that have been made since this
    /// choice point.
    solution_checkpoint: SolutionCheckpoint,
    /// The cut-level associated with this checkpoint. Determined by the context in which it was
    /// executed.
    cut_level: usize,
}

impl<R: Resolver> Checkpoint<R> {
    /// Restore the original [`GoalFrame`] from this checkpoint, used for backtracking.
    fn restore_goal_frame(self) -> GoalFrame {
        GoalFrame {
            goal: self.goal,
            cut_level: self.cut_level,
        }
    }
}

/// A goal associated with extra information.
///
/// NOTE: When we need more information, it may no longer be practical to store frames inline, and
/// we may instead want to store the associated data in a deduplicated, refcounted manner.
#[derive(Debug)]
struct GoalFrame {
    /// The goal-term to solve
    goal: term_arena::TermId,
    /// The checkpoint index at which this goal was introduced. Used for search-space pruning via
    /// [`term_arena::Term::Cut`].
    cut_level: usize,
}

/// A single assignment of variables to terms.
///
/// The variables returned in this struture correspond to the goals via [ordinals](crate::ast::Var::ord).
/// i.e. the assignment for a variable `x: Var` is stored at index
/// `x.ord()`.
///
/// Names of variables are not stored here. They can be resolved using the matching Scope.
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
#[derive(PartialEq, Debug, Clone)]
pub struct Solution(pub Vec<Option<ast::Term>>);

impl Solution {
    /// Returns a reference to the vector containing all assignments of terms to variables.
    /// The vector's indices correspond to ordinals of the variables.
    pub fn vars(&self) -> &Vec<Option<ast::Term>> {
        &self.0
    }

    /// Iterates over all variables and their assigned terms.
    pub fn iter_vars(&self) -> impl Iterator<Item = (Var, Option<&ast::Term>)> {
        self.0
            .iter()
            .enumerate()
            .map(|(i, term)| (Var::from_ord(i), term.as_ref()))
    }

    /// Returns the term matching this variable
    pub fn get(&self, var: Var) -> Option<&ast::Term> {
        self.0[var.ord()].as_ref()
    }
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

impl<R: Resolver> SolutionIter<R> {
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
    /// # use logru::resolve::RuleResolver;
    /// # use logru::search::Step;
    /// # use logru::SymbolStorage;
    /// # let mut syms = logru::SymbolStore::new();
    /// # let mut r = logru::RuleSet::new();
    /// # let s = syms.get_or_insert_named("s");
    /// # let z = syms.get_or_insert_named("z");
    /// # let is_natural = syms.get_or_insert_named("is_natural");
    /// # let add = syms.get_or_insert_named("add");
    /// #
    /// # r.insert(Rule::fact(is_natural, vec![z.into()]));
    /// # r.insert(ast::forall(|[p]| {
    /// #     Rule::fact(is_natural, vec![ast::app(s, vec![p.into()])])
    /// #     .when(is_natural, vec![p.into()])
    /// # }));
    /// # let query = ast::exists(|[x]| {
    /// #     ast::Query::single_app(
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
    /// let resolver = RuleResolver::new(&r);
    /// let mut solutions = logru::query_dfs(resolver, &query);
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
        if let Some(goal_frame) = self.unresolved_goals.pop() {
            // resolve goal
            let goal_term = self.solution.terms.get_term(goal_frame.goal);
            let solution_checkpoint = self.solution.checkpoint();
            let goals_checkpoint = self.unresolved_goals.len();
            let mut context = ResolveContext {
                solution: &mut self.solution,
                goal_stack: &mut self.unresolved_goals,
                checkpoint: &solution_checkpoint,
                goal_len: goals_checkpoint,
                cut_level: self.checkpoints.len(),
            };
            let resolved = match goal_term {
                // Variables are an implicit call to the predicate they are bound to
                term_arena::Term::Var(v) => {
                    if let Some(new_goal) = context.solution.get_var(v) {
                        // Replace goal
                        context.push_goal(new_goal);
                    }
                    // Unbound variables are vacuously true
                    Some(Resolved::Success)
                }
                // App terms are resolved
                term_arena::Term::App(app) => {
                    self.resolver.resolve(goal_frame.goal, app, &mut context)
                }
                // Cut prunes the search alternatives down to the current goal's cut level
                term_arena::Term::Cut => {
                    // Remove choices from all checkpoints between current cut level and the top:
                    for checkpoint in self.checkpoints[goal_frame.cut_level..].iter_mut() {
                        checkpoint.choice = None;
                    }
                    Some(Resolved::Success)
                }
                // Other terms are an error
                _ => {
                    // TODO: log invalid goal term
                    None
                }
            };
            let choice = match resolved {
                None => {
                    // Restore before state
                    self.unresolved_goals.push(goal_frame);
                    // Then resume from current checkpoint
                    return self.resume_or_backtrack();
                }
                // A change was applied here, remember the choice
                Some(Resolved::Success) => None,
                Some(Resolved::SuccessRetry(choice)) => Some(choice),
            };

            // At this point, the goal was successfully resolved
            self.checkpoints.push(Checkpoint {
                goal: goal_frame.goal,
                choice,
                solution_checkpoint,
                goals_checkpoint,
                cut_level: goal_frame.cut_level,
            });
            self.yield_or_continue()
        } else {
            self.resume_or_backtrack()
        }
    }

    /// Obtain a copy of the current assignment of the goal variables.
    ///
    /// Usually, this function should be called right after `step` returned `Step::Yield`. In taht
    /// case, it will return a valid solution to the query. It may be called at any point though,
    /// but the assignment will be incomplete and might not even be a part of a valid solution.
    pub fn get_solution(&self) -> Solution {
        Solution(self.solution.get_solution())
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

        // Any goals resulting from choices on this checkpoint inherit the current cut-level.
        let success = match &mut checkpoint.choice {
            None => false,
            Some(choice) => {
                let mut context = ResolveContext {
                    solution: &mut self.solution,
                    goal_stack: &mut self.unresolved_goals,
                    checkpoint: &checkpoint.solution_checkpoint,
                    goal_len: checkpoint.goals_checkpoint,
                    cut_level: checkpoint.cut_level,
                };
                self.resolver.resume(choice, checkpoint.goal, &mut context)
            }
        };

        if success {
            true
        } else {
            // checkpoint exhausted, discard checkpoint and put goal back
            let discarded = self.checkpoints.pop().expect("we know there is one here");
            self.unresolved_goals.push(discarded.restore_goal_frame());
            false
        }
    }

    /// Backtrack to the first checkpoint that allows making a choice
    fn resume_or_backtrack(&mut self) -> Step {
        while let Some(checkpoint) = self.checkpoints.last() {
            // restore to topmost checkpoint
            self.solution.restore(&checkpoint.solution_checkpoint);
            self.unresolved_goals.truncate(checkpoint.goals_checkpoint);
            // then try to resume it
            if self.resume_checkpoint() {
                // Success, continue search
                return self.yield_or_continue();
            }
            // couldn't resume, the checkpoint was discarded, so we can simply loop to the next
        }
        Step::Done
    }

    /// Depending on whether the current state is a solution or not, return [`Step::Yield`] or
    /// [`Step::Continue`].
    fn yield_or_continue(&self) -> Step {
        // Found a choice to commit to
        if self.unresolved_goals.is_empty() {
            // If no goals remain, we are done
            Step::Yield
        } else {
            // Otherwise, rinse & repeat with remaining goals
            Step::Continue
        }
    }
}

impl<R: Resolver> Iterator for SolutionIter<R> {
    type Item = Solution;

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
#[derive(Debug)]
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

/// A snapshot of the [`SolutionState`] that can be reverted back to.
///
/// Solution checkpoints work in a stack-like fashion: after restoring an older one, restoring a
/// more recent checkpoint will have no effect.
#[derive(Debug)]
pub struct SolutionCheckpoint {
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

    /// Allocate a number of unbound goal variables (needed by [`Resolver`]s to decompose goals),
    /// and return the start of the allocation.
    ///
    /// NOTE: Calling this with `0` will not allocate any variables and instead return a variable
    /// one past the highest valid variable.
    #[inline(always)]
    pub fn allocate_vars(&mut self, num_vars: usize) -> Var {
        let start = self.variables.len();
        self.variables.resize(self.variables.len() + num_vars, None);
        Var::from_ord(start)
    }

    /// Allocate a single unbound variable.
    #[inline(always)]
    pub fn allocate_var(&mut self) -> Var {
        self.allocate_vars(1)
    }

    /// Assign a value to a variable and record this operation in the undo log. A variable may only
    /// be assigned once, and the value may not contain the variable in question in order to guard
    /// against infinite terms.
    pub fn set_var(&mut self, var: Var, value: term_arena::TermId) -> bool {
        debug_assert!(self.variables[var.ord()].is_none());

        if self.occurs(var, value) {
            return false;
        }

        self.variables[var.ord()] = Some(value);
        self.assignments.push(var);

        true
    }

    /// Return the term assigned to a variable, or `None` if the variable is unbound.
    ///
    /// Similar to [`SolutionState::follow_vars`], but intended for directly reading the value of a
    /// variable, rather than simply resolving any bound variables.
    pub fn get_var(&self, mut var: Var) -> Option<TermId> {
        while let Some(term) = self.variables[var.ord()] {
            match self.terms.get_term(term) {
                term_arena::Term::Var(next) => var = next,
                _ => return Some(term),
            }
        }
        None
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
                    } else if let Some(value) = self.variables[v.ord()] {
                        // Follow already assigned variables
                        term = value;
                        continue;
                    }
                }
                term_arena::Term::App(term_arena::AppTerm(_, args)) => {
                    let terms = &self.terms;
                    self.occurs_stack.extend(terms.get_args(args))
                }
                // Primitive values cannot contain variables
                term_arena::Term::Int(_) => {}
                term_arena::Term::Cut => {}
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
    pub fn checkpoint(&self) -> SolutionCheckpoint {
        SolutionCheckpoint {
            operations_checkpoint: self.assignments.len(),
            variables_checkpoint: self.variables.len(),
            terms_checkpoint: self.terms.checkpoint(),
        }
    }

    /// Undo all operations that have been applied to the solution since the checkpoint was created.
    pub fn restore(&mut self, checkpoint: &SolutionCheckpoint) {
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
    pub fn extract_term(&self, term: term_arena::TermId) -> ast::Term {
        match self.terms.get_term(term) {
            term_arena::Term::Var(v) => {
                if let Some(value) = &self.variables[v.ord()] {
                    self.extract_term(*value)
                } else {
                    ast::Term::Var(v)
                }
            }
            term_arena::Term::App(app) => ast::Term::App(self.extract_app_term(app)),
            term_arena::Term::Int(i) => ast::Term::Int(i),
            term_arena::Term::Cut => ast::Term::Cut,
        }
    }

    /// Convert an app term from the internal arena to the AST representation.
    pub fn extract_app_term(&self, term: term_arena::AppTerm) -> ast::AppTerm {
        ast::AppTerm {
            functor: term.0,
            args: self
                .terms
                .get_args(term.1)
                .map(|arg| self.extract_term(arg))
                .collect(),
        }
    }

    /// Obtain a copy of the current assignment of the original goal variables.
    fn get_solution(&self) -> Vec<Option<ast::Term>> {
        self.variables
            .iter()
            .take(self.goal_vars)
            .map(|val| val.as_ref().map(|t| self.extract_term(*t)))
            .collect()
    }

    /// Follow the assignment of variables until reaching either an unassigned variable or an
    /// application term. Used by unification for applying substitution on-the-fly rather than
    /// needing to create a bunch of copies of terms.
    pub fn follow_vars(
        &self,
        mut term: term_arena::TermId,
    ) -> (term_arena::TermId, term_arena::Term) {
        loop {
            match self.terms.get_term(term) {
                term_arena::Term::Var(var) => {
                    if let Some(value) = self.variables[var.ord()] {
                        term = value;
                    } else {
                        return (term, term_arena::Term::Var(var));
                    }
                }
                other => return (term, other),
            }
        }
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
            // variable with any other term
            (term_arena::Term::Var(goal_var), _) => self.set_var(goal_var, rule_term_id),
            (_, term_arena::Term::Var(rule_var)) => self.set_var(rule_var, goal_term_id),
            // two application terms
            (term_arena::Term::App(goal_app), term_arena::Term::App(rule_app)) => {
                self.unify_app(goal_app, rule_app)
            }
            // two integers
            (term_arena::Term::Int(goal_int), term_arena::Term::Int(rule_int)) => {
                goal_int == rule_int
            }
            // incomptaible types
            (_, _) => false,
        }
    }

    /// Unify two app terms.
    #[inline(always)]
    pub fn unify_app(
        &mut self,
        goal_term: term_arena::AppTerm,
        rule_term: term_arena::AppTerm,
    ) -> bool {
        if goal_term.0 == rule_term.0 {
            self.unify_args(goal_term.1, rule_term.1)
        } else {
            false
        }
    }

    /// Unify two argument ranges.
    #[inline(always)]
    pub fn unify_args(
        &mut self,
        goal_args: term_arena::ArgRange,
        rule_args: term_arena::ArgRange,
    ) -> bool {
        if goal_args.len() != rule_args.len() {
            return false;
        }
        goal_args.zip(rule_args).all(|(goal_arg, rule_arg)| {
            self.unify(self.terms.get_arg(goal_arg), self.terms.get_arg(rule_arg))
        })
    }

    /// Provide access to the terms defined in this solution.
    #[inline(always)]
    pub fn terms(&self) -> &TermArena {
        &self.terms
    }

    /// Provide mutable access to the terms defined in this solution.
    #[inline(always)]
    pub fn terms_mut(&mut self) -> &mut TermArena {
        &mut self.terms
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Term, Var};
    use crate::search::{Resolver, Solution, SolutionIter};
    use crate::textual::TextualUniverse;

    /// https://github.com/fatho/logru/issues/15
    #[test]
    fn occurs_check_issue_15() {
        let mut tu = TextualUniverse::new();
        tu.load_str("refl(f(X), g(X)).").unwrap();

        // This way around works
        let solver = tu.query_dfs("refl(A, f(A)).").unwrap();
        assert_no_solution(solver);

        // This way doesn't
        let solver = tu.query_dfs("refl(f(A), A).").unwrap();
        assert_no_solution(solver);

        #[track_caller]
        fn assert_no_solution<R: Resolver + std::fmt::Debug>(mut solver: SolutionIter<R>) {
            loop {
                match solver.step() {
                    super::Step::Yield => {
                        panic!("occurs check should prevent solution: {:#?}", solver)
                    }
                    super::Step::Continue => continue,
                    super::Step::Done => break,
                }
            }
        }
    }

    #[test]
    fn solution_get() {
        let solution = Solution(vec![None, Some(Term::Int(0))]);
        assert_eq!(solution.get(Var::from_ord(1)), Some(&Term::Int(0)));
        assert_eq!(
            solution.iter_vars().collect::<Vec<_>>(),
            vec![
                (Var::from_ord(0), None),
                (Var::from_ord(1), Some(&Term::Int(0))),
            ],
        );
    }
}
