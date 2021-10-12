use crate::{
    ast::{self, Rule, Var},
    term_arena::{self, TermArena},
    universe::Universe,
};

#[derive(Debug, Clone)]
pub struct CompiledRule {
    head_blueprint: TermArena,
    head: term_arena::TermId,
    tail_blueprint: TermArena,
    tail: Vec<term_arena::TermId>,
    var_slots: usize,
}

impl CompiledRule {
    pub fn new(rule: &Rule) -> CompiledRule {
        let mut scratch = Vec::new();
        let mut head_blueprint = TermArena::new();
        let mut tail_blueprint = TermArena::new();
        let head = head_blueprint.term_app(&mut scratch, &rule.head, 0);
        let tail = rule
            .tail
            .iter()
            .map(|tail| tail_blueprint.term_app(&mut scratch, tail, 0))
            .collect();
        CompiledRule {
            head_blueprint,
            head,
            tail_blueprint,
            tail,
            var_slots: rule.head.count_var_slots().max(
                rule.tail
                    .iter()
                    .map(|tail| tail.count_var_slots())
                    .max()
                    .unwrap_or(0),
            ),
        }
    }
}

pub struct Solver {
    rules: Vec<Vec<CompiledRule>>,
}

impl Solver {
    pub fn new(universe: &Universe) -> Solver {
        let mut rules = vec![Vec::new(); universe.num_symbols()];
        for rule in universe.rules() {
            rules[rule.head.functor.ord()].push(CompiledRule::new(rule));
        }
        Solver { rules }
    }

    pub fn query(&self, query: &ast::Query) -> SolutionIter {
        // determine how many goal variables we need to allocate
        let max_var = query.count_var_slots();

        let mut solution = SolutionState::new(max_var);

        let mut scratch = Vec::new();

        // initialize solver
        SolutionIter {
            rules: &self.rules,
            unresolved_goals: query
                .goals
                .iter()
                .map(|app| solution.terms.term_app(&mut scratch, app, 0))
                .collect(),
            checkpoints: vec![],
            solution,
        }
    }
}

pub struct SolutionIter<'s> {
    rules: &'s [Vec<CompiledRule>],
    unresolved_goals: Vec<term_arena::TermId>,
    checkpoints: Vec<Checkpoint<'s>>,
    solution: SolutionState,
}

struct Checkpoint<'s> {
    goal: term_arena::TermId,
    alternatives: Vec<&'s CompiledRule>,
    goals_checkpoint: usize,
    solution_checkpoint: SolutionCheckpoint,
}

struct SolutionState {
    variables: Vec<Option<term_arena::TermId>>,
    assignments: Vec<Var>,
    goal_vars: usize,
    terms: TermArena,
}

struct SolutionCheckpoint {
    operations_checkpoint: usize,
    variables_checkpoint: usize,
    terms_checkpoint: term_arena::Checkpoint,
}

impl SolutionState {
    fn new(goal_vars: usize) -> Self {
        Self {
            assignments: vec![],
            variables: vec![None; goal_vars],
            goal_vars,
            terms: TermArena::new(),
        }
    }

    fn allocate_vars(&mut self, num_vars: usize) {
        self.variables.resize(self.variables.len() + num_vars, None);
    }

    fn set_var(&mut self, var: Var, value: term_arena::TermId) -> bool {
        debug_assert!(self.variables[var.ord()].is_none());

        if self.occurs(var, value) {
            return false;
        }

        self.variables[var.ord()] = Some(value);
        self.assignments.push(var);

        true
    }

    fn occurs(&self, var: Var, term: term_arena::TermId) -> bool {
        match self.terms.get_term(term) {
            term_arena::Term::Var(v) => v == var,
            term_arena::Term::App(_, mut args) => {
                args.any(|arg_id| self.occurs(var, self.terms.get_arg(arg_id)))
            }
        }
    }

    fn checkpoint(&self) -> SolutionCheckpoint {
        SolutionCheckpoint {
            operations_checkpoint: self.assignments.len(),
            variables_checkpoint: self.variables.len(),
            terms_checkpoint: self.terms.checkpoint(),
        }
    }

    fn restore(&mut self, checkpoint: &SolutionCheckpoint) {
        for var in self.assignments.drain(checkpoint.operations_checkpoint..) {
            self.variables[var.ord()] = None;
        }
        self.variables.truncate(checkpoint.variables_checkpoint);
        self.terms.release(&checkpoint.terms_checkpoint);
    }

    fn substitute(&self, term: term_arena::TermId) -> ast::Term {
        match self.terms.get_term(term) {
            term_arena::Term::Var(v) => {
                if let Some(value) = &self.variables[v.ord()] {
                    self.substitute(*value)
                } else {
                    ast::Term::Var(v)
                }
            }
            term_arena::Term::App(functor, args) => ast::Term::App(ast::AppTerm {
                functor,
                args: args
                    .map(|arg_id| self.substitute(self.terms.get_arg(arg_id)))
                    .collect(),
            }),
        }
    }

    fn get_solution(&self) -> Vec<Option<ast::Term>> {
        self.variables
            .iter()
            .take(self.goal_vars)
            .map(|val| val.as_ref().map(|t| self.substitute(*t)))
            .collect()
    }

    fn follow_vars(&self, mut term: term_arena::TermId) -> (term_arena::TermId, term_arena::Term) {
        loop {
            match self.terms.get_term(term) {
                term_arena::Term::Var(var) => {
                    if let Some(value) = &self.variables[var.ord()] {
                        term = *value;
                    } else {
                        return (term, term_arena::Term::Var(var));
                    }
                }
                app @ term_arena::Term::App(_, _) => return (term, app),
            }
        }
    }

    fn unify(&mut self, goal_term: term_arena::TermId, rule_term: term_arena::TermId) -> bool {
        let (goal_term_id, goal_term) = self.follow_vars(goal_term);
        let (rule_term_id, rule_term) = self.follow_vars(rule_term);

        match (goal_term, rule_term) {
            (term_arena::Term::Var(goal_var), term_arena::Term::Var(rule_var)) => {
                if goal_var != rule_var {
                    self.set_var(rule_var, goal_term_id)
                } else {
                    true
                }
            }
            (term_arena::Term::Var(goal_var), term_arena::Term::App(_, _)) => {
                self.set_var(goal_var, rule_term_id)
            }
            (term_arena::Term::App(_, _), term_arena::Term::Var(rule_var)) => {
                self.set_var(rule_var, goal_term_id)
            }
            (
                term_arena::Term::App(goal_func, goal_args),
                term_arena::Term::App(rule_func, rule_args),
            ) => {
                if goal_func != rule_func {
                    return false;
                }
                if goal_args.len() != rule_args.len() {
                    return false;
                }

                goal_args.zip(rule_args).all(|(goal_arg, rule_arg)| {
                    self.unify(self.terms.get_arg(goal_arg), self.terms.get_arg(rule_arg))
                })
            }
        }
    }

    fn unify_rule<'a>(
        &'a mut self,
        goal_term: term_arena::TermId,
        rule: &'a CompiledRule,
    ) -> Option<impl Iterator<Item = term_arena::TermId> + 'a> {
        // add uninstantiated variables for the rule
        let var_offset = self.variables.len();
        self.allocate_vars(rule.var_slots);

        let conv_rule_head = self.terms.instantiate(&rule.head_blueprint, var_offset);
        let instantiated_rule_head = conv_rule_head(rule.head);

        if self.unify(goal_term, instantiated_rule_head) {
            let conv_rule_tail = self.terms.instantiate(&rule.tail_blueprint, var_offset);
            Some(rule.tail.iter().map(move |tail| conv_rule_tail(*tail)))
        } else {
            None
        }
    }
}

enum Step {
    Yield,
    Continue,
    Done,
}

impl<'s> SolutionIter<'s> {
    fn step(&mut self) -> Step {
        if let Some(goal) = self.unresolved_goals.pop() {
            // resolve goal
            let matching_rules = match self.solution.terms.get_term(goal) {
                term_arena::Term::Var(_) => unreachable!(),
                term_arena::Term::App(functor, _) => &self.rules[functor.ord()],
            };

            // store alternatives in reverse order so that we can `pop` and still process
            // them in the original order
            let alternatives = matching_rules.iter().rev().collect::<Vec<_>>();

            self.checkpoints.push(Checkpoint {
                goal,
                alternatives,
                solution_checkpoint: self.solution.checkpoint(),
                goals_checkpoint: self.unresolved_goals.len(),
            });
        }
        if self.backtrack_resume() {
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

    /// Try the next alternative of the top-most checkpoint
    fn resume_checkpoint(&mut self) -> bool {
        let checkpoint = self
            .checkpoints
            .last_mut()
            .expect("invariant: there is always a checkpoint when this is called");
        while let Some(current) = checkpoint.alternatives.pop() {
            let result = self.solution.unify_rule(checkpoint.goal, current);
            if let Some(goals) = result {
                self.unresolved_goals.extend(goals);
                return true;
            } else {
                drop(result);
                self.solution.restore(&checkpoint.solution_checkpoint);
            }
        }
        // checkpoint exhausted, put goal back and discard
        let discarded = self.checkpoints.pop().expect("we know there is one here");
        self.unresolved_goals.push(discarded.goal);
        false
    }

    /// Backtrack to the first checkpoint that allows making a choice
    fn backtrack_resume(&mut self) -> bool {
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

impl<'s> Iterator for SolutionIter<'s> {
    type Item = Vec<Option<ast::Term>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                Step::Yield => break Some(self.solution.get_solution()),
                Step::Continue => continue,
                Step::Done => break None,
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::ast::*;

    #[test]
    fn genealogy() {
        // GOAL:
        /*

        parent(alice, carol).
        parent(bob, carol).

        parent(carol, eve).
        parent(dave, eve).

        grandparent(X, Y) :- parent(X, Z), parent(Z, Y).

        siblings(X, Y) :- parent(Z, X), parent(Z, y).

        */

        let mut u = Universe::new();

        let alice = u.alloc_symbol();
        let bob = u.alloc_symbol();
        let carol = u.alloc_symbol();
        let dave = u.alloc_symbol();
        let eve = u.alloc_symbol();
        let faithe = u.alloc_symbol();

        let parent = u.alloc_symbol();
        let grandparent = u.alloc_symbol();
        let siblings = u.alloc_symbol();

        u.add_rule(Rule::fact(parent, vec![alice.into(), carol.into()]));
        u.add_rule(Rule::fact(parent, vec![bob.into(), carol.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), eve.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), eve.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), faithe.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), faithe.into()]));

        u.add_rule(forall(|[p, q, r]| {
            Rule::fact(grandparent, vec![p.into(), r.into()])
                .when(parent, vec![p.into(), q.into()])
                .when(parent, vec![q.into(), r.into()])
        }));

        u.add_rule(forall(|[p, c1, c2]| {
            Rule::fact(siblings, vec![c1.into(), c2.into()])
                .when(parent, vec![p.into(), c1.into()])
                .when(parent, vec![p.into(), c2.into()])
        }));

        let solver = Solver::new(&u);

        // query all known grandparents of eve
        let solutions = solver.query(&exists(|[x]| {
            Query::new(AppTerm::new(grandparent, vec![x.into(), eve.into()]))
        }));
        assert_eq!(
            solutions.collect::<Vec<_>>(),
            vec![vec![Some(alice.into())], vec![Some(bob.into())],]
        );

        // query all grandchildren of bob
        let solutions = solver.query(&exists(|[x]| {
            Query::new(AppTerm::new(grandparent, vec![bob.into(), x.into()]))
        }));
        assert_eq!(
            solutions.collect::<Vec<_>>(),
            vec![vec![Some(eve.into())], vec![Some(faithe.into())],]
        );

        // query all siblings of eve
        let solutions = solver.query(&exists(|[x]| {
            Query::new(AppTerm::new(siblings, vec![eve.into(), x.into()]))
        }));
        assert_eq!(
            solutions.collect::<Vec<_>>(),
            vec![
                // one solution for each path taken
                vec![Some(eve.into())],
                vec![Some(eve.into())],
                vec![Some(faithe.into())],
                vec![Some(faithe.into())],
            ]
        );
    }

    #[test]
    fn arithmetic() {
        // GOAL:
        /*

        is_natural(z).
        is_natural(s(X)) :- is_natural(X).

        is_zero(z).

        add(X, z, X) :- is_natural(X).
        add(X, S(Y), S(Z)) :- add(X, Y, Z).

        */

        let mut u = Universe::new();

        let s = u.alloc_symbol();
        let z = u.alloc_symbol();

        let is_natural = u.alloc_symbol();
        let is_zero = u.alloc_symbol();
        let add = u.alloc_symbol();

        u.add_rule(Rule::fact(is_zero, vec![z.into()]));
        u.add_rule(Rule::fact(is_natural, vec![z.into()]));

        u.add_rule(forall(|[x]| {
            Rule::fact(is_natural, vec![ast::app(s, vec![x.into()])])
                .when(is_natural, vec![x.into()])
        }));

        u.add_rule(forall(|[x]| {
            Rule::fact(add, vec![x.into(), z.into(), x.into()]).when(is_natural, vec![x.into()])
        }));
        u.add_rule(forall(|[x, y, z]| {
            Rule::fact(
                add,
                vec![
                    x.into(),
                    ast::app(s, vec![y.into()]),
                    ast::app(s, vec![z.into()]),
                ],
            )
            .when(add, vec![x.into(), y.into(), z.into()])
        }));

        let solver = Solver::new(&u);

        // query all zero numbers
        let solutions = solver.query(&exists(|[x]| {
            Query::new(AppTerm::new(is_zero, vec![x.into()]))
        }));
        assert_eq!(solutions.collect::<Vec<_>>(), vec![vec![Some(z.into())],]);

        // query the first natural numbers
        let solutions = solver.query(&exists(|[x]| {
            Query::new(AppTerm::new(is_natural, vec![x.into()]))
        }));
        assert_eq!(
            solutions.take(3).collect::<Vec<_>>(),
            vec![
                vec![Some(z.into())],
                vec![Some(ast::app(s, vec![z.into()]))],
                vec![Some(ast::app(s, vec![ast::app(s, vec![z.into()])]))],
            ]
        );

        // compute 2 + 1
        let solutions = solver.query(&exists(|[x]| {
            Query::new(AppTerm::new(
                add,
                vec![
                    ast::app(s, vec![ast::app(s, vec![z.into()])]),
                    ast::app(s, vec![z.into()]),
                    x.into(),
                ],
            ))
        }));
        assert_eq!(
            solutions.collect::<Vec<_>>(),
            vec![vec![Some(ast::app(
                s,
                vec![ast::app(s, vec![ast::app(s, vec![z.into()])])]
            ))],]
        );

        // compute 3 - 2
        let solutions = solver.query(&exists(|[x]| {
            Query::new(AppTerm::new(
                add,
                vec![
                    x.into(),
                    ast::app(s, vec![ast::app(s, vec![z.into()])]),
                    ast::app(s, vec![ast::app(s, vec![ast::app(s, vec![z.into()])])]),
                ],
            ))
        }));
        assert_eq!(
            solutions.collect::<Vec<_>>(),
            vec![vec![Some(ast::app(s, vec![z.into()]))],]
        );
    }
}
