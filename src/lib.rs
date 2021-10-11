pub mod term;
pub mod term_arena;
pub mod union_find;
pub mod named;

use term::*;

#[derive(Debug)]
pub struct Universe {
    symbols: Vec<SymInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Sym(usize);

impl Sym {
    pub fn apply(self, args: Vec<Term>) -> AppTerm {
        AppTerm {
            functor: self,
            args,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(usize);

impl Universe {
    pub fn new_symbol(&mut self) -> Sym {
        let sym = Sym(self.symbols.len());
        self.symbols.push(SymInfo::new());
        sym
    }

    pub fn add_rule(&mut self, rule: Rule) {
        // define rule
        self.symbols[rule.head.functor.0].definitions.push(rule);
    }

    pub fn query(&self, goals: Vec<AppTerm>) -> Solver {
        // determine how many goal variables we need to allocate
        let max_var = goals
            .iter()
            .map(|goal| goal.vars())
            .flatten()
            .map(|v| v.0)
            .max()
            .map_or(0, |x| x + 1);
        // initialize solver
        Solver {
            universe: self,
            unresolved_goals: goals,
            checkpoints: vec![],
            solution: SolutionState::new(max_var),
        }
    }

    pub fn new() -> Self {
        Self { symbols: vec![] }
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

pub fn quantify<R, const N: usize>(f: impl FnOnce([Var; N]) -> R) -> R {
    // initialize variable array with temporary fresh variables
    //   that disappear once we're done solving
    let mut vars = [Var(0); N];
    vars.iter_mut()
        .enumerate()
        .for_each(|(i, var)| *var = Var(i));
    f(vars)
}

#[derive(Debug)]
struct SymInfo {
    definitions: Vec<Rule>,
}

impl SymInfo {
    fn new() -> Self {
        Self {
            definitions: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    head: AppTerm,
    tail: Vec<AppTerm>,
}

impl Rule {
    pub fn fact(pred: Sym, args: Vec<Term>) -> Self {
        Self {
            head: AppTerm {
                functor: pred,
                args,
            },
            tail: vec![],
        }
    }

    pub fn when(mut self, pred: Sym, args: Vec<Term>) -> Self {
        self.tail.push(
            AppTerm {
                functor: pred,
                args,
            }
            .into(),
        );
        self
    }

    pub fn max_var(&self) -> usize {
        std::iter::once(&self.head)
            .chain(self.tail.iter())
            .map(|goal| goal.vars())
            .flatten()
            .map(|v| v.0)
            .max()
            .unwrap_or(0)
    }
}

pub struct Solver<'u> {
    universe: &'u Universe,
    unresolved_goals: Vec<AppTerm>,
    checkpoints: Vec<Checkpoint<'u>>,
    solution: SolutionState,
}

struct Checkpoint<'u> {
    goal: AppTerm,
    alternatives: Vec<&'u Rule>,
    goals_checkpoint: usize,
    solution_checkpoint: SolutionCheckpoint,
}

struct SolutionState {
    variables: Vec<Option<Term>>,
    assignments: Vec<Var>,
    goal_vars: usize,
}

struct SolutionCheckpoint {
    operations_checkpoint: usize,
    variables_checkpoint: usize,
}

impl SolutionState {
    fn new(goal_vars: usize) -> Self {
        Self {
            assignments: vec![],
            variables: vec![None; goal_vars],
            goal_vars: goal_vars,
        }
    }

    fn allocate_vars(&mut self, num_vars: usize) {
        self.variables.resize(self.variables.len() + num_vars, None);
    }

    fn set_var(&mut self, var: Var, value: Term) -> bool {
        assert!(self.variables[var.0].is_none());

        if value.occurs(var) {
            return false;
        }

        self.variables[var.0] = Some(value);
        self.assignments.push(var);

        true
    }

    fn checkpoint(&self) -> SolutionCheckpoint {
        SolutionCheckpoint {
            operations_checkpoint: self.assignments.len(),
            variables_checkpoint: self.variables.len(),
        }
    }

    fn restore(&mut self, checkpoint: &SolutionCheckpoint) {
        for var in self
            .assignments
            .drain(checkpoint.operations_checkpoint..)
        {
            self.variables[var.0] = None;
        }
        self.variables.truncate(checkpoint.variables_checkpoint);
    }

    fn substitute(&self, term: &Term) -> Term {
        match term {
            Term::Var(v) => {
                if let Some(value) = &self.variables[v.0] {
                    self.substitute(value)
                } else {
                    Term::Var(*v)
                }
            }
            Term::App(app) => Term::App(self.substitute_app(app)),
        }
    }

    fn substitute_app(&self, term: &AppTerm) -> AppTerm {
        AppTerm {
            functor: term.functor,
            args: term.args.iter().map(|t| self.substitute(t)).collect(),
        }
    }

    fn get_solution(&self) -> Vec<Option<Term>> {
        self.variables
            .iter()
            .take(self.goal_vars)
            .map(|val| val.as_ref().map(|t| self.substitute(t)))
            .collect()
    }

    fn follow_vars(&self, mut term: Term) -> Term {
        loop {
            match term {
                Term::Var(var) => {
                    if let Some(value) = &self.variables[var.0] {
                        term = value.clone();
                    } else {
                        return Term::Var(var);
                    }
                }
                term @ Term::App(_) => return term,
            }
        }
    }

    fn unify(&mut self, goal_term: Term, rule_term: Term) -> bool {

        let goal_term = self.follow_vars(goal_term);
        let rule_term = self.follow_vars(rule_term);


        // we know that if any of the terms is a variable, it is not instantiated yet
        match (goal_term, rule_term) {
            (Term::Var(goal_var), Term::Var(rule_var)) => {
                if goal_var != rule_var {
                    self.set_var(rule_var, Term::Var(goal_var))
                } else {
                    true
                }
            }
            (Term::Var(goal_var), rule_term @ Term::App(_)) => self.set_var(goal_var, rule_term),
            (goal_term @ Term::App(_), Term::Var(rule_var)) => self.set_var(rule_var, goal_term),
            (Term::App(goal_app), Term::App(rule_app)) => self.unify_app(goal_app, rule_app),
        }
    }

    fn unify_app(&mut self, goal_term: AppTerm, rule_term: AppTerm) -> bool {
        if goal_term.functor != rule_term.functor {
            return false;
        }
        if goal_term.args.len() != rule_term.args.len() {
            return false;
        }

        goal_term
            .args
            .into_iter()
            .zip(rule_term.args.into_iter())
            .all(|(goal_arg, rule_arg)| self.unify(goal_arg, rule_arg))
    }

    fn unify_rule(&mut self, goal_term: &AppTerm, rule: &Rule) -> Option<Vec<AppTerm>> {
        // add uninstantiated variables for the rule
        let var_offset = self.variables.len();
        let rule_vars = rule.max_var() + 1;
        self.allocate_vars(rule_vars);

        let instantiated_rule_head = rule.head.instantiate(var_offset);

        if self.unify_app(goal_term.clone(), instantiated_rule_head) {
            Some(
                rule.tail
                    .iter()
                    .map(|tail| tail.instantiate(var_offset))
                    .collect(),
            )
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

impl<'u> Solver<'u> {
    fn step(&mut self) -> Step {
        if let Some(goal) = self.unresolved_goals.pop() {
            // resolve goal

            let goal_sym = &self.universe.symbols[goal.functor.0];

            // store alternatives in reverse order so that we can `pop` and still process
            // them in the original order
            let alternatives = goal_sym.definitions.iter().rev().collect::<Vec<_>>();

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
            if let Some(goals) = self.solution.unify_rule(&checkpoint.goal, &current) {
                self.unresolved_goals.extend(goals);
                return true;
            } else {
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

impl<'u> Iterator for Solver<'u> {
    type Item = Vec<Option<Term>>;

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
mod test {
    use super::*;

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

        let alice = u.new_symbol();
        let bob = u.new_symbol();
        let carol = u.new_symbol();
        let dave = u.new_symbol();
        let eve = u.new_symbol();
        let faithe = u.new_symbol();

        let parent = u.new_symbol();
        let grandparent = u.new_symbol();
        let siblings = u.new_symbol();

        u.add_rule(Rule::fact(parent, vec![alice.into(), carol.into()]));
        u.add_rule(Rule::fact(parent, vec![bob.into(), carol.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), eve.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), eve.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), faithe.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), faithe.into()]));

        u.add_rule(quantify(|[p, q, r]| {
            Rule::fact(grandparent, vec![p.into(), r.into()])
                .when(parent, vec![p.into(), q.into()])
                .when(parent, vec![q.into(), r.into()])
        }));

        u.add_rule(quantify(|[p, c1, c2]| {
            Rule::fact(siblings, vec![c1.into(), c2.into()])
                .when(parent, vec![p.into(), c1.into()])
                .when(parent, vec![p.into(), c2.into()])
        }));

        // query all known grandparents of eve
        let solver = u.query(quantify(|[x]| {
            vec![grandparent.apply(vec![x.into(), eve.into()])]
        }));
        assert_eq!(
            solver.collect::<Vec<_>>(),
            vec![vec![Some(alice.into())], vec![Some(bob.into())],]
        );

        // query all grandchildren of bob
        let solver = u.query(quantify(|[x]| {
            vec![grandparent.apply(vec![bob.into(), x.into()])]
        }));
        assert_eq!(
            solver.collect::<Vec<_>>(),
            vec![vec![Some(eve.into())], vec![Some(faithe.into())],]
        );

        // query all siblings of eve
        let solver = u.query(quantify(|[x]| {
            vec![siblings.apply(vec![eve.into(), x.into()])]
        }));
        assert_eq!(
            solver.collect::<Vec<_>>(),
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

        let s = u.new_symbol();
        let z = u.new_symbol();

        let is_natural = u.new_symbol();
        let is_zero = u.new_symbol();
        let add = u.new_symbol();

        u.add_rule(Rule::fact(is_zero, vec![z.into()]));
        u.add_rule(Rule::fact(is_natural, vec![z.into()]));

        u.add_rule(quantify(|[x]| {
            Rule::fact(is_natural, vec![s.apply(vec![x.into()]).into()])
                .when(is_natural, vec![x.into()])
        }));

        u.add_rule(quantify(|[x]| {
            Rule::fact(add, vec![x.into(), z.into(), x.into()]).when(is_natural, vec![x.into()])
        }));
        u.add_rule(quantify(|[x, y, z]| {
            Rule::fact(
                add,
                vec![
                    x.into(),
                    s.apply(vec![y.into()]).into(),
                    s.apply(vec![z.into()]).into(),
                ],
            )
            .when(add, vec![x.into(), y.into(), z.into()])
        }));

        // query all zero numbers
        let solver = u.query(quantify(|[x]| vec![is_zero.apply(vec![x.into()])]));
        assert_eq!(solver.collect::<Vec<_>>(), vec![vec![Some(z.into())],]);

        // query the first natural numbers
        let solver = u.query(quantify(|[x]| vec![is_natural.apply(vec![x.into()])]));
        assert_eq!(
            solver.take(3).collect::<Vec<_>>(),
            vec![
                vec![Some(z.into())],
                vec![Some(s.apply(vec![z.into()]).into())],
                vec![Some(s.apply(vec![s.apply(vec![z.into()]).into()]).into())],
            ]
        );

        // compute 2 + 1
        let solver = u.query(quantify(|[x]| {
            vec![add.apply(vec![
                s.apply(vec![s.apply(vec![z.into()]).into()]).into(),
                s.apply(vec![z.into()]).into(),
                x.into(),
            ])]
        }));
        assert_eq!(
            solver.collect::<Vec<_>>(),
            vec![vec![Some(
                s.apply(vec![s.apply(vec![s.apply(vec![z.into()]).into()]).into()])
                    .into()
            )],]
        );

        // compute 3 - 2
        let solver = u.query(quantify(|[x]| {
            vec![add.apply(vec![
                x.into(),
                s.apply(vec![s.apply(vec![z.into()]).into()]).into(),
                s.apply(vec![s.apply(vec![s.apply(vec![z.into()]).into()]).into()])
                    .into(),
            ])]
        }));
        assert_eq!(
            solver.collect::<Vec<_>>(),
            vec![vec![Some(s.apply(vec![z.into()]).into())],]
        );
    }
}
