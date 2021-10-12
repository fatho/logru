pub mod named;
pub mod term;
pub mod term_arena;

use term::*;
use term_arena::TermArena;

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
        self.symbols[rule.head.functor.0]
            .definitions
            .push(rule.compile());
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

        let mut solution = SolutionState::new(max_var);

        let mut scratch = Vec::new();

        // initialize solver
        Solver {
            universe: self,
            unresolved_goals: goals
                .iter()
                .map(|app| instantiate_app(&mut solution.terms, &mut scratch, app, 0))
                .collect(),
            checkpoints: vec![],
            solution,
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
    definitions: Vec<CompiledRule>,
}

impl SymInfo {
    fn new() -> Self {
        Self {
            definitions: vec![],
        }
    }
}

#[derive(Debug, Clone)]
pub struct CompiledRule {
    head_blueprint: TermArena,
    head: term_arena::TermId,
    tail_blueprint: TermArena,
    tail: Vec<term_arena::TermId>,
    var_slots: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    head: AppTerm,
    tail: Vec<AppTerm>,
}

impl Rule {
    pub fn fact(pred: Sym, args: Vec<Term>) -> Self {
        let head = AppTerm {
            functor: pred,
            args,
        };
        Self { head, tail: vec![] }
    }

    pub fn when(mut self, pred: Sym, args: Vec<Term>) -> Self {
        let app_term = AppTerm {
            functor: pred,
            args,
        };
        self.tail.push(app_term);
        self
    }

    pub fn compile(&self) -> CompiledRule {
        let mut scratch = Vec::new();
        let mut head_blueprint = TermArena::new();
        let mut tail_blueprint = TermArena::new();
        let head = instantiate_app(&mut head_blueprint, &mut scratch, &self.head, 0);
        let tail = self
            .tail
            .iter()
            .map(|tail| instantiate_app(&mut tail_blueprint, &mut scratch, tail, 0))
            .collect();
        CompiledRule {
            head_blueprint,
            head,
            tail_blueprint,
            tail,
            var_slots: self.head.count_var_slots().max(
                self.tail
                    .iter()
                    .map(|tail| tail.count_var_slots())
                    .max()
                    .unwrap_or(0),
            ),
        }
    }
}

pub struct Solver<'u> {
    universe: &'u Universe,
    unresolved_goals: Vec<term_arena::TermId>,
    checkpoints: Vec<Checkpoint<'u>>,
    solution: SolutionState,
}

struct Checkpoint<'u> {
    goal: term_arena::TermId,
    alternatives: Vec<&'u CompiledRule>,
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
        debug_assert!(self.variables[var.0].is_none());

        if self.occurs(var, value) {
            return false;
        }

        self.variables[var.0] = Some(value);
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
            self.variables[var.0] = None;
        }
        self.variables.truncate(checkpoint.variables_checkpoint);
        self.terms.release(&checkpoint.terms_checkpoint);
    }

    fn substitute(&self, term: term_arena::TermId) -> Term {
        match self.terms.get_term(term) {
            term_arena::Term::Var(v) => {
                if let Some(value) = &self.variables[v.0] {
                    self.substitute(*value)
                } else {
                    Term::Var(v)
                }
            }
            term_arena::Term::App(functor, args) => Term::App(AppTerm {
                functor,
                args: args
                    .map(|arg_id| self.substitute(self.terms.get_arg(arg_id)))
                    .collect(),
            }),
        }
    }

    fn get_solution(&self) -> Vec<Option<Term>> {
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
                    if let Some(value) = &self.variables[var.0] {
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

fn instantiate(
    arena: &mut TermArena,
    scratch: &mut Vec<term_arena::TermId>,
    term: &Term,
    offset: usize,
) -> term_arena::TermId {
    match term {
        Term::Var(v) => arena.var(Var(v.0 + offset)),
        Term::App(app) => instantiate_app(arena, scratch, app, offset),
    }
}

fn instantiate_app(
    arena: &mut TermArena,
    scratch: &mut Vec<term_arena::TermId>,
    app: &AppTerm,
    offset: usize,
) -> term_arena::TermId {
    let args_start = scratch.len();
    for arg in &app.args {
        let arg_term = instantiate(arena, scratch, arg, offset);
        scratch.push(arg_term);
    }
    let out = arena.app(app.functor, &scratch[args_start..]);
    scratch.truncate(args_start);
    out
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
            let goal_sym = match self.solution.terms.get_term(goal) {
                term_arena::Term::Var(_) => unreachable!(),
                term_arena::Term::App(functor, _) => &self.universe.symbols[functor.0],
            };

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
