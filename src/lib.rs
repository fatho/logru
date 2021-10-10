pub mod term;
pub mod union_find;
pub mod zebra;

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
            .unwrap_or(0);
        // initialize solver
        Solver {
            universe: self,
            unresolved_goals: goals,
            resolved_goals: vec![],
            assignments: vec![None; max_var],
            operations: vec![],
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
    resolved_goals: Vec<ResolvedGoal<'u>>,
    assignments: Vec<Option<Term>>,
    operations: Vec<SolverOp>,
}

enum SolverOp {
    AssignedVar(Var),
    AllocatedVars(usize),
    PushedGoals(usize),
    Resolved,
}

struct ResolvedGoal<'u> {
    goal: AppTerm,
    alternatives: Vec<&'u Rule>,
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
            println!("Resolving {:?}", goal);

            let goal_sym = &self.universe.symbols[goal.functor.0];

            // store alternatives in reverse order so that we can `pop` and still process
            // them in the original order
            let alternatives = goal_sym.definitions.iter().rev().collect::<Vec<_>>();

            self.resolve_next(goal, alternatives)
        } else {
            self.backtrack()
        }
    }

    fn unify(&mut self, goal_term: &Term, rule_term: &Term) -> bool {
        todo!("Probably won't work due to how terms are represented")
    }

    fn unify_app(&mut self, goal_term: &AppTerm, rule_term: &AppTerm) -> bool {
        if goal_term.functor != rule_term.functor {
            return false;
        }
        if goal_term.args.len() != rule_term.args.len() {
            return false;
        }

        goal_term
            .args
            .iter()
            .zip(rule_term.args.iter())
            .all(|(goal_arg, rule_arg)| self.unify(goal_arg, rule_arg))
    }

    fn resolve_next(&mut self, goal: AppTerm, mut alternatives: Vec<&'u Rule>) -> Step {
        while let Some(current) = alternatives.pop() {
            // tentatively add new operations
            let checkpoint = self.operations.len();

            self.operations.push(SolverOp::Resolved);

            // add uninstantiated variables for the rule
            let rule_vars = current.max_var();
            self.assignments.resize(self.assignments.len() + rule_vars, None);
            self.operations.push(SolverOp::AllocatedVars(rule_vars));

            if self.unify_app(&goal, &current.head) {
                // TODO: push new goals

                self.resolved_goals
                    .push(ResolvedGoal { goal, alternatives });

                if self.unresolved_goals.is_empty() {
                    // If there are no other goals, we found a solution
                    return Step::Yield;
                } else {
                    // Otherwise we need to continue
                    return Step::Continue;
                }
            } else {
                // restricted backtracking of the unification operations
                for op in self.operations.drain(checkpoint..).rev() {
                    match op {
                        SolverOp::AssignedVar(v) => self.assignments[v.0] = None,
                        SolverOp::AllocatedVars(num_vars) => {
                            self.assignments.truncate(self.assignments.len() - num_vars)
                        }
                        SolverOp::PushedGoals(_) => (),
                        // no need to do anything since we didn't actually push it yet
                        SolverOp::Resolved => (),
                    }
                }
            }
        }

        // If none of the alternatives matched, put the unresolved goal back and backtrack to
        // earlier decision.
        self.unresolved_goals.push(goal);
        self.backtrack()
    }

    fn backtrack(&mut self) -> Step {
        // pop from the backtracking stack until we can try another alternative
        while let Some(op) = self.operations.pop() {
            match op {
                SolverOp::AssignedVar(var) => {
                    self.assignments[var.0] = None;
                }
                SolverOp::AllocatedVars(num_vars) => {
                    self.assignments.truncate(self.assignments.len() - num_vars);
                }
                SolverOp::PushedGoals(num_goals) => {
                    self.unresolved_goals
                        .truncate(self.unresolved_goals.len() - num_goals);
                }
                SolverOp::Resolved => {
                    // try the next alternative in the goal resolution queue
                    let rgoal = self
                        .resolved_goals
                        .pop()
                        .expect("must have resolved goal when backtracking `Resolved`");
                    self.resolve_next(rgoal.goal, rgoal.alternatives);
                }
            }
        }
        // Nothing more to scan through
        Step::Done
    }
}

impl<'u> Iterator for Solver<'u> {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                Step::Yield => break Some(()),
                Step::Continue => continue,
                Step::Done => break None,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // pub enum List {
    //     Nil,
    //     Cons(Var<List>, Var<List>),
    // }

    // pub enum Preds {
    //     Append,
    //     IsNull,
    // }

    #[test]
    fn usage() {
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

        let parent = u.new_symbol();
        let grandparent = u.new_symbol();
        let siblings = u.new_symbol();

        u.add_rule(Rule::fact(parent, vec![alice.into(), carol.into()]));
        u.add_rule(Rule::fact(parent, vec![bob.into(), carol.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), eve.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), eve.into()]));

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

        let solver = u.query(quantify(|[x]| {
            vec![grandparent.apply(vec![x.into(), eve.into()])]
        }));
        for solution in solver {
            println!("{:?}", solution);
        }

        panic!()
    }
}
