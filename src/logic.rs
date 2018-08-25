use unification;
use unification::{Term, VarId};

use std;
use std::rc::Rc;
use std::vec::Vec;
use std::cell::RefCell;
use std::collections::HashMap;

/// An inference rule, where the rules head follows from the conjunction of the
/// rule's tail terms.
///
/// The type parameter denotes the type of discriminants for applicative forms.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Rule<A> {
    pub head: Term<A>,
    pub tail: Vec<Term<A>>
}

/// A set of inference rules.
#[derive(Debug, Clone)]
pub struct RuleSet<A> {
    rules: Vec<Rule<A>>
}

impl<A> RuleSet<A> where A: Copy + Eq {
    pub fn new() -> Self {
        RuleSet {
            rules: Vec::new()
        }
    }

    /// Add a new rule to the database.
    pub fn add_rule(&mut self, head: Term<A>, tail: Vec<Term<A>>) {
        self.rules.push(Rule {
            head: head,
            tail: tail
        })
    }

    pub fn iter(&self) -> impl Iterator<Item=&Rule<A>> {
        self.rules.iter()
    }

    pub fn query<'a, T>(&'a self, goals: T) -> Query<'a, A> where T: IntoIterator<Item=Term<A>> {
        Query::new(self, goals)
    }
}

/// A single branch in the query solver. It consists of a stack of goals that
/// need to be solved in order to prove the branch true. A goal is a term that
/// must be inferred through the given rules.
#[derive(Debug, Clone)]
struct GoalStack<A> {
    /// The topmost part of the goal stack.
    current: Vec<Term<A>>,
    /// The lower parts of the goal stack, wrapped in reference counted pointers
    /// so that theses parts of the goal stack can be shared among multiple
    /// alternatives. They only need to be copied when all current goals have
    /// been proven.
    previous: Vec<Rc<Vec<Term<A>>>>,
    solver: Rc<unification::Solver<A>>
}

impl<A> GoalStack<A> where A: Copy + Eq {
    pub fn from_goals<T>(goals: T) -> Self where T: IntoIterator<Item=Term<A>> {
        GoalStack {
            current: goals.into_iter().collect(),
            previous: vec![],
            solver: Rc::new(unification::Solver::new())
        }
    }

    /// Pop the topmost goal of the goal stack.
    pub fn pop(&mut self) -> Option<Term<A>> {
        while self.current.is_empty() {
            // copy lower parts of the stack on demand
            if let Some(prev_stack) = self.previous.pop() {
                self.current = Rc::try_unwrap(prev_stack).unwrap_or_else(|rc| (*rc).clone());
            } else {
                break;
            }
        }
        self.current.pop()
    }
}

/// A query against the database. Keeps track of all the branches that need to
/// be evaluated.
#[derive(Debug, Clone)]
pub struct Query<'a, A: 'a> {
    /// The current alternatives to explore.
    alternatives: Vec<GoalStack<A>>,
    /// The available set of rules for making inferences.
    rules: &'a RuleSet<A>,
    /// A source of fresh names.
    name_source: NameSource,
    goal_refresher: Refresher
}

/// Result of a step of the query solver.
#[derive(Debug)]
pub enum Step<A> {
    /// The query solver is done, there are no more solutions.
    Done,
    /// The query solver made progress, but did not find a solution yet.
    Again,
    /// The query solver found a solution.
    Found(Solution<A>),
}

/// A solution that makes a query true.
#[derive(Debug)]
pub struct Solution<A>(HashMap<VarId, Term<A>>);

impl<'a, A> Query<'a, A> where A: Copy + Eq {
    pub fn new<T>(rules: &'a RuleSet<A>, goals: T) -> Self where T: IntoIterator<Item=Term<A>> {
        let name_source = NameSource::new(0);
        let mut goal_refresher = Refresher::new(name_source.clone());
        Query {
            alternatives: vec![GoalStack::from_goals(goals.into_iter().map(|mut t| {goal_refresher.refresh(&mut t); t}))],
            rules: rules,
            name_source: name_source,
            goal_refresher: goal_refresher
        }
    }

    /// Process the next goal of the current alternative.
    pub fn step(&mut self) -> Step<A> {
        match self.alternatives.pop() {
            // no more branches to search, we're done
            None => Step::Done,
            Some(mut goals) => match goals.pop() {
                // current branch has no more goals, we found a solution
                None => Step::Found(self.build_solution(goals.solver)),
                // solve top-most goal of current branch
                Some(goal) => {
                    // we're potentially going to spawn of multiple branches, so
                    // make the current remaining goals shared as long as we
                    // don't touch the other branches.
                    if ! goals.current.is_empty() {
                        let remaining = std::mem::replace(&mut goals.current, vec![]);
                        goals.previous.push(Rc::new(remaining));
                    }
                    // compute branches that result from all rules matching the
                    // current goal. We extend the list of alternatives with the
                    // new branches reversed, so that the first matching goal
                    // comes last in the list of alternatives, ensuring that it
                    // will be processed first.
                    let new_alternatives = self.resolve(goal, goals).into_iter().rev();
                    self.alternatives.extend(new_alternatives);
                    // Tell caller that we made progress, but need more steps to
                    // find a solution
                    Step::Again
                }
            }
        }
    }

    /// Build a solution from the solver state, by renaming the internal
    /// variables back to those that have been used in the original goals.
    fn build_solution<S>(&self, solver: S) -> Solution<A> where S: std::ops::Deref<Target=unification::Solver<A>> {
        let mut solution = HashMap::new();
        for (renamed, original) in self.goal_refresher.resubst() {
            let var_solution = match solver.subst().get(renamed).map(Clone::clone) {
                None => Term::Var(*original),
                Some(mut t) => {
                    self.goal_refresher.undo_refresh(&mut t); t
                }
            };
            solution.insert(*original, var_solution);
        }
        Solution(solution)
    }

    /// Resolve a goal term originating from the given stack, producing new
    /// branches.
    fn resolve(&mut self, head: Term<A>, base_stack: GoalStack<A>) -> Vec<GoalStack<A>> {
        match self {
            // match on self so that the individual parts are borrowed
            // individually in the closure, otherwise, it complains that this
            // cannot be borrowed.
            Query { rules, name_source, .. } =>
                rules.iter()
                // match the head against every rule in the database
                .flat_map(|rule| {
                    // produce a fresh instantiation of the rule
                    let mut rule_head = rule.head.clone();
                    let mut rule_refresher = Refresher::new(name_source.clone());
                    rule_refresher.refresh(&mut rule_head);

                    // try to match it with the given head
                    let mut solver = (*base_stack.solver).clone();
                    solver.push_eq(rule_head.clone(), head.clone());
                    if solver.solve().is_ok() {
                        // it matches, so we instantiate the rules tail as well
                        let rule_tail = rule.tail.iter()
                            .map(Clone::clone)
                            .map(|mut t| { rule_refresher.refresh(&mut t); t })
                            .map(|t| solver.normalize(t))
                            .collect();
                        // and build a new stack based on the old one, with the new goals
                        let new_stack = GoalStack {
                            current: rule_tail,
                            previous: base_stack.previous.clone(),
                            solver: Rc::new(solver)
                        };
                        Some(new_stack)
                    } else {
                        None
                    }
                })
                .collect()
        }
    }
}

impl<'a, A> Iterator for Query<'a, A> where A: Copy + Eq {
    type Item = Solution<A>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                Step::Done => break None,
                Step::Again => (),
                Step::Found(solution) => break Some(solution)
            }
        }
    }
}

/// Shared source of unique names. It uses interior mutation to provide fresh names in multiple places.
#[derive(Debug, Clone)]
struct NameSource(Rc<RefCell<usize>>);

impl NameSource {
    pub fn new(initial: usize) -> Self {
        NameSource(Rc::new(RefCell::new(initial)))
    }

    pub fn fresh(&self) -> usize {
        let mut source = self.0.borrow_mut();
        let name = *source;
        *source += 1;
        name
    }
}

/// A refresher is used for renaming variables to fresh names.
#[derive(Debug, Clone)]
struct Refresher {
    name_source: NameSource,
    /// Substitution from old names to renamed names.
    subst: HashMap<VarId, VarId>,
    /// Substitution from renamed names to old names.
    resubst: HashMap<VarId, VarId>
}

impl Refresher {
    pub fn new(name_source: NameSource) -> Self {
        Refresher {
            name_source: name_source,
            subst: HashMap::new(),
            resubst: HashMap::new()
        }
    }

    /// Passed as a closure for the terms `subst` function. Refresh a single
    /// variable. It will always return the same name for the same input.
    fn refresh_var<A>(&mut self, x: VarId) -> Option<Term<A>> {
        if let Some(y) = self.subst.get(&x).map(Clone::clone) {
            Some(Term::Var(y))
        } else {
            let y = VarId(self.name_source.fresh());
            self.subst.insert(x, y);
            self.resubst.insert(y, x);
            Some(Term::Var(y))
        }
    }

    /// Refresh all variables in the given term with fresh ones.
    pub fn refresh<A>(&mut self, term: &mut Term<A>) where A: Copy + Eq {
        term.subst(&mut |x| self.refresh_var(x));
    }

    /// Return a reference to the backwards substitution, mapping the fresh
    /// names to the original names.
    pub fn resubst(&self) -> &HashMap<VarId, VarId> {
        &self.resubst
    }

    fn undo_refresh_var<A>(&self, x: VarId) -> Option<Term<A>> {
        self.resubst.get(&x).map(|y| Term::Var(*y))
    }

    /// Undo the renaming that has been performed as part of the refreshing.
    pub fn undo_refresh<A>(&self, term: &mut Term<A>) where A: Copy + Eq {
        term.subst(&mut |x| self.undo_refresh_var(x))
    }
}
