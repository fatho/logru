use std::vec::Vec;
use std::collections::HashMap;

/// Identifier of a variable used in unification.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarId(pub usize);

/// The type of terms used in unification.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Term<A> {
    /// An unbound variable
    Var(VarId),
    /// An applicative term `f(t_1, ..., t_n)`
    App(A, Vec<Term<A>>)
}

/// A solution for a set of constraints, assigning values to variables.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Solution<A>(HashMap<VarId, Term<A>>);

impl<A> Solution<A> {
    /// Create a new empty solution.
    pub fn new() -> Self {
        Solution(HashMap::new())
    }

    /// Build a solution from a series of assignments.
    pub fn from_assignments<I>(assignments: I) -> Solution<A>
    where I: IntoIterator<Item=(VarId, Term<A>)> {
        let mut solution = HashMap::new();
        for (k, v) in assignments {
            solution.insert(k, v);
        }
        Solution(solution)
    }

    pub fn insert(&mut self, var: VarId, term: Term<A>) {
        self.0.insert(var, term);
    }

    pub fn get(&self, var: VarId) -> Option<&Term<A>> {
        self.0.get(&var)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item=&mut Term<A>> {
        self.0.values_mut()
    }
}

/// The two types of failures that can occur during unification.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum UnificationFailure {
    /// Failed attempt to unify a variable and term, because the term contains
    /// the variable. Actually unifying those two would result in an infinite
    /// term.
    OccursCheckFailed,
    /// Two applicative terms do not match.
    NoMatch
}

pub type UnificationResult<T> = Result<T, UnificationFailure>;

/// A goal that the unifier has to prove. Currently, there are only equality
/// goals.
#[derive(Debug, Clone)]
pub enum Goal<A> {
    /// Goal for proving that the two terms are equal.
    Eq(Term<A>, Term<A>),
}

impl<A> Goal<A> where A: Copy + Eq {
    /// Apply a substitution to all terms in this goal. If the callback returns
    /// `None`, the variable is left unchanged.
    pub fn subst(&mut self, sub: &mut impl FnMut(VarId) -> Option<Term<A>>) {
        // NOTE: is taking the closure by &mut reference the only way for
        // actually using it twice in the body?
        match self {
            Goal::Eq(t1, t2) => {
                t1.subst(sub); t2.subst(sub);
            }
        }
    }
}

/// A unification solver based on the algorithm by Martelli, Montanari (1982).
#[derive(Debug, Clone)]
pub struct Solver<A> {
    /// Current stack of goals yet to be solved
    goals: Vec<Goal<A>>,
    /// The current partial solution, based on the goals that were already solved
    solution: Solution<A>
}

impl<A> Solver<A> where A: Copy + Eq {
    pub fn new() -> Self {
        Solver {
            goals: Vec::new(),
            solution: Solution::new()
        }
    }

    pub fn push_eq(&mut self, s: Term<A>, t: Term<A>) {
        let s_norm = self.normalize(s);
        let t_norm = self.normalize(t);
        self.goals.push(Goal::Eq(s_norm, t_norm))
    }

    /// Performs one solution step by processing the top most goal. If the
    /// topmost goal is unsolvable, it remains in place and subsequent calls
    /// will fail as well.
    pub fn step(&mut self) -> UnificationResult<()> {
        match self.goals.pop() {
            None => Ok(()),
            Some(goal) => match goal {
                // delete constraints that equate a variable with itself
                Goal::Eq(Term::Var(x), Term::Var(y)) if x == y => Ok(()),
                // decompose constraints involving applicative terms
                Goal::Eq(Term::App(f, fargs), Term::App(g, gargs)) => {
                    if f == g && fargs.len() == gargs.len() {
                        Ok(self.goals.extend(fargs.into_iter().zip(gargs.into_iter()).map(|(s, t)| Goal::Eq(s, t))))
                    } else {
                        // unpop unsolvable goal
                        self.goals.push(Goal::Eq(Term::App(f, fargs), Term::App(g, gargs)));
                        Err(UnificationFailure::NoMatch)
                    }
                }
                // eliminate constraints where one or both sides are a single
                // variable (the case where both sides are the same variable is
                // handled above)
                Goal::Eq(t@Term::App(_, _), Term::Var(x)) |
                Goal::Eq(Term::Var(x), t) => {
                    if t.occurs(x) {
                        // unpop unsolvable goal
                        self.goals.push(Goal::Eq(Term::Var(x), t));
                        Err(UnificationFailure::OccursCheckFailed)
                    } else {
                        // apply the new substitution to all remaining goals and existing substitutions
                        for v in self.solution.values_mut() {
                            v.subst(&mut |y| if y == x { Some(t.clone()) } else { None });
                        }
                        for g in self.goals.iter_mut() {
                            g.subst(&mut |y| if y == x { Some(t.clone()) } else { None });
                        }
                        self.solution.insert(x, t); Ok(())
                    }
                }
            }
        }
    }

    /// Solve the current set of goals, or fail.
    pub fn solve(&mut self) -> UnificationResult<()> {
        // this always terminates, because every step brings us closer to the
        // solution or fails
        while !self.goals.is_empty() {
            self.step()?;
        }
        Ok(())
    }

    /// Apply the current substitution to a term.
    pub fn normalize(&self, t: Term<A>) -> Term<A> {
        match t {
            Term::Var(x) => self.solution.get(x).map_or(Term::Var(x), Clone::clone),
            Term::App(f, args) => Term::App(f, args.into_iter().map(|s| self.normalize(s)).collect())
        }
    }

    pub fn solution(&self) -> &Solution<A> {
        &self.solution
    }
}


impl<A> Term<A> where A: Copy + Eq {
    pub fn occurs(&self, x: VarId) -> bool {
        match self {
            Term::Var(y) => x == *y,
            Term::App(_, args) => args.iter().any(|s| s.occurs(x))
        }
    }

    pub fn subst(&mut self, sub: &mut impl FnMut(VarId) -> Option<Term<A>>) {
        let new = match self {
            Term::Var(y) => sub(*y),
            Term::App(_, args) => {
                for arg in args.iter_mut() {
                    arg.subst(sub);
                }
                None
            }
        };
        if let Some(new_self) = new {
            *self = new_self;
        }
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    enum Atom {
        Leaf, Node
    }

    fn leaf() -> Term<Atom> {
        Term::App(Atom::Leaf, vec![])
    }

    fn node2(s: Term<Atom>, t: Term<Atom>) -> Term<Atom> {
        Term::App(Atom::Node, vec![s, t])
    }

    fn node3(s: Term<Atom>, t: Term<Atom>, u: Term<Atom>) -> Term<Atom> {
        Term::App(Atom::Node, vec![s, t, u])
    }

    fn var<A>(v: usize) -> Term<A> {
        Term::Var(VarId(v))
    }

    #[test]
    pub fn occurs_check() {
        let mut solver = Solver::new();
        solver.push_eq(node2(leaf(), var(0)), var(0));
        assert_eq!(solver.solve(), Err(UnificationFailure::OccursCheckFailed))
    }

    #[test]
    pub fn different_applicative_head() {
        let mut solver = Solver::new();
        solver.push_eq(node2(leaf(), var(0)), leaf());
        assert_eq!(solver.solve(), Err(UnificationFailure::NoMatch))
    }

    #[test]
    pub fn same_applicative_head_different_arg_length() {
        let mut solver = Solver::new();
        solver.push_eq(node2(leaf(), var(0)), node3(var(1), leaf(), leaf()));
        assert_eq!(solver.solve(), Err(UnificationFailure::NoMatch))
    }

    #[test]
    pub fn multiple_goals_conflict() {
        let mut solver = Solver::new();
        solver.push_eq(node2(leaf(), var(0)), node2(var(1), leaf()));
        solver.push_eq(node2(leaf(), node3(leaf(), leaf(), leaf())), node2(var(1), var(0)));
        assert_eq!(solver.solve(), Err(UnificationFailure::NoMatch))
    }

    #[test]
    pub fn unifies() {
        let mut solver = Solver::new();
        solver.push_eq(node2(leaf(), var(0)), node2(var(1), node3(leaf(), node2(var(1), leaf()), leaf())));
        assert_eq!(solver.solve(), Ok(()));
        assert_eq!(solver.solution(), &Solution::from_assignments(vec![
            (VarId(0), node3(leaf(), node2(leaf(), leaf()), leaf())),
            (VarId(1), leaf())
        ]));
    }
}
