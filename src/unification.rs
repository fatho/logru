use std::vec::Vec;
use std::collections::HashMap;

/// Identifier of a variable used in unification.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarId(pub usize);

/// The two types of failures that can occur during unification.
#[derive(Debug, Clone)]
pub enum UnificationFailure<A> {
    /// Failed attempt to unify the given variable and term, because the term
    /// contains the variable. Actually unifying those two would result in an
    /// infinite term.
    OccursCheckFailed(VarId, Term<A>),
    /// The two applicative terms do not match.
    NoMatch(Term<A>, Term<A>)
}

/// The type of terms used in unification.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Term<A> {
    /// An unbound variable
    Var(VarId),
    /// An applicative term `f(t_1, ..., t_n)`
    App(A, Vec<Term<A>>)
}

pub type UnificationResult<A, T> = Result<T, UnificationFailure<A>>;

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
    /// The current substitution, based on the goals that were already solved
    subst: HashMap<VarId, Term<A>>
}

impl<A> Solver<A> where A: Copy + Eq {
    pub fn new() -> Self {
        Solver {
            goals: Vec::new(),
            subst: HashMap::new()
        }
    }

    pub fn push_eq(&mut self, s: Term<A>, t: Term<A>) {
        let s_norm = self.normalize(s);
        let t_norm = self.normalize(t);
        self.goals.push(Goal::Eq(s_norm, t_norm))
    }

    pub fn step(&mut self) -> UnificationResult<A, ()> {
        // NOTE: When this function fails, it will have removed the conflicting
        // goal from the goal stack, so subsequent invocations might succeed
        // again. This is probably not what we want, but it doesn't hurt in the
        // way this solver is currently used.
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
                        Err(UnificationFailure::NoMatch(Term::App(f, fargs), Term::App(g, gargs)))
                    }
                }
                // eliminate constraints where one or both sides are a single
                // variable (the case where both sides are the same variable is
                // handled above)
                Goal::Eq(t@Term::App(_, _), Term::Var(x)) |
                Goal::Eq(Term::Var(x), t) => {
                    if t.occurs(x) {
                        Err(UnificationFailure::OccursCheckFailed(x, t))
                    } else {
                        // apply the new substitution to all remaining goals and existing substitutions
                        for v in self.subst.values_mut() {
                            v.subst(&mut |y| if y == x { Some(t.clone()) } else { None });
                        }
                        for g in self.goals.iter_mut() {
                            g.subst(&mut |y| if y == x { Some(t.clone()) } else { None });
                        }
                        self.subst.insert(x, t); Ok(())
                    }
                }
            }
        }
    }

    /// Solve the current set of goals, or fail.
    pub fn solve(&mut self) -> UnificationResult<A, ()> {
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
            Term::Var(x) => self.subst.get(&x).map_or(Term::Var(x), Clone::clone),
            Term::App(f, args) => Term::App(f, args.into_iter().map(|s| self.normalize(s)).collect())
        }
    }

    pub fn subst(&self) -> &HashMap<VarId, Term<A>> {
        &self.subst
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
