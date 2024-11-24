//! # An abstract syntax tree for logic terms
//!
//! This module defines a bunch of types for representing logic terms used by the solver.
//!
//! The root nodes are [Rule] for representing facts and rules for deriving facts, and [Query] for
//! representing queries against a set of rules.

/// A symbol in a logic expression, e.g. `foo` and `bar` in `foo(bar, _)`. It can refer to both a
/// predicate and data.
///
/// Internally, symbols are represented by numeric IDs for solver efficency.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(usize);

impl Sym {
    /// Return the ordinal number of this symbol.
    ///
    /// This function can be useful for lookup tables that are indexed by symbols.
    #[inline(always)]
    pub fn ord(self) -> usize {
        self.0
    }

    /// Build a symbol from its ordinal number.
    ///
    /// Inverse of [`Sym::ord`].
    #[inline(always)]
    pub fn from_ord(ord: usize) -> Sym {
        Sym(ord)
    }
}

/// A variable in a logic expression, represented by a numeric ID.
///
/// While in principle, these IDs can be chosen freely, in practice, they should be as small as
/// possible, because the solver uses them as indexes into arrays and holes in the ID range are
/// wasted space.
///
/// When using the [`forall`] and [`exists`] helpers for constructing rules and queries, then they
/// will already choose the smallest possible variable IDs (i.e. the range `0..count`).
///
/// For manually contructing variables, use [`Var::from_ord`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(usize);

impl Var {
    /// Return the ordinal number of this variable.
    ///
    /// This function can be useful for lookup tables that are indexed by variables.
    #[inline(always)]
    pub fn ord(self) -> usize {
        self.0
    }

    /// Build a variable from its ordinal number.
    ///
    /// Inverse of [`Var::ord`].
    #[inline(always)]
    pub fn from_ord(ord: usize) -> Var {
        Var(ord)
    }

    /// Apply an offset to the variable's ID.
    ///
    /// This is used for quickly generating fresh variables when rules need to be instantiated.
    /// `v.offset(n)` is equivalent to `Var::from_ord(v.ord() + n)`.
    pub fn offset(self, offset: usize) -> Var {
        Var(self.0 + offset)
    }
}

/// Representation of a logic term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A variable term.
    Var(Var),
    /// An application term, see [`AppTerm`].
    App(AppTerm),
    /// A signed 64-bit integer
    Int(i64),
    /// The special built-in cut predicate.
    ///
    /// Evaluating it prunes all further choices for the currently active rule.
    Cut,
}

impl Term {
    /// Count the number of variable slots needed for storing the variable assignments for this
    /// term.
    ///
    /// If the highest variable ordinal ([`Var::ord`]) of any variable occurring in this term is
    /// `n`, then it will return `n + 1`.
    pub fn count_var_slots(&self) -> usize {
        match self {
            Term::Var(v) => v.0 + 1,
            Term::App(app) => app.count_var_slots(),
            Term::Int(_) => 0,
            Term::Cut => 0,
        }
    }
}

impl From<Var> for Term {
    fn from(v: Var) -> Self {
        Term::Var(v)
    }
}

impl From<Sym> for Term {
    fn from(s: Sym) -> Self {
        Term::App(s.into())
    }
}

impl From<AppTerm> for Term {
    fn from(at: AppTerm) -> Self {
        Term::App(at)
    }
}

/// An application term, i.e. a term of the form `functor(arg0, arg1, ...)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppTerm {
    /// The functor being applied.
    pub functor: Sym,
    /// The arguments of the application.
    pub args: Vec<Term>,
}

impl From<Sym> for AppTerm {
    fn from(s: Sym) -> Self {
        Self {
            functor: s,
            args: vec![],
        }
    }
}

impl AppTerm {
    pub fn new(functor: Sym, args: Vec<Term>) -> Self {
        Self { functor, args }
    }

    /// Count the number of variable slots needed to accommodate for all variables in this term.
    ///
    /// See [`Term::count_var_slots`].
    pub fn count_var_slots(&self) -> usize {
        self.args
            .iter()
            .map(|t| t.count_var_slots())
            .max()
            .unwrap_or(0)
    }
}

/// Convenience constructor for an application term.
pub fn app(functor: Sym, args: Vec<Term>) -> Term {
    Term::App(AppTerm::new(functor, args))
}

/// Convenience constructor for a variable term.
pub fn var(var: Var) -> Term {
    Term::Var(var)
}

/// Representation of logic rules (and as a special case, of facts). Logically, it can be
/// interpreted as "`tail` implies `head`".
///
/// # Examples
///
/// ```
/// use logru::ast::*;
/// // Let's build the rule `grandparent(X, Y) :- parent(X, Z), parent(Z, Y).`, i.e.
/// // X is a grandparent of Y, when there is a Z such that X is a parent of Z and Z is a parent of Y.
///
/// let grandparent = Sym::from_ord(0); // Note: Normally, you'd get these `Sym`s from the `Universe`.
/// let parent = Sym::from_ord(1);
/// let rule = forall(|[x, y, z]|
///     Rule::fact(grandparent, vec![x.into(), y.into()])
///     .when(parent, vec![x.into(), z.into()])
///     .when(parent, vec![z.into(), y.into()])
/// );
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    /// The rule head, i.e. the fact that can be derived when all the `tail` terms are proven true.
    pub head: AppTerm,
    /// The terms that need to hold for the `head` to become true. If the tail is empty, then the
    /// head is always true. The rule is then called a fact.
    pub tail: Vec<Term>,
    /// Names of the variables used in this rule
    pub scope: Option<VarScope>,
}

impl Rule {
    /// Create a "fact" rule, i.e. one that always holds.
    pub fn fact(pred: Sym, args: Vec<Term>) -> Self {
        let head = AppTerm {
            functor: pred,
            args,
        };
        Self {
            head,
            tail: vec![],
            scope: None,
        }
    }

    /// Constrain a rule with an additional condition that must hold for the rule head to become
    /// true.
    pub fn when(mut self, pred: Sym, args: Vec<Term>) -> Self {
        let app_term = AppTerm {
            functor: pred,
            args,
        };
        self.tail.push(Term::App(app_term));
        self
    }
}

/// Representation of logic queries, i.e. a conjunction of facts that we want to prove true (by
/// finding a solution) or false (by exhausting the solution space).
///
/// # Examples
///
/// ```
/// use logru::ast::*;
/// // Let's build the query `grandparent(bob, X),female(X)`,
/// // for looking up all the granddaughters of Bob.
///
/// let grandparent = Sym::from_ord(0); // Note: Normally, you'd get these `Sym`s from the `Universe`.
/// let female = Sym::from_ord(1);
/// let bob = Sym::from_ord(2);
/// let rule = exists(|[x]|
///     Query::single_app(grandparent, vec![bob.into(), x.into()])
///     .and_app(female, vec![x.into()])
/// );
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    /// The conunctive goals that need to be proven as part of this query.
    pub goals: Vec<Term>,
    /// Names of the variables used in this query
    pub scope: Option<VarScope>,
}

impl Query {
    /// The query that is vacuously true
    pub fn empty() -> Query {
        Query::new(vec![], None)
    }

    /// A query consisting of a set of goals.
    pub fn new(goals: Vec<Term>, scope: Option<VarScope>) -> Query {
        Query { goals, scope }
    }

    /// A query with just a single goal.
    pub fn single_app(pred: Sym, args: Vec<Term>) -> Query {
        Query::single(Term::App(AppTerm::new(pred, args)))
    }

    /// A query with just a single goal.
    pub fn single(pred: Term) -> Query {
        Query::new(vec![pred], None)
    }

    /// Add another goal to this query.
    pub fn and_app(self, pred: Sym, args: Vec<Term>) -> Self {
        self.and(Term::App(AppTerm {
            functor: pred,
            args,
        }))
    }

    pub fn and(mut self, pred: Term) -> Self {
        self.goals.push(pred);
        self
    }

    /// Count the number of variable slots needed to accommodate for all variables in this query.
    ///
    /// See [`Term::count_var_slots`].
    pub fn count_var_slots(&self) -> usize {
        self.goals
            .iter()
            .map(|t| t.count_var_slots())
            .max()
            .unwrap_or(0)
    }
}

/// Mapping of variable names to indices inside a scope (e.g. a rule or a query).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarScope {
    names: Vec<Option<String>>,
}

impl VarScope {
    pub fn new() -> Self {
        Self { names: Vec::new() }
    }

    /// Get the index associated with a name, or insert a new association.
    pub fn get_or_insert(&mut self, name: &str) -> Var {
        self.names
            .iter()
            .position(|existing| existing.as_ref().map_or(false, |x| x == name))
            .map(Var::from_ord)
            .unwrap_or_else(|| {
                let ord = self.names.len();
                self.names.push(Some(name.to_string()));
                Var::from_ord(ord)
            })
    }

    /// Insert a new unnamed wildcard variable.
    pub fn insert_wildcard(&mut self) -> Var {
        let ord = self.names.len();
        self.names.push(None);
        Var::from_ord(ord)
    }

    /// Return the associated name of the given variable.
    pub fn get_name(&self, var: Var) -> Option<&str> {
        self.names.get(var.ord()).and_then(|n| n.as_deref())
    }
}

impl Default for VarScope {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper function for populating an array with incrementing variable IDs.
fn quantify<R, const N: usize>(f: impl FnOnce([Var; N]) -> R) -> R {
    let mut vars = [Var::from_ord(0); N];
    vars.iter_mut()
        .enumerate()
        .for_each(|(i, var)| *var = Var::from_ord(i));
    f(vars)
}

/// A universal quantification that can be used for more naturally describing the creation of rules.
///
/// See the example for the [`Rule`] type.
pub fn forall<const N: usize>(f: impl FnOnce([Var; N]) -> Rule) -> Rule {
    quantify(f)
}

/// An existential quantification that can be used for more naturally describing the creation of
/// queries.
///
/// See the example for the [`Query`] type.
pub fn exists<const N: usize>(f: impl FnOnce([Var; N]) -> Query) -> Query {
    quantify(f)
}
