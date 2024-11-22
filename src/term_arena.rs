//! # Arena allocation for terms
//!
//! This module provides an alternative representation for logic terms that is more efficient to
//! work with in the solver than the one from the [`ast`] module.
//!
//! It's not used for the "external" interface because while being more efficient in certain cases,
//! the interface is also more cumbersome to use. As a trade-off, conversion happens at interface
//! boundaries of the solver.
//!
//! The module is exported nontheless because it can be useful when writing custom solvers.
//!
//! See the [TermArena] type for a usage example.

use crate::ast::{self, Sym, Var};

/// Handle for a term stored inside a term arena.
///
/// See [`TermArena::get_term`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct TermId(usize);

/// Handle for an argument of an application term stored inside a term arena.
///
/// See [`TermArena::get_arg`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct ArgId(usize);

/// Arena allocator for storing terms
///
/// It stores terms in a contiguous block of memory indexed by handles rather than using pointers.
/// Additionally, it supports fast stack-based deallocation.
///
/// # Notes
///
/// There are no safeguards against using [`TermId`]s from one arena with another arena. But since the
/// implementation only uses safe Rust, nothing *really* bad[^reallybad] will happen in that case.
/// Still, things might panic or just silently compute the wrong result.
///
/// [^reallybad]: Like [nasal demons](https://en.wikipedia.org/wiki/Undefined_behavior).
///
/// # Examples
///
/// ```
/// use logru::term_arena::*;
/// use logru::ast::{Sym,Var};
/// let mut arena = TermArena::new();
/// // Let's build the term `foo(bar, baz(v0), v1)` where `vx` refers to variables
/// // Normally, you'd get these `Sym`s from the `Universe`.
/// let foo = Sym::from_ord(0);
/// let bar = Sym::from_ord(1);
/// let baz = Sym::from_ord(2);
/// let v0 = Var::from_ord(0);
/// let v1 = Var::from_ord(1);
/// // Now on to building the terms
/// let t_bar = arena.app(bar, &[]);
/// let t_v0 = arena.var(v0);
/// let t_baz = arena.app(baz, &[t_v0]);
/// let t_v1 = arena.var(v1);
/// let t_foo = arena.app(foo, &[t_bar, t_baz, t_v1]);
/// // Sanity check
/// match arena.get_term(t_foo) {
///     Term::App(sym, args) => {
///         assert_eq!(sym, foo);
///         assert_eq!(
///             arena.get_args(args).collect::<Vec<_>>(),
///             vec![t_bar, t_baz, t_v1]
///         );
///     }
///     _ => unreachable!(),
/// }
/// ```
#[derive(Debug, Clone)]
pub struct TermArena {
    /// Terms that have been allocated in this arena. The [`TermId`]s are used as index into this
    /// vector.
    terms: Vec<Term>,
    /// Argument pointers for application terms. Each application term refers to a range inside this
    /// vector for their argument terms. This indirection allows us to keep the terms themselves
    /// free of pointers. The `ArgId`s are used as index into this vector.
    args: Vec<TermId>,
}

impl TermArena {
    /// Create a new empty arena.
    pub fn new() -> Self {
        Self {
            terms: vec![],
            args: vec![],
        }
    }

    /// Allocate a new variable term.
    pub fn var(&mut self, var: Var) -> TermId {
        let term = TermId(self.terms.len());
        self.terms.push(Term::Var(var));
        term
    }

    /// Allocate a new application term.
    pub fn app(&mut self, functor: Sym, args: &[TermId]) -> TermId {
        let term = TermId(self.terms.len());
        let arg_start = self.args.len();
        let arg_end = arg_start + args.len();
        self.args.extend_from_slice(args);
        self.terms.push(Term::App(
            functor,
            ArgRange {
                start: arg_start,
                end: arg_end,
            },
        ));
        term
    }

    /// Allocate a new integer term.
    pub fn int(&mut self, int: i64) -> TermId {
        let term = TermId(self.terms.len());
        self.terms.push(Term::Int(int));
        term
    }

    /// Copy terms from another "blueprint" arena into this arena, and apply an offset to all the
    /// variable indices used inside the blueprint.
    ///
    /// This function is used to efficiently instantiate rules with fresh variables while solving.
    ///
    /// # Returns
    ///
    /// This function returns a closure that can be used for translating [`TermId`]s that were created
    /// from the blueprint into [`TermId`]s that can be used with this arena.
    ///
    /// # Example
    ///
    /// As an example, let's instantiate the term that was built in the [type-level
    /// exampe](TermArena#example).
    ///
    /// ```
    /// # use logru::term_arena::*;
    /// # use logru::ast::{Sym,Var};
    /// # let mut arena = TermArena::new();
    /// # let foo = Sym::from_ord(0);
    /// # let bar = Sym::from_ord(1);
    /// # let baz = Sym::from_ord(2);
    /// # let v0 = Var::from_ord(0);
    /// # let v1 = Var::from_ord(1);
    /// # let t_bar = arena.app(bar, &[]);
    /// # let t_v0 = arena.var(v0);
    /// # let t_baz = arena.app(baz, &[t_v0]);
    /// # let t_v1 = arena.var(v1);
    /// # let t_foo = arena.app(foo, &[t_bar, t_baz, t_v1]);
    /// let mut new_arena = TermArena::new();
    /// let convert_id1 = new_arena.instantiate_blueprint(&arena, 10);
    /// let convert_id2 = new_arena.instantiate_blueprint(&arena, 20);
    /// // Verify that we now have two instances of `t_v0` in our new arena with different
    /// // variable offsets applied to them:
    /// assert_eq!(new_arena.get_term(convert_id1(t_v0)), Term::Var(v0.offset(10)));
    /// assert_eq!(new_arena.get_term(convert_id2(t_v0)), Term::Var(v0.offset(20)));
    /// // Verify that the two copies of the foo term are not identical
    /// assert_ne!(new_arena.get_term(convert_id1(t_foo)), new_arena.get_term(convert_id2(t_foo)));
    /// ```
    ///
    pub fn instantiate_blueprint(
        &mut self,
        blueprint: &TermArena,
        var_offset: usize,
    ) -> impl Fn(TermId) -> TermId {
        let here = self.checkpoint();
        self.terms
            .extend(blueprint.terms.iter().map(|term| match term {
                Term::Var(var) => Term::Var(var.offset(var_offset)),
                Term::App(func, args) => Term::App(
                    *func,
                    ArgRange {
                        start: args.start + here.args,
                        end: args.end + here.args,
                    },
                ),
                Term::Int(i) => Term::Int(*i),
            }));
        self.args.extend(
            blueprint
                .args
                .iter()
                .map(|term_id| TermId(term_id.0 + here.terms)),
        );

        let term_offset = here.terms;
        move |TermId(old)| TermId(old + term_offset)
    }

    /// Transitively insert a term in AST representation into this arena.
    ///
    /// This operation needs scratch space for handling arguments of an application term. In order
    /// to avoid allocations as much as possible, this scratch space needs to be provided
    /// externally. When this function returns, the scratch vector will contain the same elements as
    /// it did before.
    pub fn insert_ast_term(&mut self, scratch: &mut Vec<TermId>, term: &ast::Term) -> TermId {
        match term {
            ast::Term::Var(v) => self.var(*v),
            ast::Term::App(app) => self.insert_ast_appterm(scratch, app),
            ast::Term::Int(i) => self.int(*i),
        }
    }

    /// Transitively insert an application term in AST representation into this arena.
    ///
    /// See `insert_ast_term` for the notes about the `scratch` argument.
    pub fn insert_ast_appterm(&mut self, scratch: &mut Vec<TermId>, app: &ast::AppTerm) -> TermId {
        let args_start = scratch.len();
        for arg in &app.args {
            let arg_term = self.insert_ast_term(scratch, arg);
            scratch.push(arg_term);
        }
        let out = self.app(app.functor, &scratch[args_start..]);
        scratch.truncate(args_start);
        out
    }

    /// Dereference an argument handle into the corresponding [`TermId`] representing that argument.
    #[inline(always)]
    pub fn get_arg(&self, arg_id: ArgId) -> TermId {
        self.args[arg_id.0]
    }

    /// Dereference a range of arguments into the corresponding [`TermId`]s representing these
    /// arguments.
    #[inline(always)]
    pub fn get_args(&self, arg_range: ArgRange) -> impl Iterator<Item = TermId> + '_ {
        self.args[arg_range.start..arg_range.end].iter().copied()
    }

    /// Dereference a range of arguments into the corresponding [`TermId`]s, like
    /// [`TermArena::get_args`], but only return a successful reesult if there are exactly `N`
    /// arguments.
    #[inline(always)]
    pub fn get_args_fixed<const N: usize>(&self, args: ArgRange) -> Option<[TermId; N]> {
        if args.len() == N {
            let mut terms = self.get_args(args);
            let arr = std::array::from_fn(|_| terms.next().unwrap());
            debug_assert!(terms.next().is_none(), "bug: we checked the length above");
            Some(arr)
        } else {
            None
        }
    }

    /// Dereference a term handle into the actual term.
    #[inline(always)]
    pub fn get_term(&self, term_id: TermId) -> Term {
        self.terms[term_id.0]
    }

    /// Create a checkpoint that can be used for quickly releasing all terms that have been
    /// allocated after the checkpoint has been created.
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            terms: self.terms.len(),
            args: self.args.len(),
        }
    }

    /// Release all terms that have been allocated after the given checkpoint has been created.
    ///
    /// # Notes
    ///
    /// Release must be called in the inverse order of checkpoint creation (though checkpoints may
    /// be entirely skipped or reverted to twice). Otherwise, unspecified things will happen and the
    /// arena becomes corrupted. This is not a safety issue since no unsafe code is used, but it
    /// might pose a correctness issue.
    pub fn release(&mut self, checkpoint: &Checkpoint) {
        debug_assert!(checkpoint.args <= self.args.len() && checkpoint.terms <= self.terms.len());
        self.args.truncate(checkpoint.args);
        self.terms.truncate(checkpoint.terms);
    }
}

impl Default for TermArena {
    fn default() -> Self {
        Self::new()
    }
}

/// A memory allocation checkpoint that can be used for quickly releasing terms that have been
/// allocated in a `TermArena`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Checkpoint {
    /// Length of the terms vector at the time of creation.
    terms: usize,
    /// Length of the args vector at the time of creation.
    args: usize,
}

/// A (possibly empty) range of arguments of an application term.
///
/// It can be iterated over for obtaining [`ArgId`]s that can be used for looking up argument terms
/// in the arena using [`TermArena::get_arg`].
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ArgRange {
    start: usize,
    end: usize,
}

// NOTE: for better performance it can be beneficial to override additional iterator functions that
// have a suboptimal default implementation.
impl Iterator for ArgRange {
    type Item = ArgId;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start;
        if start == self.end {
            None
        } else {
            self.start += 1;
            Some(ArgId(start))
        }
    }

    #[inline]
    fn any<F>(&mut self, mut f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        (self.start..self.end).any(move |x| f(ArgId(x)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl ArgRange {
    /// Number of arguments represented by this range.
    #[inline]
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Check whether there are any arguments in this range.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

/// A term stored inside a `TermArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term {
    /// A variable term.
    Var(Var),
    /// An application term of the form `foo(arg1, arg2, arg3, ...)`.
    /// The argument range can be used to get the corresponding argument terms from the arena.
    App(Sym, ArgRange),
    /// A signed 64-bit integer
    Int(i64),
}

impl Term {
    /// If this term is [`Term::Int`], return the enclosed integer.
    pub fn as_int(self) -> Option<i64> {
        match self {
            Term::Int(i) => Some(i),
            _ => None,
        }
    }

    /// If this term is [`Term::App`] return the symbol and arguments.
    pub fn as_app(self) -> Option<(Sym, ArgRange)> {
        match self {
            Term::App(sym, args) => Some((sym, args)),
            _ => None,
        }
    }
}
