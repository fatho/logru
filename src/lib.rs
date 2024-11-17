//! # Logic programming in Rust
//!
//! Logru is an embeddable and fast solver for a subset of Prolog. At the core of the solver is the
//! [Universe] type which holds all known facts and rules.
//!
//! The [Universe] type represents all identifiers using IDs, there is no textual representation.
//! For a more Prolog-like syntax, and an example on how to use the [Universe] type to build
//! higher-level abstractions, have a look at the [textual] module.
//!
//! # Example
//!
//! As an example, let's define a few predicates for solving [Peano
//! arithmetic](https://en.wikipedia.org/wiki/Peano_axioms#Addition) expressions. In Prolog, these
//! could be written like this:
//!
//! ```prolog
//! is_natural(z).
//! is_natural(s(P)) :- is_natural(P).
//!
//! add(P, z, P) :- is_natural(P).
//! add(P, s(Q), s(R)) :- add(P, Q, R).
//! ```
//!
//! The `is_natural` predicate defines that zero (z) is a natural number, and each successor (s) of
//! a natural number is also a natural number.
//!
//! Addition is also defined recursively. An expression `add(P, Q, R)` should be read as the
//! statement `P + Q = R`. The first case expresses that `P + 0 = P` for all natural numbers P,
//! while the second case expresses that `P + s(Q) = s(R)` where `P + Q = R` (i.e. we add one on
//! both sides).
//!
//! Using the [Universe] type, we can encode these rules as follows:
//!
//! ```
//! use logru::ast::{self, Rule};
//!
//! let mut u = logru::Universe::new();
//!
//! // Obtain IDs for t he symbols we want to use in our terms.
//! // The order of these calls doesn't matter.
//! let s = u.alloc_symbol();
//! let z = u.alloc_symbol();
//!
//! let is_natural = u.alloc_symbol();
//! let add = u.alloc_symbol();
//!
//! // is_natural(z).
//! u.add_rule(Rule::fact(is_natural, vec![z.into()]));
//!
//! // is_natural(s(P)) :- is_natural(P).
//! u.add_rule(ast::forall(|[p]| {
//!     Rule::fact(is_natural, vec![ast::app(s, vec![p.into()])])
//!     .when(is_natural, vec![p.into()])
//! }));
//!
//! // add(P, z, P) :- is_natural(P).
//! u.add_rule(ast::forall(|[p]| {
//!     Rule::fact(add, vec![p.into(), z.into(), p.into()])
//!     .when(is_natural, vec![p.into()])
//! }));
//!
//! // add(P, s(Q), s(R)) :- add(P, Q, R).
//! u.add_rule(ast::forall(|[p, q, r]| {
//!     Rule::fact(
//!         add,
//!         vec![
//!             p.into(),
//!             ast::app(s, vec![q.into()]),
//!             ast::app(s, vec![r.into()]),
//!         ],
//!     )
//!     .when(add, vec![p.into(), q.into(), r.into()])
//! }));
//! ```
//!
//! We can then execute queries against this universe, e.g. having the solver compute the solution
//! for `X + 2 = 3`. In our relational interpretation, this boils down to proving the statement
//! "there exists an X such that `add(X, s(s(z)), s(s(s(z))))` holds".
//!
//! ```
//! # use logru::ast::{self, Rule};
//! # use logru::solver::Plain;
//! # let mut u = logru::Universe::new();
//! # let s = u.alloc_symbol();
//! # let z = u.alloc_symbol();
//! # let is_natural = u.alloc_symbol();
//! # let add = u.alloc_symbol();
//! #
//! # u.add_rule(Rule::fact(is_natural, vec![z.into()]));
//! # u.add_rule(ast::forall(|[p]| {
//! #     Rule::fact(is_natural, vec![ast::app(s, vec![p.into()])])
//! #     .when(is_natural, vec![p.into()])
//! # }));
//! # u.add_rule(ast::forall(|[p]| {
//! #     Rule::fact(add, vec![p.into(), z.into(), p.into()])
//! #     .when(is_natural, vec![p.into()])
//! # }));
//! # u.add_rule(ast::forall(|[p, q, r]| {
//! #     Rule::fact(
//! #         add,
//! #         vec![
//! #             p.into(),
//! #             ast::app(s, vec![q.into()]),
//! #             ast::app(s, vec![r.into()]),
//! #         ],
//! #     )
//! #     .when(add, vec![p.into(), q.into(), r.into()])
//! # }));
//! let query = ast::exists(|[x]| {
//!     ast::Query::new(
//!         add,
//!         vec![
//!             x.into(),
//!             ast::app(s, vec![ast::app(s, vec![z.into()])]),
//!             ast::app(s, vec![ast::app(s, vec![ast::app(s, vec![z.into()])])]),
//!         ],
//!     )
//! });
//! // Obtain an iterator that allows us to exhaustively search the solution space:
//! let solutions = logru::query_dfs(&u, Plain, &query);
//! // Sanity check that there is only one solution, and it is the expected one
//! assert_eq!(
//!     solutions.collect::<Vec<_>>(),
//!     vec![vec![Some(ast::app(s, vec![z.into()]))],]
//! );
//! ```
//!
//! Logru provides the [query_dfs] solver for proving such statements. It performs a left-to-right
//! depth first search through the solution space. This means that it processes goals (both in the
//! original query and in matching rules) from left to right, and eagerly recurses into the first
//! available goal until it is fully resolved.
//!
//! To my knowledge, this strategy is also used by SWI Prolog. It is efficient to implement, but it
//! requires some care in how the predicates are set up in order to avoid infinite recursion.
//!
//! While not provided by Logru itself, it is possible to build custom solvers using different
//! search strategies on top of the universe abstraction.
//!
//!

pub mod arithmetic;
pub mod ast;
pub mod solver;
pub mod term_arena;
pub mod textual;
pub mod universe;

pub use solver::query_dfs;
pub use universe::Universe;
