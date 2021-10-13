# LogRu

**Log**ic programming in **Ru**st.

![ci badge](https://github.com/fatho/logru/actions/workflows/ci.yml/badge.svg)

## Overview

At the heart of this project is a small, efficient Rust library for solving first-order predicate
logic expressions like they can be found in e.g. Prolog.

Additionally, there is a [REPL example](examples/repl.rs) for interactively playing around with the
implementation.

Compared to Prolog, it currently lacks some features though. Most notable, there are
- no negation or cut,
- no built-in types (like integers), and
- no predicates with side effects (like doing IO).

## Showcase

In the REPL you can quickly get started by loading one of the provided test files with some
pre-defined facts and rules, e.g. for [Peano arithmetic](testfiles/arithmetic.lru):

```
#===================#
# LogRu REPL v0.1.0 #
#===================#

?- :load testfiles/arithmetic.lru
Loaded!
```

We can then ask it to solve 2 + 3 (and find the correct answer 5):

```
?- add(s(s(z)), s(s(s(z))), $0).
Found solution:
  $0 = s(s(s(s(s(z)))))
No more solutions.
```

It is also possible to enumerate all pairs of terms that add up to five:

```
?- add($0, $1, s(s(s(s(s(z)))))).
Found solution:
  $0 = s(s(s(s(s(z)))))
  $1 = z
Found solution:
  $0 = s(s(s(s(z))))
  $1 = s(z)
Found solution:
  $0 = s(s(s(z)))
  $1 = s(s(z))
Found solution:
  $0 = s(s(z))
  $1 = s(s(s(z)))
Found solution:
  $0 = s(z)
  $1 = s(s(s(s(z))))
Found solution:
  $0 = z
  $1 = s(s(s(s(s(z)))))
No more solutions.
```

## Rust API

The core of the API doesn't work with a textual representation of terms like the REPL does, but
encodes everything as semi-opaque IDs. There are then higher-level APIs that provide naming for
those IDs.

### Core API

At the core of the solver is the `logru::Universe` type which holds all known facts and rules.
A few simple rules for [Peano arithmetic](https://en.wikipedia.org/wiki/Peano_axioms#Addition) can
be defined like this:

```rust
let mut u = logru::Universe::new();

// Obtain IDs for t he symbols we want to use in our terms.
// The order of these calls doesn't matter.
let s = u.alloc_symbol();
let z = u.alloc_symbol();

let is_natural = u.alloc_symbol();
let add = u.alloc_symbol();

// Define the fact `is_natural(z)`, i.e. that zero is a natural number
u.add_rule(Rule::fact(is_natural, vec![z.into()]));

// Define the rule `is_natural(s(P)) :- is_natural(P)`, i.e. that
// the successor of P is a natural number if P is also a natural number.
u.add_rule(forall(|[p]| {
    Rule::fact(is_natural, vec![ast::app(s, vec![p.into()])])
    .when(is_natural, vec![p.into()])
}));

// Now we define a predicate for addition that we'll call add.
// The statement `add(P, Q, R)` is true if P + Q = R.

// Define the rule `add(P, z, P) :- is_natural(P)`, i.e. that
// adding zero to P is P if P is a natural number.
// This is the base case of Peano addition.
u.add_rule(forall(|[p]| {
    Rule::fact(add, vec![p.into(), z.into(), p.into()])
    .when(is_natural, vec![p.into()])
}));

// Finally, define the rule `add(P, s(Q), s(R)) :- add(P, Q, R)`,
// the recursive case of Peano addition.
u.add_rule(forall(|[p, q, r]| {
    Rule::fact(
        add,
        vec![
            p.into(),
            ast::app(s, vec![q.into()]),
            ast::app(s, vec![r.into()]),
        ],
    )
    .when(add, vec![p.into(), q.into(), r.into()])
}));
```

We can now ask the solver to prove statements within this universe, e.g. that "there exists an X
such that X + 2 = 3". This statement is indeed true for X = 1, and indeed, the solver will provide
this answer:

```rust
// Obtain an iterator that allows us to exhaustively search the solution space:
let solutions = query_dfs(
    &u,
    &exists(|[x]| {
        Query::new(
            add,
            vec![
                x.into(),
                ast::app(s, vec![ast::app(s, vec![z.into()])]),
                ast::app(s, vec![ast::app(s, vec![ast::app(s, vec![z.into()])])]),
            ],
        )
    }),
);
// Sanity check
assert_eq!(
    solutions.collect::<Vec<_>>(),
    vec![vec![Some(ast::app(s, vec![z.into()]))],]
);
```

The solver uses a left-to-right depth-first search through the provided and derived goals. This is
efficient to implement, but requires some care in how the predicates are set up in order to avoid an
infinite recursion.

### Textual API

For an example of the textual API, see e.g. [`examples/zebra.rs`](examples/zebra.rs), solving a
variant of the famous [Zebra puzzle](https://en.wikipedia.org/wiki/Zebra_Puzzle).

The syntax is very similar to Prolog, with the main difference that there are no wildcards (every
variable must be explicitly named) and variables are still named numerically.

### Performance

A rudimentary performance comparison with SWI Prolog has been performed using an inefficient version
of the Zebra puzzle ([`testfiles/zebra-reverse.lru`](testfiles/zebra-reverse.lru)) where the clauses
of the `puzzle` rule are reversed.

For both SWI Prolog and Logru, this makes the Puzzle a lot slower to solve (not surprising since
AFAIK SWI Prolog uses the same search order).

While Logru takes about 60ms to solve the Puzzle and to conclude that there are no further
solutions, Prolog takes about 25ms to find the solution and an additional 6ms to rule out any
further solutions for a total of 31s.

A large portion of that difference is apparently caused by the occurs check, which seems to be off
by default in Prolog. In a version of Logru compiled without occurs check, the same puzzle is solved
in ~35ms.

```
?- :load testfiles/zebra-reverse.lru
Loaded!
?- :time puzzle($0).
Found solution:
  $0 = list(house(yellow, norway, water, diplomat, fox), house(blue, italy, tea, physician, horse), house(red, england, milk, photographer, snails), house(white, spain, juice, violinist, dog), house(green, japan, coffee, painter, zebra))
No more solutions.
Took 0.0603s
```

```
?- consult('zebra-inv.pro').
true.

?- time(puzzle(Houses)).
% 86,676 inferences, 0.025 CPU in 0.025 seconds (100% CPU, 3428088 Lips)
Houses = list(house(yellow, norway, water, diplomat, fox), house(blue, italy, tea, physician, horse), house(red, england, milk, photographer, snails), house(white, spain, juice, violinist, dog), house(green, japan, coffee, painter, zebra)) ;
% 22,610 inferences, 0.006 CPU in 0.006 seconds (100% CPU, 3518245 Lips)
false.
```


## Future Plans

Without committing to any sort of timeline, additional features that are worth experimenting with
are:
- Recursion and memory limits.
- A profiling mode that counts some interesting facts and figures about the solver (e.g. number of
  steps taken, number of instantiated rules, peak memory usage).
- Making things even faster by e.g. optimising the occurs check.
- Named variables in the textual API.
- Auto-completion in the REPL.
- Impure predicates (i.e. those having an implementation in Rust and can manipulate the solver state
  directly).
- Cut and negation (which can probably be implemented given the previous point).


## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.