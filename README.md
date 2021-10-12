# LogRu

**Log**ic programming in **Ru**st.

At the heart of this project is a small, efficient Rust library for solving first-order predicate
logic expressions like they can be found in e.g. Prolog.

Additionally, there is a REPL executable for interactively playing around with the implementation.

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
