# Changelog

## v0.4.0 - 2024-12-01

Many thanks to [@dcz-self](https://github.com/dcz-self) for a bunch of contributions!

New features:
- The textual language now supports line comments with `%` ([#26](https://github.com/fatho/logru/pull/26))
- `VarScope`s now provide additional functions to inspect the variables in the scope ([#23](https://github.com/fatho/logru/pull/23))
- `TextualUniverse` is now captured immutably by prepared queries, so that multiple queries can be run concurrently against the universe ([#27](https://github.com/fatho/logru/pull/27))

Breaking changes:
- `SolutionIter` now returns `Solution`s rather than `Vec<_>`s, making it easier to relate goal variables to solution terms ([#25](https://github.com/fatho/logru/pull/25))
- The concrete symbol storage used by e.g. the parser and some resolvers is now abstracted behind a `SymbolStorage` trait (as part of the works for [#27](https://github.com/fatho/logru/pull/27))


## v0.3.0 - 2024-11-24

New features:
- Named variables and wildcards ([#14](https://github.com/fatho/logru/pull/14))
- Integer arithmetic (see `logru::resolver::arithmetic` module)
  ([#18](https://github.com/fatho/logru/pull/18))
- Extensibility through custom predicate resolvers (see `Resolver` trait and the REPL example)
  ([#17](https://github.com/fatho/logru/pull/17) and [#19](https://github.com/fatho/logru/pull/19))
- Cut ([#20](https://github.com/fatho/logru/pull/20))

Major breaking changes:
- Numeric variable naming is no longer supported.
- Struct `CompiledRuleDb` is now called `RuleSet`.
- Module `solver` is now called `search`.
- The `Universe` type is now roughly subsumed by the `SymbolStore` and `RuleResolver` types.
- The `NamedUniverse` type has been absorbed by `SymbolStore`, which now provides allocating symbol
  IDs and naming them in one.

Bug fixes:
- Occurs check did not follow bound variables (fixed in
  [#16](https://github.com/fatho/logru/pull/16))


## v0.2.0 - 2021-10-13

Initial release