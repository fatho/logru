# Changelog

## 0.3 - 2024-11-24

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

## 0.2 - 2021-10-13

Initial release