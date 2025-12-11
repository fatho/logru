use std::collections::HashMap;
use std::convert::TryInto;

use crate::ast::Sym;
use crate::search::{Resolved, Resolver, SolutionState};
use crate::term_arena::{AppTerm, ArgRange, Term, TermId};
use crate::universe::SymbolStorage;

/// A special resolver for integer arithmetic. It provides a special predicate `is/2` which
/// evaluates integer expressions.
///
/// The second argument of `is/2` must be a integer expression consisting of the terms below. When
/// the first argument is:
/// - an unbound variable, it will be bound to the result
/// - an integer, the predicate succeeds if and only if the result is equal to that integer.
///
/// Expressions are represented using an integer term, or one of the following compound terms, which
/// each take two expressions as arguments:
/// - `add/2`: addition
/// - `sub/2`: subtraction
/// - `mul/2`: multiplication
/// - `div/2`: division
/// - `rem/2`: remainder
///
/// Notably, free variables are not allowed in those expressions.
///
/// Integer overflow errors will fail the `is/2` predicate.
///
/// # Examples
///
/// - Computing the result of an expression and binding it to `X`:
///   ```prolog
///   is(X, add(2, 3)).
///   ```
/// - Comparing `4` to the result of the expression (predicate succeeds):
///   ```prolog
///   is(4, mul(2, 2)).
///   ```
/// - Comparing `4` to the result of the expression (predicate fails):
///   ```prolog
///   is(4, add(1, 2)).
///   ```
#[derive(Clone)]
pub struct ArithmeticResolver {
    exp_map: HashMap<Sym, Exp>,
    pred_map: HashMap<Sym, Pred>,
}

impl ArithmeticResolver {
    pub fn new<T: SymbolStorage>(symbols: &mut T) -> Self {
        let exps = [
            ("add", Exp::Add),
            ("sub", Exp::Sub),
            ("mul", Exp::Mul),
            ("div", Exp::Div),
            ("rem", Exp::Rem),
            ("pow", Exp::Pow),
        ];
        let preds = [("is", Pred::Is)];
        Self {
            exp_map: symbols.build_sym_map(exps),
            pred_map: symbols.build_sym_map(preds),
        }
    }

    fn eval_exp(&self, solution: &SolutionState, exp: TermId) -> Option<i64> {
        // TODO: evaluate expressions iteratively to prevent stack overflows
        match solution.follow_vars(exp).1 {
            // TODO: log: an unbound variable is an error
            Term::Var(_) => None,
            Term::App(AppTerm(sym, arg_range)) => {
                let op = self.exp_map.get(&sym)?;
                let [a1, a2] = solution.terms().get_args_fixed(arg_range)?;
                let v1 = self.eval_exp(solution, a1)?;
                let v2 = self.eval_exp(solution, a2)?;
                // TODO: log overflow errors
                let ret = match op {
                    Exp::Add => v1.checked_add(v2)?,
                    Exp::Sub => v1.checked_sub(v2)?,
                    Exp::Mul => v1.checked_mul(v2)?,
                    Exp::Div => v1.checked_div(v2)?,
                    Exp::Rem => v1.checked_rem(v2)?,
                    Exp::Pow => v1.checked_pow(v2.try_into().ok()?)?,
                };
                Some(ret)
            }
            Term::Int(i) => Some(i),
            // TODO: log: any other term is an error
            _ => None,
        }
    }

    fn resolve_is(
        &mut self,
        args: ArgRange,
        context: &mut crate::search::ResolveContext,
    ) -> Option<Resolved<()>> {
        let [left, right] = context.solution().terms().get_args_fixed(args)?;
        // Right must be fully instantiated and evaluate to integer formula
        let right_val = self.eval_exp(context.solution(), right)?;

        // Left must be variable or integer
        let (_left_id, left_term) = context.solution().follow_vars(left);
        match dbg!(left_term) {
            Term::Var(var) => {
                let prev_constraint = context
                    .solution()
                    .get_var_constraint(var)
                    .map(|term_id| context.solution().terms().get_term(term_id))
                    .and_then(|term| match term {
                        Term::Constraint(c) => Some(c),
                        // Constraints could be anything but a custom type is nicer to use on the Rust side
                        _ => None,
                    });

                let new_constraint = prev_constraint.map(|c|
                    std::cmp::min(c, right_val)
                ).unwrap_or(right_val);
                if new_constraint == 1 {
                    // numbers don't go below 0, so A<1 means A==0.
                    let result_term = context.solution_mut().terms_mut().int(0);
                    context
                        .solution_mut()
                        .set_var_constraint(var, result_term)
                        .then_some(Resolved::Success)
                } else if Some(new_constraint) == prev_constraint {
                    Some(Resolved::Success)
                } else if new_constraint < 1 {
                    // numbers don't go below 0, so A<something-less-than-1 means A<0, so no solution
                    None
                } else {
                    // Allocate result and assign to unbound variable
                    let result_term = context.solution_mut().terms_mut().constraint(new_constraint);
                    context
                        .solution_mut()
                        .set_var_constraint(var, result_term)
                        .then_some(Resolved::Success)
                }
            }
            Term::Int(left_val) => (left_val == right_val).then_some(Resolved::Success),
            // TODO: log invalid terms
            _ => None,
        }
    }
}

#[derive(Clone)]
enum Exp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
}

#[derive(Clone, Debug)]
enum Pred {
    Is,
}

impl Resolver for ArithmeticResolver {
    /// The arithmetic resolver provides no choice.
    type Choice = ();

    fn resolve(
        &mut self,
        _goal_id: crate::term_arena::TermId,
        AppTerm(sym, args): crate::term_arena::AppTerm,
        context: &mut crate::search::ResolveContext,
    ) -> Option<Resolved<Self::Choice>> {
        let pred = self.pred_map.get(dbg!(&sym))?;
        match pred {
            Pred::Is => self.resolve_is(dbg!(args), context),
        }
    }

    fn resume(
        &mut self,
        _choice: &mut Self::Choice,
        _goal_id: crate::term_arena::TermId,
        _context: &mut crate::search::ResolveContext,
    ) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Term;
    use crate::query_dfs;
    use crate::resolve::ResolverExt;
    use crate::search::Solution;
    use crate::textual::TextualUniverse;

    use super::ArithmeticResolver;

    #[test]
    fn simple() {
        let tu = TextualUniverse::new();
        let mut query = tu
            .prepare_query("is(X, add(3, mul(3, sub(6, div(10, rem(10, pow(2,3))))))).")
            .unwrap();
        let resolver = ArithmeticResolver::new(&mut query.symbols_mut());
        let mut results = query_dfs(resolver.or_else(tu.resolver()), query.query());
        assert_eq!(results.next(), Some(Solution(vec![Some(Term::Int(6))])));
        assert!(results.next().is_none());
    }

    #[test]
    fn complex() {
        let mut tu = TextualUniverse::new();
        let mut arith = ArithmeticResolver::new(&mut tu.symbols);
        tu.load_str(
            r"
        eq(Exp1, Exp2) :- is(X, Exp1), is(X, Exp2), !.
        eq(Exp1, Exp2) :- is(Exp1, Exp2), !.
        eq(Exp1, Exp2) :- is(Exp2, Exp1), !.
        ",
        )
        .unwrap();
        {
            let query = tu.prepare_query("eq(add(2, 2), pow(2, 2)).").unwrap();
            let mut results = query_dfs(arith.by_ref().or_else(tu.resolver()), query.query());
            assert_eq!(results.next(), Some(Solution(vec![])));
            assert!(results.next().is_none());
        }
        {
            let query = tu.prepare_query("eq(X, pow(2, 2)).").unwrap();
            let mut results = query_dfs(arith.by_ref().or_else(tu.resolver()), query.query());
            assert_eq!(results.next(), Some(Solution(vec![Some(Term::Int(4))])));
            assert!(results.next().is_none());
        }
        {
            let query = tu.prepare_query("eq(add(2, 2), X).").unwrap();
            let mut results = query_dfs(arith.by_ref().or_else(tu.resolver()), query.query());
            assert_eq!(results.next(), Some(Solution(vec![Some(Term::Int(4))])));
            assert!(results.next().is_none());
        }
        {
            let query = tu.prepare_query("eq(2, 2).").unwrap();
            let mut results = query_dfs(arith.by_ref().or_else(tu.resolver()), query.query());
            assert_eq!(results.next(), Some(Solution(vec![])));
            assert!(results.next().is_none());
        }
    }
}
