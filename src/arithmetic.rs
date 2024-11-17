use std::collections::HashMap;
use std::iter::FromIterator;

use crate::ast::Sym;
use crate::solver::BuiltinHandler;
use crate::term_arena::Term;
use crate::textual::NamedUniverse;

/// Built-in handler providing arithmetic expressions.
pub struct ArithmeticBuiltin {
    expr_lookup: HashMap<Sym, Expr>,
    pred_lookup: HashMap<Sym, Predicate>,
}

impl ArithmeticBuiltin {
    pub fn new(universe: &mut NamedUniverse) -> Self {
        Self {
            expr_lookup: HashMap::from_iter([
                (universe.symbol("add"), Expr::Add),
                (universe.symbol("sub"), Expr::Sub),
                (universe.symbol("mul"), Expr::Mul),
                (universe.symbol("div"), Expr::Div),
            ]),
            pred_lookup: HashMap::from_iter([(universe.symbol("is"), Predicate::Is)]),
        }
    }

    fn eval_expr(
        &mut self,
        solution: &mut crate::solver::SolutionState,
        term: crate::term_arena::TermId,
    ) -> Option<i64> {
        match solution.follow_vars(term).1 {
            Term::Var(_) => {
                // free variables are an error in expression terms
                None
            }
            Term::App(sym, args) => {
                let exp = *self.expr_lookup.get(&sym)?;
                let mut arg_iter = args;
                let t1 = arg_iter.next()?;
                let t2 = arg_iter.next()?;
                let None = arg_iter.next() else {
                    return None;
                };
                let v1 = self.eval_expr(solution, solution.terms().get_arg(t1))?;
                let v2 = self.eval_expr(solution, solution.terms().get_arg(t2))?;
                let ret = match exp {
                    Expr::Add => v1 + v2,
                    Expr::Sub => v1 - v2,
                    Expr::Mul => v1 * v2,
                    Expr::Div => v1 / v2,
                };
                Some(ret)
            }
            Term::Int(val) => Some(val),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Expr {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone, Copy)]
enum Predicate {
    Is,
}

impl BuiltinHandler for ArithmeticBuiltin {
    type Choice = Choice;

    fn next_choice(
        &mut self,
        choice: &mut Self::Choice,
        solution: &mut crate::solver::SolutionState,
        goal: crate::term_arena::TermId,
    ) -> bool {
        if choice.done {
            return false;
        }
        choice.done = true;
        match choice.pred {
            Predicate::Is => {
                // Unwrap goal with two arguments
                let Term::App(_, mut args) = solution.terms().get_term(goal) else {
                    return false;
                };
                let Some(first) = args.next() else {
                    return false;
                };
                let Some(second) = args.next() else {
                    return false;
                };
                let None = args.next() else {
                    return false;
                };

                // Evaluate RHS
                let Some(value) = self.eval_expr(solution, solution.terms().get_arg(second)) else {
                    return false;
                };
                // Allocate value and unify
                let value_term = solution.terms_mut().int(value);
                let lhs_term = solution.terms().get_arg(first);
                solution.unify(lhs_term, value_term)
            }
        }
    }

    fn lookup_predicate(&mut self, head: Sym) -> Option<Self::Choice> {
        self.pred_lookup
            .get(&head)
            .copied()
            .map(|pred| Choice { pred, done: false })
    }
}

pub struct Choice {
    pred: Predicate,
    done: bool,
}

#[cfg(test)]
mod tests {
    use crate::ast::{self};
    use crate::textual::TextualUniverse;

    use super::ArithmeticBuiltin;

    #[test]
    fn real_arithmetic() {
        let mut universe = TextualUniverse::new();
        let mut arith = ArithmeticBuiltin::new(universe.inner_mut());
        // The built-in `is` evaluation predicate can be used to define a bidirectional `plus`
        // predicate where `plus($0, $1, $2)` holds iff `$0 + $1 == $2`.
        // At least two of the involved variables must be bound, otherwise the predicate fails.
        universe
            .load_str(
                r"
plus($0, $1, $2) :- is($2, add($0, $1)).
plus($0, $1, $2) :- is($1, sub($2, $0)).
plus($0, $1, $2) :- is($0, sub($2, $1)).
        ",
            )
            .unwrap();
        let query = universe
            .query_dfs_with_builtins(&mut arith, "is($0, add(1, 4)), is($1, mul(4, $0)).")
            .unwrap();
        let solutions: Vec<_> = query.collect();
        assert_eq!(
            solutions,
            &[vec![Some(ast::Term::Int(5)), Some(ast::Term::Int(20))]]
        );

        // A chain of `plus` in all variations used for computing a final value
        let query = universe
            .query_dfs_with_builtins(
                &mut arith,
                "plus(1, 5, $0), plus($0, $1, 10), plus($2, $0, $1), is(-2, $2).",
            )
            .unwrap();
        let solutions: Vec<_> = query.collect();
        assert_eq!(
            solutions,
            &[vec![
                Some(ast::Term::Int(6)),
                Some(ast::Term::Int(4)),
                Some(ast::Term::Int(-2))
            ]]
        );

        // `is` fails for invalid equations
        let query = universe
            .query_dfs_with_builtins(&mut arith, "plus(1, 5, $0), plus($0, $1, 10), is(10, $1).")
            .unwrap();
        let solutions: Vec<_> = query.collect();
        assert_eq!(solutions, Vec::<Vec<_>>::new());
    }
}
