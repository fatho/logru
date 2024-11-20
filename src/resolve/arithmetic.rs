use std::collections::HashMap;
use std::convert::TryInto;
use std::mem::MaybeUninit;

use crate::ast::Sym;
use crate::search::{Resolved, Resolver, SolutionState};
use crate::term_arena::{ArgRange, Term, TermArena, TermId};
use crate::SymbolStore;

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
pub struct ArithmeticResolver {
    exp_map: HashMap<Sym, Exp>,
    pred_map: HashMap<Sym, Pred>,
}

impl ArithmeticResolver {
    pub fn new(symbols: &mut SymbolStore) -> Self {
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
            exp_map: IntoIterator::into_iter(exps)
                .map(|(name, op)| (symbols.get_or_insert_named(name), op))
                .collect(),
            pred_map: IntoIterator::into_iter(preds)
                .map(|(name, op)| (symbols.get_or_insert_named(name), op))
                .collect(),
        }
    }

    fn eval_exp(&self, solution: &SolutionState, exp: TermId) -> Option<i64> {
        // TODO: evaluate expressions iteratively to prevent stack overflows
        match solution.follow_vars(exp).1 {
            // TODO: log: an unbound variable is an error
            Term::Var(_) => None,
            Term::App(sym, arg_range) => {
                let op = self.exp_map.get(&sym)?;
                let [a1, a2] = fixed_args(solution.terms(), arg_range)?;
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
        }
    }

    fn resolve_is(
        &mut self,
        args: ArgRange,
        context: &mut crate::search::ResolveContext,
    ) -> Resolved<()> {
        let Some([left, right]) = fixed_args(context.solution().terms(), args) else {
            return Resolved::Fail;
        };
        // Right must be fully instantiated and evaluate to integer formula
        let Some(right_val) = self.eval_exp(context.solution(), right) else {
            return Resolved::Fail;
        };

        // Left must be variable or integer
        let (_left_id, left_term) = context.solution().follow_vars(left);
        match left_term {
            Term::Var(var) => {
                // Allocate result and assign to unbound variable
                let result_term = context.solution_mut().terms_mut().int(right_val);
                if context.solution_mut().set_var(var, result_term) {
                    Resolved::Success
                } else {
                    Resolved::Fail
                }
            }
            Term::Int(left_val) => {
                if left_val == right_val {
                    Resolved::Success
                } else {
                    Resolved::Fail
                }
            }
            Term::App(_, _) => Resolved::Fail,
        }
    }
}

enum Exp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
}

enum Pred {
    Is,
}

impl Resolver for ArithmeticResolver {
    /// The arithmetic resolver provides no choice.
    type Choice = ();

    fn resolve(
        &mut self,
        _goal_id: crate::term_arena::TermId,
        goal_term: crate::term_arena::Term,
        context: &mut crate::search::ResolveContext,
    ) -> Resolved<Self::Choice> {
        if let Term::App(sym, args) = goal_term {
            if let Some(pred) = self.pred_map.get(&sym) {
                return match pred {
                    Pred::Is => self.resolve_is(args, context),
                };
            }
        }
        Resolved::Fail
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

fn fixed_args<const N: usize>(arena: &TermArena, mut args: ArgRange) -> Option<[TermId; N]> {
    let mut res = [MaybeUninit::uninit(); N];
    for arg_term in res.iter_mut() {
        let arg = args.next()?;
        *arg_term = MaybeUninit::new(arena.get_arg(arg))
    }
    if args.is_empty() {
        // SAFETY: If we reach this point, all elements were initialized above.
        unsafe { Some(res.map(|u| u.assume_init())) }
    } else {
        None
    }
}
