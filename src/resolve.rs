use crate::search::{ResolveContext, Resolved, Resolver, SolutionState};
use crate::universe::CompiledRule;
use crate::{term_arena, RuleSet};

/// A goal resolver that uses a user-defined [`RuleSet`] for resolving goals.
#[derive(Debug)]
pub struct RuleResolver<'a> {
    rules: &'a RuleSet,
}

impl<'a> RuleResolver<'a> {
    pub const fn new(rules: &'a RuleSet) -> Self {
        Self { rules }
    }

    /// Unify a goal term with a rule and return the new sub goals if the unification was
    /// successful.
    fn unify_rule(
        &self,
        goal_term: term_arena::TermId,
        rule: &'a CompiledRule,
        solution: &mut SolutionState,
    ) -> Option<impl Iterator<Item = term_arena::TermId> + 'a> {
        // add uninstantiated variables for the rule
        let var_start = solution.allocate_vars(rule.var_slots());
        let var_offset = var_start.ord();

        // instantiate head for now
        let (head, head_blueprint) = rule.head();
        let conv_rule_head = solution
            .terms_mut()
            .instantiate_blueprint(head_blueprint, var_offset);
        let instantiated_rule_head = conv_rule_head(head);

        if solution.unify(goal_term, instantiated_rule_head) {
            // instantiate tail terms
            let (tail, tail_blueprint) = rule.tail();
            let conv_rule_tail = solution
                .terms_mut()
                .instantiate_blueprint(tail_blueprint, var_offset);
            // and return the updated term IDs (in reverse order) so that the originally leftmost
            // goal ends up on the top of the goal stack, and hence is processed next.
            Some(tail.iter().rev().map(move |tail| conv_rule_tail(*tail)))
        } else {
            None
        }
    }

    fn apply_first_rule(
        &self,
        mut rules: &'a [CompiledRule],
        goal_id: term_arena::TermId,
        context: &mut ResolveContext,
    ) -> Option<&'a [CompiledRule]> {
        while let Some((first, rest)) = rules.split_first() {
            rules = rest;
            let result = self.unify_rule(goal_id, first, context.solution_mut());
            if let Some(goals) = result {
                context.extend_goals(goals);
                return Some(rest);
            } else {
                context.reset();
            }
        }
        None
    }
}

impl<'a> Resolver for RuleResolver<'a> {
    type Choice = &'a [CompiledRule];

    fn resolve(
        &mut self,
        goal_id: term_arena::TermId,
        goal_term: term_arena::Term,
        context: &mut ResolveContext,
    ) -> Resolved<Self::Choice> {
        if let term_arena::Term::App(sym, _) = goal_term {
            let rules = self.rules.rules_by_head(sym);
            if let Some(rest) = self.apply_first_rule(rules, goal_id, context) {
                if rest.is_empty() {
                    Resolved::Success
                } else {
                    Resolved::SuccessRetry(rest)
                }
            } else {
                Resolved::Fail
            }
        } else {
            // Reject all other terms as potential goals in this resolver
            // That way, eventually another resolver may pick them up.
            Resolved::Fail
        }
    }

    fn resume(
        &mut self,
        choice: &mut Self::Choice,
        goal_id: term_arena::TermId,
        context: &mut ResolveContext,
    ) -> bool {
        if let Some(rest) = self.apply_first_rule(choice, goal_id, context) {
            *choice = rest;
            true
        } else {
            false
        }
    }
}

/// Extension methods for resolvers that aid in building them.
pub trait ResolverExt: Resolver {
    fn or_else<R: Resolver>(self, other: R) -> OrElse<Self, R>
    where
        Self: Sized,
    {
        OrElse {
            first: self,
            second: other,
        }
    }
}

impl<R: Resolver> ResolverExt for R {}

/// A resolver that first tries to resolve a goal with the first resolver, and if that fails,
/// resorts to the second resolver.
pub struct OrElse<R1, R2> {
    pub first: R1,
    pub second: R2,
}

/// A choice between two choices. Used by the [`OrElse`] resolver.
#[derive(Debug)]
pub enum OrElseChoice<C1, C2> {
    First(C1),
    Second(C2),
}

impl<R1: Resolver, R2: Resolver> Resolver for OrElse<R1, R2> {
    type Choice = OrElseChoice<R1::Choice, R2::Choice>;

    fn resolve(
        &mut self,
        goal_id: term_arena::TermId,
        goal_term: term_arena::Term,
        context: &mut ResolveContext,
    ) -> Resolved<Self::Choice> {
        match self.first.resolve(goal_id, goal_term, context) {
            Resolved::Fail => match self.second.resolve(goal_id, goal_term, context) {
                Resolved::Fail => Resolved::Fail,
                Resolved::Success => Resolved::Success,
                Resolved::SuccessRetry(choice) => {
                    Resolved::SuccessRetry(OrElseChoice::Second(choice))
                }
            },
            Resolved::Success => Resolved::Success,
            Resolved::SuccessRetry(choice) => Resolved::SuccessRetry(OrElseChoice::First(choice)),
        }
    }

    fn resume(
        &mut self,
        choice: &mut Self::Choice,
        goal_id: term_arena::TermId,
        context: &mut ResolveContext,
    ) -> bool {
        match choice {
            OrElseChoice::First(choice) => self.first.resume(choice, goal_id, context),
            OrElseChoice::Second(choice) => self.second.resume(choice, goal_id, context),
        }
    }
}
