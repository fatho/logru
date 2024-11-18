use crate::search::{ResolveContext, Resolver, SolutionState};
use crate::universe::CompiledRule;
use crate::{term_arena, RuleSet};

/// A goal resolver that uses a user-defined [`RuleSet`] for resolving goals.
#[derive(Debug)]
pub struct RuleResolver<'a> {
    rules: &'a RuleSet,
}

impl<'a> RuleResolver<'a> {
    pub fn new(rules: &'a RuleSet) -> Self {
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
}

impl<'a> Resolver for RuleResolver<'a> {
    type Choice = &'a [CompiledRule];

    #[inline(always)]
    fn resolve(
        &mut self,
        _goal_id: term_arena::TermId,
        goal_term: term_arena::Term,
        _context: &mut ResolveContext,
    ) -> Self::Choice {
        match goal_term {
            // TODO: make unbound variables vacuously true
            term_arena::Term::Var(_) => &[],
            term_arena::Term::App(sym, _) => self.rules.rules_by_head(sym),
        }
    }

    #[inline(always)]
    fn resume(
        &mut self,
        choice: &mut Self::Choice,
        goal_id: term_arena::TermId,
        context: &mut ResolveContext,
    ) -> bool {
        while let Some((first, rest)) = choice.split_first() {
            *choice = rest;
            let result = self.unify_rule(goal_id, first, context.solution_mut());
            if let Some(goals) = result {
                context.extend_goals(goals);
                return true;
            } else {
                context.reset();
            }
        }
        false
    }
}
