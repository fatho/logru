use crate::search::{ResolveContext, Resolved, Resolver};
use crate::term_arena;

/// Extension methods for resolvers that aid in building them.
pub trait ResolverExt: Resolver {
    /// First try the current resolver, and if that fails, use the other one.
    fn or_else<R: Resolver>(self, other: R) -> OrElse<Self, R>
    where
        Self: Sized,
    {
        OrElse {
            first: self,
            second: other,
        }
    }

    /// Use the resolver by reference, rather than by value.
    fn by_ref(&mut self) -> &mut Self {
        self
    }
}

impl<R: Resolver> ResolverExt for R {}

/// A resolver that first tries to resolve a goal with the first resolver, and if that fails,
/// resorts to the second resolver.
#[derive(Clone)]
pub struct OrElse<R1, R2> {
    pub first: R1,
    pub second: R2,
}

/// A choice between two choices. Used by the [`OrElse`] resolver.
#[derive(Debug, Clone)]
pub enum OrElseChoice<C1, C2> {
    First(C1),
    Second(C2),
}

impl<R1: Resolver, R2: Resolver> Resolver for OrElse<R1, R2> {
    type Choice = OrElseChoice<R1::Choice, R2::Choice>;

    fn resolve(
        &mut self,
        goal_id: term_arena::TermId,
        goal_term: term_arena::AppTerm,
        context: &mut ResolveContext,
    ) -> Option<Resolved<Self::Choice>> {
        self.first
            .resolve(goal_id, goal_term, context)
            .map(|resolved| resolved.map_choice(OrElseChoice::First))
            .or_else(|| {
                self.second
                    .resolve(goal_id, goal_term, context)
                    .map(|resolved| resolved.map_choice(OrElseChoice::Second))
            })
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
