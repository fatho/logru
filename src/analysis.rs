//! Program analysis proceduress

use crate::ast::{Rule, Term, Var};
use std::collections::{HashMap, HashSet};

/// Finds variables occuring only once in the rule (together in head and tail).
pub fn find_unique_variables(rule: &Rule) -> HashSet<Var> {
    let vars = count_variables(rule);
    vars.into_iter()
        .filter(|(_var, count)| *count == 1)
        .map(|(var, _count)| var)
        .collect()
}

/// Counts the number of occurrences of all variables in the rule (both in head and tail).
pub fn count_variables(rule: &Rule) -> HashMap<Var, usize> {
    let mut vars = HashMap::new();
    count_in_args(&mut vars, &rule.head.args);
    count_in_args(&mut vars, &rule.tail);
    vars
}

fn count_in_args(mut vars: &mut HashMap<Var, usize>, args: &[Term]) {
    for term in args {
        match term {
            Term::Var(var) => *vars.entry(*var).or_insert(0) += 1,
            Term::Int(_) => {}
            Term::Cut => {}
            Term::App(appterm) => count_in_args(&mut vars, &appterm.args),
        }
    }
}
