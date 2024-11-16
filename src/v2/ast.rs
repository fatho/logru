use std::fmt::Display;
use std::sync::Arc;

pub struct Rule {
    pub head: CompoundTerm,
    pub tail: Vec<Term>,
}

pub enum Term {
    Var(Arc<str>),
    Compound(CompoundTerm),
}

impl Term {
    pub fn atom(name: impl Into<Arc<str>>) -> Self {
        Term::Compound(CompoundTerm {
            head: name.into(),
            args: Vec::new(),
        })
    }

    pub fn compound(name: impl Into<Arc<str>>, args: Vec<Term>) -> Self {
        Term::Compound(CompoundTerm::new(name, args))
    }

    pub fn var(name: impl Into<Arc<str>>) -> Self {
        Term::Var(name.into())
    }
}

pub struct CompoundTerm {
    pub head: Arc<str>,
    pub args: Vec<Term>,
}

impl CompoundTerm {
    pub fn new_atom(name: impl Into<Arc<str>>) -> Self {
        Self::new(name, vec![])
    }

    pub fn new(name: impl Into<Arc<str>>, args: Vec<Term>) -> Self {
        Self {
            head: name.into(),
            args,
        }
    }
}

impl Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.head)?;
        if let Some((first, rest)) = self.tail.split_first() {
            write!(f, " :- {}", first)?;
            for r in rest {
                write!(f, ", {}", r)?;
            }
        }
        write!(f, ".")
    }
}

impl Display for CompoundTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.head)?;
        if let Some((first, rest)) = self.args.split_first() {
            write!(f, "(")?;
            write!(f, "{}", first)?;
            for r in rest {
                write!(f, ", {}", r)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(var) => write!(f, "{var}"),
            Term::Compound(compound_term) => write!(f, "{compound_term}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{CompoundTerm, Rule, Term};

    #[test]
    fn display_simple_fact() {
        let rule = Rule {
            head: CompoundTerm::new_atom("true"),
            tail: Vec::new(),
        };
        assert_eq!(rule.to_string(), "true.");
    }

    #[test]
    fn display_compound_fact_1() {
        let rule = Rule {
            head: CompoundTerm::new("female", vec![Term::atom("alice")]),
            tail: Vec::new(),
        };
        assert_eq!(rule.to_string(), "female(alice).");
    }

    #[test]
    fn display_compound_fact_2() {
        let rule = Rule {
            head: CompoundTerm::new("parent", vec![Term::atom("alice"), Term::atom("bob")]),
            tail: Vec::new(),
        };
        assert_eq!(rule.to_string(), "parent(alice, bob).");
    }

    #[test]
    fn display_rule_1() {
        let rule = Rule {
            head: CompoundTerm::new("child", vec![Term::var("X"), Term::var("Y")]),
            tail: vec![Term::compound(
                "parent",
                vec![Term::var("Y"), Term::var("X")],
            )],
        };
        assert_eq!(rule.to_string(), "child(X, Y) :- parent(Y, X).");
    }

    #[test]
    fn display_rule_2() {
        let rule = Rule {
            head: CompoundTerm::new("grandparent", vec![Term::var("X"), Term::var("Y")]),
            tail: vec![
                Term::compound("parent", vec![Term::var("X"), Term::var("Z")]),
                Term::compound("parent", vec![Term::var("Z"), Term::var("Y")]),
            ],
        };
        assert_eq!(
            rule.to_string(),
            "grandparent(X, Y) :- parent(X, Z), parent(Z, Y)."
        );
    }
}
