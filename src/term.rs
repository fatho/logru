use super::{Var, Sym};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(Var),
    App(AppTerm),
}

impl Term {
    pub fn vars(&self) -> VarIter {
        VarIter {
            backtrack: vec![&self],
        }
    }

    pub fn instantiate(&self, offset: usize) -> Term {
        match self {
            Term::Var(v) => Term::Var(Var(v.0 + offset)),
            Term::App(appterm) => Term::App(appterm.instantiate(offset)),
        }
    }
}

impl From<Var> for Term {
    fn from(v: Var) -> Self {
        Term::Var(v)
    }
}

impl From<Sym> for Term {
    fn from(s: Sym) -> Self {
        Term::App(s.into())
    }
}

impl From<AppTerm> for Term {
    fn from(at: AppTerm) -> Self {
        Term::App(at)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppTerm {
    pub functor: Sym,
    pub args: Vec<Term>,
}

impl From<Sym> for AppTerm {
    fn from(s: Sym) -> Self {
        Self { functor: s, args: vec![] }
    }
}

impl AppTerm {
    pub fn vars(&self) -> VarIter {
        VarIter {
            backtrack: self.args.iter().rev().collect()
        }
    }

    pub fn instantiate(&self, offset: usize) -> AppTerm {
        AppTerm {
            functor: self.functor,
            args: self.args.iter().map(|t| t.instantiate(offset)).collect(),
        }
    }
}

pub struct VarIter<'a> {
    backtrack: Vec<&'a Term>,
}

impl<'a> Iterator for VarIter<'a> {
    type Item = Var;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.backtrack.pop() {
                Some(term) => match term {
                    Term::Var(var) => break Some(*var),
                    Term::App(app) => {
                        self.backtrack.extend(app.args.iter().rev());
                    },
                }
                None => break None,
            }
        }
    }
}


pub struct VarIterMut<'a> {
    backtrack: Vec<&'a mut Term>,
}

impl<'a> Iterator for VarIterMut<'a> {
    type Item = &'a mut Var;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.backtrack.pop() {
                Some(term) => match term {
                    Term::Var(var) => break Some(var),
                    Term::App(app) => {
                        self.backtrack.extend(app.args.iter_mut().rev());
                    },
                }
                None => break None,
            }
        }
    }
}


#[test]
fn test_var_iter() {
    assert_eq!(Term::Var(Var(0)).vars().collect::<Vec<_>>(), vec![Var(0)]);

    assert_eq!(Term::App(AppTerm {
        functor: Sym(0),
        args: vec![
            Term::App(AppTerm {
                functor: Sym(1),
                args: vec![],
            }),
            Term::App(AppTerm {
                functor: Sym(2),
                args: vec![
                    Term::Var(Var(0)),
                    Term::App(AppTerm {
                        functor: Sym(1),
                        args: vec![Term::Var(Var(1))],
                    }),
                    Term::Var(Var(2)),
                ],
            }),
        ],
    }).vars().collect::<Vec<_>>(), vec![Var(0), Var(1), Var(2)]);
}
