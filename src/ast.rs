#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Sym(usize);

impl Sym {
    #[inline(always)]
    pub fn ord(self) -> usize {
        self.0
    }

    #[inline(always)]
    pub fn from_ord(ord: usize) -> Sym {
        Sym(ord)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(usize);

impl Var {
    #[inline(always)]
    pub fn ord(self) -> usize {
        self.0
    }

    #[inline(always)]
    pub fn from_ord(ord: usize) -> Var {
        Var(ord)
    }

    pub fn offset(self, offset: usize) -> Var {
        Var(self.0 + offset)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(Var),
    App(AppTerm),
}

impl Term {
    pub fn count_var_slots(&self) -> usize {
        match self {
            Term::Var(v) => v.0 + 1,
            Term::App(app) => app.count_var_slots(),
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
        Self {
            functor: s,
            args: vec![],
        }
    }
}

impl AppTerm {
    pub fn new(functor: Sym, args: Vec<Term>) -> Self {
        Self { functor, args }
    }

    pub fn count_var_slots(&self) -> usize {
        self.args
            .iter()
            .map(|t| t.count_var_slots())
            .max()
            .unwrap_or(0)
    }
}

pub fn app(functor: Sym, args: Vec<Term>) -> Term {
    Term::App(AppTerm::new(functor, args))
}

pub fn var(var: Var) -> Term {
    Term::Var(var)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub head: AppTerm,
    pub tail: Vec<AppTerm>,
}

impl Rule {
    pub fn fact(pred: Sym, args: Vec<Term>) -> Self {
        let head = AppTerm {
            functor: pred,
            args,
        };
        Self { head, tail: vec![] }
    }

    pub fn when(mut self, pred: Sym, args: Vec<Term>) -> Self {
        let app_term = AppTerm {
            functor: pred,
            args,
        };
        self.tail.push(app_term);
        self
    }
}

pub fn quantify<R, const N: usize>(f: impl FnOnce([Var; N]) -> R) -> R {
    // initialize variable array with temporary fresh variables
    //   that disappear once we're done solving
    let mut vars = [Var::from_ord(0); N];
    vars.iter_mut()
        .enumerate()
        .for_each(|(i, var)| *var = Var::from_ord(i));
    f(vars)
}

pub fn forall<const N: usize>(f: impl FnOnce([Var; N]) -> Rule) -> Rule {
    quantify(f)
}

pub fn exists<const N: usize>(f: impl FnOnce([Var; N]) -> Rule) -> Rule {
    quantify(f)
}
