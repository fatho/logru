use crate::ast::{self, Sym, Var};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct TermId(usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct ArgId(usize);

#[derive(Debug, Clone)]
pub struct TermArena {
    terms: Vec<Term>,
    args: Vec<TermId>,
}

impl TermArena {
    pub fn new() -> Self {
        Self {
            terms: vec![],
            args: vec![],
        }
    }

    pub fn var(&mut self, var: Var) -> TermId {
        let term = TermId(self.terms.len());
        self.terms.push(Term::Var(var));
        term
    }

    pub fn app(&mut self, functor: Sym, args: &[TermId]) -> TermId {
        let term = TermId(self.terms.len());
        let arg_start = self.args.len();
        let arg_end = arg_start + args.len();
        self.args.extend_from_slice(args);
        self.terms.push(Term::App(
            functor,
            ArgRange {
                start: arg_start,
                end: arg_end,
            },
        ));
        term
    }

    pub fn atom(&mut self, atom: Sym) -> TermId {
        self.app(atom, &[])
    }

    pub fn instantiate(
        &mut self,
        blueprint: &TermArena,
        var_offset: usize,
    ) -> impl Fn(TermId) -> TermId {
        let here = self.checkpoint();
        self.terms
            .extend(blueprint.terms.iter().map(|term| match term {
                Term::Var(var) => Term::Var(var.offset(var_offset)),
                Term::App(func, args) => Term::App(
                    *func,
                    ArgRange {
                        start: args.start + here.args,
                        end: args.end + here.args,
                    },
                ),
            }));
        self.args.extend(
            blueprint
                .args
                .iter()
                .map(|term_id| TermId(term_id.0 + here.terms)),
        );

        let term_offset = here.terms;
        move |TermId(old)| TermId(old + term_offset)
    }

    pub fn term(&mut self, scratch: &mut Vec<TermId>, term: &ast::Term, offset: usize) -> TermId {
        match term {
            ast::Term::Var(v) => self.var(v.offset(offset)),
            ast::Term::App(app) => self.term_app(scratch, app, offset),
        }
    }

    pub fn term_app(
        &mut self,
        scratch: &mut Vec<TermId>,
        app: &ast::AppTerm,
        offset: usize,
    ) -> TermId {
        let args_start = scratch.len();
        for arg in &app.args {
            let arg_term = self.term(scratch, arg, offset);
            scratch.push(arg_term);
        }
        let out = self.app(app.functor, &scratch[args_start..]);
        scratch.truncate(args_start);
        out
    }

    pub fn get_arg(&self, arg_id: ArgId) -> TermId {
        self.args[arg_id.0]
    }

    pub fn get_term(&self, term_id: TermId) -> Term {
        self.terms[term_id.0]
    }

    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            terms: self.terms.len(),
            args: self.args.len(),
        }
    }

    pub fn release(&mut self, checkpoint: &Checkpoint) {
        if checkpoint.args > self.args.len() || checkpoint.terms > self.terms.len() {
            panic!("{:?} cannot be restored at this moment", checkpoint);
        }
        self.args.truncate(checkpoint.args);
        self.terms.truncate(checkpoint.terms);
    }
}

impl Default for TermArena {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ArgRange {
    start: usize,
    end: usize,
}

impl Iterator for ArgRange {
    type Item = ArgId;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start;
        if start == self.end {
            None
        } else {
            self.start += 1;
            Some(ArgId(start))
        }
    }

    fn any<F>(&mut self, mut f: F) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> bool,
    {
        (self.start..self.end).any(move |x| f(ArgId(x)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl ArgRange {
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term {
    Var(Var),
    App(Sym, ArgRange),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Checkpoint {
    terms: usize,
    args: usize,
}
