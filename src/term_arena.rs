use std::ops::Range;

use crate::{Sym, Var};


pub struct Solver {

}



#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TermId(usize);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ArgId(usize);

#[derive(Debug)]
pub struct TermArena {
    terms: Vec<Term>,
    args: Vec<TermId>,
}

impl TermArena {
    pub fn new() -> Self {
        Self { terms: vec![], args: vec![] }
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
        self.terms.push(Term::App(functor, ArgRange(arg_start..arg_end)));
        term
    }


    pub fn atom(&mut self, atom: Sym) -> TermId {
        self.app(atom, &[])
    }


    pub fn get_arg(&self, arg_id: ArgId) -> TermId {
        self.args[arg_id.0]
    }

    pub fn get_term(&self, term_id: TermId) -> Term {
        self.terms[term_id.0].clone()
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgRange(Range<usize>);

impl Iterator for ArgRange {
    type Item = ArgId;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(ArgId)
    }
}

impl ArgRange {
    pub fn len(&self) -> usize {
        self.0.end - self.0.start
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(Var),
    App(Sym, ArgRange),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Checkpoint {
    terms: usize,
    args: usize,
}
