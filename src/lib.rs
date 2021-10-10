pub mod union_find;
pub mod zebra;

#[derive(Debug)]
pub struct Universe {
    symbols: Vec<SymInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Sym(usize);

impl Sym {
    pub fn apply(self, args: Vec<Term>) -> AppTerm {
        AppTerm { functor: self, args }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(usize);

impl Universe {
    pub fn new_symbol(&mut self) -> Sym {
        let sym = Sym(self.symbols.len());
        self.symbols.push(SymInfo::new());
        sym
    }

    pub fn add_rule(&mut self, rule: Rule) {
        // define rule
        self.symbols[rule.head.functor.0].definitions.push(rule);
    }

    pub fn query(&self, goals: Vec<AppTerm>) -> Solver {
        Solver {
            universe: self,
            goals,
        }
    }

    pub fn new() -> Self {
        Self {
            symbols: vec![],
        }
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

pub fn quantify<R, const N: usize>(f: impl FnOnce([Var; N]) -> R) -> R {
    // initialize variable array with temporary fresh variables
    //   that disappear once we're done solving
    let mut vars = [Var(0); N];
    vars.iter_mut()
        .enumerate()
        .for_each(|(i, var)| *var = Var(i));
    f(vars)
}

#[derive(Debug)]
struct SymInfo {
    definitions: Vec<Rule>,
}

impl SymInfo {
    fn new() -> Self {
        Self {
            definitions: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(Var),
    App(AppTerm),
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


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    head: AppTerm,
    tail: Vec<AppTerm>,
}

impl Rule {
    pub fn fact(pred: Sym, args: Vec<Term>) -> Self {
        Self {
            head: AppTerm { functor: pred, args},
            tail: vec![],
        }
    }

    pub fn when(mut self, pred: Sym, args: Vec<Term>) -> Self {
        self.tail.push(AppTerm { functor: pred, args}.into());
        self
    }
}

pub struct Solver<'u> {
    universe: &'u Universe,
    goals: Vec<AppTerm>,
    //assignments: Vec<Option<Sym>>,
}

enum Step {
    Yield,
    Skip,
    Done,
}

impl<'u> Solver<'u> {
    fn step(&mut self) -> Step {
        // if let Some(goal) = self.goals.pop() {

        //     // resolve goal


        //     todo!()
        // } else {
        //     todo!("backtrack")
        // }
        todo!()
    }
}

impl<'u> Iterator for Solver<'u> {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                Step::Yield => todo!(),
                Step::Skip => continue,
                Step::Done => break None,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // pub enum List {
    //     Nil,
    //     Cons(Var<List>, Var<List>),
    // }

    // pub enum Preds {
    //     Append,
    //     IsNull,
    // }

    #[test]
    fn usage() {
        // GOAL:
        /*

        parent(alice, carol).
        parent(bob, carol).

        parent(carol, eve).
        parent(dave, eve).

        grandparent(X, Y) :- parent(X, Z), parent(Z, Y).

        siblings(X, Y) :- parent(Z, X), parent(Z, y).

        */

        let mut u = Universe::new();

        let alice = u.new_symbol();
        let bob = u.new_symbol();
        let carol = u.new_symbol();
        let dave = u.new_symbol();
        let eve = u.new_symbol();

        let parent = u.new_symbol();
        let grandparent = u.new_symbol();
        let siblings = u.new_symbol();

        u.add_rule(Rule::fact(parent, vec![alice.into(), carol.into()]));
        u.add_rule(Rule::fact(parent, vec![bob.into(), carol.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), eve.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), eve.into()]));

        u.add_rule(quantify(|[p, q, r]| {
            Rule::fact(grandparent, vec![p.into(), r.into()])
                .when(parent, vec![p.into(), q.into()])
                .when(parent, vec![q.into(), r.into()])
        }));

        u.add_rule(quantify(|[p, c1, c2]| {
            Rule::fact(siblings, vec![c1.into(), c2.into()])
                .when(parent, vec![p.into(), c1.into()])
                .when(parent, vec![p.into(), c2.into()])
        }));

        let solver = u.query(quantify(|[x]| {
            vec![grandparent.apply(vec![x.into(), eve.into()])]
        }));
        for solution in solver {
            println!("{:?}", solution);
        }

        panic!()
    }
}
