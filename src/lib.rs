pub mod union_find;
pub mod zebra;

#[derive(Debug)]
pub struct Universe {
    fresh_symbol: usize,
    fresh_var: usize,
    predicates: Vec<PredInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Sym(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pred(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(usize);

impl Universe {
    pub fn new_symbol(&mut self) -> Sym {
        let sym = Sym(self.fresh_symbol);
        self.fresh_symbol += 1;
        sym
    }

    pub fn new_predicate(&mut self) -> Pred {
        let pred = Pred(self.predicates.len());
        self.predicates.push(PredInfo::new());
        pred
    }

    pub fn add_rule<const N: usize>(&mut self, definer: impl FnOnce([Var; N]) -> Rule) {
        // initialize variable array
        let mut vars = [Var(0); N];
        vars.iter_mut().for_each(|var| *var = self.new_var());

        // define rule
        let rule = definer(vars);
        self.predicates[rule.head.pred.0].definitions.push(rule);
    }

    pub fn query<const N: usize>(&self, _goals: impl FnOnce([Var; N]) -> Vec<Goal>) -> Solver {
        Solver {}
    }

    pub fn new() -> Self {
        Self {
            fresh_symbol: 0,
            fresh_var: 0,
            predicates: vec![],
        }
    }

    fn new_var(&mut self) -> Var {
        let var = Var(self.fresh_var);
        self.fresh_var += 1;
        var
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
struct PredInfo {
    definitions: Vec<Rule>,
}

impl PredInfo {
    fn new() -> Self {
        Self {
            definitions: vec![],
        }
    }
}

pub struct Solver {}

impl Iterator for Solver {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Var(Var),
    Sym(Sym),
}

impl From<Var> for Value {
    fn from(v: Var) -> Self {
        Value::Var(v)
    }
}

impl From<Sym> for Value {
    fn from(s: Sym) -> Self {
        Value::Sym(s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Goal {
    pred: Pred,
    args: Vec<Value>,
}

impl Goal {
    pub fn new(pred: Pred, args: Vec<Value>) -> Self {
        Self { pred, args }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    head: Goal,
    tail: Vec<Goal>,
}

impl Rule {
    pub fn fact(pred: Pred, args: Vec<Value>) -> Self {
        Self {
            head: Goal { pred, args },
            tail: vec![],
        }
    }

    pub fn when(mut self, pred: Pred, args: Vec<Value>) -> Self {
        self.tail.push(Goal { pred, args });
        self
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

        let parent = u.new_predicate();
        let grandparent = u.new_predicate();
        let siblings = u.new_predicate();

        u.add_rule(|[]| Rule::fact(parent, vec![alice.into(), carol.into()]));
        u.add_rule(|[]| Rule::fact(parent, vec![bob.into(), carol.into()]));

        u.add_rule(|[]| Rule::fact(parent, vec![carol.into(), eve.into()]));
        u.add_rule(|[]| Rule::fact(parent, vec![dave.into(), eve.into()]));

        u.add_rule(|[p, q, r]| {
            Rule::fact(grandparent, vec![p.into(), r.into()])
                .when(parent, vec![p.into(), q.into()])
                .when(parent, vec![q.into(), r.into()])
        });

        u.add_rule(|[p, c1, c2]| {
            Rule::fact(siblings, vec![c1.into(), c2.into()])
                .when(parent, vec![p.into(), c1.into()])
                .when(parent, vec![p.into(), c2.into()])
        });

        let solver = u.query(|[x]| vec![Goal::new(grandparent, vec![x.into(), eve.into()])]);
        for solution in solver {
            println!("{:?}", solution);
        }
    }
}
