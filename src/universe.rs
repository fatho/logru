use crate::ast::*;

#[derive(Debug)]
pub struct Universe {
    symbols: Vec<()>,
    rules: Vec<Rule>,
}

impl Universe {
    pub fn alloc_symbol(&mut self) -> Sym {
        let sym = Sym::from_ord(self.symbols.len());
        self.symbols.push(());
        sym
    }

    pub fn alloc_symbols(&mut self, count: usize) -> impl Iterator<Item = Sym> {
        let fresh_start = self.symbols.len();
        self.symbols.resize(self.symbols.len() + count, ());
        (fresh_start..fresh_start + count).map(Sym::from_ord)
    }

    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    pub fn new() -> Self {
        Self {
            symbols: vec![],
            rules: vec![],
        }
    }

    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    pub fn num_symbols(&self) -> usize {
        self.symbols.len()
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast;

    #[test]
    fn genealogy() {
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

        let alice = u.alloc_symbol();
        let bob = u.alloc_symbol();
        let carol = u.alloc_symbol();
        let dave = u.alloc_symbol();
        let eve = u.alloc_symbol();
        let faithe = u.alloc_symbol();

        let parent = u.alloc_symbol();
        let grandparent = u.alloc_symbol();
        let siblings = u.alloc_symbol();

        u.add_rule(Rule::fact(parent, vec![alice.into(), carol.into()]));
        u.add_rule(Rule::fact(parent, vec![bob.into(), carol.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), eve.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), eve.into()]));

        u.add_rule(Rule::fact(parent, vec![carol.into(), faithe.into()]));
        u.add_rule(Rule::fact(parent, vec![dave.into(), faithe.into()]));

        u.add_rule(forall(|[p, q, r]| {
            Rule::fact(grandparent, vec![p.into(), r.into()])
                .when(parent, vec![p.into(), q.into()])
                .when(parent, vec![q.into(), r.into()])
        }));

        u.add_rule(forall(|[p, c1, c2]| {
            Rule::fact(siblings, vec![c1.into(), c2.into()])
                .when(parent, vec![p.into(), c1.into()])
                .when(parent, vec![p.into(), c2.into()])
        }));

        // // query all known grandparents of eve
        // let solver = u.query(quantify(|[x]| {
        //     vec![grandparent.apply(vec![x.into(), eve.into()])]
        // }));
        // assert_eq!(
        //     solver.collect::<Vec<_>>(),
        //     vec![vec![Some(alice.into())], vec![Some(bob.into())],]
        // );

        // // query all grandchildren of bob
        // let solver = u.query(quantify(|[x]| {
        //     vec![grandparent.apply(vec![bob.into(), x.into()])]
        // }));
        // assert_eq!(
        //     solver.collect::<Vec<_>>(),
        //     vec![vec![Some(eve.into())], vec![Some(faithe.into())],]
        // );

        // // query all siblings of eve
        // let solver = u.query(quantify(|[x]| {
        //     vec![siblings.apply(vec![eve.into(), x.into()])]
        // }));
        // assert_eq!(
        //     solver.collect::<Vec<_>>(),
        //     vec![
        //         // one solution for each path taken
        //         vec![Some(eve.into())],
        //         vec![Some(eve.into())],
        //         vec![Some(faithe.into())],
        //         vec![Some(faithe.into())],
        //     ]
        // );
    }

    #[test]
    fn arithmetic() {
        // GOAL:
        /*

        is_natural(z).
        is_natural(s(X)) :- is_natural(X).

        is_zero(z).

        add(X, z, X) :- is_natural(X).
        add(X, S(Y), S(Z)) :- add(X, Y, Z).

        */

        let mut u = Universe::new();

        let s = u.alloc_symbol();
        let z = u.alloc_symbol();

        let is_natural = u.alloc_symbol();
        let is_zero = u.alloc_symbol();
        let add = u.alloc_symbol();

        u.add_rule(Rule::fact(is_zero, vec![z.into()]));
        u.add_rule(Rule::fact(is_natural, vec![z.into()]));

        u.add_rule(forall(|[x]| {
            Rule::fact(is_natural, vec![ast::app(s, vec![x.into()])])
                .when(is_natural, vec![x.into()])
        }));

        u.add_rule(forall(|[x]| {
            Rule::fact(add, vec![x.into(), z.into(), x.into()]).when(is_natural, vec![x.into()])
        }));
        u.add_rule(forall(|[x, y, z]| {
            Rule::fact(
                add,
                vec![
                    x.into(),
                    ast::app(s, vec![y.into()]),
                    ast::app(s, vec![z.into()]),
                ],
            )
            .when(add, vec![x.into(), y.into(), z.into()])
        }));

        // // query all zero numbers
        // let solver = u.query(quantify(|[x]| vec![ast::app(is_zero, vec![x.into()])]));
        // assert_eq!(solver.collect::<Vec<_>>(), vec![vec![Some(z.into())],]);

        // // query the first natural numbers
        // let solver = u.query(quantify(|[x]| vec![ast::app(is_natural, vec![x.into()])]));
        // assert_eq!(
        //     solver.take(3).collect::<Vec<_>>(),
        //     vec![
        //         vec![Some(z.into())],
        //         vec![Some(ast::app(s, vec![z.into()]).into())],
        //         vec![Some(ast::app(s, vec![ast::app(s, vec![z.into()]).into()]).into())],
        //     ]
        // );

        // // compute 2 + 1
        // let solver = u.query(quantify(|[x]| {
        //     vec![ast::app(add, vec![
        //         ast::app(s, vec![ast::app(s, vec![z.into()]).into()]).into(),
        //         ast::app(s, vec![z.into()]).into(),
        //         x.into(),
        //     ])]
        // }));
        // assert_eq!(
        //     solver.collect::<Vec<_>>(),
        //     vec![vec![Some(
        //         ast::app(s, vec![ast::app(s, vec![ast::app(s, vec![z.into()]).into()]).into()])
        //             .into()
        //     )],]
        // );

        // // compute 3 - 2
        // let solver = u.query(quantify(|[x]| {
        //     vec![ast::app(add, vec![
        //         x.into(),
        //         ast::app(s, vec![ast::app(s, vec![z.into()]).into()]).into(),
        //         ast::app(s, vec![ast::app(s, vec![ast::app(s, vec![z.into()]).into()]).into()])
        //             .into(),
        //     ])]
        // }));
        // assert_eq!(
        //     solver.collect::<Vec<_>>(),
        //     vec![vec![Some(ast::app(s, vec![z.into()]).into())],]
        // );
    }
}
