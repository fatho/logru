use super::*;
use crate::{ast::*, RuleResolver, RuleSet, SymbolStore};

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

    let mut s = SymbolStore::new();
    let mut r = RuleSet::new();

    let alice = s.get_or_insert_named("alice");
    let bob = s.get_or_insert_named("bob");
    let carol = s.get_or_insert_named("carol");
    let dave = s.get_or_insert_named("dave");
    let eve = s.get_or_insert_named("eve");
    let faithe = s.get_or_insert_named("faithe");

    let parent = s.get_or_insert_named("parent");
    let grandparent = s.get_or_insert_named("grandparent");
    let siblings = s.get_or_insert_named("siblings");

    r.insert(Rule::fact(parent, vec![alice.into(), carol.into()]));
    r.insert(Rule::fact(parent, vec![bob.into(), carol.into()]));

    r.insert(Rule::fact(parent, vec![carol.into(), eve.into()]));
    r.insert(Rule::fact(parent, vec![dave.into(), eve.into()]));

    r.insert(Rule::fact(parent, vec![carol.into(), faithe.into()]));
    r.insert(Rule::fact(parent, vec![dave.into(), faithe.into()]));

    r.insert(forall(|[p, q, r]| {
        Rule::fact(grandparent, vec![p.into(), r.into()])
            .when(parent, vec![p.into(), q.into()])
            .when(parent, vec![q.into(), r.into()])
    }));

    r.insert(forall(|[p, c1, c2]| {
        Rule::fact(siblings, vec![c1.into(), c2.into()])
            .when(parent, vec![p.into(), c1.into()])
            .when(parent, vec![p.into(), c2.into()])
    }));

    let mut resolver = RuleResolver::new(&r);
    // query all known grandparents of eve
    let solutions = query_dfs(
        &mut resolver,
        &exists(|[x]| Query::single_app(grandparent, vec![x.into(), eve.into()])),
    );
    assert_eq!(
        solutions.collect::<Vec<_>>(),
        vec![vec![Some(alice.into())], vec![Some(bob.into())],]
    );

    // query all grandchildren of bob
    let solutions = query_dfs(
        &mut resolver,
        &exists(|[x]| Query::single_app(grandparent, vec![bob.into(), x.into()])),
    );
    assert_eq!(
        solutions.collect::<Vec<_>>(),
        vec![vec![Some(eve.into())], vec![Some(faithe.into())],]
    );

    // query all siblings of eve
    let solutions = query_dfs(
        &mut resolver,
        &exists(|[x]| Query::single_app(siblings, vec![eve.into(), x.into()])),
    );
    assert_eq!(
        solutions.collect::<Vec<_>>(),
        vec![
            // one solution for each path taken
            vec![Some(eve.into())],
            vec![Some(faithe.into())],
            vec![Some(eve.into())],
            vec![Some(faithe.into())],
        ]
    );
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

    let mut u = SymbolStore::new();
    let mut r = RuleSet::new();

    let s = u.get_or_insert_named("s");
    let z = u.get_or_insert_named("z");

    let is_natural = u.get_or_insert_named("is_natural");
    let is_zero = u.get_or_insert_named("is_zero");
    let add = u.get_or_insert_named("add");

    r.insert(Rule::fact(is_zero, vec![z.into()]));
    r.insert(Rule::fact(is_natural, vec![z.into()]));

    r.insert(forall(|[x]| {
        Rule::fact(is_natural, vec![ast::app(s, vec![x.into()])]).when(is_natural, vec![x.into()])
    }));

    r.insert(forall(|[x]| {
        Rule::fact(add, vec![x.into(), z.into(), x.into()]).when(is_natural, vec![x.into()])
    }));
    r.insert(forall(|[x, y, z]| {
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

    let mut resolver = RuleResolver::new(&r);
    // query all zero numbers
    let solutions = query_dfs(
        &mut resolver,
        &exists(|[x]| Query::single_app(is_zero, vec![x.into()])),
    );
    assert_eq!(solutions.collect::<Vec<_>>(), vec![vec![Some(z.into())],]);

    // query the first natural numbers
    let solutions = query_dfs(
        &mut resolver,
        &exists(|[x]| Query::single_app(is_natural, vec![x.into()])),
    );
    assert_eq!(
        solutions.take(3).collect::<Vec<_>>(),
        vec![
            vec![Some(z.into())],
            vec![Some(ast::app(s, vec![z.into()]))],
            vec![Some(ast::app(s, vec![ast::app(s, vec![z.into()])]))],
        ]
    );

    // compute 2 + 1
    let solutions = query_dfs(
        &mut resolver,
        &exists(|[x]| {
            Query::single_app(
                add,
                vec![
                    ast::app(s, vec![ast::app(s, vec![z.into()])]),
                    ast::app(s, vec![z.into()]),
                    x.into(),
                ],
            )
        }),
    );
    assert_eq!(
        solutions.collect::<Vec<_>>(),
        vec![vec![Some(ast::app(
            s,
            vec![ast::app(s, vec![ast::app(s, vec![z.into()])])]
        ))],]
    );

    // compute 3 - 2
    let solutions = query_dfs(
        &mut resolver,
        &exists(|[x]| {
            Query::single_app(
                add,
                vec![
                    x.into(),
                    ast::app(s, vec![ast::app(s, vec![z.into()])]),
                    ast::app(s, vec![ast::app(s, vec![ast::app(s, vec![z.into()])])]),
                ],
            )
        }),
    );
    assert_eq!(
        solutions.collect::<Vec<_>>(),
        vec![vec![Some(ast::app(s, vec![z.into()]))],]
    );
}
