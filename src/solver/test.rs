use super::*;
use crate::{ast::*, universe::Universe};

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

    // query all known grandparents of eve
    let solutions = query_dfs(
        &u,
        &exists(|[x]| Query::new(grandparent, vec![x.into(), eve.into()])),
    );
    assert_eq!(
        solutions.collect::<Vec<_>>(),
        vec![vec![Some(alice.into())], vec![Some(bob.into())],]
    );

    // query all grandchildren of bob
    let solutions = query_dfs(
        &u,
        &exists(|[x]| Query::new(grandparent, vec![bob.into(), x.into()])),
    );
    assert_eq!(
        solutions.collect::<Vec<_>>(),
        vec![vec![Some(eve.into())], vec![Some(faithe.into())],]
    );

    // query all siblings of eve
    let solutions = query_dfs(
        &u,
        &exists(|[x]| Query::new(siblings, vec![eve.into(), x.into()])),
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

    let mut u = Universe::new();

    let s = u.alloc_symbol();
    let z = u.alloc_symbol();

    let is_natural = u.alloc_symbol();
    let is_zero = u.alloc_symbol();
    let add = u.alloc_symbol();

    u.add_rule(Rule::fact(is_zero, vec![z.into()]));
    u.add_rule(Rule::fact(is_natural, vec![z.into()]));

    u.add_rule(forall(|[x]| {
        Rule::fact(is_natural, vec![ast::app(s, vec![x.into()])]).when(is_natural, vec![x.into()])
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

    // query all zero numbers
    let solutions = query_dfs(&u, &exists(|[x]| Query::new(is_zero, vec![x.into()])));
    assert_eq!(solutions.collect::<Vec<_>>(), vec![vec![Some(z.into())],]);

    // query the first natural numbers
    let solutions = query_dfs(&u, &exists(|[x]| Query::new(is_natural, vec![x.into()])));
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
        &u,
        &exists(|[x]| {
            Query::new(
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
        &u,
        &exists(|[x]| {
            Query::new(
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
