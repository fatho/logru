use std::collections::HashMap;
use std::convert::TryFrom;
use std::sync::Arc;
use std::time::{Duration, Instant};

use logru::v2::ast::{CompoundTerm, Rule, Term, Var};
use logru::v2::parser::Parser;
use logru::v2::solver::{query_dfs, Solver};
use logru::v2::stack::{Addr, Arity, Atom, Word, FrozenStack};
use logru::v2::universe::{builtin_atoms, Universe};

fn main() {
    let repeats = std::env::args()
        .nth(1)
        .and_then(|arg| arg.parse().ok())
        .unwrap_or(1);

    let mut parser = Parser::new();
    let zebra = include_str!("../testfiles/zebra_v2.lru");
    let prog = parser
        .parse_rules_str(zebra)
        .expect("can parse built-in file");

    let query = parser.parse_query_str("puzzle(Houses).").unwrap();
    let mut u = Universe::new();
    let mut atoms = HashMap::new();

    for rule in prog.iter() {
        println!("{rule}");
        allocate_rule_atoms(&mut u, &mut atoms, rule);
        u.add_rule(|stack| {
            let mut rule_vars = HashMap::new();
            let head = compound_term_to_stack(stack, &atoms, &mut rule_vars, &rule.head);
            let tail = match rule.tail.len() {
                0 => None,
                // TODO: optimize layout for single-RHS rules
                // 1 => {
                //     Some(compound_term_to_stack(stack, &atoms, &mut rule_vars, &rule.tail[0]))
                // }
                _ => Some(known_compound_term_to_stack(
                    stack,
                    &atoms,
                    &mut rule_vars,
                    builtin_atoms::CONJ,
                    &rule.tail,
                )),
            };
            (head, tail)
        });
    }
    println!("\n?- {query}");
    for term in query.goals.iter() {
        allocate_term_atoms(&mut u, &mut atoms, term);
    }

    println!("{atoms:#?}");

    println!("{u:#?}");

    let mut total = Duration::ZERO;
    for i in 0..repeats {
        let mut qvars: HashMap<Arc<str>, Addr> = HashMap::new();
        let mut s = query_dfs(&mut u, |stack| {
            known_compound_term_to_stack(
                stack,
                &atoms,
                &mut qvars,
                builtin_atoms::CONJ,
                &query.goals,
            )
        });

        let reverse_atoms: HashMap<_, _> = atoms
            .iter()
            .map(|(name, atom)| (*atom, name.clone()))
            .collect();

        let mut solutions = 0;
        let before = Instant::now();
        loop {
            if s.is_solution() {
                if i == 0 {
                    for (var, loc) in qvars.iter() {
                        let term = extract_solver_term(&reverse_atoms, &s, *loc);
                        println!("{var} = {term}");
                    }
                }
                solutions += 1;
            }
            if !s.next_state() {
                break;
            }
        }
        let duration = before.elapsed();
        total += duration;
        if i == 0 {
            println!(
                "Took {:.3}s with {} solutions",
                duration.as_secs_f64(),
                solutions
            );
        }
    }
    println!("Took {:.3}s for {repeats} rounds", total.as_secs_f64(),);
    // for _ in 0..repeats {
    //     let search = logru::query_dfs(u.inner(), &query);
    //     let before = Instant::now();
    //     let solutions = search.collect::<Vec<_>>();
    //     let duration = before.elapsed();

    //     for solution in solutions.iter() {
    //         for var in solution {
    //             if let Some(term) = var {
    //                 println!("{}", u.pretty().term_to_string(term));
    //             } else {
    //                 println!("<bug: no solution>");
    //             }
    //         }
    //     }
    //     println!(
    //         "Took {:.3}s with {} solutions",
    //         duration.as_secs_f64(),
    //         solutions.len()
    //     );
    // }
}

fn allocate_rule_atoms(universe: &mut Universe, atoms: &mut HashMap<Arc<str>, Atom>, rule: &Rule) {
    allocate_compound_atoms(universe, atoms, &rule.head);
    for term in rule.tail.iter() {
        allocate_term_atoms(universe, atoms, term);
    }
}

fn allocate_term_atoms(universe: &mut Universe, atoms: &mut HashMap<Arc<str>, Atom>, term: &Term) {
    match term {
        Term::Var(_) => {}
        Term::Compound(compound) => allocate_compound_atoms(universe, atoms, compound),
    }
}

fn allocate_compound_atoms(
    universe: &mut Universe,
    atoms: &mut HashMap<Arc<str>, Atom>,
    compound: &CompoundTerm,
) {
    atoms
        .entry(compound.head.clone())
        .or_insert_with(|| universe.reserve_atom());
    for arg in compound.args.iter() {
        allocate_term_atoms(universe, atoms, arg);
    }
}

fn term_to_stack(
    stack: &mut FrozenStack<'_>,
    atoms: &HashMap<Arc<str>, Atom>,
    var_scope: &mut HashMap<Arc<str>, Addr>,
    term: &Term,
    target: Addr,
) {
    match term {
        Term::Var(var) => match var {
            Var::Unnamed => {
                // simply leave target unassigned
            }
            Var::Named(name) => {
                if let Some(bound) = var_scope.get(name.as_ref()) {
                    // bound variable, point target to it
                    stack[target] = Word::Ptr(Some(*bound)).into();
                } else {
                    // fresh variable, simply leave target unassigned, but remember the address
                    var_scope.insert(name.clone(), target);
                }
            }
        },
        Term::Compound(compound) => {
            // Allocate term, store it in target, and fill recursively
            let head = compound_term_to_stack(stack, atoms, var_scope, compound);
            stack[target] = Word::Ptr(Some(head)).into();
        }
    }
}

fn compound_term_to_stack(
    stack: &mut FrozenStack<'_>,
    atoms: &HashMap<Arc<str>, Atom>,
    var_scope: &mut HashMap<Arc<str>, Addr>,
    compound: &CompoundTerm,
) -> Addr {
    // Allocate term, store it in target, and fill recursively
    let atom = *atoms
        .get(compound.head.as_ref())
        .expect("atom must be preallocated");
    known_compound_term_to_stack(stack, atoms, var_scope, atom, &compound.args)
}

fn known_compound_term_to_stack(
    stack: &mut FrozenStack<'_>,
    atoms: &HashMap<Arc<str>, Atom>,
    var_scope: &mut HashMap<Arc<str>, Addr>,
    atom: Atom,
    args: &[Term],
) -> Addr {
    // Allocate term, store it in target, and fill recursively
    let arity = args.len();
    let head = stack.alloc_zeroed_range(1 + arity);
    stack[head] = Word::App(atom, Arity::try_from(arity).unwrap()).into();
    for (off, arg) in args.iter().enumerate() {
        term_to_stack(stack, atoms, var_scope, arg, head.offset(1 + off as u32));
    }
    head
}

fn extract_solver_term(
    reverse_atoms: &HashMap<Atom, Arc<str>>,
    solver: &Solver,
    addr: Addr,
) -> Term {
    let (addr, value) = solver.deref_addr(addr);
    match value {
        logru::v2::solver::DerefTerm::Free => Term::Var(Var::Unnamed),
        logru::v2::solver::DerefTerm::App(atom, arity) => {
            let name = reverse_atoms.get(&atom).expect("should be known").clone();
            let args = addr
                .arg_iter(arity)
                .map(|arg| extract_solver_term(reverse_atoms, solver, arg))
                .collect();
            Term::compound(name, args)
        }
    }
}
