pub mod unification;
pub mod logic;
pub mod union_find;

use std::vec::Vec;

mod prolog_example {
    use super::*;
    use super::unification::*;
    use super::logic::*;

    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    enum Atom {
        Z, S, Add, Or, Eq
    }

    fn z() -> Term<Atom> {
        Term::App(Atom::Z, Vec::new())
    }

    fn s(t: Term<Atom>) -> Term<Atom> {
        Term::App(Atom::S, vec![t])
    }

    fn var<A>(v: usize) -> Term<A> {
        Term::Var(VarId(v))
    }

    fn add(a: Term<Atom>, b: Term<Atom>, result: Term<Atom>) -> Term<Atom> {
        Term::App(Atom::Add, vec![a, b, result])
    }

    fn or(a: Term<Atom>, b: Term<Atom>) -> Term<Atom> {
        Term::App(Atom::Or, vec![a, b])
    }

    fn eq(a: Term<Atom>, b: Term<Atom>) -> Term<Atom> {
        Term::App(Atom::Eq, vec![a, b])
    }


    pub fn main() {
        let mut pl = RuleSet::new();
        pl.add_rule(add(var(0), z(), var(0)), vec![]);
        pl.add_rule(add(var(0), s(var(1)), s(var(2))), vec![add(var(0), var(1), var(2))]);
        pl.add_rule(or(var(0), var(1)), vec![var(0)]);
        pl.add_rule(or(var(0), var(1)), vec![var(1)]);
        pl.add_rule(eq(var(0), var(0)), vec![]);

        let q = pl.query(vec![
            // add(var(0), s(s(z())), s(s(s(s(z())))))
            // add(var(0), s(s(z())), s(s(var(0))))
            // add(var(0), var(1), s(s(s(s(z())))))

            or(add(var(0), s(s(z())), s(s(s(s(z()))))),
               add(var(0), s(s(z())), s(s(s(z()))))),
            or(eq(var(0), s(s(z()))),
               eq(s(s(s(z()))), var(0)))
        ]);

        for solution in q {
            println!("Solution: {:?}", solution)
        }
        // loop {
        //     println!("State: {:?}", q);
        //     match q.step() {
        //         Step::Done => break,
        //         Step::Again => println!("\nAgain!\n"),
        //         Step::Found(solution) => {
        //             println!("\nSolution: {:?}\n", solution)
        //         }
        //     }
        // }
        // println!("\nDone!\n");
    }
}

mod nat_example {
    use super::unification::*;

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    enum NatCon {
        Z, S
    }

    fn z() -> Term<NatCon> {
        Term::App(NatCon::Z, Vec::new())
    }

    fn s(t: Term<NatCon>) -> Term<NatCon> {
        Term::App(NatCon::S, vec![t])
    }

    fn var<A>(v: VarId) -> Term<A> {
        Term::Var(v)
    }

    pub fn main() {
        // let mut u = Unifier::<NatCon>::new();
        let v0 = VarId(0); // u.new_var();
        let v1 = VarId(1); // u.new_var();
        let v2 = VarId(2); // u.new_var();

        let a = s(s(z()));
        let b = s(var(v0));
        let c = s(s(var(v0)));
        let d = s(s(s(var(v1))));
        let e = s(s(s(var(v2))));

        let mut solver = Solver::new();

        println!("Before:\n  a: {:?}\n  b: {:?}\n  c: {:?}\n  d: {:?}\n  e: {:?}", a, b, c, d, e);
        println!("Solver: {:?}\n", solver);

        solver.push_eq(d.clone(), e.clone());
        solver.solve().unwrap();

        println!("Normalized:\n  a: {:?}\n  b: {:?}\n  c: {:?}\n  d: {:?}\n  e: {:?}", solver.normalize(a.clone()), solver.normalize(b.clone()), solver.normalize(c.clone()), solver.normalize(d.clone()), solver.normalize(e.clone()));
        println!("Solver: {:?}\n", solver);

        solver.push_eq(c.clone(), d.clone());
        solver.solve().unwrap();

        println!("Normalized:\n  a: {:?}\n  b: {:?}\n  c: {:?}\n  d: {:?}\n  e: {:?}", solver.normalize(a.clone()), solver.normalize(b.clone()), solver.normalize(c.clone()), solver.normalize(d.clone()), solver.normalize(e.clone()));
        println!("Solver: {:?}\n", solver);

        solver.push_eq(a.clone(), b.clone());
        solver.solve().unwrap();

        println!("Normalized:\n  a: {:?}\n  b: {:?}\n  c: {:?}\n  d: {:?}\n  e: {:?}", solver.normalize(a.clone()), solver.normalize(b.clone()), solver.normalize(c.clone()), solver.normalize(d.clone()), solver.normalize(e.clone()));
        println!("Solver: {:?}\n", solver);

    }
}

fn main() {
    // nat_example::main();
    prolog_example::main();
}

