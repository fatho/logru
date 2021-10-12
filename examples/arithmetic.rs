use logru::{named::NamedUniverse, solver::Solver};

fn main() {
    let mut u = NamedUniverse::new();

    u.fact("is_natural(z)").unwrap();
    u.rule("is_natural(s($0))", &["is_natural($0)"]).unwrap();

    u.rule("add($0,z,$0)", &["is_natural($0)"]).unwrap();
    u.rule("add($0,s($1),s($2))", &["add($0,$1,$2)"]).unwrap();

    u.rule("mul($0,z,z)", &["is_natural($0)"]).unwrap();
    u.rule("mul($0,s($1),$2)", &["add($0,$3,$2)", "mul($0,$1,$3)"])
        .unwrap();

    let query = u.parse_query(&["mul($0,$0,$1)"]).unwrap();
    let solver = Solver::new(u.inner());
    let solutions = solver.query(&query);

    for solution in solutions.take(10) {
        println!("SOLUTION:");
        for (index, var) in solution.into_iter().enumerate() {
            if let Some(term) = var {
                println!("  ${} = {}", index, u.term_to_string(&term));
            } else {
                println!("<bug: no solution>");
            }
        }
    }
}
