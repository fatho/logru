use logru::solver::Plain;
use logru::{solver::query_dfs, textual::TextualUniverse};

fn main() {
    let mut u = TextualUniverse::new();

    u.load_str(
        r#"
    is_natural(z).
    is_natural(s($0)) :- is_natural($0).

    add($0, z, $0) :- is_natural($0).
    add($0, s($1), s($2)) :- add($0, $1, $2).

    mul($0, z, z) :- is_natural($0).
    mul($0, s($1), $2) :- mul($0,$1,$3), add($0,$3,$2).
    "#,
    )
    .unwrap();

    let query = u.prepare_query("mul($0,$0,$1).").unwrap();
    let solutions = query_dfs(u.inner().inner(), Plain, &query);

    for solution in solutions.take(10) {
        println!("SOLUTION:");
        for (index, var) in solution.into_iter().enumerate() {
            if let Some(term) = var {
                println!("  ${} = {}", index, u.pretty().term_to_string(&term));
            } else {
                println!("<bug: no solution>");
            }
        }
    }
}
