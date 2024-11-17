use logru::{solver::query_dfs, textual::TextualUniverse};

fn main() {
    let mut u = TextualUniverse::new();

    u.load_str(include_str!("../testfiles/arithmetic.lru"))
        .unwrap();

    let query = u.prepare_query("mul(A,A,B).").unwrap();
    let solutions = query_dfs(u.rules(), &query);

    for solution in solutions.take(10) {
        println!("SOLUTION:");
        for (index, var) in solution.into_iter().enumerate() {
            if let Some(term) = var {
                println!(
                    "  ${} = {}",
                    index,
                    u.pretty().term_to_string(&term, query.scope.as_ref())
                );
            } else {
                println!("<bug: no solution>");
            }
        }
    }
}
