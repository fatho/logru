use logru::{search::query_dfs, textual::TextualUniverse};

fn main() {
    let mut u = TextualUniverse::new();

    u.load_str(include_str!("../testfiles/arithmetic.lru"))
        .unwrap();

    let query = u.prepare_query("mul(A,A,B).").unwrap();
    let solutions = query_dfs(u.resolver(), query.query());

    for solution in solutions.take(10) {
        println!("SOLUTION:");
        for (var, term) in solution.iter_vars() {
            if let Some(term) = term {
                println!("  ${} = {}", var.ord(), query.pretty().term_to_string(term));
            } else {
                println!("<bug: no solution>");
            }
        }
    }
}
