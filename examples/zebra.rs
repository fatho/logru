use std::time::Instant;

use logru::solver::Plain;

fn main() {
    let repeats = std::env::args()
        .nth(1)
        .and_then(|arg| arg.parse().ok())
        .unwrap_or(1);

    let mut u = logru::textual::TextualUniverse::new();
    u.load_str(include_str!("../testfiles/zebra.lru")).unwrap();

    let query = u.prepare_query("puzzle($0).").unwrap();
    for _ in 0..repeats {
        let search = logru::query_dfs(u.inner().inner(), Plain, &query);
        let before = Instant::now();
        let solutions = search.collect::<Vec<_>>();
        let duration = before.elapsed();

        for solution in solutions.iter() {
            for var in solution {
                if let Some(term) = var {
                    println!("{}", u.pretty().term_to_string(term));
                } else {
                    println!("<bug: no solution>");
                }
            }
        }
        println!(
            "Took {:.3}s with {} solutions",
            duration.as_secs_f64(),
            solutions.len()
        );
    }
}
