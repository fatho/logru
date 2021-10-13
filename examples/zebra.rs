use std::time::Instant;

fn main() {
    let repeats = std::env::args()
        .nth(1)
        .and_then(|arg| arg.parse().ok())
        .unwrap_or(1);

    let mut u = logru::textual::TextualUniverse::new();
    u.load_str(include_str!("../testfiles/zebra.lru")).unwrap();

    for _ in 0..repeats {
        let mut solutions = u.query_dfs("puzzle($0).").unwrap();
        let before = Instant::now();
        let solution = solutions.next().unwrap();
        let duration = before.elapsed();

        for var in solution {
            if let Some(term) = var {
                println!("{}", u.pretty().term_to_string(&term));
            } else {
                println!("<bug: no solution>");
            }
        }
        println!("Took {:.3}s", duration.as_secs_f64());
    }
}
