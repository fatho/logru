use std::time::Instant;

fn main() {
    let mut u = logru::textual::TextualUniverse::new();
    u.load_str(include_str!("../testfiles/zebra.lru")).unwrap();

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
