use std::time::Instant;

use logru::v2::parser::Parser;

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

    for rule in prog.iter() {
        println!("{rule}")
    }
    println!("\n?- {query}");

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
