use logru::solver::query_dfs;
use logru::textual::TextualUniverse;
use rustyline::error::ReadlineError;
use rustyline::Editor;

fn main() {
    // `()` can be used when no completer is required
    let mut rl = Editor::<()>::new();
    // if rl.load_history("history.txt").is_err() {
    //     println!("No previous history.");
    // }
    let mut universe = TextualUniverse::default();
    'outer: loop {
        let readline = rl.readline("?- ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                if line.starts_with(':') {
                    let end_of_command = line.find(' ').unwrap_or_else(|| line.len());
                    match &line[0..end_of_command] {
                        ":reset" => {
                            universe = TextualUniverse::default();
                        }
                        ":load" => {
                            if end_of_command == line.len() {
                                println!("Usage:\n\t:load <filename>")
                            }
                            let filename = &line[end_of_command + 1..];
                            match std::fs::read_to_string(filename) {
                                Ok(contents) => match universe.load_str(&contents) {
                                    Ok(()) => {
                                        println!("Loaded!");
                                    }
                                    Err(err) => {
                                        println!("Failed to parse: {:?}", err);
                                    }
                                },
                                Err(err) => {
                                    println!("Failed to load: {}", err);
                                }
                            }
                        }
                        ":help" => {
                            println!(
                                "Available commands:
            \t:help
            \t:reset
            \t:load <filename>"
                            )
                        }
                        other => {
                            println!("Unknown command: {}", other)
                        }
                    }
                } else {
                    match universe.prepare_query(&line) {
                        Ok(query) => {
                            let solutions = query_dfs(universe.inner(), &query);
                            for solution in solutions {
                                println!("Found solution:");
                                for (index, var) in solution.into_iter().enumerate() {
                                    print!("  ${} = ", index);
                                    if let Some(term) = var {
                                        println!("{}", universe.pretty().term_to_string(&term));
                                    } else {
                                        println!("<any>");
                                    }
                                }
                                let readline = rl.readline(".. ");
                                match readline {
                                    Ok(_) => continue,
                                    Err(ReadlineError::Interrupted) => break,
                                    Err(_) => break 'outer,
                                }
                            }
                            println!("No more solutions.")
                        }
                        Err(err) => {
                            println!("Failed to parse: {:?}", err);
                        }
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("not yet implemented, use CTRL+D for quitting");
            }
            Err(ReadlineError::Eof) => {
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    // rl.save_history("history.txt").unwrap();
}
