use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::{self, AtomicBool};
use std::sync::Arc;
use std::time::Instant;

use logru::ast::{Sym, Var, VarScope};
use logru::resolve::{ArithmeticResolver, ResolverExt};
use logru::search::{query_dfs, Resolved, Resolver};
use logru::term_arena::{AppTerm, ArgRange};
use logru::textual::{Prettifier, TextualUniverse};
use logru::SymbolStore;
use rustyline::completion::Completer;
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::Hinter;
use rustyline::history::DefaultHistory;
use rustyline::validate::Validator;
use rustyline::{Editor, Helper};

const HEADER: &str = "
#===================#
# LogRu REPL v0.1.0 #
#===================#
";

fn main() {
    // install global collector configured based on RUST_LOG env var.
    tracing_subscriber::fmt::init();

    println!("{}", HEADER);

    let mut rl = Editor::<AppState, DefaultHistory>::new().expect("Failed to initialize REPL");

    // ================= SETUP HISTORY ========================
    let history_path = get_history_path();
    if let Some(history_path) = history_path.as_ref() {
        match rl.load_history(history_path.as_path()) {
            Ok(()) => tracing::debug!("History loaded"),
            Err(ReadlineError::Io(ioerr)) if ioerr.kind() == std::io::ErrorKind::NotFound => {
                tracing::info!("No previous history")
            }
            Err(err) => tracing::error!("Failed to load history: {}", err),
        }
    }

    // ================= CTRL-C HANDLING ========================

    //rustyline also handles Ctrl-C, but only during prompts. For cancelling long runnign
    // evaluations, we need our own handling.
    let interrupted = Arc::new(AtomicBool::new(false));
    let interrupted_in_handler = interrupted.clone();
    if let Err(err) =
        ctrlc::set_handler(move || interrupted_in_handler.store(true, atomic::Ordering::SeqCst))
    {
        tracing::error!(
            "Could not install Ctrl-C handler, evaluations cannot be interrupted: {}",
            err
        );
    }

    // ================= INITIALIZE STATE ========================

    rl.set_helper(Some(AppState::new(interrupted)));

    // ================= ACTUAL REPL ========================

    loop {
        match rl.readline("?- ") {
            Ok(line) => {
                rl.add_history_entry(&line).expect("Couldn't add history");
                dispatch(rl.helper_mut().unwrap(), line)
            }
            Err(ReadlineError::Interrupted) => {
                // Intentionally silenced to prevent accidentally closing the REPL due to poor
                // timing, because Ctrl-C is also used for interrupting computations.
            }
            Err(ReadlineError::Eof) => {
                println!("^D");
                break;
            }
            Err(err) => {
                tracing::error!("readline: {}", err);
                break;
            }
        }
    }

    // ================= CLEANUP ========================

    if let Some(history_path) = history_path.as_ref() {
        if let Err(err) = rl.save_history(history_path) {
            tracing::error!("Failed to save history: {}", err);
        } else {
            tracing::debug!("History saved");
        }
    }
}

struct AppState {
    universe: TextualUniverse,
    commands: ReplCommands,
    arithmetic: ArithmeticResolver,
    interrupted: Arc<AtomicBool>,
}

impl AppState {
    pub fn new(interrupted: Arc<AtomicBool>) -> Self {
        let mut universe = TextualUniverse::new();
        let commands = ReplCommands::new(&mut universe.symbols);
        let arithmetic = ArithmeticResolver::new(&mut universe.symbols);
        Self {
            universe,
            commands,
            interrupted,
            arithmetic,
        }
    }
}

impl Helper for AppState {}
impl Validator for AppState {}
impl Highlighter for AppState {}
impl Hinter for AppState {
    type Hint = String;
}
impl Completer for AppState {
    type Candidate = String;
}

fn dispatch(state: &mut AppState, line: String) {
    if line.starts_with(':') {
        let (command, args) = line.split_once(' ').unwrap_or((&line, ""));
        for cmd in COMMANDS {
            if command == cmd.name {
                return (cmd.run)(state, args);
            }
        }
        println!("No such command: {}", command);
    } else {
        query(state, &line);
    }
}

fn query(state: &mut AppState, args: &str) {
    state.interrupted.store(false, atomic::Ordering::SeqCst);
    match state.universe.prepare_query(args) {
        Ok(query) => {
            let builtins = state
                .commands
                .as_resolver(&state.universe.symbols, query.scope.as_ref());
            let resolver = builtins
                .or_else(&mut state.arithmetic)
                .or_else(state.universe.resolver());
            let mut solutions = query_dfs(resolver, &query);
            loop {
                if state.interrupted.load(atomic::Ordering::SeqCst) {
                    println!("Interrupted!");
                    break;
                }
                match solutions.step() {
                    logru::search::Step::Yield => {
                        let solution = solutions.get_solution();
                        println!("Found solution:");
                        for (index, var) in solution.into_iter().enumerate() {
                            if let Some(name) = query
                                .scope
                                .as_ref()
                                .and_then(|s| s.get_name(Var::from_ord(index)))
                            {
                                print!("  {} = ", name);
                            } else {
                                print!("  _{} = ", index);
                            }
                            if let Some(term) = var {
                                println!(
                                    "{}",
                                    state
                                        .universe
                                        .pretty()
                                        .term_to_string(&term, query.scope.as_ref())
                                );
                            } else {
                                println!("<any>");
                            }
                        }
                    }
                    logru::search::Step::Continue => continue,
                    logru::search::Step::Done => {
                        println!("No more solutions.");
                        break;
                    }
                }
            }
        }
        Err(err) => {
            println!("Failed to parse: {:?}", err);
        }
    }
}

static COMMANDS: &[Command] = &[
    Command {
        name: ":define",
        args: "<source>",
        help: "Insert definitions from the literal source text.",
        run: &|state, args| {
            if args.is_empty() {
                println!("Usage:\n\t:define <source>");
                return;
            }
            match state.universe.load_str(args) {
                Ok(()) => {
                    println!("Defined!");
                }
                Err(err) => {
                    println!("Failed to parse: {:?}", err);
                }
            }
        },
    },
    Command {
        name: ":help",
        args: "",
        help: "Show this help message.",
        run: &|_state, _args| {
            println!("Available commands:");
            let max_width = COMMANDS
                .iter()
                .map(|cmd| cmd.name.len() + cmd.args.len() + 1)
                .max()
                .unwrap_or(0);
            let spaces: String = " ".repeat(max_width + 2);
            for cmd in COMMANDS {
                let width = cmd.name.len() + cmd.args.len() + 1;
                let num_spaces = max_width - width + 2;
                println!(
                    "  {} {}{}{}",
                    cmd.name,
                    cmd.args,
                    &spaces[0..num_spaces],
                    cmd.help
                );
            }
        },
    },
    Command {
        name: ":load",
        args: "<filename>",
        help: "Load definitions from the given file.",
        run: &|state, args| {
            if args.is_empty() {
                println!("Usage:\n\t:load <filename>");
                return;
            }
            match std::fs::read_to_string(args) {
                Ok(contents) => match state.universe.load_str(&contents) {
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
        },
    },
    Command {
        name: ":reset",
        args: "",
        help: "Forget all previously loaded facts and rules.",
        run: &|state, _args| {
            state.universe = TextualUniverse::new();
        },
    },
    Command {
        name: ":time",
        args: "<query>",
        help: "Time the duration of the query execution.",
        run: &|state, args| {
            let start = Instant::now();
            query(state, args);
            let duration = start.elapsed();
            println!("Took {:.4}s", duration.as_secs_f64());
        },
    },
];

struct Command {
    name: &'static str,
    args: &'static str,
    help: &'static str,
    run: &'static (dyn Fn(&mut AppState, &str) + Sync + Send + 'static),
}

fn get_history_path() -> Option<PathBuf> {
    if let Some(mut config_path) = dirs::config_dir() {
        config_path.push("logru");
        match std::fs::create_dir(&config_path) {
            Ok(()) => (),
            Err(ioerr) if ioerr.kind() == std::io::ErrorKind::AlreadyExists => (),
            Err(other) => {
                tracing::error!(
                    "Failed to create config dir {}: {}",
                    config_path.display(),
                    other
                );
                return None;
            }
        };
        config_path.push("history.txt");
        tracing::info!("Using history file: {}", config_path.display());
        Some(config_path)
    } else {
        tracing::error!("Could not determine config folder, history will not be persisted");
        None
    }
}

/// Mapping from symbols to built-in REPL commands.
struct ReplCommands {
    goals: HashMap<Sym, ReplCmd>,
}

impl ReplCommands {
    pub fn new(syms: &mut SymbolStore) -> Self {
        let commands = [("debug", ReplCmd::Debug)];
        Self {
            goals: syms.build_sym_map(commands),
        }
    }

    pub fn as_resolver<'s>(
        &'s self,
        symbols: &'s SymbolStore,
        query_scope: Option<&'s VarScope>,
    ) -> ReplResolver<'s> {
        ReplResolver {
            goals: &self.goals,
            symbols,
            query_scope,
        }
    }
}

/// Resolver providing special REPL commands.
struct ReplResolver<'s> {
    goals: &'s HashMap<Sym, ReplCmd>,
    symbols: &'s SymbolStore,
    query_scope: Option<&'s VarScope>,
}

impl<'s> ReplResolver<'s> {
    fn debug(
        &self,
        args: ArgRange,
        context: &mut logru::search::ResolveContext,
    ) -> Option<Resolved<()>> {
        let arg_terms = context.solution().terms().get_args(args);
        let arg_str = arg_terms
            .map(|term_id| {
                let term = context.solution().extract_term(term_id);
                Prettifier::new(self.symbols).term_to_string(&term, self.query_scope)
            })
            .collect::<Vec<_>>()
            .join(", ");
        tracing::info!("debug({arg_str})");
        Some(Resolved::Success)
    }
}

/// Built-in REPL commands.
#[derive(Debug)]
enum ReplCmd {
    /// Debug-prints the argument to the console.
    Debug,
}

impl<'s> Resolver for ReplResolver<'s> {
    // For now, all built-in commands are single-shot.
    type Choice = ();

    fn resolve(
        &mut self,
        _goal_id: logru::term_arena::TermId,
        goal_term: logru::term_arena::Term,
        context: &mut logru::search::ResolveContext,
    ) -> Option<Resolved<Self::Choice>> {
        let AppTerm(sym, args) = goal_term.as_app()?;
        let goal = self.goals.get(&sym)?;
        match goal {
            ReplCmd::Debug => self.debug(args, context),
        }
    }

    fn resume(
        &mut self,
        _choice: &mut Self::Choice,
        _goal_id: logru::term_arena::TermId,
        _context: &mut logru::search::ResolveContext,
    ) -> bool {
        false
    }
}
