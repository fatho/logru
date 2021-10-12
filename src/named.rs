use std::collections::HashMap;

use crate::{
    term::{AppTerm, Term},
    Rule, Solver, Sym, Universe, Var,
};

#[derive(Debug)]
pub struct NamedUniverse {
    names: HashMap<String, Sym>,
    syms: HashMap<Sym, String>,
    universe: Universe,
}

#[derive(Debug)]
pub struct ParseError;

impl NamedUniverse {
    pub fn new() -> Self {
        Self {
            names: HashMap::new(),
            syms: HashMap::new(),
            universe: Universe::new(),
        }
    }

    pub fn symbol(&mut self, name: &str) -> Sym {
        if let Some(sym) = self.names.get(name) {
            *sym
        } else {
            let sym = self.universe.new_symbol();
            self.names.insert(name.to_owned(), sym);
            self.syms.insert(sym, name.to_owned());
            sym
        }
    }

    pub fn term(&mut self, term: &str) -> Result<Term, ParseError> {
        self.parse_term(term).map(|(t, _)| t)
    }

    pub fn fact(&mut self, term: &str) -> Result<(), ParseError> {
        if let Term::App(term) = self.term(term)? {
            self.universe.add_rule(Rule {
                head: term,
                tail: vec![],
            });
            Ok(())
        } else {
            Err(ParseError)
        }
    }

    pub fn rule(&mut self, head: &str, tail: &[&str]) -> Result<(), ParseError> {
        if let Term::App(term) = self.term(head)? {
            let mut args = Vec::new();

            for arg in tail {
                if let Term::App(arg) = self.term(arg)? {
                    args.push(arg)
                } else {
                    return Err(ParseError);
                }
            }

            self.universe.add_rule(Rule {
                head: term,
                tail: args,
            });
            Ok(())
        } else {
            Err(ParseError)
        }
    }

    pub fn query(&mut self, goals_str: &[&str]) -> Result<Solver, ParseError> {
        let goals = self.parse_query(goals_str)?;
        Ok(self.universe.query(goals))
    }

    pub fn parse_query(&mut self, goals_str: &[&str]) -> Result<Vec<AppTerm>, ParseError> {
        let mut goals = Vec::new();

        for goal in goals_str {
            if let Term::App(arg) = self.term(goal)? {
                goals.push(arg)
            } else {
                return Err(ParseError);
            }
        }

        Ok(goals)
    }

    fn parse_term<'a>(&mut self, term: &'a str) -> Result<(Term, &'a str), ParseError> {
        let mut chars = term.char_indices();

        match chars.next() {
            Some((_, '$')) => {
                // variable
                let (num_part, rest) =
                    if let Some((last, _)) = chars.find(|(_, ch)| !ch.is_ascii_digit()) {
                        (&term[1..last], &term[last..])
                    } else {
                        (&term[1..], "")
                    };
                Ok((
                    Term::Var(Var(num_part.parse().map_err(|_| ParseError)?)),
                    rest,
                ))
            }
            Some((_, ch)) if ch.is_alphanumeric() || ch == '_' => {
                if let Some((last, ch)) = chars.find(|(_, ch)| !ch.is_alphabetic() && *ch != '_') {
                    // not all alphabetic, compound term
                    let sym = self.symbol(&term[..last]);
                    let mut args = Vec::new();

                    if ch == '(' {
                        let (first_arg, mut remaining) = self.parse_term(chars.as_str())?;
                        args.push(first_arg);

                        loop {
                            let mut remaining_chars = remaining.chars();
                            match remaining_chars.next() {
                                Some(',') => {
                                    let (next_arg, next_remaining) =
                                        self.parse_term(remaining_chars.as_str())?;
                                    args.push(next_arg);
                                    remaining = next_remaining;
                                }
                                Some(')') => {
                                    break Ok((
                                        Term::App(AppTerm { functor: sym, args }),
                                        remaining_chars.as_str(),
                                    ))
                                }
                                _ => break Err(ParseError),
                            }
                        }
                    } else {
                        Ok((Term::App(AppTerm { functor: sym, args }), &term[last..]))
                    }
                } else {
                    // all alphabetic, simple term
                    let sym = self.symbol(term);
                    Ok((
                        Term::App(AppTerm {
                            functor: sym,
                            args: Vec::new(),
                        }),
                        "",
                    ))
                }
            }
            _ => Err(ParseError),
        }
    }

    pub fn term_to_string(&self, term: &Term) -> String {
        let mut out = String::new();
        self.pretty(&mut out, term).unwrap();
        out
    }

    pub fn pretty<W: std::fmt::Write>(&self, writer: &mut W, term: &Term) -> std::fmt::Result {
        match term {
            Term::Var(v) => write!(writer, "${}", v.0),
            Term::App(app) => self.pretty_app(writer, app),
        }
    }

    pub fn pretty_app<W: std::fmt::Write>(
        &self,
        writer: &mut W,
        term: &AppTerm,
    ) -> std::fmt::Result {
        if let Some(name) = &self.syms.get(&term.functor) {
            write!(writer, "{}", name)?;
        } else {
            write!(writer, "<unk:{}>", term.functor.0)?;
        }

        if let Some((first, rest)) = term.args.split_first() {
            write!(writer, "(")?;

            self.pretty(writer, first)?;
            for arg in rest {
                write!(writer, ",")?;
                self.pretty(writer, arg)?;
            }

            write!(writer, ")")?;
        }

        Ok(())
    }

    pub fn inner_mut(&mut self) -> &mut Universe {
        &mut self.universe
    }

    pub fn inner(&self) -> &Universe {
        &self.universe
    }
}

impl Default for NamedUniverse {
    fn default() -> Self {
        Self::new()
    }
}


#[test]
fn parse_test() {
    let mut nu = NamedUniverse::new();

    let mut roundtrip = |term_str| {
        let t = nu.term(term_str).unwrap();
        assert_eq!(nu.term_to_string(&t), term_str);
    };

    roundtrip("foo");
    roundtrip("exists(foo)");
    roundtrip("add(s(s(z)),s(z),$0)");
}
