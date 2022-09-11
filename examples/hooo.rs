use hooo::*;
use hooo::tactic::Tactic;

pub fn new_tactic(new_tactic: Tactic, tactics: &mut Vec<Tactic>) {
    if let Some(_) = new_tactic.find(tactics.iter()) {
        eprintln!("Tactic already in use");
    } else {
        tactics.push(new_tactic);
        if Tactic::Silence.find(tactics.iter()).is_none() {
            for t in &*tactics {
                println!("{}", t);
            }
        }
    }
}

fn main() {
    println!("=== HOOO 0.1 ===");
    println!("For more information, type `help`");

    let mut facts: Vec<Expr> = vec![];
    let mut tactics: Vec<Tactic> = vec![];
    let mut new_suggestions: Vec<(Expr, String)> = vec![];

    loop {
        use std::io::{self, Write};

        let mut input = String::new();
        print!("> ");
        io::stdout().flush().unwrap();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {}
            Err(_) => {
                println!("ERROR: Could not read input");
                continue;
            }
        };

        match input.trim() {
            "" => {
                // Print separator for readability.
                print!("\n------------------------------------<o=o");
                println!("o=o>------------------------------------\n");
                continue;
            }
            "clear" => {
                tactics.clear();
                facts.clear();
            }
            "help" => println!("{}", include_str!("../assets/help/help.txt")),
            "help tactic" => println!("{}", include_str!("../assets/help/tactic.txt")),
            "help app" => println!("{}", include_str!("../assets/help/app.txt")),
            "help and" => println!("{}", include_str!("../assets/help/and.txt")),
            "help qubit" => println!("{}", include_str!("../assets/help/qubit.txt")),
            "bye" => break,
            "use zero" => new_tactic(Tactic::Zero, &mut tactics),
            "use silence" => new_tactic(Tactic::Silence, &mut tactics),
            "use eq" => new_tactic(Tactic::Eq, &mut tactics),
            "use sym" => new_tactic(Tactic::Sym, &mut tactics),
            "use hooo" => new_tactic(Tactic::Hooo, &mut tactics),
            "use debug" => new_tactic(Tactic::Debug, &mut tactics),
            "use app" => new_tactic(Tactic::App, &mut tactics),
            "use and" => new_tactic(Tactic::And, &mut tactics),
            "use imply" => new_tactic(Tactic::Imply, &mut tactics),
            "use modus" => new_tactic(Tactic::Modus, &mut tactics),
            "use qubit" => new_tactic(Tactic::Qubit, &mut tactics),
            x if x.starts_with("rem ") => {
                let rest = x[4..].trim();
                let mut found: Option<usize> = None;
                for (i, t) in tactics.iter().enumerate() {
                    if &format!("{}", t) == rest {
                        found = Some(i);
                        break;
                    }
                }
                if let Some(ind) = found {
                    tactics.swap_remove(ind);
                    if Tactic::Silence.find(tactics.iter()).is_none() {
                        for t in &tactics {
                            println!("{}", t);
                        }
                    }
                } else {
                    let expr = match parsing::parse_str(rest, &[]) {
                        Ok(x) => x,
                        Err(err) => {
                            eprintln!("ERROR:\n{}", err);
                            continue;
                        }
                    };
                    if let Some(ind) = expr.find(facts.iter()) {
                        facts.swap_remove(ind);
                        if Tactic::Silence.find(tactics.iter()).is_none() {
                            for f in &facts {
                                println!("{}", f);
                            }
                        }
                    }
                }

                // Continue using zero tactic if removing other tactics helped.
                if Tactic::Zero.find(tactics.iter()).is_some() {
                    loop {
                        new_suggestions.clear();
                        for t in &tactics {
                            t.suggestions(&facts, &mut new_suggestions);
                        }
                        if new_suggestions.len() == 1 {
                            let s = &new_suggestions[0];
                            if s.1 != "".to_string() {
                                println!("{} by {}", s.0, s.1);
                            } else {
                                println!("{} by {}", s.0, s.1);
                            }
                            facts.push(s.0.clone());
                        } else {break}
                    }
                }
            }
            x => {
                use std::str::FromStr;

                if x != "sugg" {
                    let expr = if let Ok(n) = usize::from_str(x) {
                        if n < new_suggestions.len() {
                            new_suggestions[n].0.clone()
                        } else {continue}
                    } else {
                        match parsing::parse_str(x, &[]) {
                            Ok(x) => x,
                            Err(err) => {
                                eprintln!("ERROR:\n{}", err);
                                continue;
                            }
                        }
                    };

                    if Tactic::Debug.find(tactics.iter()).is_some() {
                        println!("{:?}", expr);
                    }

                    let found = expr.find(facts.iter());
                    if let Some(ind) = found {
                        let n = facts.len() - 1;
                        facts.swap(ind, n);
                    } else {
                        facts.push(expr);
                    }
                }

                if Tactic::Silence.find(tactics.iter()).is_none() {
                    for f in &facts {
                        println!("{}", f);
                    }
                }

                if Tactic::Zero.find(tactics.iter()).is_some() {
                    loop {
                        new_suggestions.clear();
                        for t in &tactics {
                            t.suggestions(&facts, &mut new_suggestions);
                        }
                        if new_suggestions.len() == 1 {
                            let s = &new_suggestions[0];
                            if s.1 != "".to_string() {
                                println!("{} by {}", s.0, s.1);
                            } else {
                                println!("{} by {}", s.0, s.1);
                            }
                            facts.push(s.0.clone());
                        } else {break}
                    }
                } else {
                    new_suggestions.clear();
                    for t in &tactics {
                        t.suggestions(&facts, &mut new_suggestions);
                    }
                }

                if new_suggestions.len() != 0 {
                    println!("Suggestions:");
                    for (i, s) in new_suggestions.iter().enumerate() {
                        if s.1 != "".to_string() {
                            println!("{}. {} by {}", i, s.0, s.1);
                        } else {
                            println!("{}. {} by {}", i, s.0, s.1);
                        }
                    }
                }
            }
        }
    }
}
