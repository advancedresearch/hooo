use crate::*;
use tactic::Tactic;
use context::Context;
use user_input::UserInput;

fn new_tactic(new_tactic: Tactic, tactics: &mut Vec<Tactic>) {
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

/// The main loop of the repl.
pub fn main() {
    use UserInput::*;

    println!("=== HOOO 0.1 ===");
    println!("For more information, type `help`");

    let mut context = Context::new();

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

        let user_input = UserInput::from_str(&input).refine(&context);
        match user_input {
            Separator => {
                // Print separator for readability.
                print!("\n------------------------------------<o=o");
                println!("o=o>------------------------------------\n");
                continue;
            }
            Clear => {
                context.tactics.clear();
                context.facts.clear();
            }
            HelpMain => println!("{}", include_str!("../assets/help/help.txt")),
            HelpTactic => println!("{}", include_str!("../assets/help/tactic.txt")),
            Help(Tactic::App) => println!("{}", include_str!("../assets/help/app.txt")),
            Help(Tactic::And) => println!("{}", include_str!("../assets/help/and.txt")),
            Help(Tactic::Qubit) => println!("{}", include_str!("../assets/help/qubit.txt")),
            Help(t) => eprintln!("Undocumented: {}", t),
            Bye => break,
            Use(t) => new_tactic(t, &mut context.tactics),
            RemTactic(ind) => {
                context.tactics.swap_remove(ind);
                if Tactic::Silence.find(context.tactics.iter()).is_none() {
                    for t in &context.tactics {
                        println!("{}", t);
                    }
                }

                context.zero();
            }
            RemExpr(ind) => {
                context.facts.swap_remove(ind);
                if Tactic::Silence.find(context.tactics.iter()).is_none() {
                    for f in &context.facts {
                        println!("{}", f);
                    }
                }

                context.zero();
            }
            ParseError(err) => {
                eprintln!("ERROR:\n{}", err);
            }
            SuggestionOutOfBounds(ind) => {
                eprintln!("ERROR:\nSuggestion `{}` out of bounds `{}`",
                    ind, context.new_suggestions.len());
            }
            CouldNotFindExpr(expr) => {
                eprintln!("ERROR:\nCould not find expr `{}`", expr);
            }
            PickSuggestion(ind) => {
                let expr = context.new_suggestions[ind].0.clone();
                context.add_expr(expr);
                context.make_suggestions();
            }
            Sugg => {
                context.make_suggestions();
            }
            AddExpr(expr) => {
                context.add_expr(expr);
                context.make_suggestions();
            }
            // These cases are handled by the refine step.
            Rem(_) | Unknown(_) => {}
        }
    }
}
