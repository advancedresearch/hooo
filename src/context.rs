//! # Context

use crate::*;
use tactic::Tactic;
use user_input::UserInput;

/// Represents context.
pub struct Context {
    /// List of expressions in context.
    pub facts: Vec<Expr>,
    /// List of tactics currently in use.
    pub tactics: Vec<Tactic>,
    /// A list of new suggestions.
    pub new_suggestions: Vec<(Expr, String)>,
}

impl Context {
    /// Creates a new empty context.
    pub fn new() -> Context {
        Context {
            facts: vec![],
            tactics: vec![],
            new_suggestions: vec![],
        }
    }

    /// If zero tactic is enabled, then zero tactic.
    pub fn zero(&mut self) {
        if Tactic::Zero.find(self.tactics.iter()).is_some() {
            loop {
                self.new_suggestions.clear();
                for t in &self.tactics {
                    t.suggestions(&self.facts, &mut self.new_suggestions);
                }
                if self.new_suggestions.len() == 1 {
                    let s = &self.new_suggestions[0];
                    if s.1 != "".to_string() {
                        println!("{} by {}", s.0, s.1);
                    } else {
                        println!("{} by {}", s.0, s.1);
                    }
                    self.facts.push(s.0.clone());
                } else {break}
            }
        }
    }

    /// Make new suggestions.
    pub fn make_suggestions(&mut self) {
        self.zero();
        if Tactic::Zero.find(self.tactics.iter()).is_none() {
            self.new_suggestions.clear();
            for t in &self.tactics {
                t.suggestions(&self.facts, &mut self.new_suggestions);
            }
        }

        if self.new_suggestions.len() != 0 {
            println!("Suggestions:");
            for (i, s) in self.new_suggestions.iter().enumerate() {
                if s.1 != "".to_string() {
                    println!("{}. {} by {}", i, s.0, s.1);
                } else {
                    println!("{}. {} by {}", i, s.0, s.1);
                }
            }
        }
    }

    /// Add expression to context.
    pub fn add_expr(&mut self, expr: Expr) {
        if Tactic::Debug.find(self.tactics.iter()).is_some() {
            println!("{:?}", expr);
        }

        let found = expr.find(self.facts.iter());
        if let Some(ind) = found {
            let n = self.facts.len() - 1;
            self.facts.swap(ind, n);
        } else {
            self.facts.push(expr);
        }

        if Tactic::Silence.find(self.tactics.iter()).is_none() {
            for f in &self.facts {
                println!("{}", f);
            }
        }
    }

    /// Handles user input.
    pub fn handle(&mut self, user_input: UserInput) -> Result<(), String> {
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

        use UserInput::*;

        match user_input {
            Separator => {
                // Print separator for readability.
                print!("\n------------------------------------<o=o");
                println!("o=o>------------------------------------\n");
            }
            Clear => {
                self.tactics.clear();
                self.facts.clear();
            }
            HelpMain => println!("{}", include_str!("../assets/help/help.txt")),
            HelpTactic => println!("{}", include_str!("../assets/help/tactic.txt")),
            Help(Tactic::App) => println!("{}", include_str!("../assets/help/app.txt")),
            Help(Tactic::And) => println!("{}", include_str!("../assets/help/and.txt")),
            Help(Tactic::Qubit) => println!("{}", include_str!("../assets/help/qubit.txt")),
            Help(t) => return Err(format!("Undocumented: {}", t)),
            Bye => {}
            Use(t) => new_tactic(t, &mut self.tactics),
            RemTactic(ind) => {
                self.tactics.swap_remove(ind);
                if Tactic::Silence.find(self.tactics.iter()).is_none() {
                    for t in &self.tactics {
                        println!("{}", t);
                    }
                }

                self.zero();
            }
            RemExpr(ind) => {
                self.facts.swap_remove(ind);
                if Tactic::Silence.find(self.tactics.iter()).is_none() {
                    for f in &self.facts {
                        println!("{}", f);
                    }
                }

                self.zero();
            }
            ParseError(err) => return Err(err),
            SuggestionOutOfBounds(ind) => return Err(
                format!("Suggestion `{}` out of bounds `{}`",
                    ind, self.new_suggestions.len())
            ),
            CouldNotFindExpr(expr) => return Err(
                format!("Could not find expr `{}`", expr)
            ),
            PickSuggestion(ind) => {
                let expr = self.new_suggestions[ind].0.clone();
                self.add_expr(expr);
                self.make_suggestions();
            }
            Sugg => {
                self.make_suggestions();
            }
            AddExpr(expr) => {
                self.add_expr(expr);
                self.make_suggestions();
            }
            // These cases are handled by the refine step.
            Rem(_) | SuggCheck(_) | Unknown(_) => {}
        }
        Ok(())
    }
}
