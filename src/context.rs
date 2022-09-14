//! # Context

use crate::*;
use tactic::{Info, Suggestion, Tactic};
use user_input::UserInput;

/// Represents context.
pub struct Context {
    /// List of expressions in context.
    pub facts: Vec<Expr>,
    /// List of tactics currently in use.
    pub tactics: Vec<Tactic>,
    /// A list of new suggestions.
    pub new_suggestions: Vec<(Expr, Info)>,
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

    /// Get suggestions.
    pub fn suggestions(&mut self) {
        self.new_suggestions.clear();

        let mut n: usize = 0;
        let mut key: Vec<usize> = vec![];
        let dumb_limit = 30;
        for t in &self.tactics {
            t.suggestions(Suggestion::Simple, &self.facts, &mut self.new_suggestions);
        }
        // Find simple suggestions that are dumb.
        for i in n..self.new_suggestions.len() {
            if format!("{}", self.new_suggestions[i].0).len() > dumb_limit {
                key.push(3);
            } else {
                key.push(1);
            }
        }

        n = self.new_suggestions.len();
        for t in &self.tactics {
            t.suggestions(Suggestion::Advanced, &self.facts, &mut self.new_suggestions);
        }
        for _ in n..self.new_suggestions.len() {
            key.push(2);
        }

        n = self.new_suggestions.len();
        for t in &self.tactics {
            t.suggestions(Suggestion::Rare, &self.facts, &mut self.new_suggestions);
        }
        for _ in n..self.new_suggestions.len() {
            key.push(4);
        }

        // Detect `false` and put it first.
        for i in 0..self.new_suggestions.len() {
            if self.new_suggestions[i].0 == Expr::Fa {
                key[i] = 0;
            }
        }

        let mut res = Vec::with_capacity(self.new_suggestions.len());
        for k in 0..5 {
            for i in 0..self.new_suggestions.len() {
                if key[i] == k {
                    res.push(self.new_suggestions[i].clone());
                }
            }
        }
        self.new_suggestions = res;
    }

    /// If zero tactic is enabled, then zero tactic.
    pub fn zero(&mut self) {
        if Tactic::Zero.find(self.tactics.iter()).is_some() {
            loop {
                self.suggestions();
                if self.new_suggestions.len() == 1 {
                    let s = &self.new_suggestions[0];
                    println!("{} by {}", s.0, s.1.0);
                    self.facts.push(s.0.clone());
                } else {break}
            }
        }
    }

    /// Make new suggestions.
    pub fn make_suggestions(&mut self) {
        self.zero();
        if Tactic::Zero.find(self.tactics.iter()).is_none() {
            self.suggestions();
        }

        if self.new_suggestions.len() != 0 {
            println!("Suggestions:");
            for (i, s) in self.new_suggestions.iter().enumerate() {
                println!("{}. {} by {}", i, s.0, s.1.0);
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
                tactics.sort();
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
                if Tactic::Debug.find(self.tactics.iter()).is_some() {
                    let (tactic, rule) = &self.new_suggestions[ind].1;
                    println!("{}::{:?}", tactic, rule);
                }
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
