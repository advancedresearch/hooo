//! # Context

use crate::*;
use tactic::Tactic;

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
}
