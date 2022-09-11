//! # User input

use crate::*;
use context::Context;
use tactic::Tactic;

/// Represents user input.
pub enum UserInput {
    /// Print readable separator.
    Separator,
    /// Clear tactics and expressions from context.
    Clear,
    /// Help main.
    HelpMain,
    /// Help about tactics in general.
    HelpTactic,
    /// Help with tactic.
    Help(Tactic),
    /// Quit REPL.
    Bye,
    /// Use tactic.
    Use(Tactic),
    /// Remove tactic.
    RemTactic(usize),
    /// Remove expression.
    RemExpr(usize),
    /// Make new suggestions.
    Sugg,
    /// Add expression.
    AddExpr(Expr),
    /// Parsing error.
    ParseError(String),
    /// Could not find expression.
    CouldNotFindExpr(Expr),
    /// Pick this suggestion.
    PickSuggestion(usize),
    /// The suggestion is outside of the bounds of new suggestions.
    SuggestionOutOfBounds(usize),
    /// Unrefined removal string (requires context to be refined).
    Rem(String),
    /// Unrefined suggestion check.
    SuggCheck(String),
    /// Unrefined unknown string (requires context to be refined).
    Unknown(String),
}

impl UserInput {
    /// Refines the user input to provide errors in relation to context.
    pub fn refine(self, context: &Context) -> UserInput {
        use UserInput::*;

        match self {
            Separator |
            Clear |
            Sugg |
            HelpMain |
            HelpTactic |
            Help(_) |
            Bye |
            Use(_) |
            RemTactic(_) |
            RemExpr(_) |
            AddExpr(_) |
            ParseError(_) |
            CouldNotFindExpr(_) |
            PickSuggestion(_) |
            SuggestionOutOfBounds(_) => self,
            Rem(ref rest) => {
                let mut found: Option<usize> = None;
                for (i, t) in context.tactics.iter().enumerate() {
                    if &format!("{}", t) == rest {
                        found = Some(i);
                        break;
                    }
                }
                if let Some(ind) = found {
                    RemTactic(ind)
                } else {
                    let expr = match parsing::parse_str(rest, &[]) {
                        Ok(x) => x,
                        Err(err) => return ParseError(err),
                    };
                    if let Some(ind) = expr.find(context.facts.iter()) {
                        RemExpr(ind)
                    } else {
                        CouldNotFindExpr(expr)
                    }
                }
            }
            SuggCheck(ref rest) => {
                let expr = match parsing::parse_str(rest, &[]) {
                    Ok(x) => x,
                    Err(err) => return ParseError(err),
                };
                if let Some(ind) = expr.find(context.new_suggestions.iter().map(|(a, _)| a)) {
                    PickSuggestion(ind)
                } else {
                    CouldNotFindExpr(expr)
                }
            }
            Unknown(ref x) => {
                use std::str::FromStr;

                if let Ok(n) = usize::from_str(x) {
                    if n < context.new_suggestions.len() {
                        PickSuggestion(n)
                    } else {
                        SuggestionOutOfBounds(n)
                    }
                } else {
                    AddExpr(match parsing::parse_str(x, &[]) {
                        Ok(x) => x,
                        Err(err) => return ParseError(err),
                    })
                }
            }
        }
    }

    /// Convert string into user input.
    pub fn from_str(input: &str) -> Self {
        use UserInput::*;

        match input.trim() {
            "" => Separator,
            "clear" => Clear,
            "sugg" => Sugg,
            "help" => HelpMain,
            "help tactic" => HelpTactic,
            "help app" => Help(Tactic::App),
            "help and" => Help(Tactic::And),
            "help qubit" => Help(Tactic::Qubit),
            "bye" => Bye,
            "use zero" => Use(Tactic::Zero),
            "use silence" => Use(Tactic::Silence),
            "use eq" => Use(Tactic::Eq),
            "use sym" => Use(Tactic::Sym),
            "use hooo" => Use(Tactic::Hooo),
            "use debug" => Use(Tactic::Debug),
            "use app" => Use(Tactic::App),
            "use and" => Use(Tactic::And),
            "use imply" => Use(Tactic::Imply),
            "use modus" => Use(Tactic::Modus),
            "use qubit" => Use(Tactic::Qubit),
            "use sesh" => Use(Tactic::Sesh),
            x if x.starts_with("sugg ") => {
                let rest = x[5..].trim();
                if rest == "" {Sugg} else {SuggCheck(rest.into())}
            }
            x if x.starts_with("rem ") => {
                let rest = x[4..].trim();
                Rem(rest.into())
            }
            x => Unknown(x.into())
        }
    }

    /// Convert source into a sequence of user input.
    pub fn from_source(src: &str) -> Vec<Self> {
        src.split(";").map(|input| Self::from_str(input)).collect()
    }

    /// Get sequence of user input from file.
    pub fn from_file(file: &str) -> Result<Vec<Self>, String> {
        use std::fs::File;
        use std::io::Read;

        let mut data_file = File::open(file).map_err(|err|
            format!("Could not open `{}`, {}", file, err))?;
        let mut data = String::new();
        data_file.read_to_string(&mut data).unwrap();

        let inputs = UserInput::from_source(&data);
        Ok(inputs)
    }
}

/// Checks user input.
pub fn check(inputs: Vec<UserInput>) -> Result<(), String> {
    let mut context = Context::new();
    for input in inputs.into_iter() {
        let input = input.refine(&context);
        context.handle(input)?;
    }
    Ok(())
}

/// Checks file.
pub fn check_file(file: &str) -> Result<(), String> {
    let inputs = UserInput::from_file(&file)
        .map_err(|err| format!("{}\nIn file `{}`", err, file))?;
    check(inputs)
        .map_err(|err| format!("{}\nIn file `{}`", err, file))
}
