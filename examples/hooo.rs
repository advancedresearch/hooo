use std::fmt;

use hooo::*;

#[derive(PartialEq)]
pub enum Tactic {
    Silence,
    App,
    Debug,
    And,
    Hooo,
    Eq,
    Sym,
    Imply,
    Zero,
    Modus,
    Qubit,
}

impl Tactic {
    pub fn find<'a>(&self, tactics: impl Iterator<Item = &'a Tactic>) -> Option<usize> {
        let mut found: Option<usize> = None;
        for (i, t) in tactics.enumerate() {
            if t == self {
                found = Some(i);
                break;
            }
        }
        found
    }

    pub fn suggestions(&self, facts: &[Expr], new_suggestions: &mut Vec<(Expr, String)>) {
        use Tactic::*;

        let mut add = |expr: Expr, comment: String| {
            if expr.find(facts.iter()).is_none() &&
               expr.find(new_suggestions.iter().map(|&(ref e, _)| e)).is_none() {
                   // Detect refl.
                   if let Some((a, b)) = expr.eq() {
                       if a == b {return}
                   }
                   // Detect dual refl.
                   if let Some((op, a, b)) = expr.dual() {
                       if (op == Expr::Eq) && (a == b) {return}
                   }
                   if expr == Expr::Tr {return}
                   new_suggestions.push((expr, comment))
               }
        };

        match self {
            Zero => {}
            Silence => {}
            Debug => {}
            App => {
                for f in facts {
                    if let Some((f, a_ty, b_ty)) = f.fun_ty() {
                        for g in facts {
                            if let Some((x, c_ty)) = g.ty() {
                                if a_ty == c_ty {
                                    let expr = ty(app(f.clone(), x), b_ty.clone());
                                    add(expr, format!("{}", App));
                                }
                            }
                        }
                    }
                    if let Some((a, b)) = f.imply() {
                        for g in facts {
                            if g == &a {
                                add(b.clone(), format!("{}", App));
                                break;
                            }
                        }
                    }
                }
            }
            And => {
                for f in facts {
                    if let Some((f, a_ty, b_ty)) = f.and_ty() {
                        let expr = ty(fst(a_ty.clone(), b_ty.clone(), f.clone()), a_ty.clone());
                        add(expr, format!("{}", And));
                        let expr = ty(snd(a_ty.clone(), b_ty.clone(), f), b_ty);
                        add(expr, format!("{}", And));
                    }
                    if let Some((a, b)) = f.and() {
                        add(a.clone(), format!("{}", And));
                        add(b.clone(), format!("{}", And));
                        if &b == &imply(a.clone(), Expr::Fa) {
                            add(paradox_eq(), format!("{}", And));
                        }
                    }
                }
            }
            Hooo => {
                for f in facts {
                    if let Some((base, exp)) = f.pow() {
                        if base == exp {
                            add(refl(), format!("{}", Hooo));
                        }
                        if let Expr::Bin(_) = base {
                            add(hooo(), format!("{}", Hooo));
                        }
                        if let Expr::Bin(_) = exp {
                            add(hooo_dual(), format!("{}", Hooo));
                        }
                    }
                    if let Expr::Bin(abc) = f {
                        if let Some(op) = abc.0.dual_op() {
                            match op {
                                Expr::Eq => add(wave_eq(), format!("{}", Hooo)),
                                Expr::Ty => add(wave_ty(), format!("{}", Hooo)),
                                Expr::And => add(wave_and_or(), format!("{}", Hooo)),
                                _ => {}
                            }
                        }
                    }
                    if let Some((_, _)) = f.wave() {
                        add(hooo_wave(), format!("{}", Hooo));
                    }
                }
            }
            Eq => {
                for f in facts {
                    if let Expr::Bin(abc) = f {
                        if abc.0 == Expr::Eq {
                            add(eq(abc.2.clone(), abc.1.clone()), format!("{}", Eq));

                            for g in facts {
                                if let Ok(res) = rewrite(f, g) {
                                    add(res, format!("{}", Eq));
                                }
                                if let Ok(res) = rewrite_left(f, g) {
                                    add(res, format!("{}", Eq));
                                }
                                if let Ok(res) = rewrite_middle(f, g) {
                                    add(res, format!("{}", Eq));
                                }
                                if let Ok(res) = rewrite_right(f, g) {
                                    add(res, format!("{}", Eq));
                                }
                            }
                        }
                    }
                }
            }
            Sym => {
                for f in facts {
                    if let Expr::Bin(abc) = f {
                        match abc.0 {
                            Expr::Eq => add(eq_symmetry(), format!("{}", Sym)),
                            Expr::And => add(and_symmetry(), format!("{}", Sym)),
                            Expr::Or => add(or_symmetry(), format!("{}", Sym)),
                            Expr::Wave => add(wave_symmetry(), format!("{}", Sym)),
                            _ => {}
                        }
                    }
                }
            }
            Imply => {
                for f in facts {
                    if let Expr::Bin(abc) = f {
                        match abc.0 {
                            Expr::Imply => {
                                for g in facts {
                                    if g == &abc.1 {
                                        add(abc.2.clone(), format!("{}", Imply));
                                    }
                                }
                            }
                            Expr::Rimply => {
                                for g in facts {
                                    if g == &abc.2 {
                                        add(abc.1.clone(), format!("{}", Imply));
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            Modus => {
                add(modus_ponens(), format!("{}", Modus));
                add(modus_tollens(), format!("{}", Modus));
            }
            Qubit => {
                for f in facts {
                    if let Expr::Un(ab) = f {
                        if ab.0 == Expr::Qubit {
                            for g in facts {
                                if let Some((a, b)) = g.qubit_eq() {
                                    if a == ab.1 {
                                        add(qu(b), format!("{}", Qubit));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

impl fmt::Display for Tactic {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        use Tactic::*;

        match self {
            Zero => write!(w, "zero")?,
            Silence => write!(w, "silence")?,
            Eq => write!(w, "eq")?,
            Sym => write!(w, "sym")?,
            Hooo => write!(w, "hooo")?,
            Debug => write!(w, "debug")?,
            App => write!(w, "app")?,
            And => write!(w, "and")?,
            Imply => write!(w, "imply")?,
            Modus => write!(w, "modus")?,
            Qubit => write!(w, "qubit")?,
        }
        Ok(())
    }
}

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
