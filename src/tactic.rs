//! # Tactics

use crate::*;

/// Represents tactics.
#[derive(PartialEq)]
pub enum Tactic {
    /// The silence tactic.
    Silence,
    /// The app tactic.
    App,
    /// The debug tactic.
    Debug,
    /// The and tactic.
    And,
    /// The hooo tactic.
    Hooo,
    /// The eq tactic.
    Eq,
    /// The sym tactic.
    Sym,
    /// The imply tactic.
    Imply,
    /// The zero tactic.
    Zero,
    /// The modus tactic.
    Modus,
    /// The qubit tactic.
    Qubit,
}

impl Tactic {
    /// Finds tactic in iterator.
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

    /// Provides new suggestions.
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
