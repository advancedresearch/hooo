//! # Tactics

use crate::*;

/// Represents tactics.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Tactic {
    /// The silence tactic.
    Silence,
    /// The app tactic.
    App,
    /// The debug tactic.
    Debug,
    /// The eq tactic.
    Eq,
    /// The and tactic.
    And,
    /// The or tactic.
    Or,
    /// The hooo tactic.
    Hooo,
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
    /// The sesh tactic.
    Sesh,
    /// The tauto tactic.
    Tauto,
}

/// Represents a suggestion level.
pub enum Suggestion {
    /// Do simple suggestions only.
    Simple,
    /// Do adanced suggestions only.
    Advanced,
    /// Do rare suggestions only.
    Rare,
    /// Do all kinds of suggestions.
    BrainStorm,
}

impl Suggestion {
    /// Whether suggestion is simple.
    pub fn is_simple(&self) -> bool {
        use Suggestion::*;

        match self {
            Simple | BrainStorm => true,
            Advanced | Rare => false,
        }
    }

    /// Whether suggestion is advanced.
    pub fn is_advanced(&self) -> bool {
        use Suggestion::*;

        match self {
            Advanced | BrainStorm => true,
            Simple | Rare => false,
        }
    }

    /// Whether suggestion is rare.
    pub fn is_rare(&self) -> bool {
        use Suggestion::*;

        match self {
            Rare | BrainStorm => true,
            Simple | Advanced => false,
        }
    }
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
    pub fn suggestions(
        &self,
        sugg: Suggestion,
        facts: &[Expr],
        new_suggestions: &mut Vec<(Expr, String)>,
    ) {
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

        // Do some simple inference.
        if sugg.is_simple() {
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
                Eq => {
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            if abc.0 == Expr::Eq {
                                for g in facts {
                                    if f == g {continue}
                                    if g.has_bind_symbol() {continue}

                                    if let Ok(res) = transform::rewrite(f, g) {
                                        add(res, format!("{}", Eq));
                                    }
                                }
                            }
                        }
                    }

                    for f in facts {
                        if let Some((a, b)) = f.eq() {
                            add(eq(b, a), format!("{}", Eq));
                        }
                    }
                }
                And => {
                    for f in facts {
                        if let Some((a, b)) = f.eq() {
                            if let Some((a1, a2)) = a.and() {
                                let found_a1 = a1.find(facts.iter()).is_some();
                                let found_a2 = a2.find(facts.iter()).is_some();
                                match (found_a1, found_a2) {
                                    (true, true) => add(and(a1, a2), format!("{}", And)),
                                    (false, true) => add(eq(a1, b), format!("{}", And)),
                                    (true, false) => add(eq(a2, b), format!("{}", And)),
                                    (false, false) => {}
                                }
                            }
                        }
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
                        if let Some(_) = f.eq() {
                            add(eq_def(), format!("{}", And));
                        }
                        if let Some((a, b)) = f.imply() {
                            for g in facts {
                                if let Some((b2, a2)) = g.imply() {
                                    if (a == a2) && (b == b2) {
                                        add(eq_def(), format!("{}", And));
                                    }
                                }
                            }
                        }
                    }
                }
                Or => {
                    for f in facts {
                        if let Some((a, _)) = f.eq() {
                            if let Some((a1, a2)) = a.or() {
                                for g in facts {
                                    if (g == &a1) || (g == &a2) {
                                        add(or(a1, a2), format!("{}", Or));
                                        break;
                                    }
                                }
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
                Sym => {
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            match abc.0 {
                                Expr::Eq => add(eq_symmetry(), format!("{}", Sym)),
                                Expr::And => add(and_symmetry(), format!("{}", Sym)),
                                Expr::Or => add(or_symmetry(), format!("{}", Sym)),
                                Expr::Wave => add(wave_symmetry(), format!("{}", Sym)),
                                Expr::Imply => add(imply_symmetry(), format!("{}", Sym)),
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
                        if let Some((a, b)) = f.eq() {
                            let mut a_found = false;
                            let mut b_found = true;
                            for g in facts {
                                if let Some(c) = g.qu() {
                                    a_found |= c == a;
                                    b_found |= c == b;
                                }
                            }
                            if a_found && b_found {
                                add(qual_def(), format!("{}", Qubit));
                            }
                        }
                    }

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

                    for f in facts {
                        if f.qu().is_some() {
                            add(qual_eq_qubit(), format!("{}", Qubit));
                        }
                    }
                }
                Sesh => {
                    for f in facts {
                        if f.qu_not().is_some() {
                            add(sesh_qubit_eq(), format!("{}", Sesh));
                        }
                        if f.not_qu().is_some() {
                            add(sesh_qubit_eq(), format!("{}", Sesh));
                        }
                    }
                }
                Tauto => {
                    for f in facts {
                        if let Some((a, b)) = f.pow() {
                            if b == Expr::Tr {
                                add(tauto_def(), format!("{}", Tauto));
                            }
                            if a == Expr::Fa {
                                add(para_def(), format!("{}", Tauto));
                            }
                        }
                        if let Some((f, _)) = f.app() {
                            match f {
                                Expr::Tauto => {
                                    add(tauto_def(), format!("{}", Tauto));
                                    add(uniform_def(), format!("{}", Tauto));
                                }
                                Expr::Para => {
                                    add(para_def(), format!("{}", Para));
                                    add(uniform_def(), format!("{}", Tauto));
                                }
                                Expr::Uniform => add(uniform_def(), format!("{}", Uniform)),
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        if sugg.is_advanced() {
            match self {
                Zero => {}
                Silence => {}
                Debug => {}
                App => {}
                And => {
                    fn search<F>(f: &Expr, a1: Expr, a2: Expr, facts: &[Expr], add: &mut F)
                        where F: FnMut(Expr, String)
                    {
                        let mut hc1: Vec<transform::Context> = vec![];
                        let mut hc2: Vec<transform::Context> = vec![];
                        for g in facts {
                            let mut hc = transform::Context::new();
                            if hc.bind(&a1, g).is_ok() {
                                hc1.push(hc);
                            }
                            let mut hc = transform::Context::new();
                            if hc.bind(&a2, g).is_ok() {
                                hc2.push(hc);
                            }
                        }
                        for hc1 in &hc1 {
                            for hc2 in &hc2 {
                                if let Ok(hc) = hc1.join(&hc2) {
                                    if let Ok(expr) = hc.synth(f) {
                                        add(expr, format!("{}", And));
                                    }
                                }
                            }
                        }

                        if let Some((a, b)) = a1.and() {
                            search(f, a, b, facts, add);
                        }
                        if let Some((a, b)) = a2.and() {
                            search(f, a, b, facts, add);
                        }
                    }

                    for f in facts {
                        if let Some((a, _)) = f.eq() {
                            if f.has_bind_symbol() {
                                if let Some((a1, a2)) = a.and() {
                                    search(f, a1, a2, facts, &mut add);
                                }
                            }
                        }
                    }
                }
                Or => {
                    for f in facts {
                        if let Some((a, _)) = f.eq() {
                            if f.has_bind_symbol() {
                                if let Some((a1, a2)) = a.or() {
                                    for g in facts {
                                        let mut hc = transform::Context::new();
                                        if hc.bind(&a1, g).is_ok() {
                                            if let Ok(expr) = hc.synth(f) {
                                                add(expr, format!("{}", Or));
                                            }
                                        }
                                        let mut hc = transform::Context::new();
                                        if hc.bind(&a2, g).is_ok() {
                                            if let Ok(expr) = hc.synth(f) {
                                                add(expr, format!("{}", Or));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Hooo => {}
                Eq => {}
                Sym => {}
                Imply => {
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            match abc.0 {
                                Expr::Imply => {
                                    if f.has_bind_symbol() {
                                        for g in facts {
                                            let mut hc = transform::Context::new();
                                            if hc.bind(&abc.1, g).is_ok() {
                                                if let Ok(expr) = hc.synth(f) {
                                                    add(expr, format!("{}", Imply));
                                                }
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                Modus => {}
                Qubit => {}
                Sesh => {}
                Tauto => {}
            }
        }

        if sugg.is_rare() {
            match self {
                Silence => {}
                App => {}
                Debug => {}
                And => {}
                Or => {}
                Hooo => {}
                Sym => {}
                Imply => {}
                Zero => {}
                Modus => {}
                Qubit => {}
                Sesh => {}
                Tauto => {}
                Eq => {
                    // Suggest rewriting rules in branches.
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            if abc.0 == Expr::Eq {
                                add(eq(abc.2.clone(), abc.1.clone()), format!("{}", Eq));

                                for g in facts {
                                    if f == g {continue}
                                    if g.has_bind_symbol() {continue}

                                    if let Ok(res) = transform::rewrite_left(f, g) {
                                        add(res, format!("{}", Eq));
                                    }
                                    if let Ok(res) = transform::rewrite_middle(f, g) {
                                        add(res, format!("{}", Eq));
                                    }
                                    if let Ok(res) = transform::rewrite_right(f, g) {
                                        add(res, format!("{}", Eq));
                                    }
                                }
                            }
                        }
                    }

                    // Suggest rewrite of rules using rules themselves.
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            if abc.0 == Expr::Eq {
                                if let Ok(res) = transform::rewrite(f, f) {
                                    add(res, format!("{}", Eq));
                                }
                                if let Ok(res) = transform::rewrite_left(f, f) {
                                    add(res, format!("{}", Eq));
                                }
                                if let Ok(res) = transform::rewrite_middle(f, f) {
                                    add(res, format!("{}", Eq));
                                }
                                if let Ok(res) = transform::rewrite_right(f, f) {
                                    add(res, format!("{}", Eq));
                                }
                            }
                        }
                    }

                    // Suggest rewriting rules with bind symbols.
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            if abc.0 == Expr::Eq {
                                add(eq(abc.2.clone(), abc.1.clone()), format!("{}", Eq));

                                for g in facts {
                                    if f == g {continue}
                                    if !g.has_bind_symbol() {continue}

                                    if let Ok(res) = transform::rewrite(f, g) {
                                        add(res, format!("{}", Eq));
                                    }
                                    if let Ok(res) = transform::rewrite_left(f, g) {
                                        add(res, format!("{}", Eq));
                                    }
                                    if let Ok(res) = transform::rewrite_middle(f, g) {
                                        add(res, format!("{}", Eq));
                                    }
                                    if let Ok(res) = transform::rewrite_right(f, g) {
                                        add(res, format!("{}", Eq));
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
            Or => write!(w, "or")?,
            Imply => write!(w, "imply")?,
            Modus => write!(w, "modus")?,
            Qubit => write!(w, "qubit")?,
            Sesh => write!(w, "sesh")?,
            Tauto => write!(w, "tauto")?,
        }
        Ok(())
    }
}
