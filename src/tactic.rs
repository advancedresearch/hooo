//! # Tactics

use crate::*;

/// Represents tactics.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
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
    /// The qual tactic.
    Qual,
}

/// The rule of some tactic that generated a suggestion.
#[derive(Clone, Copy, Debug)]
pub enum Rule {
    /// Found a matching expression of type to apply to some function.
    ApplyType,
    /// Found a matching expression of imply (modus ponens).
    ApplyImplication,
    /// Rewrite equality rule using another expression.
    EqualityRewrite,
    /// Swap sides of equality.
    EqualitySymmetry,
    /// Equality rewrite left.
    EqualityRewriteLeft,
    /// Equality rewrite middle.
    EqualityRewriteMiddle,
    /// Equality rewrite right.
    EqualityRewriteRight,
    /// Equality rewrite self.
    EqualityRewriteSelf,
    /// Equality rewrite self left.
    EqualityRewriteSelfLeft,
    /// Equality rewrite self middle.
    EqualityRewriteSelfMiddle,
    /// Equality rewrite self right.
    EqualityRewriteSelfRight,
    /// Equality rewrite rule.
    EqualityRewriteRule,
    /// Equality rewrite rule left.
    EqualityRewriteRuleLeft,
    /// Equality rewrite rule middle.
    EqualityRewriteRuleMiddle,
    /// Equality rewrite rule right.
    EqualityRewriteRuleRight,
    /// And formation.
    AndFormation,
    /// And equality reduction 1.
    AndEqualityReduction1,
    /// And equality reduction 2.
    AndEqualityReduction2,
    /// And implication reduction 1.
    AndImplicationReduction1,
    /// And implication reduction 2.
    AndImplicationReduction2,
    /// And first type.
    AndFirstType,
    /// And second type.
    AndSecondType,
    /// And first.
    AndFirst,
    /// And second.
    AndSecond,
    /// And paradox.
    AndParadox,
    /// And equality definition by equality.
    AndEqualityDefinitionByEquality,
    /// And equality definition by implication.
    AndEqualityDefinitionByImplication,
    /// And recursive rewrite.
    AndRecursiveRewrite,
    /// Or formation.
    OrFormation,
    /// Or rewrite equality 1.
    OrRewriteEquality1,
    /// Or rewrite equality 2.
    OrRewriteEquality2,
    /// Hooo reflexivity.
    HoooReflexivity,
    /// Hooo overloading.
    HoooOverloading,
    /// Hooo dual.
    HoooDual,
    /// Hooo wave equality.
    HoooWaveEquality,
    /// Hooo wave type.
    HoooWaveType,
    /// Hooo wave and or.
    HoooWaveAndOr,
    /// Hooo wave.
    HoooWave,
    /// Symmetry equality.
    SymmetryEquality,
    /// Symmetry and.
    SymmetryAnd,
    /// Symmetry or.
    SymmetryOr,
    /// Symmetry wave.
    SymmetryWave,
    /// Symmetry imply.
    SymmetryImply,
    /// Symmetry quality.
    SymmetryQuality,
    /// Imply modus ponens.
    ImplyModusPonens,
    /// Imply modus ponens reverse.
    ImplyModusPonensReverse,
    /// Imply transitivity.
    ImplyTransitivity,
    /// Imply rewrite.
    ImplyRewrite,
    /// Modus ponens.
    ModusPonens,
    /// Modus tollens.
    ModusTollens,
    /// Qubit quality definition.
    QubitQualityDefinition,
    /// Qubit substitution.
    QubitSubstitution,
    /// Qubit quality equals qubit.
    QubitQualityEqualsQubit,
    /// Sesh qubit quality.
    SeshQubitEquality,
    /// Tauto tautology definition.
    TautoTautologyDefinition,
    /// Tauto paradox definition.
    TautoParadoxDefinition,
    /// Tauto uniform definition.
    TautoUniformDefinition,
    /// Tauto theory definition.
    TautoTheoryDefinition,
    /// Qual left.
    QualLeft,
    /// Qual right.
    QualRight,
    /// Qual transitivity.
    QualTransitivity,
}

impl Rule {
    /// Gets the tactic of the rule.
    pub fn get_tactic(&self) -> Tactic {
        use Rule::*;
        use Tactic::*;

        match self {
            ApplyType |
            ApplyImplication => App,
            EqualityRewrite |
            EqualitySymmetry |
            EqualityRewriteLeft |
            EqualityRewriteMiddle |
            EqualityRewriteRight |
            EqualityRewriteSelf |
            EqualityRewriteSelfLeft |
            EqualityRewriteSelfMiddle |
            EqualityRewriteSelfRight |
            EqualityRewriteRule |
            EqualityRewriteRuleLeft |
            EqualityRewriteRuleMiddle |
            EqualityRewriteRuleRight => Eq,
            AndFormation |
            AndEqualityReduction1 |
            AndEqualityReduction2 |
            AndImplicationReduction1 |
            AndImplicationReduction2 |
            AndFirstType |
            AndSecondType |
            AndFirst |
            AndSecond |
            AndParadox |
            AndEqualityDefinitionByEquality |
            AndEqualityDefinitionByImplication |
            AndRecursiveRewrite => And,
            OrFormation |
            OrRewriteEquality1 |
            OrRewriteEquality2 => Or,
            HoooReflexivity |
            HoooOverloading |
            HoooDual |
            HoooWaveEquality |
            HoooWaveType |
            HoooWaveAndOr |
            HoooWave => Hooo,
            SymmetryEquality |
            SymmetryAnd |
            SymmetryOr |
            SymmetryWave |
            SymmetryImply |
            SymmetryQuality => Sym,
            ImplyModusPonens |
            ImplyModusPonensReverse |
            ImplyTransitivity |
            ImplyRewrite => Imply,
            ModusPonens |
            ModusTollens => Modus,
            QubitQualityDefinition |
            QubitSubstitution |
            QubitQualityEqualsQubit => Qubit,
            SeshQubitEquality => Sesh,
            TautoTautologyDefinition |
            TautoParadoxDefinition |
            TautoUniformDefinition |
            TautoTheoryDefinition => Tauto,
            QualLeft |
            QualRight |
            QualTransitivity => Qual,
        }
    }
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

/// The type of suggestion info.
pub type Info = (Tactic, Rule);

impl Tactic {
    /// Converts from string.
    pub fn from_str(s: &str) -> Option<Self> {
        use Tactic::*;

        match s {
            "silence" => Some(Silence),
            "app" => Some(App),
            "debug" => Some(Debug),
            "eq" => Some(Eq),
            "and" => Some(And),
            "or" => Some(Or),
            "hooo" => Some(Hooo),
            "sym" => Some(Sym),
            "imply" => Some(Imply),
            "zero" => Some(Zero),
            "modus" => Some(Modus),
            "qubit" => Some(Qubit),
            "sesh" => Some(Sesh),
            "tauto" => Some(Tauto),
            "qual" => Some(Qual),
            _ => None,
        }
    }

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
        new_suggestions: &mut Vec<(Expr, Info)>,
    ) {
        use Tactic::*;
        use Rule::*;

        let mut add = |expr: Expr, rule: Rule| {
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
                   new_suggestions.push((expr, (self.clone(), rule)))
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
                                        add(expr, ApplyType);
                                    }
                                }
                            }
                        }
                        if let Some((a, b)) = f.imply() {
                            for g in facts {
                                if g == &a {
                                    add(b.clone(), ApplyImplication);
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
                                        add(res, EqualityRewrite);
                                    }
                                }
                            }
                        }
                    }

                    for f in facts {
                        if let Some((a, b)) = f.eq() {
                            add(eq(b, a), EqualitySymmetry);
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
                                    (true, true) => add(and(a1, a2), AndFormation),
                                    (false, true) => add(eq(a1, b), AndEqualityReduction1),
                                    (true, false) => add(eq(a2, b), AndEqualityReduction2),
                                    (false, false) => {}
                                }
                            }
                        }
                        if let Some((a, b)) = f.imply() {
                            if let Some((a1, a2)) = a.and() {
                                let found_a1 = a1.find(facts.iter()).is_some();
                                let found_a2 = a2.find(facts.iter()).is_some();
                                match (found_a1, found_a2) {
                                    (true, true) => add(and(a1, a2), AndFormation),
                                    (false, true) => add(eq(a1, b), AndImplicationReduction1),
                                    (true, false) => add(eq(a2, b), AndImplicationReduction2),
                                    (false, false) => {}
                                }
                            }
                        }
                        if let Some((f, a_ty, b_ty)) = f.and_ty() {
                            let expr = ty(fst(a_ty.clone(), b_ty.clone(), f.clone()), a_ty.clone());
                            add(expr, AndFirstType);
                            let expr = ty(snd(a_ty.clone(), b_ty.clone(), f), b_ty);
                            add(expr, AndSecondType);
                        }
                        if let Some((a, b)) = f.and() {
                            add(a.clone(), AndFirst);
                            add(b.clone(), AndSecond);
                            if &b == &imply(a.clone(), Expr::Fa) {
                                add(paradox_eq(), AndParadox);
                            }
                        }
                        if let Some(_) = f.eq() {
                            add(eq_def(), AndEqualityDefinitionByEquality);
                        }
                        if let Some((a, b)) = f.imply() {
                            for g in facts {
                                if let Some((b2, a2)) = g.imply() {
                                    if (a == a2) && (b == b2) {
                                        add(eq_def(), AndEqualityDefinitionByImplication);
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
                                        add(or(a1, a2), OrFormation);
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
                                add(refl(), HoooReflexivity);
                            }
                            if let Expr::Bin(_) = base {
                                add(hooo(), HoooOverloading);
                            }
                            if let Expr::Bin(_) = exp {
                                add(hooo_dual(), HoooDual);
                            }
                        }
                        if let Expr::Bin(abc) = f {
                            if let Some(op) = abc.0.dual_op() {
                                match op {
                                    Expr::Eq => add(wave_eq(), HoooWaveEquality),
                                    Expr::Ty => add(wave_ty(), HoooWaveType),
                                    Expr::And => add(wave_and_or(), HoooWaveAndOr),
                                    _ => {}
                                }
                            }
                        }
                        if let Some((_, _)) = f.wave() {
                            add(hooo_wave(), HoooWave);
                        }
                    }
                }
                Sym => {
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            match abc.0 {
                                Expr::Eq => add(eq_symmetry(), SymmetryEquality),
                                Expr::And => add(and_symmetry(), SymmetryAnd),
                                Expr::Or => add(or_symmetry(), SymmetryOr),
                                Expr::Wave => add(wave_symmetry(), SymmetryWave),
                                Expr::Imply => add(imply_symmetry(), SymmetryImply),
                                Expr::Qual => add(qual_symmetry(), SymmetryQuality),
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
                                            add(abc.2.clone(), ImplyModusPonens);
                                        }
                                    }
                                }
                                Expr::Rimply => {
                                    for g in facts {
                                        if g == &abc.2 {
                                            add(abc.1.clone(), ImplyModusPonensReverse);
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }

                    'outer: for f in facts {
                        if let Some((_, b)) = f.imply() {
                            for g in facts {
                                if let Some((b2, _)) = g.imply() {
                                    if b == b2 {
                                        add(imply_transitivity(), ImplyTransitivity);
                                        break 'outer;
                                    }
                                }
                            }
                        }
                    }
                }
                Modus => {
                    add(modus_ponens(), ModusPonens);
                    add(modus_tollens(), ModusTollens);
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
                                add(qual_def(), QubitQualityDefinition);
                            }
                        }
                        if let Some((a, b)) = f.qual() {
                            if a != b {
                                add(qual_def(), QubitQualityDefinition);
                            }
                        }
                    }

                    for f in facts {
                        if let Expr::Un(ab) = f {
                            if ab.0 == Expr::Qubit {
                                for g in facts {
                                    if let Some((a, b)) = g.qubit_eq() {
                                        if a == ab.1 {
                                            add(qu(b), QubitSubstitution);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    for f in facts {
                        if f.qu().is_some() {
                            add(qual_eq_qubit(), QubitQualityEqualsQubit);
                        }
                        if let Some((a, b)) = f.qual() {
                            if a == b {
                                add(qual_eq_qubit(), QubitQualityEqualsQubit);
                            }
                        }
                    }
                }
                Sesh => {
                    for f in facts {
                        if f.qu_not().is_some() {
                            add(sesh_qubit_eq(), SeshQubitEquality);
                        }
                        if f.not_qu().is_some() {
                            add(sesh_qubit_eq(), SeshQubitEquality);
                        }
                    }
                }
                Tauto => {
                    for f in facts {
                        if let Some((a, b)) = f.pow() {
                            if b == Expr::Tr {
                                add(tauto_def(), TautoTautologyDefinition);
                            }
                            if a == Expr::Fa {
                                add(para_def(), TautoParadoxDefinition);
                            }
                        }
                        if let Some((f, _)) = f.app() {
                            match f {
                                Expr::Tauto => {
                                    add(tauto_def(), TautoTautologyDefinition);
                                    add(uniform_def(), TautoUniformDefinition);
                                }
                                Expr::Para => {
                                    add(para_def(), TautoParadoxDefinition);
                                    add(uniform_def(), TautoUniformDefinition);
                                }
                                Expr::Uniform => add(uniform_def(), TautoUniformDefinition),
                                Expr::Theory => add(theory_def(), TautoTheoryDefinition),
                                _ => {}
                            }
                        }
                    }
                }
                Qual => {
                    for f in facts {
                        if let Some((a, b)) = f.qual() {
                            add(qual(a.clone(), a), QualLeft);
                            add(qual(b.clone(), b), QualRight);
                        }
                    }

                    for f in facts {
                        if let Some((_, b)) = f.qual() {
                            for g in facts {
                                if let Some((b2, _)) = g.qual() {
                                    if b == b2 {
                                        add(qual_transitivity(), QualTransitivity);
                                    }
                                }
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
                        where F: FnMut(Expr, Rule)
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
                                        add(expr, AndRecursiveRewrite);
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
                        if let Bin(abc) = f {
                            match abc.0 {
                                Expr::Imply | Expr::Eq => {
                                    if f.has_bind_symbol() {
                                        if let Some((a1, a2)) = abc.1.and() {
                                            search(f, a1, a2, facts, &mut add);
                                        }
                                    }
                                }
                                _ => {}
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
                                                add(expr, OrRewriteEquality1);
                                            }
                                        }
                                        let mut hc = transform::Context::new();
                                        if hc.bind(&a2, g).is_ok() {
                                            if let Ok(expr) = hc.synth(f) {
                                                add(expr, OrRewriteEquality2);
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
                                                    add(expr, ImplyRewrite);
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
                Qual => {}
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
                Qual => {}
                Eq => {
                    // Suggest rewriting rules in branches.
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            if abc.0 == Expr::Eq {
                                for g in facts {
                                    if f == g {continue}
                                    if g.has_bind_symbol() {continue}

                                    if let Ok(res) = transform::rewrite_left(f, g) {
                                        add(res, EqualityRewriteLeft);
                                    }
                                    if let Ok(res) = transform::rewrite_middle(f, g) {
                                        add(res, EqualityRewriteMiddle);
                                    }
                                    if let Ok(res) = transform::rewrite_right(f, g) {
                                        add(res, EqualityRewriteRight);
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
                                    add(res, EqualityRewriteSelf);
                                }
                                if let Ok(res) = transform::rewrite_left(f, f) {
                                    add(res, EqualityRewriteSelfLeft);
                                }
                                if let Ok(res) = transform::rewrite_middle(f, f) {
                                    add(res, EqualityRewriteSelfMiddle);
                                }
                                if let Ok(res) = transform::rewrite_right(f, f) {
                                    add(res, EqualityRewriteSelfRight);
                                }
                            }
                        }
                    }

                    // Suggest rewriting rules with bind symbols.
                    for f in facts {
                        if let Expr::Bin(abc) = f {
                            if abc.0 == Expr::Eq {
                                for g in facts {
                                    if f == g {continue}
                                    if !g.has_bind_symbol() {continue}

                                    if let Ok(res) = transform::rewrite(f, g) {
                                        add(res, EqualityRewriteRule);
                                    }
                                    if let Ok(res) = transform::rewrite_left(f, g) {
                                        add(res, EqualityRewriteRuleLeft);
                                    }
                                    if let Ok(res) = transform::rewrite_middle(f, g) {
                                        add(res, EqualityRewriteRuleMiddle);
                                    }
                                    if let Ok(res) = transform::rewrite_right(f, g) {
                                        add(res, EqualityRewriteRuleRight);
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
            Qual => write!(w, "qual")?,
        }
        Ok(())
    }
}
