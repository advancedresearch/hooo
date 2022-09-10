#![deny(missing_docs)]

//! # hooo
//! Propositional logic with exponentials
//!
//! ```text
//! === HOOO 0.1 ===
//! For more information, type `help`
//! > use silence
//! > use zero
//! > use and
//! > use eq
//! > use hooo
//! > ((a = b) ^ True)
//! (((A □ B) ^ X) = ((A ^ X) □ (B ^ X))) by hooo
//! ((a ^ ⊤) = (b ^ ⊤)) by eq
//! ```
//!
//! To run hooo from you Terminal, type:
//!
//! ```text
//! cargo install --example hooo hooo
//! ```
//!
//! Then, to run:
//!
//! ```text
//! hooo
//! ```
//!
//! ### Motivation
//!
//! The ongoing research on [PSQ](https://advancedresearch.github.io/quality/summary.html#psq---path-semantical-quantum-propositional-logic)
//! suggests that propositional logic can be extended with [Category Theory Exponentials](https://ncatlab.org/nlab/show/exponential+object).
//!
//! The problem is that PSQ contains a qubit operator `~` with the special property
//! that it has congruence by tautological identity only.
//! In current theorem provers, it has not been possible to reason about this.
//!
//! For example, `a == b` does not imply `~a == ~b`,
//! only when `a == b` is provable from none assumptions.
//!
//! The `(a == b)^true` relation is an *exponential* proposition
//! which proves that `a == b` from none assumptions.
//! This gives `a == b` the *tautological identity* needed for substitution in the qubit operator `~`.
//!
//! It turns out that this is semantically the same as [Higher Order Operator Overloading](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#higher-order-operator-overloading).
//!
//! Or simply: hooo

use std::sync::Arc;
use std::fmt;

pub mod parsing;

use Expr::*;

/// Represents a Hooo expression.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    /// Generic `X`.
    X,
    /// Generic `Y`.
    Y,
    /// Generic `A`.
    A,
    /// Generic `B`.
    B,
    /// Generic binary operator `a □ b`.
    Sq,
    /// Generic binary operator `a ◇ b`.
    Di,
    /// `⊤`.
    Tr,
    /// `⊥`.
    Fa,
    /// Type `a : b`.
    Ty,
    /// Imply `a → b`.
    Imply,
    /// Reverse imply `a ← b`.
    Rimply,
    /// Pow `a ^ b`.
    Pow,
    /// And `a ⋀ b`.
    And,
    /// Or `a ⋁ b`.
    Or,
    /// Equality `a = b`.
    Eq,
    /// Wave `a ~◇~ b`.
    Wave,
    /// Qubit `~a`.
    Qubit,
    /// First and component.
    Fst,
    /// Second and component.
    Snd,
    /// Left or constructor.
    Left,
    /// Right or constructor.
    Right,
    /// Swap or equality proof.
    SwapOr,
    /// `[f(x)]`.
    SubTyFst,
    /// `[f x]`.
    SubTySnd,
    /// Apply.
    App,
    /// Hooo equality proof.
    Hooo,
    /// Hooo dual equality proof.
    HoooDual,
    /// Hooo wave equality proof.
    HoooWave,
    /// Swap wave equality proof.
    SwapWave,
    /// Pow-mul equality proof.
    PowMul,
    /// Variable.
    Var(Arc<String>),
    /// Binary operation.
    Bin(Box<(Expr, Expr, Expr)>),
    /// Unary operation.
    Un(Box<(Expr, Expr)>),
}

impl fmt::Display for Expr {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            X => write!(w, "X")?,
            Y => write!(w, "Y")?,
            A => write!(w, "A")?,
            B => write!(w, "B")?,
            Sq => write!(w, "□")?,
            Di => write!(w, "◇")?,
            Tr => write!(w, "⊤")?,
            Fa => write!(w, "⊥")?,
            Ty => write!(w, ":")?,
            Imply => write!(w, "→")?,
            Rimply => write!(w, "←")?,
            Pow => write!(w, "^")?,
            And => write!(w, "⋀")?,
            Or => write!(w, "⋁")?,
            Eq => write!(w, "=")?,
            Wave => write!(w, "~◇~")?,
            Qubit => write!(w, "~")?,
            Fst => write!(w, "fst")?,
            Snd => write!(w, "snd")?,
            Left => write!(w, "left")?,
            Right => write!(w, "right")?,
            SwapOr => write!(w, "swap_or")?,
            SubTyFst => write!(w, "0↞")?,
            SubTySnd => write!(w, "1↞")?,
            App => write!(w, "↞")?,
            Hooo => write!(w, "hooo")?,
            HoooDual => write!(w, "hooo_dual")?,
            HoooWave => write!(w, "hooo_wave")?,
            SwapWave => write!(w, "swap_wave")?,
            PowMul => write!(w, "pow_mul")?,
            Var(x) => write!(w, "{}", x)?,
            Bin(abc) => {
                write!(w, "(")?;
                if abc.1.is_bin() {
                    write!(w, "'{}'", abc.1)?;
                } else {
                    write!(w, "{}", abc.1)?;
                }
                write!(w, " {} ", abc.0)?;
                if abc.2.is_bin() {
                    write!(w, "'{}'", abc.2)?;
                } else {
                    write!(w, "{}", abc.2)?;
                }
                write!(w, ")")?;
            }
            Un(ab) => {
                write!(w, "{}{}", ab.0, ab.1)?;
            }
        }
        Ok(())
    }
}

impl From<&str> for Expr {
    fn from(val: &str) -> Expr {Var(Arc::new(val.into()))}
}

impl Expr {
    /// Get `(A = B) ^ ⊤` info.
    pub fn qubit_eq(&self) -> Option<(Expr, Expr)> {
        if let Some(res) = self.pow() {
            match res {
                (Bin(abc), Tr) if abc.0 == Eq => {
                    return Some((abc.1.clone(), abc.2.clone()));
                }
                _ => {}
            }
        }
        None
    }

    /// Get imply info.
    pub fn imply(&self) -> Option<(Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == Imply {
                return Some((abc.1.clone(), abc.2.clone()))
            }
        }
        None
    }

    /// Get dual info.
    pub fn dual(&self) -> Option<(Expr, Expr, Expr)> {
        if let Bin(abc) = self {
            if let Some(op) = abc.0.dual_op() {
                return Some((op, abc.1.clone(), abc.2.clone()))
            }
        }
        None
    }

    /// Get eq info.
    pub fn eq(&self) -> Option<(Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == Eq {
                return Some((abc.1.clone(), abc.2.clone()))
            }
        }
        None
    }

    /// Get and info.
    pub fn and(&self) -> Option<(Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == And {
                return Some((abc.1.clone(), abc.2.clone()))
            }
        }
        None
    }

    /// Get wave info.
    pub fn wave(&self) -> Option<(Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == Wave {
                return Some((abc.1.clone(), abc.2.clone()))
            }
        }
        None
    }

    /// Get dual operator info.
    pub fn dual_op(&self) -> Option<Expr> {
        if let Some((op, x)) = self.pow() {
            if op == Fa {return Some(x)}
        }
        None
    }

    /// Get pow info.
    pub fn pow(&self) -> Option<(Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == Pow {
                return Some((abc.1.clone(), abc.2.clone()))
            }
        }
        None
    }

    /// Get and info.
    pub fn and_ty(&self) -> Option<(Expr, Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == Ty {
                if let Bin(xyz) = &abc.2 {
                    if xyz.0 == And {
                        return Some((abc.1.clone(), xyz.1.clone(), xyz.2.clone()))
                    }
                }
            }
        }
        None
    }

    /// Get type info.
    pub fn ty(&self) -> Option<(Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == Ty {return Some((abc.1.clone(), abc.2.clone()))}
        }
        None
    }

    /// Find item in iterator that equals itself.
    pub fn find<'a>(&self, facts: impl Iterator<Item = &'a Expr>) -> Option<usize> {
        let mut found: Option<usize> = None;
        for (i, f) in facts.enumerate() {
            if f == self {
                found = Some(i);
                break;
            }
        }
        found
    }

    /// Returns `f : A -> B`.
    pub fn fun_ty(&self) -> Option<(Expr, Expr, Expr)> {
        if let Bin(abc) = self {
            if abc.0 == Ty {
                if let Bin(xyz) = &abc.2 {
                    if xyz.0 == Imply {
                        return Some((abc.1.clone(), xyz.1.clone(), xyz.2.clone()))
                    }
                }
            }
        }
        None
    }

    /// Substitue this rule using pattern with expression.
    pub fn subst(&self, pat: &Expr, e: &Expr) -> Result<Self, ()> {
        substitue(self, pat, e)
    }

    /// Whether the expression is a binary operator.
    pub fn is_bin(&self) -> bool {
        match self {
            Ty |
            Imply |
            Rimply |
            Pow |
            And |
            Or |
            Eq |
            Wave |
            App |
            Sq |
            Di => true,
            _ => false,
        }
    }

    /// Wether the expression is a symbol.
    pub fn is_sym(&self) -> bool {
        match self {
            Tr |
            Fa |
            Ty |
            Imply |
            Rimply |
            Pow |
            And |
            Or |
            Eq |
            Wave |
            Fst |
            Snd |
            Left |
            Right |
            SwapOr |
            SubTyFst |
            SubTySnd |
            App |
            Hooo |
            HoooDual |
            HoooWave |
            SwapWave |
            PowMul => true,
            _ => false,
        }
    }

    /// Whether the expression contains binding symbols.
    pub fn has_bind_symbol(&self) -> bool {
        match self {
            X | Y | A | B | Sq | Di => true,
            Bin(abc) =>
                abc.0.has_bind_symbol() |
                abc.1.has_bind_symbol() |
                abc.2.has_bind_symbol(),
            _ => false,
        }
    }
}

/// Stores a context for binding variables
/// to one side of an equation.
#[derive(Debug)]
pub struct Context {
    x: Option<Expr>,
    y: Option<Expr>,
    a: Option<Expr>,
    b: Option<Expr>,
    sq: Option<Expr>,
    di: Option<Expr>,
}

impl Context {
    /// Creates a new empty binding context.
    pub fn new() -> Context {
        Context {
            x: None,
            y: None,
            a: None,
            b: None,
            sq: None,
            di: None,
        }
    }

    /// Set unknown to some expression.
    pub fn set(&mut self, pat: &Expr, e: &Expr) -> Result<(), ()> {
        let f = |ptr: &mut Option<Expr>| -> Result<(), ()> {
            if let Some(old) = &*ptr {
                if old == e {Ok(())} else {Err(())}
            } else {
                *ptr = Some(e.clone());
                Ok(())
            }
        };

        match pat {
            X => f(&mut self.x),
            Y => f(&mut self.y),
            A => f(&mut self.a),
            B => f(&mut self.b),
            Sq => f(&mut self.sq),
            Di => f(&mut self.di),
            _ => return Err(())
        }
    }

    /// Bind context using pattern to expression.
    pub fn bind(&mut self, pat: &Expr, e: &Expr) -> Result<(), ()> {
        match (pat, e) {
            (X | Y | A | B | Sq | Di, _) => self.set(pat, e),
            (x, y) if x.is_sym() && y.is_sym() && (x == y) => Ok(()),
            (Bin(abc), Bin(xyz)) => {
                self.bind(&abc.0, &xyz.0)?;
                self.bind(&abc.1, &xyz.1)?;
                self.bind(&abc.2, &xyz.2)
            }
            (Var(x), Var(y)) if x == y => Ok(()),
            _ => Err(())
        }
    }

    /// Bind equality in left expression.
    pub fn bind_eq_left(&mut self, pat: &Expr, e: &Expr) -> Result<(), ()> {
        match pat {
            Bin(abc) if abc.0 == Eq => self.bind(&abc.1, e),
            _ => Err(())
        }
    }

    /// Bind equality in right expression.
    pub fn bind_eq_right(&mut self, pat: &Expr, e: &Expr) -> Result<(), ()> {
        match pat {
            Bin(abc) if abc.0 == Eq => self.bind(&abc.2, e),
            _ => Err(())
        }
    }

    /// Bind in left argument.
    pub fn bind_left(&mut self, pat: &Expr, e: &Expr) -> Result<(), ()> {
        match pat {
            Bin(abc) => self.bind(&abc.1, e),
            _ => Err(())
        }
    }

    /// Bind in right argument.
    pub fn bind_right(&mut self, pat: &Expr, e: &Expr) -> Result<(), ()> {
        match pat {
            Bin(abc) => self.bind(&abc.2, e),
            _ => Err(())
        }
    }

    /// Synthesize using pattern into an expression.
    pub fn synth(&self, pat: &Expr) -> Result<Expr, ()> {
        match pat {
            X => if let Some(x) = &self.x {Ok(x.clone())} else {Ok(X)},
            Y => if let Some(x) = &self.y {Ok(x.clone())} else {Ok(Y)},
            A => if let Some(x) = &self.a {Ok(x.clone())} else {Ok(A)},
            B => if let Some(x) = &self.b {Ok(x.clone())} else {Ok(B)},
            Sq => if let Some(x) = &self.sq {Ok(x.clone())} else {Ok(Sq)},
            Di => if let Some(x) = &self.di {Ok(x.clone())} else {Ok(Di)},
            x if x.is_sym() => Ok(pat.clone()),
            Var(_) => Ok(pat.clone()),
            Bin(abc) => {
                let a = self.synth(&abc.0)?;
                let b = self.synth(&abc.1)?;
                let c = self.synth(&abc.2)?;
                Ok(Bin(Box::new((a, b, c))))
            }
            _ => Err(())
        }
    }

    /// Synthesize in left argument.
    pub fn synth_eq_left(&mut self, pat: &Expr) -> Result<Expr, ()> {
        match pat {
            Bin(abc) if abc.0 == Eq => self.synth(&abc.1),
            _ => Err(())
        }
    }

    /// Synthesize in right argument.
    pub fn synth_eq_right(&mut self, pat: &Expr) -> Result<Expr, ()> {
        match pat {
            Bin(abc) if abc.0 == Eq => self.synth(&abc.2),
            _ => Err(())
        }
    }
}

/// Substitute pattern in rule with expression.
pub fn substitue(rule: &Expr, pat: &Expr, e: &Expr) -> Result<Expr, ()> {
    let mut c = Context::new();
    c.set(pat, e)?;
    c.synth(rule)
}

/// Rewrite expression using rule.
pub fn rewrite(rule: &Expr, e: &Expr) -> Result<Expr, ()> {
    let mut c = Context::new();
    if c.bind_eq_left(rule, e).is_ok() {
        c.synth_eq_right(rule)
    } else {
        Err(())
    }
}

/// Perform transformation in left argument.
pub fn in_left<F>(e: &Expr, f: F) -> Result<Expr, ()>
    where F: Fn(&Expr) -> Result<Expr, ()>
{
    match e {
        Bin(abc) => Ok(Bin(Box::new((
            abc.0.clone(),
            f(&abc.1)?,
            abc.2.clone()
        )))),
        _ => Err(())
    }
}

/// Perform transformation in middle argument.
pub fn in_middle<F>(e: &Expr, f: F) -> Result<Expr, ()>
    where F: Fn(&Expr) -> Result<Expr, ()>
{
    match e {
        Bin(abc) => Ok(Bin(Box::new((
            f(&abc.0)?,
            abc.1.clone(),
            abc.2.clone()
        )))),
        _ => Err(())
    }
}

/// Perform transformation in right argument.
pub fn in_right<F>(e: &Expr, f: F) -> Result<Expr, ()>
    where F: Fn(&Expr) -> Result<Expr, ()>
{
    match e {
        Bin(abc) => Ok(Bin(Box::new((
            abc.0.clone(),
            abc.1.clone(),
            f(&abc.2)?
        )))),
        _ => Err(())
    }
}

/// Rewrite left argument.
pub fn rewrite_left(rule: &Expr, e: &Expr) -> Result<Expr, ()> {
    in_left(e, |e| rewrite(rule, e))
}

/// Rewrites middle argument.
pub fn rewrite_middle(rule: &Expr, e: &Expr) -> Result<Expr, ()> {
    in_middle(e, |e| rewrite(rule, e))
}

/// Rewrites right argument.
pub fn rewrite_right(rule: &Expr, e: &Expr) -> Result<Expr, ()> {
    in_right(e, |e| rewrite(rule, e))
}

/// `a : b`.
pub fn ty(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Ty, a, b)))
}

/// `[f(x)]`.
pub fn sub_ty_fst(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((SubTyFst, a, b)))
}

/// `[f x]`.
pub fn sub_ty_snd(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((SubTySnd, a, b)))
}

/// `a ↞ b`.
pub fn app(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((App, a, b)))
}

/// `(((fst ↞ a_ty) ↞ b_ty) ↞ a)`.
pub fn fst(a_ty: Expr, b_ty: Expr, a: Expr) -> Expr {
    app(app(app(Fst, a_ty), b_ty), a)
}

///  `(((snd ↞ a_ty) ↞ b_ty) ↞ a)`.
pub fn snd(a_ty: Expr, b_ty: Expr, a: Expr) -> Expr {
    app(app(app(Snd, a_ty), b_ty), a)
}

/// `((left ↞ a_ty) ↞ b_ty) ↞ a`.
pub fn left(a_ty: Expr, b_ty: Expr, a: Expr) -> Expr {
    app(app(app(Left, a_ty), b_ty), a)
}

/// `((right ↞ a_ty) ↞ b_ty) ↞ b`.
pub fn right(a_ty: Expr, b_ty: Expr, b: Expr) -> Expr {
    app(app(app(Right, a_ty), b_ty), b)
}

/// `(swap_or ↞ a_ty) ↞ b_ty`.
pub fn swap_or(a_ty: Expr, b_ty: Expr) -> Expr {
    app(app(SwapOr, a_ty), b_ty)
}

/// `a ^ b`.
pub fn pow(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Pow, a, b)))
}

/// `a = b`.
pub fn eq(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Eq, a, b)))
}

/// `a → b`.
pub fn imply(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Imply, a, b)))
}

/// `a → ⊥`.
pub fn not(a: Expr) -> Expr {
    imply(a, Fa)
}

/// `~a`.
pub fn qu(a: Expr) -> Expr {
    Un(Box::new((Qubit, a)))
}

/// `a ⋀ b`.
pub fn and(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((And, a, b)))
}

/// `a ⋁ b`.
pub fn or(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Or, a, b)))
}

/// `a □ b`.
pub fn sq(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Sq, a, b)))
}

/// `a ◇ b`.
pub fn di(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Di, a, b)))
}

/// `a ⊥^'op' b`.
pub fn dual(op: Expr, a: Expr, b: Expr) -> Expr {
    Bin(Box::new((pow(Fa, op), a, b)))
}

/// `a ~ b`.
///
/// This describes the duality between two operators.
pub fn wave(a: Expr, b: Expr) -> Expr {
    Bin(Box::new((Wave, a, b)))
}

/// `X^X = ⊤`.
pub fn refl() -> Expr {
    eq(pow(X, X), Tr)
}

/// `(A : (X ^ X)) = (⊤ : ⊤)`.
pub fn refl_red() -> Expr {
    eq(ty(A, pow(X, X)), ty(Tr, Tr))
}

/// `X^⊥ = ⊤`.
pub fn absurd() -> Expr {
    eq(pow(X, Fa), Tr)
}

/// `(A : (X ^ ⊥)) = (⊤ : ⊤)`.
pub fn absurd_red() -> Expr {
    eq(ty(A, pow(X, Fa)), ty(Tr, Tr))
}

/// `⊤^X = ⊤`
pub fn htrue() -> Expr {
    eq(pow(Tr, X), Tr)
}

/// `(A : (⊤ ^ X)) = (⊤ : ⊤)`.
pub fn htrue_red() -> Expr {
    eq(ty(A, pow(Tr, X)), ty(Tr, Tr))
}

/// `(A □ B)^X = (A^X □ B^X)`.
pub fn hooo() -> Expr {
    eq(pow(sq(A, B), X), sq(pow(A, X), pow(B, X)))
}

/// `(Y : ((A □ B) ^ X)) = (((((fst ↞ ((A □ B) ^ X)) ↞ ((A ^ X) □ (B ^ X))) ↞ hooo) ↞ Y) : ((A ^ X) □ (B ^ X)))`.
pub fn hooo_red() -> Expr {
    let a = pow(sq(A, B), X);
    let b = sq(pow(A, X), pow(B, X));
    eq(
        ty(Y, pow(sq(A, B), X)),
        ty(app(fst(a, b, Hooo), Y), sq(pow(A, X), pow(B, X)))
    )
}

/// `hooo : (A □ B)^X = (A^X □ B^X)`.
pub fn hooo_def() -> Expr {
    ty(Hooo, hooo())
}

/// `X^(A □ B) = (X^A ⊥^'□' X^B)`.
pub fn hooo_dual() -> Expr {
    eq(pow(X, sq(A, B)), dual(Sq, pow(X, A), pow(X, B)))
}

/// `(Y : (X ^ (A □ B))) = (((((fst ↞ (X ^ (A □ B))) ↞ ((X ^ A) (⊥ ^ □) (X ^ B))) ↞ hooo_dual) ↞ Y) : ((X ^ A) (⊥ ^ □) (X ^ B)))`.
pub fn hooo_dual_red() -> Expr {
    let a = pow(X, sq(A, B));
    let b = dual(Sq, pow(X, A), pow(X, B));
    eq(
        ty(Y, a.clone()),
        ty(app(fst(a, b.clone(), HoooDual), Y), b)
    )
}

/// `(□ ~ ◇) = (((⊥ ^ □) = ◇) ⋀ ((⊥ ^ ◇) = □))`.
pub fn hooo_wave() -> Expr {
    eq(wave(Sq, Di), and(eq(pow(Fa, Sq), Di), eq(pow(Fa, Di), Sq)))
}

/// `(Y : (□ ~ ◇)) = (((((fst ↞ (□ ~ ◇)) ↞ (((⊥ ^ □) = ◇) ⋀ ((⊥ ^ ◇) = □))) ↞ hooo_wave) ↞ Y) : (((⊥ ^ □) = ◇) ⋀ ((⊥ ^ ◇) = □)))`.
pub fn hooo_wave_red() -> Expr {
    let a = wave(Sq, Di);
    let b = and(eq(pow(Fa, Sq), Di), eq(pow(Fa, Di), Sq));
    eq(
        ty(Y, a.clone()),
        ty(app(fst(a, b.clone(), HoooWave), Y), b)
    )
}

/// `(A ~ B) = (B ~ A)`.
pub fn wave_symmetry() -> Expr {
    eq(wave(A, B), wave(B, A))
}

/// `(Y : (A ~ B)) = (((((fst ↞ (A ~ B)) ↞ (B ~ A)) ↞ swap_wave) ↞ Y) : (B ~ A))`.
pub fn wave_red_symmetry() -> Expr {
    let a = wave(A, B);
    let b = wave(B, A);
    eq(
        ty(Y, a.clone()),
        ty(app(fst(a, b.clone(), SwapWave), Y), b)
    )
}

/// `'⋀' ~ '⋁'`.
pub fn wave_and_or() -> Expr {wave(And, Or)}

/// `'→' ~ '←'`.
pub fn wave_imply_rimply() -> Expr {wave(Imply, Rimply)}

/// `':' ~ ':'`.
pub fn wave_ty() -> Expr {wave(Ty, Ty)}

/// `'=' ~ '='`.
pub fn wave_eq() -> Expr {wave(Eq, Eq)}

/// `(A ⋀ (A → ⊥)) = ⊥`.
pub fn paradox_eq() -> Expr {
    eq(and(A, imply(A, Fa)), Fa)
}

/// `(A ⋀ (B → A)) → B`.
pub fn modus_ponens() -> Expr {
    imply(and(A, imply(A, B)), B)
}

/// `((A → B) → ((B → ⊥) → (A → ⊥)))`.
pub fn modus_tollens() -> Expr {
    imply(imply(A, B), imply(not(B), not(A)))
}

/// `(A = B) = ((A → B) ⋀ (B → A))`.
pub fn eq_def() -> Expr {
    eq(eq(A, B), and(imply(A, B), imply(B, A)))
}

/// `(X : (A = B)) = (X : ((A → B) ⋀ (B → A)))`.
pub fn eq_red_def() -> Expr {
    let a = eq(A, B);
    let b = and(imply(A, B), imply(B, A));
    eq(ty(X, a), ty(X, b))
}

/// `((A ^ X) ^ Y) = (A ^ (X ⋀ Y))`.
pub fn exp_def() -> Expr {
    eq(pow(pow(A, X), Y), pow(A, and(X, Y)))
}

/// `(B : ((A ^ X) ^ Y)) = (((((fst ↞ ((A ^ X) ^ Y)) ↞ (A ^ (X ⋀ Y))) ↞ pow_mul) ↞ B) : (A ^ (X ⋀ Y)))`.
pub fn exp_red_def() -> Expr {
    let a = pow(pow(A, X), Y);
    let b = pow(A, and(X, Y));
    eq(ty(B, a.clone()), ty(app(fst(a, b.clone(), PowMul), B), b))
}

/// `fst : ((A ⋀ B) → A)`.
pub fn fst_ty() -> Expr {
    ty(Fst, imply(and(A, B), A))
}

/// `snd : ((A ⋀ B) → B)`.
pub fn snd_ty() -> Expr {
    ty(Snd, imply(and(A, B), B))
}

/// `((f ↞ x) ⋀ ((f : (A → B)) ⋀ (x : A))) = ((f ↞ x) : B)`.
pub fn app_ty(f: Expr, x: Expr) -> Expr {
    eq(
        and(app(f.clone(), x.clone()),
            and(ty(f.clone(), imply(A, B)),
                ty(x.clone(), A))), ty(app(f, x), B))
}

/// `(A ⋀ B) = (B ⋀ A)`
pub fn and_symmetry() -> Expr {
    eq(and(A, B), and(B, A))
}

/// `(X : (A ⋀ B)) = (((((fst ↞ A) ↞ B) ↞ X) ⋀ (((snd ↞ A) ↞ B) ↞ X)) : (B ⋀ A))`.
pub fn and_red_symmetry() -> Expr {
    eq(ty(X, and(A, B)), ty(and(fst(A, B, X), snd(A, B, X)), and(B, A)))
}

/// `(A ⋁ B) = (B ⋁ A)`.
pub fn or_symmetry() -> Expr {
    eq(or(A, B), or(B, A))
}

/// `(X : (A ⋁ B)) = (((swap_or ↞ A) ↞ B) : (B ⋁ A))`.
pub fn or_red_symmetry() -> Expr {
    eq(ty(X, or(A, B)), ty(swap_or(A, B), or(B, A)))
}

/// `(A = B) = (B = A)`.
pub fn eq_symmetry() -> Expr {
    eq(eq(A, B), eq(B, A))
}

/// `(X : (A = B)) = (((((fst ↞ A) ↞ B) ↞ X) ⋀ (((snd ↞ A) ↞ B) ↞ X)) : (B = A))`.
pub fn eq_red_symmetry() -> Expr {
    eq(ty(X, eq(A, B)), ty(and(fst(A, B, X), snd(A, B, X)), eq(B, A)))
}

/// `(⊤ ⋀ X) = X`.
pub fn and_left_tr() -> Expr {
    eq(and(Tr, X), X)
}

/// `(X ⋀ ⊤) = X`.
pub fn and_right_tr() -> Expr {
    eq(and(X, Tr), X)
}

/// `(⊥ ⋀ X) = ⊥`.
pub fn and_left_fa() -> Expr {
    eq(and(Fa, X), Fa)
}

/// `(X ⋀ ⊥) = ⊥`.
pub fn and_right_fa() -> Expr {
    eq(and(X, Fa), Fa)
}

/// `(⊤ ⋁ X) = ⊤`.
pub fn or_left_tr() -> Expr {
    eq(or(Tr, X), Tr)
}

/// `(X ⋁ ⊤) = ⊤`.
pub fn or_right_tr() -> Expr {
    eq(or(X, Tr), Tr)
}

/// `(⊥ ⋁ X) = X`.
pub fn or_left_fa() -> Expr {
    eq(or(Fa, X), X)
}

/// `(X ⋁ ⊥) = X`.
pub fn or_right_fa() -> Expr {
    eq(or(X, Fa), X)
}

/// `(A : (⊤ ⋀ X)) = ((((snd ↞ ⊤) ↞ X) ↞ A) : X)`.
pub fn and_red_left_tr() -> Expr {
    eq(ty(A, and(Tr, X)), ty(snd(Tr, X, A), X))
}

/// `(A : (X ⋀ ⊤)) = ((((fst ↞ X) ↞ ⊤) ↞ A) : X)`.
pub fn and_red_right_tr() -> Expr {
    eq(ty(A, and(X, Tr)), ty(fst(X, Tr, A), X))
}

/// `(A : (⊥ ⋀ X)) = ((((fst ↞ ⊥) ↞ X) ↞ A) : ⊥)`.
pub fn and_red_left_fa() -> Expr {
    eq(ty(A, and(Fa, X)), ty(fst(Fa, X, A), Fa))
}

/// `(A : (X ⋀ ⊥)) = ((((snd ↞ X) ↞ ⊥) ↞ A) : ⊥)`.
pub fn and_red_right_fa() -> Expr {
    eq(ty(A, and(X, Fa)), ty(snd(X, Fa, A), Fa))
}

/// `(A : (⊤ ⋁ X)) = (⊤ : ⊤)`.
pub fn or_red_left_tr() -> Expr {
    eq(ty(A, or(Tr, X)), ty(Tr, Tr))
}

/// `(A : (X ⋁ ⊤)) = (⊤ : ⊤)`.
pub fn or_red_right_tr() -> Expr {
    eq(ty(A, or(X, Tr)), ty(Tr, Tr))
}

/// `((((right ↞ ⊥) ↞ X) ↞ A) : (⊥ ⋁ X)) = (A : X)`.
pub fn or_red_left_fa() -> Expr {
    eq(ty(right(Fa, X, A), or(Fa, X)), ty(A, X))
}

/// `((((left ↞ X) ↞ ⊥) ↞ A) : (X ⋁ ⊥)) = (A : X)`.
pub fn or_red_right_fa() -> Expr {
    eq(ty(left(X, Fa, A), or(X, Fa)), ty(A, X))
}

/// `(X → ⊤) = ⊤`.
pub fn imply_right_tr() -> Expr {
    eq(imply(X, Tr), Tr)
}

/// `(A : (X → ⊤)) = (⊤ : ⊤)`.
pub fn imply_red_right_tr() -> Expr {
    eq(ty(A, imply(X, Tr)), ty(Tr, Tr))
}

/// `(⊥ → X) = ⊤`.
pub fn imply_left_fa() -> Expr {
    eq(imply(Fa, X), Tr)
}

/// `(A : (⊥ → X)) = (⊤ : ⊤)`.
pub fn imply_red_left_fa() -> Expr {
    eq(ty(A, imply(Fa, X)), ty(Tr, Tr))
}

/// `((A : x) ⋀ (B : y)) = ((A ⋀ B) : (x ⋀ y))`.
pub fn and_intro(ty_a: Expr, ty_b: Expr) -> Expr {
    eq(and(ty(A, ty_a.clone()), ty(B, ty_b.clone())), ty(and(A, B), and(ty_a, ty_b)))
}

/// `((A : x) ⋁ (B : y)) = ((((left ↞ x) ↞ y) ↞ A) : (x ⋁ y))`.
pub fn or_intro_left(ty_a: Expr, ty_b: Expr) -> Expr {
    eq(or(ty(A, ty_a.clone()), ty(B, ty_b.clone())),
       ty(left(ty_a.clone(), ty_b.clone(), A), or(ty_a, ty_b)))
}

/// `((A : x) ⋁ (B : y)) = ((((right ↞ x) ↞ y) ↞ B) : (x ⋁ y))`.
pub fn or_intro_right(ty_a: Expr, ty_b: Expr) -> Expr {
    eq(or(ty(A, ty_a.clone()), ty(B, ty_b.clone())),
       ty(right(ty_a.clone(), ty_b.clone(), B), or(ty_a, ty_b)))
}

/// `((A = B) ^ ⊤) = ((A ^ ⊤) = (B ^ ⊤))`.
pub fn hooo_tauto_eq() -> Expr {
    hooo().subst(&Sq, &Eq).unwrap().subst(&X, &Tr).unwrap()
}

/// Checks that type level equality matches equality with proofs.
pub fn check_eq(eq_ab: &Expr, proof_eq_ab: &Expr) -> bool {
    match (eq_ab, proof_eq_ab) {
        (Bin(abc), Bin(xyz)) if (abc.0 == Eq) && (xyz.0 == Eq) => {
            match (&xyz.1, &xyz.2) {
                (Bin(ty_a), Bin(ty_b)) if (ty_a.0 == Ty) && (ty_b.0 == Ty) => {
                    (abc.1 == ty_a.2) && (abc.2 == ty_b.2)
                }
                _ => false
            }
        }
        _ => false,
    }
}

/*
/// `(A ^ (: 0↞ B)) = (B : A)`
pub fn pow_sub_ty() -> Expr {
    eq(pow(A, sub_ty_fst(Ty, B)), ty(B, A))
}

// `(X : (A □ B)) = ((X : A) □ (X : B))`.
pub fn ty_hooo() -> Expr {
    // `((A □ B) ^ X) = ((A ^ X) □ (B ^ X))`.
    let e = hooo();
    // `((A □ B) ^ (: 0↞ X)) = ((A ^ (: 0↞ X)) □ (B ^ (: 0↞ X)))`.
    let e = e.subst(&X, &sub_ty_fst(Ty, X)).unwrap();
    // `(X : (A □ B)) = ((A ^ (: 0↞ X)) □ (B ^ (: 0↞ X)))`.
    let e = rewrite_left(&pow_sub_ty(), &e).unwrap();
    // `(X : (A □ B)) = ((X : A) □ (B ^ (: 0↞ X)))`.
    let e = in_right(&e, |e| rewrite_left(&pow_sub_ty(), &e)).unwrap();
    // `(X : (A □ B)) = ((X : A) □ (X : B))`.
    let e = in_right(&e, |e| rewrite_right(&pow_sub_ty(), &e)).unwrap();
    e
}
*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_refl() {
        assert_eq!(
            rewrite(&refl(), &pow(Tr, Tr)),
            Ok(Tr)
        );
    }

    // `(a ⋀ b → a)^⊤ = ((a ⋀ b)^⊤ → a^⊤`.
    #[test]
    fn test_fst() {
        let e = pow(imply(and("a".into(), "b".into()), "a".into()), Tr);
        let e = rewrite(&hooo(), &e).unwrap();
        assert!(!e.has_bind_symbol());
        assert_eq!(e, imply(pow(and("a".into(), "b".into()), Tr), pow("a".into(), Tr)));
    }

    #[test]
    fn test_rewrite() {
        let ty_x_a = ty("x".into(), "a".into());
        let eq_ab = eq("a".into(), "b".into());
        let e = rewrite_right(&eq_ab, &ty_x_a).unwrap();
        assert_eq!(format!("{}", e), "(x : b)".to_string());
    }

    #[test]
    fn test_proofs() {
        assert!(check_eq(&and_symmetry(), &and_red_symmetry()));
        assert!(check_eq(&or_symmetry(), &or_red_symmetry()));
        assert!(check_eq(&eq_symmetry(), &eq_red_symmetry()));
        assert!(check_eq(&wave_symmetry(), &wave_red_symmetry()));
        assert!(check_eq(&and_left_tr(), &and_red_left_tr()));
        assert!(check_eq(&and_right_tr(), &and_red_right_tr()));
        assert!(check_eq(&and_left_fa(), &and_red_left_fa()));
        assert!(check_eq(&and_right_fa(), &and_red_right_fa()));
        assert!(check_eq(&or_left_tr(), &or_red_left_tr()));
        assert!(check_eq(&or_right_tr(), &or_red_right_tr()));
        assert!(check_eq(&or_left_fa(), &or_red_left_fa()));
        assert!(check_eq(&or_right_fa(), &or_red_right_fa()));
        assert!(check_eq(&imply_right_tr(), &imply_red_right_tr()));
        assert!(check_eq(&imply_left_fa(), &imply_red_left_fa()));
        assert!(check_eq(&hooo(), &hooo_red()));
        assert!(check_eq(&hooo_dual(), &hooo_dual_red()));
        assert!(check_eq(&hooo_wave(), &hooo_wave_red()));
        assert!(check_eq(&htrue(), &htrue_red()));
        assert!(check_eq(&absurd(), &absurd_red()));
        assert!(check_eq(&refl(), &refl_red()));
        assert!(check_eq(&eq_def(), &eq_red_def()));
        assert!(check_eq(&exp_def(), &exp_red_def()));
    }

    #[test]
    fn test() {
        println!("{}", exp_red_def());
        // assert!(false);
    }
}
