//! # Transform

use crate::*;

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

    /// Joins two contexts into a single one.
    pub fn join(&self, other: &Context) -> Result<Context, ()> {
        let f = |a: &Option<Expr>, b: &Option<Expr>| -> Result<Option<Expr>, ()> {
            match (a, b) {
                (Some(x), Some(y)) if x == y => Ok(Some(x.clone())),
                (Some(x), None) | (None, Some(x)) => Ok(Some(x.clone())),
                (None, None) => Ok(None),
                _ => Err(())
            }
        };

        Ok(Context {
            x: f(&self.x, &other.x)?,
            y: f(&self.y, &other.y)?,
            a: f(&self.a, &other.a)?,
            b: f(&self.b, &other.b)?,
            sq: f(&self.sq, &other.sq)?,
            di: f(&self.di, &other.di)?,
        })
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
            (Un(ab), Un(xy)) => {
                self.bind(&ab.0, &xy.0)?;
                self.bind(&ab.1, &xy.1)
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
            Un(ab) => {
                let a = self.synth(&ab.0)?;
                let b = self.synth(&ab.1)?;
                Ok(Un(Box::new((a, b))))
            }
            Subst(abc) => {
                let a = self.synth(&abc.0)?;
                let b = self.synth(&abc.1)?;
                let c = self.synth(&abc.2)?;
                a.subst(&b, &c)
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
    if pat.has_bind_symbol() {
        let mut c = Context::new();
        c.set(pat, e)?;
        c.synth(rule)
    } else {
        fn subst(rule: &Expr, pat: &Expr, e: &Expr) -> Result<Expr, ()> {
            match rule {
                x if x == pat => Ok(e.clone()),
                x if x.is_sym() => Ok(rule.clone()),
                X | Y | A | B => Ok(rule.clone()),
                Bin(abc) => {
                    let a = subst(&abc.0, pat, e)?;
                    let b = subst(&abc.1, pat, e)?;
                    let c = subst(&abc.2, pat, e)?;
                    Ok(Bin(Box::new((a, b, c))))
                }
                Un(ab) => {
                    let a = subst(&ab.0, pat, e)?;
                    let b = subst(&ab.1, pat, e)?;
                    Ok(Un(Box::new((a, b))))
                }
                _ => Err(())
            }
        }

        subst(rule, pat, e)
    }
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
        Bin(abc) if abc.0 == Qual => Err(()),
        Bin(abc) if abc.0 == Pow => Err(()),
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
        Bin(abc) if abc.0 == Qual => Err(()),
        Bin(abc) if abc.0 == Pow => Err(()),
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
