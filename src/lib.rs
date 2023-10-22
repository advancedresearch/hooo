/*!
# Hooo
Propositional logic with exponentials

To install Hooo, type:

```text
cargo install --example hooo hooo
```

Then, to check a file with Hooo, type:

```text
hooo <file.hooo>
```

### Example: Absurd

```text
fn absurd false -> a {
    x : false;
    let r = match x : a;
    return r;
}
```

### Working with projects

To check a whole project, type:

```text
hooo <project directory>
```

Hooo will generate a "Hooo.config" file, which you can modify to use other libraries:

```text
dependencies {
    path("../my_library");
}
```

By default, Hooo adds a "std" library which you can use in the following way:

```text
use std::not_double;
```

This will add a term `not_double : a -> !!a`.

## Introduction to Hooo

Intuitionistic Propositional Logic (IPL) is the most important mathematical language
in the world, because it is the foundation for constructive logic and many type systems.

Usually, IPL is thought of as a "simple language" that is generalized in various ways.
For example, by adding predicates, one gets First Order Logic.

Previously, IPL was thought of as "complete" in the sense that it can derive every
formula that is true about propositions.
To reason about IPL at meta-level, mathematicians relied on some meta-language (e.g. Sequent Calculus)
or some modal logic.

For example, in Provability Logic, `□(a => b)` is introduced by proving `⊢ a => b` in Sequent Calculus.

Recently, I discovered that, while logical implication (`=>`) in IPL corresponds to lambda/closures,
there is no possible way to express the analogue of function pointers (`->`).
People thought previously that, since logical implication is a kind of exponential object,
that IPL covered exponentials in the sense of Category Theory.
However, there can be more than one kind of exponential!
The extension of IPL to include function pointers is called "exponential propositions".

Exponential propositions allows a unification of the meta-language of IPL with its object-language.
This means that IPL in its previous form is "incomplete", in the sense that there are no ways
to express exponential propositions.

Hooo finalizes intuitionistic logic by introducing exponential propositions (HOOO EP).
This solves the previous problems of using a separate meta-language.
Inference rules in Hooo are first-class citizens.

There is no separation between the language and meta-language in Hooo.
All types, including rules, are constructive propositions.

### Relation to Provability Logic

HOOO EP might sound like Provability Logic, but it is not the same thing.
Provability Logic is incompatible with HOOO EP, since Löb's axiom is absurd.
For proof, see `lob_absurd` in "source/std/modal.hooo".

# HOOO EP

"HOOO EP" stands for "Higher Order Operator Overloading Exponential Propositions".

HOOO EP was first developed in the [Prop](https://github.com/advancedresearch/prop) library,
which exploited function pointers in Rust's type system.

There are 3 axioms in HOOO EP:

```text
pow_lift : a^b -> (a^b)^c
tauto_hooo_imply : (a => b)^c -> (a^c => b^c)^true
tauto_hooo_or : (a | b)^c -> (a^c | b^c)^true
```

The philosophy of HOOO EP is that the axioms are intuitive.
This is how people can know that the axioms can be trusted.

From these axioms, there are infinitely complex logical consequences.
It is important to keep the axioms few and simple to not cause trouble later on.

However, some statements many people find "obviously true" can be difficult to prove.
This is why a library is needed to show how to prove such statements.

For example, in Hooo, one can prove that function composition is possible:

```text
fn pow_transitivity b^a & c^b -> c^a {
    x : b^a;
    y : c^b;

    fn f a -> ((b^a & c^b) => c) {
        x : a;

        lam g (b^a & c^b) => c {
            y : b^a;
            z : c^b;

            let x2 = y(x) : b;
            let x3 = z(x2) : c;
            return x3;
        }
        return g;
    }

    use hooo_imply;
    let x2 = hooo_imply(f) : (b^a & c^b)^a => c^a;

    use pow_lift;
    let x3 = pow_lift(x) : (b^a)^a;
    let y3 = pow_lift(y) : (c^b)^a;

    use refl;
    let x4 = refl(x3, y3) : (b^a)^a & (c^b)^a;

    use hooo_rev_and;
    let x5 = hooo_rev_and(x4) : (b^a & c^b)^a;

    let x6 = x2(x5) : c^a;
    return x6;
}
```

Notice how complex this proof is compared to proving lambda/closure composition:

```text
fn imply_transitivity (a => b) & (b => c) -> (a => c) {
    x : a => b;
    y : b => c;
    lam f (a => c) {
        arg : a;
        let x2 = x(arg) : b;
        let x3 = y(x2) : c;
        return x3;
    }
    return f;
}
```

Intuitively, function composition is possible, so most people just take it for granted.
Previously, mathematicians needed a meta-language to prove such properties.
Now, people can prove these properties directly using Hooo-like languages.

Hooo is designed for meta-theorem proving in constructive/intuitionistic logic.
This means that Hooo can reason about its own rules.
From existing rules, you can generate new rules, by leveraging the full
power of meta-theorem proving in constructive logic.

An exponential proposition is a function pointer, or an inference rule.
You can write the type of function pointers as `a -> b` or `b^a`.

## Syntax

```text
a -> b     Exponential/function pointer/inference rule
b^a        Exponential/function pointer/inference rule
a => b     Imply (lambda/closure)
a & b      And (struct type)
a | b      Or (enum type)
!a         Not (sugar for `a => false`)
a == b     Equal (sugar for `(a => b) & (b => a)`)
a =^= b    Pow equal (sugar for `b^a & a^b`)
true       True (unit type)
false      False (empty type)
all(a)     Lifts `a` to matching all types
foo'       Symbol `foo`
foo(a)     Apply symbol `foo` to `a`

x : a      Premise/argument
let y      Theorem/variable

return x   Helps the solver make a conclusion

axiom foo : a               Introduce axiom `foo` of type `a`
() : a                      Prove `a`, e.g. `() : true`
f(x)                        Apply one argument `x` to `f`
f(x, y, ...)                Apply multiple arguments
match x : a                 If `x : false`
match x (l, r) : c          If `x : (a | b)`, `l : a => c` and `r : b => c`
use <tactic>                Imports tactic
fn <name> a -> b { ... }    Function
lam <name> a => b { ... }   Lambda/closure
```

The `^` operator has high precedence, while `->` has low precedence.

E.g. `b^a => b` is parsed as `(b^a) => b`.
`b -> a => b` is parsed as `b -> (a => b)`.

### Symbols

The current version of Hooo uses ad-hoc symbols.
This means that instead of declaring data structures
or predicates, one can just use e.g. `foo(a, b)`.

An explicit symbol `foo` is written `foo'`.

Symbols are global, so `foo'` is `foo'` everywhere.

Hooo does not support quantification over symbols.
With other words, in some sense Hooo is restricted a First Order Logic style of quantification.

*/

use std::sync::Arc;
use std::collections::HashSet;
use std::collections::HashMap;
use std::fmt;
use std::path::Path;
use piston_meta::Range;
use lazy_static::lazy_static;

pub mod parsing;

/// Used to keep track of how much it costs to prove something.
pub struct Search {
    pub n: u64,
    pub debug: bool,
}

impl Search {
    /// Creates a new search.
    pub fn new() -> Search {Search {n: 0, debug: false}}

    /// Increase the counter that shows cost.
    pub fn inc(&mut self) {self.n += 1}

    /// Asserts that length is less or equal than some limit.
    pub fn le(&self, n: u64) {
        assert!(self.n <= n, "{} <= {}", self.n, n);
    }

    /// Beat length.
    pub fn beat(&self, n: u64) {
        if self.n >= n {panic!("record attempt failed {} >= {}", self.n, n)}
        else {panic!("new record {} < {}", self.n, n)}
    }
}

#[derive(Clone)]
pub struct Context {
    /// Stores the terms.
    pub terms: Vec<Term>,
    /// Stores the term names.
    pub term_names: Vec<Arc<String>>,
    /// Stores the proofs.
    pub proofs: Vec<Type>,
    /// Stores proof cache.
    pub proof_cache: HashSet<Type>,
}

impl Context {
    pub fn new() -> Context {
        Context {
            terms: vec![],
            term_names: vec![],
            proofs: vec![],
            proof_cache: HashSet::new(),
        }
    }

    pub fn has_term_ty(&self, name: &str, ty: &Type) -> bool {
        for (term_name, term) in self.term_names.iter().zip(self.terms.iter()) {
            if &**term_name == name {return term.get_type().has_bound(ty)}
        }
        false
    }

    pub fn has_term(&self, name: &str) -> bool {
        self.term_names.iter().any(|n| &**n == name)
    }

    pub fn run_str(
        &mut self,
        script: &str,
        search: &mut Search,
        loader: &mut Loader,
    ) -> Result<Option<Arc<String>>, String> {
        parsing::run_str(self, script, search, loader)
    }

    pub fn run(
        &mut self,
        file: &str,
        search: &mut Search,
        loader: &mut Loader,
    ) -> Result<Option<Arc<String>>, String> {
        use std::fs::File;
        use std::io::Read;

        let mut data_file =
        File::open(file).map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        let mut data = String::new();
        data_file.read_to_string(&mut data)
            .map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        self.run_str(&data, search, loader)
    }

    pub fn new_term(
        &mut self,
        (name, t): (Arc<String>, Term),
        search: &mut Search
    ) -> Result<(), String> {
        let ty = t.get_type();
        match t.has_type(&ty, self, search) {
            Ok(()) => {
                self.terms.push(t);
                self.term_names.push(name.clone());
                self.proof_cache.insert(ty);
                Ok(())
            }
            Err(err) => Err(format!("{}\nType mismatch `{}`", err, name)),
        }
    }

    #[must_use]
    pub fn fun<F: FnOnce(&mut Context, &mut Search) -> Result<(), (Range, String)>>(
        &mut self,
        range: Range,
        name: Arc<String>,
        ty: Type,
        search: &mut Search,
        f: F
    ) -> Result<(), (Range, String)> {
        if !ty.is_safe_to_prove() {
            return Err((range, format!("Not safe to prove `{}`", ty.to_str(true, None))));
        }

        if let Type::Pow(_) = &ty {
            let mut ctx = Context::new();
            f(&mut ctx, search)?;
            if ctx.prove(ty.clone(), search) && ctx.safe(&ty) {
                // Force the proof since it is safe.
                let ty = ty.lift();
                self.add_proof(ty.clone());
                self.new_term((name, Term::FunDecl(ty)), search)
                    .map_err(|err| (range, err))?;
                Ok(())
            } else {Err((range, format!("Could not prove `{}`", ty.to_str(true, None))))}
        } else {Err((range, "Expected `->`".into()))}
    }

    #[must_use]
    pub fn lam<F: FnOnce(&mut Context, &mut Search) -> Result<(), (Range, String)>>(
        &mut self,
        range: Range,
        name: Arc<String>,
        ty: Type,
        search: &mut Search,
        f: F
    ) -> Result<(), (Range, String)> {
        if !ty.is_safe_to_prove() {
            return Err((range, format!("Not safe to prove `{}`", ty.to_str(true, None))));
        }

        if let Type::Imply(_) = ty {
            let mut ctx = self.clone();
            f(&mut ctx, search)?;
            if ctx.prove(ty.clone(), search) {
                // Force the proof since it is safe.
                self.add_proof(ty.clone());
                self.new_term((name, Term::LamDecl(ty)), search)
                    .map_err(|err| (range, err))?;
                Ok(())
            } else {Err((range, format!("Could not prove `{}`", ty.to_str(true, None))))}
        } else {Err((range, "Expected `=>`".into()))}
    }

    // Returns `true` if type is safe to add to list of proofs.
    //
    // There are only some exponential propositions (power) that are unsafe.
    // If every initial term is covered in the assumption, then it is safe.
    fn safe(&self, ty: &Type) -> bool {
        if self.terms.len() == 0 {true}
        else if let Type::Pow(ab) = ty {
            let mut cover = true;
            for term in &self.terms {
                if term.is_safe() {continue};

                let ty = term.get_type();
                if !ty.is_covered(&ab.1) {
                    cover = false;
                    break;
                }
            }
            cover
        }
        else {true}
    }

    fn fast_proof(&mut self, proof: &Type) -> bool {
        use Type::*;

        match proof {
            True => true,
            Or(ab) if self.has_proof(&ab.0) || self.has_proof(&ab.1) => true,
            And(ab) if self.has_proof(&ab.0) && self.has_proof(&ab.1) => true,
            Imply(ab) if self.has_proof(&ab.1) => true,
            Pow(ab) => {
                let has = self.has_proof(&ab.0);
                if has && self.safe(proof) {return true};

                if let True = ab.1 {
                    // tauto_hooo_imply `(a => b)^c  ->  (a^c => b^c)^true`.
                    if let Imply(ab) = &ab.0 {
                        if let (Pow(ref x), Pow(ref y)) = **ab {
                            if x.1 == y.1 {
                                let transform = pow(imply(x.0.clone(), y.0.clone()), x.1.clone());
                                return self.has_proof(&transform);
                            }
                        }
                    }

                    // tauto_hooo_or `(a | b)^c  ->  (a^c | b^c)^true`.
                    if let Or(ab) = &ab.0 {
                        if let (Pow(ref x), Pow(ref y)) = **ab {
                            if x.1 == y.1 {
                                let transform = pow(or(x.0.clone(), y.0.clone()), x.1.clone());
                                return self.has_proof(&transform);
                            }
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    pub fn has_proof(&mut self, proof: &Type) -> bool {
        if self.proof_cache.contains(proof) {return true};

        if self.proofs.iter().any(|n| n.has_bound(proof)) {
            self.proof_cache.insert(proof.clone());
            true
        } else if self.terms.iter().any(|n| n.get_type().has_bound(proof)) {
            self.proof_cache.insert(proof.clone());
            true
        } else if self.fast_proof(proof) {
            self.proof_cache.insert(proof.clone());
            true
        } else {
            false
        }
    }

    pub fn proof_has(&self, proof: &Type) -> bool {
        self.proofs.iter().any(|n| proof.has_bound(n))
    }

    /// Adds a proof by first checking redundance.
    pub fn add_proof(&mut self, proof: Type) {
        if !self.has_proof(&proof) {
            self.proofs.push(proof.clone());
            self.proof_cache.insert(proof);
        }
    }

    #[must_use]
    pub fn prove_depth(&mut self, ty: Type, depth: u32, search: &mut Search) -> bool {
        use Type::*;

        if depth == 0 {return false}
        if self.has_proof(&ty) {return true}

        // Conclude pow that covers context.
        if let Pow(ab) = &ty {
            if self.prove_depth(ab.0.clone(), depth - 1, search) {
                self.add_proof(ty);
                return true;
            }

            search.inc();
        }

        false
    }

    #[must_use]
    pub fn prove(&mut self, ty: Type, search: &mut Search) -> bool {self.prove_depth(ty, 3, search)}
}

/// Represents a term.
#[derive(Clone, Debug)]
pub enum Term {
    /// Proof `()` of some statement that can be proved.
    Check(Type),
    /// An axiom.
    Axiom(Type),
    /// A variable must be covered by context to be lifted.
    Var(Type),
    /// Function declaration.
    FunDecl(Type),
    /// Lambda declaration.
    LamDecl(Type),
    /// Function application.
    App(Arc<String>, Vec<Arc<String>>, Type),
    /// Match statement.
    Match(Vec<Arc<String>>, Type),
}

lazy_static! {
    static ref MATCH_TYPE: Result<Type, String> = {
        "(a | b) & ((a => c) & (b => c))  ->  c".try_into()
    };
}

impl Term {
    pub fn is_safe(&self) -> bool {
        use Term::*;

        match self {
            Var(_) => false,
            Check(_) | Axiom(_) | FunDecl(_) | LamDecl(_) | App(..) | Match(..) => true,
        }
    }

    pub fn get_type(&self) -> Type {
        use Term::*;

        match self {
            Check(t) => t.clone(),
            Axiom(t) => t.clone(),
            Var(t) => t.clone(),
            FunDecl(ty) => ty.clone(),
            LamDecl(ty) => ty.clone(),
            App(_, _, t) => t.clone(),
            Match(_, t) => t.clone(),
        }
    }

    pub fn has_type(&self, ty: &Type, ctx: &mut Context, search: &mut Search) -> Result<(), String> {
        use Term::*;

        match self {
            App(f, args, t) if t.has_bound(ty) => {
                let mut fun_decl: Option<usize> = None;
                let mut arg_inds: Vec<Option<usize>> = vec![None; args.len()];
                for (i, term_name) in ctx.term_names.iter().enumerate().rev() {
                    if term_name == f {
                        fun_decl = Some(i);
                    }
                }
                for (j, arg) in args.iter().enumerate() {
                    for (i, term_name) in ctx.term_names.iter().enumerate().rev() {
                        if term_name == arg {
                            arg_inds[j] = Some(i);
                            break;
                        }
                    }
                }

                for (i, arg_ind) in arg_inds.iter().enumerate() {
                    if arg_ind.is_none() {
                        return Err(format!("Argument `{}` is not found", args[i]));
                    }
                }

                if let Some(fun_decl) = fun_decl {
                    let ty_f = ctx.terms[fun_decl].get_type();
                    let ty_f = if let Type::All(x) = ty_f {(*x).clone()} else {ty_f};
                    if args.len() == 0 {
                        if ty_f.has_bound(t) {return Ok(())}
                        else {
                            if let Type::All(_) = ty_f {return Err("Did not expect `all(..)`".into())}
                            else {
                                return if Type::All(Box::new(ty_f.clone())).has_bound(ty) {
                                    Ok(())
                                } else {
                                    Err(format!("Expected `{}`, found `{}`", ty, ty_f))
                                };
                            }
                        }
                    } else {
                        let arg_ind = arg_inds.pop().unwrap();
                        let mut ty_arg = ctx.terms[arg_ind.unwrap()].get_type();
                        for arg_ind in arg_inds.into_iter().rev() {
                            ty_arg = and(ctx.terms[arg_ind.unwrap()].get_type(), ty_arg);
                        }
                        if let Type::Pow(ab) = &ty_f {
                            return if ty_arg.app_to_has_bound(&ab.1, &ab.0, t) {
                                Ok(())
                            } else {
                                Err(format!("Expected `{}`, could not apply `{}` to `{}`",
                                    t, ty_f.to_str(true, None), ty_arg))
                            };
                        } else if let Type::Imply(ab) = &ty_f {
                            return if ty_arg.app_to_has_bound(&ab.0, &ab.1, t) {
                                Ok(())
                            } else {
                                Err(format!("Expected `{}`', could not apply `{}` to `{}`",
                                    t, ty_f, ty_arg))
                            };
                        } else {
                            return Err("Expected `->` or `=>`".into());
                        }
                    }
                } else {
                    return Err(format!("Could not find `{}`", f));
                }
            }
            Match(args, t) if t.has_bound(ty) => {
                let mut arg_inds: Vec<Option<usize>> = vec![None; args.len()];
                for (j, arg) in args.iter().enumerate() {
                    for (i, term_name) in ctx.term_names.iter().enumerate().rev() {
                        if term_name == arg {
                            arg_inds[j] = Some(i);
                            break;
                        }
                    }
                }

                for (i, arg_ind) in arg_inds.iter().enumerate() {
                    if arg_ind.is_none() {
                        return Err(format!("Argument `{}` is not found", args[i]));
                    }
                }

                let arg_ind = arg_inds.pop().unwrap();
                let mut ty_arg = ctx.terms[arg_ind.unwrap()].get_type();
                for arg_ind in arg_inds.into_iter().rev() {
                    ty_arg = and(ctx.terms[arg_ind.unwrap()].get_type(), ty_arg);
                }
                let ty_f: Type = if args.len() == 1 {"false -> a".try_into().unwrap()}
                    else {MATCH_TYPE.as_ref().unwrap().clone()};
                if let Type::Pow(ab) = ty_f.lift() {
                    if ty_arg.app_to_has_bound(&ab.1, &ab.0, t) {
                        return Ok(());
                    };
                }
                return Err("Internal error in type checker".into());
            }
            Axiom(t) if t.has_bound(ty) => Ok(()),
            FunDecl(t) if t.has_bound(ty) => Ok(()),
            LamDecl(t) if t.has_bound(ty) => Ok(()),
            Var(t) if t.has_bound(ty) => Ok(()),
            Check(t) if ctx.prove(t.clone(), search) &&
                ctx.prove(ty.clone(), search) => Ok(()),
            _ => return Err("Type check error #100".into()),
        }
    }
}

/// Represent types.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    /// Unit type.
    True,
    /// Empty type.
    False,
    /// A type variable that binds to expressions of same name.
    Ty(Arc<String>),
    /// A type variable that can bind to any expression.
    AllTy(Arc<String>),
    /// Exponential type (function pointer).
    Pow(Box<(Type, Type)>),
    /// Tuple.
    And(Box<(Type, Type)>),
    /// Or.
    Or(Box<(Type, Type)>),
    /// Imply.
    Imply(Box<(Type, Type)>),
    /// For-all.
    All(Box<Type>),
    /// Symbol.
    Sym(Arc<String>),
    /// Application.
    App(Box<(Type, Type)>),
}

#[derive(Copy, Clone)]
pub enum Op {
    Pow,
    And,
    Or,
    Imply,
    Not,
    Eq,
    Excm,
    PowEq,
    All,
    App,
}

fn needs_parens(ty: &Type, parent_op: Option<Op>) -> bool {
    use Type::*;

    if ty.as_not().is_some() {
        if let Some(Op::Pow) = parent_op {return true};

        return false;
    }
    if ty.as_excm().is_some() {return false};
    match ty {
        True | False | Ty(_) | AllTy(_) | All(_) | App(_) | Sym(_) => false,
        _ => {
            match (ty.op(), parent_op) {
                (Some(Op::Pow), Some(Op::And) | Some(Op::Or) | Some(Op::Imply)) => false,
                _ => true,
            }
        }
    }
}

impl Type {
    pub fn op(&self) -> Option<Op> {
        use Type::*;

        if self.as_not().is_some() {return Some(Op::Not)};
        if self.as_eq().is_some() {return Some(Op::Eq)};
        if self.as_excm().is_some() {return Some(Op::Excm)};
        if self.as_pow_eq().is_some() {return Some(Op::PowEq)};
        match self {
            True | False | Ty(_) | AllTy(_) => None,
            Pow(_) => Some(Op::Pow),
            And(_) => Some(Op::And),
            Or(_) => Some(Op::Or),
            Imply(_) => Some(Op::Imply),
            All(_) => Some(Op::All),
            Sym(_) => None,
            App(_) => Some(Op::App),
        }
    }

    pub fn as_not(&self) -> Option<&Type> {
        if let Type::Imply(ab) = self {
            if let Type::False = ab.1 {Some(&ab.0)} else {None}
        } else {None}
    }

    pub fn as_eq(&self) -> Option<(&Type, &Type)> {
        if let Type::And(ab) = self {
            if let (Type::Imply(ab), Type::Imply(cd)) = &**ab {
                if ab.0 == cd.1 && ab.1 == cd.0 {Some((&ab.0, &ab.1))} else {None}
            } else {None}
        } else {None}
    }

    pub fn as_excm(&self) -> Option<&Type> {
        if let Type::Or(ab) = self {
            if let Some(b) = ab.1.as_not() {
                if &ab.0 == b {return Some(&ab.0)} else {None}
            } else {None}
        } else {None}
    }

    pub fn as_pow_eq(&self) -> Option<(&Type, &Type)> {
        if let Type::And(ab) = self {
            if let (Type::Pow(ab), Type::Pow(cd)) = &**ab {
                if ab.1 == cd.0 && ab.0 == cd.1 {Some((&ab.1, &ab.0))} else {None}
            } else {None}
        } else {None}
    }

    pub fn as_app_sym(&self) -> Option<(&Arc<String>, &Type)> {
        if let Type::App(ab) = self {
            if let Type::Sym(s) = &ab.0 {
                return Some((s, &ab.1));
            } else {None}
        } else {None}
    }

    pub fn as_multi_app_sym(&self) -> Option<(&Arc<String>, Vec<&Type>)> {
        let mut args: Vec<&Type> = vec![];
        let mut ty = self;
        loop {
            if let Type::App(ab) = ty {
                args.push(&ab.1);
                ty = &ab.0;
            } else if let Type::Sym(f) = ty {
                args.reverse();
                return Some((f, args));
            } else {
                return None;
            }
        }
    }

    pub fn to_str(&self, top: bool, parent_op: Option<Op>) -> String {
        if top {
            if let Type::Pow(ab) = self {
                let op = self.op();
                return format!("{} -> {}", ab.1.to_str(false, op), ab.0.to_str(false, op));
            }
        }

        if needs_parens(self, parent_op) {format!("({})", self)}
        else {format!("{}", self)}
    }
}

impl fmt::Display for Type {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use Type::*;

        let op = self.op();
        if let Some(a) = self.as_not() {
            return write!(w, "!{}", a.to_str(false, op));
        }
        if let Some((a, b)) = self.as_eq() {
            return write!(w, "{} == {}", a.to_str(false, op), b.to_str(false, op));
        }
        if let Some(a) = self.as_excm() {
            return write!(w, "excm({})", a);
        }
        if let Some((a, b)) = self.as_pow_eq() {
            return write!(w, "{} =^= {}", a, b);
        }
        if let Some((a, b)) = self.as_app_sym() {
            return write!(w, "{}({})", a, b);
        }
        if let Some((f, args)) = self.as_multi_app_sym() {
            if args.len() == 0 {
                return write!(w, "{}'", f);
            }

            write!(w, "{}(", f)?;
            let mut first = true;
            for arg in args {
                if !first {
                    write!(w, ", ")?;
                }
                first = false;
                write!(w, "{}", arg)?;
            }
            return write!(w, ")");
        }
        match self {
            True => write!(w, "true")?,
            False => write!(w, "false")?,
            Ty(a) => write!(w, "{}", a)?,
            AllTy(a) => write!(w, "{}", a)?,
            Pow(ab) => write!(w, "{}^{}", ab.0.to_str(false, op), ab.1.to_str(false, op))?,
            And(ab) => write!(w, "{} & {}", ab.0.to_str(false, op), ab.1.to_str(false, op))?,
            Or(ab) => write!(w, "{} | {}", ab.0.to_str(false, op), ab.1.to_str(false, op))?,
            Imply(ab) => write!(w, "{} => {}", ab.0.to_str(false, op), ab.1.to_str(false, op))?,
            All(a) => write!(w, "all({})", a)?,
            Sym(a) => write!(w, "{}'", a)?,
            App(ab) => write!(w, "{}({})", ab.0.to_str(false, op), ab.1)?,
        }
        Ok(())
    }
}

impl TryFrom<&str> for Type {
    type Error = String;
    fn try_from(s: &str) -> Result<Type, String> {
        parsing::parse_ty_str(s)
    }
}

impl Type {
    pub fn is_safe_to_prove(&self) -> bool {
        use Type::*;

        match self {
            True | False | Ty(_) => true,
            And(ab) => ab.0.is_safe_to_prove() && ab.1.is_safe_to_prove(),
            Or(ab) => ab.0.is_safe_to_prove() && ab.1.is_safe_to_prove(),
            Imply(ab) => ab.1.is_safe_to_prove(),
            Pow(ab) => ab.0.is_safe_to_prove(),
            AllTy(_) | All(_) => false,
            Sym(_) => true,
            App(_) => true,
        }
    }

    pub fn is_covered(&self, other: &Type) -> bool {
        use Type::*;

        if self.has_bound(other) {return true};

        match other {
            And(ab) => self.is_covered(&ab.0) || self.is_covered(&ab.1),
            _ => false,
        }
    }

    pub fn lift(self) -> Type {
        use Type::*;

        match self {
            True => True,
            False => False,
            Ty(a) => AllTy(a),
            AllTy(a) => AllTy(a),
            And(ab) => and(ab.0.lift(), ab.1.lift()),
            Imply(ab) => imply(ab.0.lift(), ab.1.lift()),
            Pow(ab) => pow(ab.0.lift(), ab.1.lift()),
            Or(ab) => or(ab.0.lift(), ab.1.lift()),
            All(_) => self,
            Sym(_) => self,
            App(ab) => app(ab.0.lift(), ab.1.lift()),
        }
    }

    #[must_use]
    pub fn bind(&self, contra: bool, val: &Type, bind: &mut Vec<(Type, Type)>) -> bool {
        use Type::*;

        match if contra {(val, self)} else {(self, val)} {
            (True, True) => true,
            (False, False) => true,
            (Ty(a), Ty(b)) => a == b,
            (Sym(a), Sym(b)) => a == b,
            (_, AllTy(a)) if contra => {
                for (name, v) in bind.iter() {
                    if let AllTy(name) = name {
                        if name == a && val != v {return false}
                    }
                }
                bind.push((self.clone(), val.clone()));
                true
            }
            (AllTy(a), _) if !contra => {
                for (name, v) in bind.iter() {
                    if let AllTy(name) = name {
                        if name == a && val != v {return false}
                    }
                }
                bind.push((self.clone(), val.clone()));
                true
            }
            (And(ab), And(cd)) |
            (Or(ab), Or(cd)) |
            (App(ab), App(cd)) => {
                let (ab, cd) = if contra {(cd, ab)} else {(ab, cd)};
                if !ab.0.bind(contra, &cd.0, bind) {return false};
                if !ab.1.bind(contra, &cd.1, bind) {return false};
                true
            }
            (Pow(ab), Pow(cd)) => {
                let (ab, cd) = if contra {(cd, ab)} else {(ab, cd)};
                if !ab.0.bind(contra, &cd.0, bind) {return false};
                if !ab.1.bind(!contra, &cd.1, bind) {return false};
                true
            }
            (Imply(ab), Imply(cd)) => {
                let (ab, cd) = if contra {(cd, ab)} else {(ab, cd)};
                if !ab.0.bind(!contra, &cd.0, bind) {return false};
                if !ab.1.bind(contra, &cd.1, bind) {return false};
                true
            }
            (Pow(ab), Imply(cd)) => {
                if contra {
                    if !cd.0.bind(!contra, &ab.1, bind) {return false};
                    if !cd.1.bind(contra, &ab.0, bind) {return false};
                } else {
                    if !ab.1.bind(!contra, &cd.0, bind) {return false};
                    if !ab.0.bind(contra, &cd.1, bind) {return false};
                }
                true
            }
            (All(a), All(b)) => {
                let mut bind = vec![];
                if a.bind(contra, b, &mut bind) {
                    bind.push((self.clone(), All(Box::new(a.replace(&bind)))));
                    true
                } else {false}
            }
            _ => false,
        }
    }

    pub fn replace(&self, bind: &[(Type, Type)]) -> Type {
        use Type::*;

        for (arg, val) in bind {
            if arg == self {return val.clone()}
        }
        match self {
            True => self.clone(),
            False => self.clone(),
            Ty(_) => self.clone(),
            Sym(_) => self.clone(),
            AllTy(_) => self.clone(),
            Pow(ab) => pow(ab.0.replace(bind), ab.1.replace(bind)),
            Imply(ab) => imply(ab.0.replace(bind), ab.1.replace(bind)),
            And(ab) => and(ab.0.replace(bind), ab.1.replace(bind)),
            Or(ab) => or(ab.0.replace(bind), ab.1.replace(bind)),
            App(ab) => app(ab.0.replace(bind), ab.1.replace(bind)),
            All(a) => All(Box::new(a.replace(bind))),
        }
    }

    /// Whether application type checks.
    pub fn app_to_has_bound(&self, a: &Type, b: &Type, t: &Type) -> bool {
        let mut bind = vec![];
        let contra = true;
        if a.bind(contra, self, &mut bind) {
            if b.replace(&bind).has_(false, t) {return true} else {false}
        } else {false}
    }

    pub fn has_bound(&self, other: &Type) -> bool {
        let mut bind = vec![];
        let contra = false;
        if self.bind(contra, other, &mut bind) {
            self.replace(&bind).has_(contra, other)
        } else {false}
    }

    pub fn has_(&self, contra: bool, other: &Type) -> bool {
        use Type::*;

        match (self, other) {
            (False, False) => true,
            (True, True) => true,
            (Ty(a), Ty(b)) if a == b => true,
            (_, AllTy(_)) if contra => true,
            (AllTy(_), _) if !contra => true,
            (And(ab), And(cd)) if ab.0.has_(contra, &cd.0) && ab.1.has_(contra, &cd.1) => true,
            (Or(ab), Or(cd)) if ab.0.has_(contra, &cd.0) && ab.1.has_(contra, &cd.1) => true,
            (Pow(ab), Imply(cd)) if cd.0.has_(!contra, &ab.1) && ab.0.has_(contra, &cd.1) => true,
            (Pow(ab), Pow(cd)) if cd.1.has_(!contra, &ab.1) &&
                                  ab.0.has_(contra, &cd.0) => true,
            (Imply(ab), Imply(cd)) if cd.0.has_(!contra, &ab.0) && ab.1.has_(contra, &cd.1) => true,
            // TODO: Add unit tests for this case.
            (x, Or(ab)) if x.has_(contra, &ab.0) || x.has_(contra, &ab.1) => true,
            (All(a), All(b)) if a.has_(contra, b) => true,
            (Sym(a), Sym(b)) if a == b => true,
            (App(ab), App(cd)) if ab.0.has_(contra, &cd.0) && ab.1.has_(contra, &cd.1) => true,
            _ => false,
        }
    }
}

/// Loads function types.
#[derive(Clone)]
pub struct Loader {
    /// The working directory.
    pub dir: Arc<String>,
    /// Function type cache.
    pub functions: HashMap<Arc<String>, Type>,
    /// Whether to execute script when parsing.
    ///
    /// First time when traversing a project,
    /// this is set to `false` in order to extract function definitions.
    pub run: bool,
    /// Library dependencies.
    pub dependencies: Vec<LibInfo>,
    /// Stores trace to avoid cyclic proofs.
    pub trace: Vec<Arc<String>>,
    pub silent: bool,
    pub files: Vec<String>,
}

impl Loader {
    pub fn new(dir: Arc<String>) -> Result<Loader, String> {
        use rayon::prelude::*;
        use std::sync::Mutex;

        let mut loader = Loader {
            dir: dir.clone(),
            functions: HashMap::new(),
            run: false,
            dependencies: vec![],
            trace: vec![],
            silent: false,
            files: vec![],
        };

        let std = parsing::lib_str(include_str!("../source/std/Hooo.config"))?;
        loader.dependencies.push(std);

        let files: Vec<String> = std::fs::read_dir(&**loader.dir).unwrap()
            .filter(|entry| {
                if let Ok(entry) = entry {
                    let path = entry.path();
                    if path.is_file() {
                        if let Some(ext) = path.extension() {
                            ext == "hooo"
                        } else {false}
                    } else {false}
                } else {false}
            })
            .map(|entry| entry.unwrap().path().to_str().unwrap().into())
        .collect();

        let (tx, rx) = std::sync::mpsc::channel();
        let error: Arc<Mutex<Result<(), String>>> = Arc::new(Ok(()).into());

        // Extract all functions.
        let _ = (0..files.len()).into_par_iter().map(|i| {
            let mut ctx = Context::new();
            let mut search = Search::new();
            let mut loader = loader.clone();
            let file = &files[i];
            match ctx.run(file, &mut search, &mut loader) {
                Ok(_) => {}
                Err(err) => {
                    let mut error = error.lock().unwrap();
                    *error = Err(
                        format!("Load error #100\nIn file `{}`\n{}", file, err));
                    return None;
                }
            }
            for fun in loader.functions.into_iter() {
                tx.send(fun).unwrap();
            }
            Some(i)
        }).while_some().max();

        drop(tx);

        let error = error.lock().unwrap();
        let _ = error.as_ref().map_err(|err| err.clone())?;

        while let Ok(x) = rx.recv() {
            loader.functions.insert(x.0, x.1);
        }

        loader.files = files;

        loader.run = true;

        Ok(loader)
    }

    pub fn load_info(&mut self) -> Result<Option<LibInfo>, String> {
        let path = Path::new(&**self.dir).join("Hooo.config");
        if path.exists() {
            match LibInfo::from_path(&path) {
                Ok(x) => {
                    for dep in &x.dependencies {
                        match dep {
                            Dep::Path(p) => {
                                let dep_path = Path::new(&**self.dir).join(&**p).join("Hooo.config");
                                match LibInfo::from_path(&dep_path) {
                                    Ok(x) => self.dependencies.push(x),
                                    Err(err) => return Err(err),
                                }
                            }
                        }
                    }
                    Ok(Some(x))
                }
                Err(err) => Err(err),
            }
        } else {Ok(None)}
    }

    pub fn load_fun(&mut self, ns: &[Arc<String>], f: &Arc<String>) -> Result<Type, String> {
        let this_lib = ns.len() == 0 || &**ns[0] == "crate";

        if this_lib {
            for tr in &self.trace {
                if &**tr == &**f {
                    return Err(format!("Cyclic proof, `{}` uses `{}`", tr, f));
                }
            }
        }

        let functions = if this_lib {&self.functions}
            else {
                let mut found: Option<usize> = None;
                for (i, lib) in self.dependencies.iter().enumerate() {
                    if &lib.name == &ns[0] {
                        found = Some(i);
                        break;
                    }
                }
                if let Some(i) = found {
                    &self.dependencies[i].functions
                } else {
                    return Err(format!("Could not load namespace `{}`", ns[0]))
                }
            };

        if let Some(ty) = functions.get(f) {
            return Ok(ty.clone());
        } else {
            return Err(format!("Could not find `{}`", f));
        }
    }
}

#[derive(Clone)]
pub enum Dep {
    Path(Arc<String>),
}

/// Stores library information.
#[derive(Clone)]
pub struct LibInfo {
    pub name: Arc<String>,
    pub version: Arc<String>,
    pub description: Arc<String>,
    pub functions: HashMap<Arc<String>, Type>,
    pub dependencies: Vec<Dep>,
}

impl LibInfo {
    pub fn from_path(path: &Path) -> Result<LibInfo, String> {
        use std::fs::File;
        use std::io::Read;

        let file = path.to_str().unwrap();
        let mut data_file =
        File::open(path).map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        let mut data = String::new();
        data_file.read_to_string(&mut data)
            .map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        parsing::lib_str(&data)
    }
}

pub fn var(a: &str, t: Type) -> (Arc<String>, Term) {(Arc::new(a.into()), Term::Var(t))}

pub fn ty(a: &str) -> Type {Type::Ty(Arc::new(a.into()))}
pub fn pow(a: Type, b: Type) -> Type {Type::Pow(Box::new((a, b)))}
pub fn and(a: Type, b: Type) -> Type {Type::And(Box::new((a, b)))}
pub fn or(a: Type, b: Type) -> Type {Type::Or(Box::new((a, b)))}
pub fn imply(a: Type, b: Type) -> Type {Type::Imply(Box::new((a, b)))}
pub fn not(a: Type) -> Type {imply(a, Type::False)}
pub fn eq(a: Type, b: Type) -> Type {and(imply(a.clone(), b.clone()), imply(b, a))}
pub fn pow_eq(a: Type, b: Type) -> Type {and(pow(b.clone(), a.clone()), pow(a, b))}
pub fn tauto(a: Type) -> Type {pow(a, Type::True)}
pub fn para(a: Type) -> Type {pow(Type::False, a)}
pub fn app(a: Type, b: Type) -> Type {Type::App(Box::new((a, b)))}
pub fn sym(a: &str) -> Type {Type::Sym(Arc::new(a.into()))}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pow() {
        let mut ctx = Context::new();
        ctx.new_term(var("true", ty("Bool")), &mut Search::new()).unwrap();
        assert!(ctx.prove(ty("Bool"), &mut Search::new()));
        assert!(ctx.prove(pow(ty("Bool"), ty("Bool")), &mut Search::new()));
        ctx.new_term(var("x", pow(ty("Bool"), ty("Bool"))), &mut Search::new()).unwrap();
        assert!(ctx.prove(imply(ty("Bool"), ty("Bool")), &mut Search::new()));
    }

    #[test]
    fn test_and() {
        let mut ctx = Context::new();
        ctx.new_term(var("x", ty("A")), &mut Search::new()).unwrap();
        ctx.new_term(var("y", ty("B")), &mut Search::new()).unwrap();
        assert!(ctx.prove(and(ty("A"), ty("B")), &mut Search::new()));
    }

    #[test]
    fn test_anti_pow() {
        let mut ctx = Context::new();
        assert!(ctx.fun(Range::empty(0), Arc::new("foo".into()), "a^b -> a^b".try_into().unwrap(),
        &mut Search::new(), |ctx, search| {
            ctx.new_term(var("x", "a^b".try_into().unwrap()), &mut Search::new()).unwrap();
            if ctx.prove("a^b".try_into().unwrap(), search) {Ok(())} else {Err((Range::empty(0), "error".into()))}
        }).is_ok());
        assert!(!ctx.prove("a^b".try_into().unwrap(), &mut Search::new()));
    }

    #[test]
    fn test_replace() {
        let mut ctx = Context::new();
        ctx.new_term(var("x", "a^b".try_into().unwrap()), &mut Search::new()).unwrap();
        assert!(!ctx.prove("d^c".try_into().unwrap(), &mut Search::new()));
    }

    #[test]
    fn test_parse_pow() {
        let a: Type = "a -> b".try_into().unwrap();
        assert_eq!(a, "b^a".try_into().unwrap());

        let a: Type = "a -> b -> c".try_into().unwrap();
        assert_eq!(a, "(c^b)^a".try_into().unwrap());

        let a: Type = "a => b -> c => d".try_into().unwrap();
        assert_eq!(a, "(c => d)^(a => b)".try_into().unwrap());

        let a: Type = "a & b -> c".try_into().unwrap();
        assert_eq!(a, pow(ty("c"), and(ty("a"), ty("b"))));

        let a: Type = "a & b & c -> d".try_into().unwrap();
        assert_eq!(a, pow(ty("d"), and(ty("a"), and(ty("b"), ty("c")))));

        let a: Type = "a^c == b^c".try_into().unwrap();
        assert_eq!(a, eq(pow(ty("a"), ty("c")), pow(ty("b"), ty("c"))));
    }

    #[test]
    fn test_parse_imply() {
        let a: Type = "a => b".try_into().unwrap();
        assert_eq!(a, imply(ty("a"), ty("b")));

        let a: Type = match "a & b => c".try_into() {
            Ok(x) => x,
            Err(err) => {
                eprintln!("{}", err);
                panic!();
            }
        };
        assert_eq!(a, imply(and(ty("a"), ty("b")), ty("c")));
    }

    #[test]
    fn test_parse_sym() {
        let a: Type = "a'".try_into().unwrap();
        assert_eq!(a, sym("a"));
        assert_eq!(format!("{}", a), "a'".to_string());

        let a: Type = "a' =^= b'".try_into().unwrap();
        assert_eq!(a, pow_eq(sym("a"), sym("b")));
        assert_eq!(format!("{}", a), "a' =^= b'".to_string());
    
        let a: Type = "a' & b'".try_into().unwrap();
        assert_eq!(a, and(sym("a"), sym("b")));
        assert_eq!(format!("{}", a), "a' & b'".to_string());
    
        let a: Type = "a' & b' -> c'".try_into().unwrap();
        assert_eq!(a, pow(sym("c"), and(sym("a"), sym("b"))));

        let a: Type = "ty(add', nat' & nat' -> nat')".try_into().unwrap();
        assert_eq!(a, app(app(sym("ty"), sym("add")), pow(sym("nat"), and(sym("nat"), sym("nat")))));
    }

    #[test]
    fn test_all() {
        let a: Type = "all(a)".try_into().unwrap();
        assert_eq!(a, Type::All(Box::new(Type::AllTy(Arc::new("a".into())))));

        let b: Type = "all(b)".try_into().unwrap();
        assert!(a.has_bound(&b));

        let a: Type = "all(a -> a)".try_into().unwrap();
        assert!(a.has_bound(&a));

        let b: Type = "all(a -> b)".try_into().unwrap();
        assert!(b.has_bound(&a));
        assert!(!a.has_bound(&b));
    }

    #[test]
    fn test_display() {
        let a: Type = "!a".try_into().unwrap();
        assert_eq!(format!("{}", a), "!a".to_string());

        let a: Type = "!!a".try_into().unwrap();
        assert_eq!(format!("{}", a), "!!a".to_string());

        let a: Type = "!(a & b)".try_into().unwrap();
        assert_eq!(format!("{}", a), "!(a & b)".to_string());

        let a: Type = "a == b".try_into().unwrap();
        assert_eq!(format!("{}", a), "a == b".to_string());

        let a: Type = "excm(a)".try_into().unwrap();
        assert_eq!(format!("{}", a), "excm(a)".to_string());

        let a: Type = "a & excm(b)".try_into().unwrap();
        assert_eq!(format!("{}", a), "a & excm(b)".to_string());

        let a: Result<Type, String> = "false^true^true".try_into();
        assert!(a.is_err());

        let a: Type = "!((false^true)^true)".try_into().unwrap();
        assert_eq!(format!("{}", a), "!((false^true)^true)".to_string());

        let a: Type = "!((false^true)^true) => false^true".try_into().unwrap();
        assert_eq!(format!("{}", a), "!((false^true)^true) => false^true".to_string());

        let a: Result<Type, String> = "!a^true".try_into();
        assert!(a.is_err());

        let a: Type = "(!a)^true".try_into().unwrap();
        assert_eq!(format!("{}", a), "(!a)^true".to_string());

        let a: Type = "a =^= b".try_into().unwrap();
        assert_eq!(format!("{}", a), "a =^= b".to_string());

        let a: Type = "!a == !b".try_into().unwrap();
        assert_eq!(format!("{}", a), "!a == !b".to_string());

        let a: Type = "!a => !b".try_into().unwrap();
        assert_eq!(format!("{}", a), "!a => !b".to_string());

        let a: Type = "!a & !b".try_into().unwrap();
        assert_eq!(format!("{}", a), "!a & !b".to_string());

        let a: Type = "!a | !b".try_into().unwrap();
        assert_eq!(format!("{}", a), "!a | !b".to_string());

        let a: Type = "!a =^= !b".try_into().unwrap();
        assert_eq!(format!("{}", a), "!a =^= !b".to_string());

        let a: Type = "q(a, b)".try_into().unwrap();
        assert_eq!(format!("{}", a), "q(a, b)".to_string());
    }

    #[test]
    fn test_safe_to_prove() {
        let a: Type = "all(a -> b)".try_into().unwrap();
        assert!(!a.is_safe_to_prove());

        let a: Type = "all(a) -> b".try_into().unwrap();
        assert!(a.is_safe_to_prove());
    }

    #[test]
    fn test_has() {
        let fun_ab: Type = "a -> b".try_into().unwrap();
        let ab: Type = "a => b".try_into().unwrap();
        assert!(fun_ab.has_bound(&ab));

        let x: Type = "(a => b) -> c".try_into().unwrap();
        let y: Type = "(a -> b) -> c".try_into().unwrap();
        assert!(x.has_bound(&y));

        let x: Type = pow(ty("a"), Type::AllTy(Arc::new("b".into())));
        let y: Type = "a^b".try_into().unwrap();
        assert!(x.has_(false, &y));
    }

    #[test]
    fn test_bind() {
        let mut bind = vec![];
        let a: Type = "a".try_into().unwrap();
        assert!(a.bind(false, &a, &mut bind));

        let mut bind = vec![];
        assert!(a.bind(true, &a, &mut bind));

        let mut bind = vec![];
        assert!(a.clone().lift().bind(false, &a, &mut bind));
        let mut bind = vec![];
        assert!(a.clone().lift().bind(true, &a, &mut bind));
        let mut bind = vec![];
        assert!(!a.bind(false, &a.clone().lift(), &mut bind));

        let x: Type = "a^b".try_into().unwrap();
        let mut bind = vec![];
        assert!(x.clone().lift().bind(false, &x, &mut bind));
        let mut bind = vec![];
        assert!(x.clone().lift().bind(true, &x, &mut bind));
        let mut bind = vec![];
        assert!(!x.bind(false, &x.clone().lift(), &mut bind));
        let mut bind = vec![];
        assert!(!x.bind(true, &x.clone().lift(), &mut bind));

        let x: Type = "qu(a)".try_into().unwrap();
        let y: Type = "qu(true)".try_into().unwrap();
        let mut bind = vec![];
        assert!(x.lift().bind(false, &y, &mut bind));
    }

    #[test]
    fn test_app_to_has_bound() {
        let a: Type = "a".try_into().unwrap();
        let b: Type = "b".try_into().unwrap();
        assert!(a.app_to_has_bound(&a, &b, &b));
        assert!(a.app_to_has_bound(&a, &b.clone().lift(), &b));
        assert!(a.app_to_has_bound(&a.clone().lift(), &b, &b));

        let all_a: Type = "all(a)".try_into().unwrap();
        assert!(!a.app_to_has_bound(&all_a, &b, &b));
        assert!(all_a.app_to_has_bound(&all_a, &b, &b));

        let all_ab: Type = "all(a -> b)".try_into().unwrap();
        let all_aa: Type = "all(a -> a)".try_into().unwrap();
        assert!(all_ab.has_bound(&all_aa));
        assert!(all_ab.app_to_has_bound(&all_aa, &b, &b));
        assert!(!all_aa.app_to_has_bound(&all_ab, &b, &b));

        let ab: Type = "a => b".try_into().unwrap();
        let fun_ab: Type = "a -> b".try_into().unwrap();
        assert!(fun_ab.app_to_has_bound(&ab, &b, &b));
    }

    #[test]
    fn test_sym() {
        let a: Type = "qu'".try_into().unwrap();
        assert_eq!(a, sym("qu"));

        let a: Type = "qu(a)".try_into().unwrap();
        assert_eq!(a, app(sym("qu"), ty("a")));
        assert!(a.has_bound(&a));

        let a: Type = "qu'(a)".try_into().unwrap();
        assert_eq!(a, app(sym("qu"), ty("a")));

        let a: Type = "qu(a) & (a == b)^true  ->  qu(b)".try_into().unwrap();
        assert_eq!(a, pow(app(sym("qu"), ty("b")),
            and(app(sym("qu"), ty("a")), tauto(eq(ty("a"), ty("b"))))));

        let a: Type = "q(a, b)".try_into().unwrap();
        assert_eq!(a, app(app(sym("q"), ty("a")), ty("b")));
    }
}
