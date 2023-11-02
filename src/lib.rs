#![doc = include_str!("../README.md")]

use std::sync::Arc;
use rustc_hash::FxHashSet as HashSet;
use rustc_hash::FxHashMap as HashMap;
use std::fmt;
use std::path::Path;
use piston_meta::Range;
use lazy_static::lazy_static;
use meta_cache::MetaCache;

pub mod parsing;
pub mod meta_cache;

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
    /// Stores symbols.
    pub symbols: Vec<Arc<String>>,
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
            symbols: vec![],
            terms: vec![],
            term_names: vec![],
            proofs: vec![],
            proof_cache: HashSet::default(),
        }
    }

    pub fn is_symbol_declared(&self, symbol: &str) -> bool {
        for s in &self.symbols {
            if &**s == symbol {return true}
        }
        false
    }

    pub fn is_type_declared(&self, ty: &Type, sym_blocks: &mut Vec<Arc<String>>) -> bool {
        use Type::*;

        match ty {
            Sym(s) => {
                self.is_symbol_declared(s) ||
                sym_blocks.iter().any(|n| n == s)
            }
            True | False | Ty(_) | AllTy(_) => true,
            Pow(ab) | And(ab) | Or(ab) | Imply(ab) |
            App(ab) | Sd(ab) | Jud(ab) | Comp(ab) | Q(ab) | Pair(ab) =>
                self.is_type_declared(&ab.0, sym_blocks) &&
                self.is_type_declared(&ab.1, sym_blocks),
            All(a) | Nec(a) | Pos(a) | Qu(a) => self.is_type_declared(a, sym_blocks),
            SymBlock(ab) => {
                let n = sym_blocks.len();
                sym_blocks.push(ab.0.clone());
                let res = self.is_type_declared(&ab.1, sym_blocks);
                sym_blocks.truncate(n);
                res
            }
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
        file: &str,
        script: &str,
        search: &mut Search,
        loader: &mut Loader,
        meta_cache: &MetaCache,
    ) -> Result<Option<(bool, Arc<String>)>, String> {
        parsing::run_str(file, self, script, search, loader, meta_cache)
    }

    pub fn run(
        &mut self,
        file: &str,
        search: &mut Search,
        loader: &mut Loader,
        meta_cache: &MetaCache,
    ) -> Result<Option<(bool, Arc<String>)>, String> {
        use std::fs::File;
        use std::io::Read;

        let mut data_file =
        File::open(file).map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        let mut data = String::new();
        data_file.read_to_string(&mut data)
            .map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        self.run_str(file, &data, search, loader, meta_cache)
    }

    pub fn new_term(
        &mut self,
        (name, t): (Arc<String>, Term),
        is_use: bool,
        search: &mut Search
    ) -> Result<(), String> {
        let ty = t.get_type();
        if !is_use && !self.is_type_declared(&ty, &mut vec![]) {
            return Err("Some symbols where not declared".into())
        }
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
    pub fn fun<F: FnOnce(&mut Context, &mut Search) -> Result<bool, (Range, String)>>(
        &mut self,
        range: Range,
        name: Arc<String>,
        ty: Type,
        search: &mut Search,
        f: F
    ) -> Result<(), (Range, String)> {
        if let Type::Pow(_) = &ty {
            let mut ctx = Context::new();
            ctx.symbols = self.symbols.clone();
            let unsafe_flag = f(&mut ctx, search)?;
            if ctx.prove(ty.clone(), search) && ctx.safe(&ty) {
                if !unsafe_flag && !ty.is_safe_to_prove() {
                    return Err((range, format!("Not safe to prove `{}`\nUse `unsafe return`", ty.to_str(true, None))));
                }
                // Force the proof since it is safe.
                let ty = ty.lift();
                self.add_proof(ty.clone());
                let is_use = false;
                self.new_term((name, Term::FunDecl(ty)), is_use, search)
                    .map_err(|err| (range, err))?;
                Ok(())
            } else {Err((range, format!("Could not prove `{}`", ty.to_str(true, None))))}
        } else {Err((range, "Expected `->`".into()))}
    }

    #[must_use]
    pub fn lam<F: FnOnce(&mut Context, &mut Search) -> Result<bool, (Range, String)>>(
        &mut self,
        range: Range,
        name: Arc<String>,
        ty: Type,
        search: &mut Search,
        f: F
    ) -> Result<(), (Range, String)> {
        if let Type::Imply(_) = ty {
            let mut ctx = self.clone();
            let unsafe_flag = f(&mut ctx, search)?;
            if ctx.prove(ty.clone(), search) {
                if !unsafe_flag && !ty.is_safe_to_prove() {
                    return Err((range, format!("Not safe to prove `{}`", ty.to_str(true, None))));
                }

                // Force the proof since it is safe.
                self.add_proof(ty.clone());
                let is_use = false;
                self.new_term((name, Term::LamDecl(ty)), is_use, search)
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
            Sd(_) if proof.symbolic_distinct() => true,
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
    pub fn prove_depth(&mut self, ty: Type, depth: u32, _search: &mut Search) -> bool {
        if depth == 0 {return false}
        if self.has_proof(&ty) {return true}
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
    static ref MATCH_TYPE: Type = {
        // `(a | b) & ((a => c) & (b => c))  ->  c`.
        pow(ty("c"), and(or(ty("a"), ty("b")), and(imply(ty("a"), ty("c")), imply(ty("b"), ty("c")))))
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
                            return if Type::All(Box::new(ty_f.clone())).has_bound(ty) {
                                Ok(())
                            } else {
                                Err(format!("Expected `{}`, found `{}`", ty, ty_f))
                            };
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
                                Err(format!("Type check error #200\nExpected:\n\n  {}\n\n\
                                    Could not apply:\n\n  {}\n\nTo:\n\n  {}\n",
                                    t, ty_f.to_str(true, None), ty_arg))
                            };
                        } else if let Type::Imply(ab) = &ty_f {
                            return if ty_arg.app_to_has_bound(&ab.0, &ab.1, t) {
                                Ok(())
                            } else {
                                Err(format!("Expected:\n\n  {}\n\n\
                                    Could not apply:\n\n  {}\n\n To:\n\n  {}\n",
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
                let ty_f: Type = if args.len() == 1 {pow(crate::ty("a"), Type::False)}
                    else {MATCH_TYPE.clone()};
                if let Type::Pow(ab) = ty_f.lift() {
                    if ty_arg.app_to_has_bound(&ab.1, &ab.0, t) {
                        return Ok(());
                    };
                }
                return Err("Internal error in type checker".into());
            }
            Axiom(t) => {
                if t.has_bound(ty) {return Ok(())}
                else {return Err(format!(
                    "Type check error #300\nExpected `{}`, found `{}`",
                    ty, t
                ))}
            }
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
    /// Symbolic distinction.
    Sd(Box<(Type, Type)>),
    /// Type judgement.
    Jud(Box<(Type, Type)>),
    /// Function composition.
    Comp(Box<(Type, Type)>),
    /// Necessary (modal logic).
    Nec(Box<Type>),
    /// Possibly (modal logoc).
    Pos(Box<Type>),
    /// Path semantical qubit.
    Qu(Box<Type>),
    /// Path semantical quality.
    Q(Box<(Type, Type)>),
    /// Avatar Logic pair.
    Pair(Box<(Type, Type)>),
    /// Symbolic block (used to freeze variables).
    SymBlock(Box<(Arc<String>, Type)>),
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
    Sd,
    Jud,
    Comp,
    Nec,
    Pos,
    Qu,
    Q,
    Pair,
    SymBlock,
}

fn needs_parens(ty: &Type, parent_op: Option<Op>) -> bool {
    use Type::*;

    if ty.as_not().is_some() ||
       ty.as_nec().is_some() ||
       ty.as_pos().is_some() ||
       ty.as_qu().is_some() {
        if let Some(Op::Pow) = parent_op {return true};

        return false;
    }
    if ty.as_excm().is_some() {return false};
    match ty {
        True | False | Ty(_) | AllTy(_) | All(_) |
        App(_) | Sym(_) | Nec(_) | Qu(_) | Pair(_) => false,
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
            Sd(_) => Some(Op::Sd),
            Jud(_) => Some(Op::Jud),
            Comp(_) => Some(Op::Comp),
            Nec(_) => Some(Op::Nec),
            Pos(_) => Some(Op::Pos),
            Qu(_) => Some(Op::Qu),
            Q(_) => Some(Op::Q),
            Pair(_) => Some(Op::Pair),
            SymBlock(_) => Some(Op::SymBlock),
        }
    }

    pub fn symbolic_distinct(&self) -> bool {
        if let Type::Sd(ab) = self {
            if let (Type::Sym(a), Type::Sym(b)) = &**ab {
                if a != b {return true} else {false}
            } else {false}
        } else {false}
    }

    pub fn as_not(&self) -> Option<&Type> {
        if let Type::Imply(ab) = self {
            if let Type::False = ab.1 {Some(&ab.0)} else {None}
        } else {None}
    }

    pub fn as_nec(&self) -> Option<&Type> {
        if let Type::Nec(a) = self {Some(a)} else {None}
    }

    pub fn as_pos(&self) -> Option<&Type> {
        if let Type::Pos(a) = self {Some(a)} else {None}
    }

    pub fn as_qu(&self) -> Option<&Type> {
        if let Type::Qu(a) = self {Some(a)} else {None}
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

    pub fn as_multi_app(&self) -> Option<(&Type, Vec<&Type>)> {
        let mut args: Vec<&Type> = vec![];
        let mut ty = self;
        loop {
            if let Type::App(ab) = ty {
                args.push(&ab.1);
                ty = &ab.0;
            } else {
                if args.len() < 2 {return None}
                else {
                    args.reverse();
                    return Some((ty, args))
                }
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
            return write!(w, "{}'({})", a, b);
        }
        if let Some((f, args)) = self.as_multi_app() {
            write!(w, "{}(", f.to_str(false, None))?;
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
            All(a) => write!(w, "all({})", a.to_str(true, op))?,
            Sym(a) => write!(w, "{}'", a)?,
            App(ab) => write!(w, "{}({})", ab.0.to_str(false, op), ab.1)?,
            Sd(ab) => write!(w, "sd({}, {})", ab.0, ab.1)?,
            Jud(ab) => write!(w, "{} : {}", ab.0.to_str(false, op), ab.1.to_str(true, op))?,
            Comp(ab) => write!(w, "{} . {}", ab.0, ab.1)?,
            Nec(a) => write!(w, "□{}", a.to_str(false, op))?,
            Pos(a) => write!(w, "◇{}", a.to_str(false, op))?,
            Qu(a) => write!(w, "~{}", a.to_str(false, op))?,
            Q(ab) => write!(w, "{} ~~ {}", ab.0.to_str(false, op), ab.1.to_str(false, op))?,
            Pair(ab) => write!(w, "({}, {})", ab.0.to_str(true, op), ab.1.to_str(true, op))?,
            SymBlock(ab) => write!(w, "sym({}, {})", ab.0, ab.1.to_str(true, op))?,
        }
        Ok(())
    }
}

impl TryFrom<&str> for Type {
    type Error = String;
    fn try_from(s: &str) -> Result<Type, String> {
        parsing::parse_ty_str(s, &MetaCache::new())
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
            App(ab) => {
                if let SymBlock(_) = &ab.0 {false} else {true}
            }
            Sd(_) => true,
            Jud(_) => true,
            Comp(_) => true,
            Nec(_) => true,
            Pos(_) => true,
            Qu(_) => true,
            Q(_) => true,
            Pair(_) => true,
            SymBlock(ab) => ab.1.is_safe_to_prove(),
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
            Sd(ab) => sd(ab.0.lift(), ab.1.lift()),
            Jud(ab) => jud(ab.0.lift(), ab.1.lift()),
            Comp(ab) => comp(ab.0.lift(), ab.1.lift()),
            Nec(a) => nec(a.lift()),
            Pos(a) => pos(a.lift()),
            Qu(a) => qu(a.lift()),
            Q(ab) => q(ab.0.lift(), ab.1.lift()),
            Pair(ab) => pair(ab.0.lift(), ab.1.lift()),
            SymBlock(ab) => sym_block(ab.0.clone(), ab.1.lift()),
        }
    }

    #[must_use]
    pub fn bind(&self, contra: bool, val: &Type, bind: &mut Vec<(Type, Type)>) -> bool {
        use Type::*;

        fn bind_ty<F: FnOnce(&mut Vec<(Type, Type)>)>(
            bind: &mut Vec<(Type, Type)>,
            a: &Type,
            b: &Type,
            f: F,
        ) -> bool {
            let mut found = false;
            for (ty, val) in bind.iter() {
                if ty == a {
                    if val != b && val != &b.clone().lift() {
                        return false;
                    }
                    found = true;
                    break;
                }
            }
            if !found {f(bind)};
            true
        }

        match if contra {(val, self)} else {(self, val)} {
            (True, True) => true,
            (False, False) => true,
            (Ty(a), Ty(b)) => a == b,
            (Sym(a), Sym(b)) => {
                let (a, b) = if contra {(b, a)} else {(a, b)};
                for (ty, v) in bind.iter() {
                    if let Type::Sym(name) = ty {
                        if name == a && val == v {return true}
                    }
                }
                a == b
            }
            (Sym(a), b) if !contra => {
                for (ty, val) in bind.iter() {
                    if let Type::Sym(name) = ty {
                        if name == a && b == val {return true}
                    }
                }
                false
            }
            (b, Sym(a)) if contra => {
                for (ty, val) in bind.iter() {
                    if let Type::Sym(name) = ty {
                        if name == a && b == val {return true}
                    }
                }
                false
            }
            (_, AllTy(_)) if contra => {
                bind_ty(bind, self, val, |bind|
                    bind.push((self.clone(), val.clone())))
            }
            (AllTy(_), _) if !contra => {
                bind_ty(bind, self, val, |bind|
                    bind.push((self.clone(), val.clone())))
            }
            (_, AllTy(_)) if !contra => true,
            (AllTy(_), _) if contra => true,
            (Nec(a), Nec(b)) |
            (Pos(a), Pos(b)) |
            (Qu(a), Qu(b)) => {
                let (a, b) = if contra {(b, a)} else {(a, b)};
                a.bind(contra, b, bind)
            }
            (And(ab), And(cd)) |
            (Or(ab), Or(cd)) |
            (App(ab), App(cd)) |
            (Sd(ab), Sd(cd)) |
            (Jud(ab), Jud(cd)) |
            (Comp(ab), Comp(cd)) |
            (Q(ab), Q(cd)) |
            (Pair(ab), Pair(cd)) => {
                let (ab, cd) = if contra {(cd, ab)} else {(ab, cd)};
                if !ab.0.bind(contra, &cd.0, bind) {return false};
                if !ab.1.bind(contra, &cd.1, bind) {return false};
                true
            }
            (App(ab), x) if !contra => {
                if let Type::SymBlock(s_ab) = &ab.0 {
                    let n = bind.len();
                    bind.push((Type::Sym(s_ab.0.clone()), ab.1.clone()));
                    let res = s_ab.1.bind(contra, &x, bind);
                    if res {
                        let ty = s_ab.1.replace(bind);
                        bind.truncate(n);
                        bind.push((self.clone(), ty));
                        return true;
                    } else {
                        bind.truncate(n);
                    }
                }
                false
            }
            (x, App(ab)) if contra => {
                if let Type::SymBlock(s_ab) = &ab.0 {
                    let n = bind.len();
                    bind.push((Type::Sym(s_ab.0.clone()), ab.1.clone()));
                    let res = s_ab.1.bind(contra, &x, bind);
                    if res {
                        let ty = s_ab.1.replace(bind);
                        bind.truncate(n);
                        bind.push((self.clone(), ty));
                        return true;
                    } else {
                        bind.truncate(n);
                    }
                }
                false
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
                let mut bind: Vec<(Type, Type)> = bind.iter()
                    .filter(|(a, b)| {
                        if contra {
                            if let Sym(_) = b {true} else {false}
                        } else {
                            if let Sym(_) = a {true} else {false}
                        }
                    })
                    .map(|(a, b)| if contra {(b.clone(), a.clone())}
                                  else {(a.clone(), b.clone())})
                    .collect();
                if a.bind(contra, b, &mut bind) {
                    bind.push((self.clone(), All(Box::new(a.replace(&bind)))));
                    true
                } else {false}
            }
            (All(a), b) if !contra => a.bind(contra, b, bind),
            (SymBlock(ab), SymBlock(cd)) => {
                let (ab, cd) = if contra {(cd, ab)} else {(ab, cd)};
                let n = bind.len();
                bind.push((Sym(ab.0.clone()), Sym(cd.0.clone())));
                let res = ab.1.bind(contra, &cd.1, bind);
                if res {
                    let ty = self.replace(bind);
                    bind.truncate(n);
                    bind.push((self.clone(), ty));
                } else {bind.truncate(n)};
                res
            }
            (_, App(ab)) if !contra => {
                if let Type::SymBlock(s_ab) = &ab.0 {
                    let _ = self.bind(contra, &s_ab.1, bind);
                    let mut bind2 = vec![];
                    let contra = false;
                    if val.bind(contra, &self.replace(bind), &mut bind2) {
                        let ty = val.replace(&bind2);
                        if ty.has_(contra, &self) {
                            bind.push((self.clone(), val.clone()));
                            return true;
                        }
                    }
                }
                false
            }
            (App(ab), _) if contra => {
                if let Type::SymBlock(s_ab) = &ab.0 {
                    let _ = self.bind(contra, &s_ab.1, bind);
                    let mut bind2 = vec![];
                    let contra = true;
                    if val.bind(contra, &self.replace(bind), &mut bind2) {
                        let ty = val.replace(&bind2);
                        if ty.has_(contra, self) {
                            bind.push((self.clone(), val.clone()));
                            return true;
                        }
                    }
                }
                false
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
            Sd(ab) => sd(ab.0.replace(bind), ab.1.replace(bind)),
            Jud(ab) => jud(ab.0.replace(bind), ab.1.replace(bind)),
            Comp(ab) => comp(ab.0.replace(bind), ab.1.replace(bind)),
            Nec(a) => nec(a.replace(bind)),
            Pos(a) => pos(a.replace(bind)),
            Qu(a) => qu(a.replace(bind)),
            Q(ab) => q(ab.0.replace(bind), ab.1.replace(bind)),
            Pair(ab) => pair(ab.0.replace(bind), ab.1.replace(bind)),
            SymBlock(ab) => {
                let mut a = ab.0.clone();
                for (arg, val) in bind {
                    if let Type::Sym(name) = arg {
                        if name == &a {
                            if let Type::Sym(other_name) = val {
                                a = other_name.clone();
                                break;
                            }
                        }
                    }
                }
                sym_block(a, ab.1.replace(bind))
            }
        }
    }

    /// Prepease type for Herbrandization.
    pub fn de_all(&self) -> Option<Type> {
        use Type::*;

        match self {
            True | False | Ty(_) | Sym(_) => Some(self.clone()),
            All(s) => Some((**s).clone()),
            And(ab) => Some(and(ab.0.de_all()?, ab.1.de_all()?)),
            Or(ab) => Some(or(ab.0.de_all()?, ab.1.de_all()?)),
            Imply(ab) => Some(imply(ab.0.de_all()?, ab.1.de_all()?)),
            Pair(ab) => Some(pair(ab.0.de_all()?, ab.1.de_all()?)),
            App(ab) => Some(app(ab.0.de_all()?, ab.1.de_all()?)),
            Sd(ab) => Some(sd(ab.0.de_all()?, ab.1.de_all()?)),
            Jud(ab) => Some(jud(ab.0.de_all()?, ab.1.de_all()?)),
            Comp(ab) => Some(comp(ab.0.de_all()?, ab.1.de_all()?)),
            Q(ab) => Some(q(ab.0.de_all()?, ab.1.de_all()?)),
            Pow(ab) => Some(pow(ab.0.de_all()?, ab.1.de_all()?)),
            Nec(a) => Some(nec(a.de_all()?)),
            Pos(a) => Some(pos(a.de_all()?)),
            Qu(a) => Some(qu(a.de_all()?)),
            SymBlock(ab) => Some(sym_block(ab.0.clone(), ab.1.de_all()?)),
            AllTy(_) => None,
        }
    }

    pub fn herbrandization(&self, f_in: &Type, f_out: &Type, exp_t: &Type) -> bool {
        use Type::*;

        if let All(exp) = exp_t {
            let s = &if let Some(x) = self.de_all() {x} else {return false};
            let mut bind = vec![];
            let contra = true;
            if f_in.bind(contra, s, &mut bind) {
                if f_out.replace(&bind).has_(false, exp) {return true}
            }
        }
        false
    }

    /// Whether application type checks.
    pub fn app_to_has_bound(&self, f_in: &Type, f_out: &Type, exp_t: &Type) -> bool {
        let mut bind = vec![];
        let contra = true;
        if f_in.bind(contra, self, &mut bind) {
            if f_out.replace(&bind).has_(false, exp_t) {return true} else {false}
        } else {self.herbrandization(f_in, f_out, exp_t)}
    }

    pub fn has_bound(&self, other: &Type) -> bool {
        let mut bind = vec![];
        let contra = false;
        if self.bind(contra, other, &mut bind) {
            self.replace(&bind).has_(contra, other)
        } else {false}
    }

    pub fn has_bound_contra(&self, other: &Type) -> bool {
        let mut bind = vec![];
        let contra = true;
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
            
            (All(a), All(b)) |
            (Nec(a), Nec(b)) |
            (Pos(a), Pos(b)) |
            (Qu(a), Qu(b)) if a.has_(contra, b) => true,
            
            (All(a), b) if !contra => a.has_(contra, b),
            (a, All(b)) if contra => a.has_(contra, b),
            (Sym(a), Sym(b)) if a == b => true,
            
            (App(ab), App(cd)) |
            (Sd(ab), Sd(cd)) |
            (Jud(ab), Jud(cd)) |
            (Comp(ab), Comp(cd)) |
            (Q(ab), Q(cd)) |
            (Pair(ab), Pair(cd))
            if ab.0.has_(contra, &cd.0) && ab.1.has_(contra, &cd.1) => true,
            
            (SymBlock(ab), SymBlock(cd)) => ab.1.has_(contra, &cd.1),
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
    pub function_files: HashMap<Arc<String>, usize>,
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
    pub fn new(dir: Arc<String>, meta_cache: &MetaCache) -> Result<Loader, String> {
        use rayon::prelude::*;
        use std::sync::Mutex;

        let mut loader = Loader {
            dir: dir.clone(),
            functions: HashMap::default(),
            function_files: HashMap::default(),
            run: false,
            dependencies: vec![],
            trace: vec![],
            silent: false,
            files: vec![],
        };

        let std = parsing::lib_str(include_str!("../source/std/Hooo.config"), meta_cache)?;
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
            match ctx.run(file, &mut search, &mut loader, meta_cache) {
                Ok(_) => {}
                Err(err) => {
                    let mut error = error.lock().unwrap();
                    *error = Err(
                        format!("Load error #100\nIn file `{}`\n{}", file, err));
                    return None;
                }
            }
            for (name, ty) in loader.functions.into_iter() {
                tx.send((name, (ty, i))).unwrap();
            }
            for sym in ctx.symbols.into_iter() {
               tx.send((sym.clone(), (Type::Sym(sym), i))).unwrap();
            }
            Some(i)
        }).while_some().max();

        drop(tx);

        let error = error.lock().unwrap();
        let _ = error.as_ref().map_err(|err| err.clone())?;

        while let Ok((name, (ty, i))) = rx.recv() {
            loader.functions.insert(name.clone(), ty);
            loader.function_files.insert(name, i);
        }

        loader.files = files;

        loader.run = true;

        Ok(loader)
    }

    pub fn load_info(&mut self, meta_cache: &MetaCache) -> Result<Option<LibInfo>, String> {
        let path = Path::new(&**self.dir).join("Hooo.config");
        if path.exists() {
            match LibInfo::from_path(&path, meta_cache) {
                Ok(x) => {
                    for dep in &x.dependencies {
                        match dep {
                            Dep::Path(p) => {
                                let dep_path = Path::new(&**self.dir).join(&**p).join("Hooo.config");
                                match LibInfo::from_path(&dep_path, meta_cache) {
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
    pub fn from_path(path: &Path, meta_cache: &MetaCache) -> Result<LibInfo, String> {
        use std::fs::File;
        use std::io::Read;

        let file = path.to_str().unwrap();
        let mut data_file =
        File::open(path).map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        let mut data = String::new();
        data_file.read_to_string(&mut data)
            .map_err(|err| format!("Could not open `{}`, {}", file, err))?;
        parsing::lib_str(&data, meta_cache)
    }
}

pub fn var(a: &str, t: Type) -> (Arc<String>, Term) {(Arc::new(a.into()), Term::Var(t))}

pub fn ty(a: &str) -> Type {Type::Ty(Arc::new(a.into()))}
pub fn all_ty(a: &str) -> Type {Type::AllTy(Arc::new(a.into()))}
pub fn pow(a: Type, b: Type) -> Type {Type::Pow(Box::new((a, b)))}
pub fn and(a: Type, b: Type) -> Type {Type::And(Box::new((a, b)))}
pub fn or(a: Type, b: Type) -> Type {Type::Or(Box::new((a, b)))}
pub fn imply(a: Type, b: Type) -> Type {Type::Imply(Box::new((a, b)))}
pub fn not(a: Type) -> Type {imply(a, Type::False)}
pub fn excm(a: Type) -> Type {or(a.clone(), not(a))}
pub fn eq(a: Type, b: Type) -> Type {and(imply(a.clone(), b.clone()), imply(b, a))}
pub fn pow_eq(a: Type, b: Type) -> Type {and(pow(b.clone(), a.clone()), pow(a, b))}
pub fn tauto(a: Type) -> Type {pow(a, Type::True)}
pub fn para(a: Type) -> Type {pow(Type::False, a)}
pub fn app(a: Type, b: Type) -> Type {Type::App(Box::new((a, b)))}
pub fn all(a: Type) -> Type {Type::All(Box::new(a.lift()))}
pub fn sym(a: &str) -> Type {Type::Sym(Arc::new(a.into()))}
pub fn sd(a: Type, b: Type) -> Type {Type::Sd(Box::new((a, b)))}
pub fn jud(a: Type, b: Type) -> Type {Type::Jud(Box::new((a, b)))}
pub fn comp(a: Type, b: Type) -> Type {Type::Comp(Box::new((a, b)))}
pub fn nec(a: Type) -> Type {Type::Nec(Box::new(a))}
pub fn pos(a: Type) -> Type {Type::Pos(Box::new(a))}
pub fn qu(a: Type) -> Type {Type::Qu(Box::new(a))}
pub fn q(a: Type, b: Type) -> Type {Type::Q(Box::new((a, b)))}
pub fn pair(a: Type, b: Type) -> Type {Type::Pair(Box::new((a, b)))}
pub fn sym_block(a: Arc<String>, b: Type) -> Type {Type::SymBlock(Box::new((a, b)))}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_replace() {
        let mut ctx = Context::new();
        let is_use = false;
        ctx.new_term(var("x", "a^b".try_into().unwrap()), is_use,
            &mut Search::new()).unwrap();
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
    
        let a: Type = "(f, g)(a)".try_into().unwrap();
        assert_eq!(a, app(pair(ty("f"), ty("g")), ty("a")));
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

        let a: Type = "ty'(add', nat' & nat' -> nat')".try_into().unwrap();
        assert_eq!(a, app(app(sym("ty"), sym("add")), pow(sym("nat"), and(sym("nat"), sym("nat")))));

        let a: Type = "f(a)".try_into().unwrap();
        assert_eq!(a, app(ty("f"), ty("a")));
        assert_eq!(format!("{}", a), "f(a)");

        let a: Type = "f(a, b)".try_into().unwrap();
        assert_eq!(a, app(app(ty("f"), ty("a")), ty("b")));
        assert_eq!(format!("{}", a), "f(a, b)");

        let a: Type = "sym(a, a')".try_into().unwrap();
        assert_eq!(a, sym_block(Arc::new("a".into()), sym("a")));
        assert_eq!(format!("{}", a), "sym(a, a')");
    }

    #[test]
    fn test_parse_sd() {
        let a: Type = "sd(a, b)".try_into().unwrap();
        assert_eq!(a, sd(ty("a"), ty("b")));
        assert_eq!(format!("{}", a), "sd(a, b)".to_string());
    }

    #[test]
    fn test_parse_jud() {
        let a: Type = "a : b".try_into().unwrap();
        assert_eq!(a, jud(ty("a"), ty("b")));
        assert_eq!(format!("{}", a), "a : b".to_string());

        let a: Type = "a : b -> c".try_into().unwrap();
        assert_eq!(a, jud(ty("a"), pow(ty("c"), ty("b"))));
        assert_eq!(format!("{}", a), "a : b -> c".to_string());

        let a: Type = "(a => b) : b -> c".try_into().unwrap();
        assert_eq!(format!("{}", a), "(a => b) : b -> c".to_string());
    }

    #[test]
    fn test_parse_modal() {
        let a: Type = "□a".try_into().unwrap();
        assert_eq!(a, nec(ty("a")));
        assert_eq!(format!("{}", a), "□a".to_string());

        let a: Type = "◇a".try_into().unwrap();
        assert_eq!(a, pos(ty("a")));
        assert_eq!(format!("{}", a), "◇a".to_string());
    }

    #[test]
    fn test_parse_ps() {
        let a: Type = "~a".try_into().unwrap();
        assert_eq!(a, qu(ty("a")));
        assert_eq!(format!("{}", a), "~a".to_string());

        let a: Type = "~a & (a == b)^true  ->  ~b".try_into().unwrap();
        assert_eq!(a, pow(qu(ty("b")), and(qu(ty("a")), tauto(eq(ty("a"), ty("b"))))));

        let a: Type = "a ~~ b".try_into().unwrap();
        assert_eq!(a, q(ty("a"), ty("b")));
        assert_eq!(format!("{}", a), "a ~~ b".to_string());
    }

    #[test]
    fn test_parse_ava() {
        let a: Type = "(a, b)".try_into().unwrap();
        assert_eq!(a, pair(ty("a"), ty("b")));
        assert_eq!(format!("{}", a), "(a, b)".to_string());
    }

    #[test]
    fn test_parse_comp() {
        let a: Type = "f . g".try_into().unwrap();
        assert_eq!(a, comp(ty("f"), ty("g")));
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

        let a: Type = "q'(a, b)".try_into().unwrap();
        assert_eq!(format!("{}", a), "q'(a, b)".to_string());
    
        let a: Type = "all(a -> b)".try_into().unwrap();
        assert_eq!(format!("{}", a), "all(a -> b)".to_string());
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

        let x: Type = "all(a)".try_into().unwrap();
        let y: Type = "b".try_into().unwrap();
        assert!(x.has_bound(&y));

        let x: Type = "all(a -> a)".try_into().unwrap();
        let y: Type = "all(a -> b)".try_into().unwrap();
        assert!(!x.has_bound(&y));
        assert!(y.has_bound(&x));
        assert!(x.has_bound_contra(&y));
        assert!(!y.has_bound_contra(&x));
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
        assert!(a.bind(false, &a.clone().lift(), &mut bind));

        let x: Type = "a^b".try_into().unwrap();
        let mut bind = vec![];
        assert!(x.clone().lift().bind(false, &x, &mut bind));
        let mut bind = vec![];
        assert!(x.clone().lift().bind(true, &x, &mut bind));
        let mut bind = vec![];
        assert!(x.bind(false, &x.clone().lift(), &mut bind));
        let mut bind = vec![];
        assert!(x.bind(true, &x.clone().lift(), &mut bind));

        let x: Type = "qu'(a)".try_into().unwrap();
        let y: Type = "qu'(true)".try_into().unwrap();
        let mut bind = vec![];
        assert!(x.lift().bind(false, &y, &mut bind));

        let x: Type = "(~b)^(~a & (a == b)^true)".try_into().unwrap();
        let mut bind = vec![];
        assert!(x.bind(false, &x, &mut bind));
        let mut bind = vec![];
        assert!(x.clone().lift().bind(false, &x, &mut bind));
        assert!(x.has_bound(&x));
        
        let a: Type = "(a == b)^true".try_into().unwrap();
        let b: Type = "(x' == y')^true".try_into().unwrap();
        assert!(a.lift().bind(true, &b, &mut vec![]));
    
        let a: Type = and(tauto(eq(all_ty("a"), all_ty("b"))), all_ty("b"));
        let b: Type = and(tauto(eq(ty("x"), ty("y"))).lift(), ty("y"))
            .try_into().unwrap();
        assert!(a.bind(true, &b, &mut vec![]));
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

        let a: Type = "qu'(a)".try_into().unwrap();
        assert_eq!(a, app(sym("qu"), ty("a")));
        assert!(a.has_bound(&a));

        let a: Type = "qu'(a)".try_into().unwrap();
        assert_eq!(a, app(sym("qu"), ty("a")));

        let a: Type = "qu'(a) & (a == b)^true  ->  qu'(b)".try_into().unwrap();
        assert_eq!(a, pow(app(sym("qu"), ty("b")),
            and(app(sym("qu"), ty("a")), tauto(eq(ty("a"), ty("b"))))));

        let a: Type = "q'(a, b)".try_into().unwrap();
        assert_eq!(a, app(app(sym("q"), ty("a")), ty("b")));

        let a: Type = "sym(a, a')".try_into().unwrap();
        let b: Type = "sym(b, b')".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(b.has_bound(&a));
        assert!(a.has_bound_contra(&b));
        assert!(b.has_bound_contra(&a));

        let a: Type = "sym(a, a')(b)".try_into().unwrap();
        let b: Type = "b".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(b.has_bound(&a));
        assert!(a.has_bound_contra(&b));
        assert!(b.has_bound_contra(&a));

        let a: Type = "sym(a, a')(b)".try_into().unwrap();
        let b: Type = "a'".try_into().unwrap();
        assert!(!a.has_bound(&b));
        assert!(!b.has_bound(&a));

        let a: Type = "sym(a, a')(b) -> c".try_into().unwrap();
        let b: Type = "b -> c".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(b.has_bound(&a));
        assert!(a.has_bound_contra(&b));
        assert!(b.has_bound_contra(&a));

        let a: Type = "sym(a, all(b))(a)".try_into().unwrap();
        let b: Type = "b".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(b.has_bound(&a));

        let a: Type = "sym(a, b)(a)".try_into().unwrap();
        let b: Type = "b".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(b.has_bound(&a));
        assert!(a.has_bound_contra(&b));
        assert!(b.has_bound_contra(&a));

        let a: Type = "sym(a, b => c)(a)".try_into().unwrap();
        let b: Type = "b => c".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(b.has_bound(&a));
        assert!(a.has_bound_contra(&b));
        assert!(b.has_bound_contra(&a));

        let a: Type = "all((a => c) -> c)".try_into().unwrap();
        let b: Type = "a => c -> c".try_into().unwrap();
        assert!(a.has_bound(&b));

        let a: Type = "(a => c) -> c".try_into().unwrap();
        let b: Type = "sym(b, a => c)(b) -> c".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(b.has_bound(&a));
        assert!(a.has_bound_contra(&b));
        assert!(b.has_bound_contra(&a));

        let a: Type = "all((e => f) -> f)".try_into().unwrap();
        let b: Type = "sym(b, a => c)(b) -> c".try_into().unwrap();
        assert!(a.has_bound(&b));
        assert!(!b.has_bound(&a));
        assert!(!a.has_bound_contra(&b));
        assert!(!b.has_bound_contra(&a));

        let b: Type = "sym(b, a => d)(b) -> c".try_into().unwrap();
        assert!(!a.has_bound(&b));

        let a: Type = "all((e => f) => f)".try_into().unwrap();
        let b: Type = "sym(b, a => d)(b) => c".try_into().unwrap();
        assert!(!a.has_bound(&b));

        let a: Type = "all(f => (e => f))".try_into().unwrap();
        let b: Type = "c => sym(b, a => c)(b)".try_into().unwrap();
        assert!(!a.has_bound(&b));

        let b: Type = "c => sym(b, a => d)(b)".try_into().unwrap();
        assert!(!a.has_bound(&b));

        let b: Type = "sym(a, all((a' => f) => f))(b)".try_into().unwrap();
        assert!(!a.has_bound(&b));
        assert!(!b.has_bound(&a));

        let a: Type = "sym(a, a')(b)".try_into().unwrap();
        let b: Type = "sym(a, c)(b)".try_into().unwrap();
        assert!(!a.has_bound(&b));
        assert!(!b.has_bound(&a));
        assert!(!a.has_bound_contra(&b));
        assert!(!b.has_bound_contra(&a));

        let a: Type = "sym(a, all(a'))(c)".try_into().unwrap();
        let b: Type = "sym(b, all(b'))(c)".try_into().unwrap();
        assert!(a.has_bound(&b));
    }
}
