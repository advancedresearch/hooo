use crate::*;

use piston_meta::{syntax_errstr, Convert, Range, Syntax};
use lazy_static::lazy_static;
use crate::meta_cache::MetaCache;

fn parse_lib(
    meta_cache: &MetaCache,
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, LibInfo), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut name: Option<Arc<String>> = None;
    let mut version: Option<Arc<String>> = None;
    let mut description: Option<Arc<String>> = None;
    let mut functions: HashMap<Arc<String>, Type> = HashMap::default();
    let mut dependencies: Vec<Dep> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = convert.meta_string("name") {
            convert.update(range);
            name = Some(val);
        } else if let Ok((range, val)) = convert.meta_string("version") {
            convert.update(range);
            version = Some(val);
        } else if let Ok((range, val)) = convert.meta_string("desc") {
            convert.update(range);
            description = Some(val);
        } else if let Ok((range, (name, _, ty))) = parse_var(meta_cache, "fun", convert, ignored) {
            convert.update(range);
            functions.insert(name, ty.lift());
        } else if let Ok((range, val)) = convert.meta_string("dep_path") {
            convert.update(range);
            dependencies.push(Dep::Path(val));
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let name = name.ok_or(())?;
    let version = version.ok_or(())?;
    let description = description.ok_or(())?;
    let lib = LibInfo {
        name, version, description, functions, dependencies,
    };
    Ok((convert.subtract(start), lib))
}

fn run_ctx(
    file: &str,
    meta_cache: &MetaCache,
    ctx: &mut Context,
    search: &mut Search,
    loader: &mut Loader,
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Option<(bool, Arc<String>)>), (Range, String)> {
    let start = convert;
    let start_range = convert.start_node(node)
        .map_err(|()| (convert.ignore(), format!("Expected start node {}", node)))?;
    convert.update(start_range);

    let mut ret: Option<(bool, Arc<String>)> = None;
    let mut unsafe_flag = false;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        }

        match parse_var(meta_cache, "fun_decl", convert, ignored) {
            Ok((range, (name, _, ty))) => {
                convert.update(range);
                if loader.run {
                    let n = loader.trace.len();
                    loader.trace.push(name.clone());
                    if !loader.silent {println!("fn {}", name)};
                    ctx.fun(range, name.clone(), ty.clone(), search, |ctx, search| {
                        match run_ctx(file, meta_cache, ctx, search, loader,
                            "script", convert, ignored)
                        {
                            Ok((range, ret)) => {
                                convert.update(range);
                                if let Some((unsafe_flag, ret)) = ret {
                                    if let Some(ab) = ty.fun_norm() {
                                        if ctx.has_term_ty(&ret, &ab.1) {
                                            ctx.add_proof(ty.clone());
                                        }
                                    }
                                    Ok(unsafe_flag)
                                } else {Ok(false)}
                            }
                            Err(err) => Err(err),
                        }
                    })?;
                    loader.trace.truncate(n);
                } else {
                    if let Type::Pow(_) | Type::Fun(_) = &ty {
                        if loader.functions.contains_key(&name) {
                            return Err((range, format!("Already has function `{}`", name)));
                        }

                        loader.functions.insert(name, ty.lift());
                    }
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        if let Ok((range, val)) = convert.meta_string("sym") {
            convert.update(range);
            if loader.load_fun(&[], &val).is_ok() {
                if let Some(i) = loader.function_files.get(&val) {
                    let other_file = &loader.files[*i];
                    if file != other_file {
                        return Err((range, format!(
                            "Name `{}` already declared in `{}`.\n\
                            Try `use {};` instead.",
                            val, loader.files[*i], val)));
                    }
                }
            }
            ctx.symbols.push(val);
            continue;
        }

        if !loader.run {
            let range = convert.ignore();
            convert.update(range);
            continue;
        }

        match parse_var(meta_cache, "axiom", convert, ignored) {
            Ok((range, (name, args, ty))) => {
                convert.update(range);
                if loader.run {
                    if args.len() == 0 {
                        let is_use = false;
                        ctx.new_term((name, Term::Axiom(ty)), is_use, search)
                            .map_err(|err| (range, err))?;
                    } else {
                        return Err((range, "Parsing axiom".into()));
                    }
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        match parse_var(meta_cache, "var", convert, ignored) {
            Ok((range, (name, args, ty))) => {
                convert.update(range);
                if loader.run {
                    if args.len() == 0 {
                        let is_use = false;
                        ctx.new_term((name, Term::Var(ty)), is_use, search)
                            .map_err(|err| (range, err))?;
                    } else {
                        return Err((range, "Parsing variable".into()));
                    }
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        match parse_var(meta_cache, "app", convert, ignored) {
            Ok((range, (name, args, ty))) => {
                convert.update(range);
                if loader.run {
                    if args.len() >= 1 {
                        let is_use = false;
                        ctx.new_term(
                            (name,
                             Term::App(
                                args[0].clone(),
                                args[1..].into(), ty)),
                            is_use, search)
                            .map_err(|err| (range, err))?;
                    } else {
                        return Err((range, "Parsing application: Expected arguments".into()));
                    }
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        match parse_var(meta_cache, "match", convert, ignored) {
            Ok((range, (name, args, ty))) => {
                convert.update(range);
                if loader.run {
                    if args.len() == 3 || args.len() == 1 {
                        let is_use = false;
                        ctx.new_term(
                            (name, Term::Match(args, ty)), is_use, search)
                            .map_err(|err| (range, err))?;
                    } else {
                        return Err((range, "Parsing application".into()));
                    }
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        match parse_var(meta_cache, "check", convert, ignored) {
            Ok((range, (name, _, ty))) => {
                convert.update(range);
                if loader.run {
                    let is_use = false;
                    ctx.new_term((name, Term::Check(ty)), is_use, search)
                        .map_err(|err| (range, err))?;
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        match parse_var(meta_cache, "lam_decl", convert, ignored) {
            Ok((range, (name, _, ty))) => {
                convert.update(range);
                if loader.run {
                    if !loader.silent {println!("lam {}", name)};
                    ctx.lam(range, name.clone(), ty.clone(), search, |ctx, search| {
                        match run_ctx(file, meta_cache, ctx, search, loader,
                            "script", convert, ignored)
                        {
                            Ok((range, ret)) => {
                                convert.update(range);
                                if let Some((unsafe_flag, ret)) = ret {
                                    if let Type::Imply(ab) = &ty {
                                        if ctx.has_term_ty(&ret, &ab.1) {
                                            ctx.add_proof(ty.clone());
                                        }
                                    }
                                    Ok(unsafe_flag)
                                } else {Ok(false)}
                            }
                            Err(err) => Err(err),
                        }
                    })?;
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        if let Ok((range, val)) = convert.meta_string("return") {
            convert.update(range);
            if loader.run {
                if !ctx.has_term(&val) {return Err((range, format!("Could not find `{}`", val)))};

                ret = Some((unsafe_flag, val));
                unsafe_flag = false;
            }
        } else if let Ok((range, _)) = convert.meta_bool("unsafe") {
            convert.update(range);
            unsafe_flag = true;
        } else if let Ok((range, (ns, fun))) = parse_use("use", convert, ignored) {
            convert.update(range);
            if loader.run {
                let ty = loader.load_fun(&ns, &fun).map_err(|err| (range, err))?;
                match ty {
                    Type::Pow(_) | Type::Fun(_) => {
                        let is_use = true;
                        ctx.new_term((fun, Term::FunDecl(ty)), is_use, search)
                            .map_err(|err| (range, err))?;
                    }
                    Type::Sym(name) => {
                        ctx.symbols.push(name);
                    }
                    _ => return Err((range, format!("Unexpected type `{}`", ty))),
                }
            }
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    Ok((convert.subtract(start), ret))
}

fn parse_use(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, (Vec<Arc<String>>, Arc<String>)), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut fun: Option<Arc<String>> = None;
    let mut ns: Vec<Arc<String>> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = convert.meta_string("fun") {
            convert.update(range);
            fun = Some(val);
        } else if let Ok((range, val)) = convert.meta_string("ns") {
            convert.update(range);
            ns.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let fun = fun.ok_or(())?;
    Ok((convert.subtract(start), (ns, fun)))
}

fn parse_var(
    meta_cache: &MetaCache,
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, (Arc<String>, Vec<Arc<String>>, Type)), Option<String>> {
    let start = convert;
    let start_range = convert.start_node(node).map_err(|_| None)?;
    convert.update(start_range);

    let mut name: Option<Arc<String>> = None;
    let mut args: Vec<Arc<String>> = vec![];
    let mut ty: Option<Type> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = convert.meta_string("name") {
            convert.update(range);
            name = Some(val);
        } else if let Ok((range, val)) = convert.meta_string("arg") {
            convert.update(range);
            args.push(val);
        } else if let Ok((range, val)) = convert.meta_string("ty") {
            convert.update(range);
            ty = Some(parse_ty_str(&**val, meta_cache)
                .map_err(|err| Some(format!("```\n{}\n```\n{}", val, err)))?);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let name = name.ok_or(None)?;
    let ty = ty.ok_or(None)?;
    Ok((convert.subtract(start), (name, args, ty)))
}

fn parse_ty(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Type), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut ty: Option<Type> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_or("or", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, val)) = parse_pair("pair", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, (f, args))) = parse_app("app", convert, ignored) {
            convert.update(range);
            let mut val = f;
            for arg in args.into_iter() {
                val = app(val, arg);
            }
            ty = Some(val);
        } else if let Ok((range, val)) = parse_un("un", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, val)) = parse_bin("bin", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, _)) = convert.meta_bool("true") {
            convert.update(range);
            ty = Some(Type::True);
        } else if let Ok((range, _)) = convert.meta_bool("false") {
            convert.update(range);
            ty = Some(Type::False);
        } else if let Ok((range, val)) = convert.meta_string("sym") {
            convert.update(range);
            ty = Some(Type::Sym(val));
        } else if let Ok((range, val)) = convert.meta_string("loc_sym") {
            convert.update(range);
            ty = Some(Type::LocSym(val));
        } else if let Ok((range, val)) = parse_ty_var("var", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let ty = ty.ok_or(())?;
    Ok((convert.subtract(start), ty))
}

fn parse_pair(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Type), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut args: Vec<Type> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_ty("arg", convert, ignored) {
            convert.update(range);
            args.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    if args.len() == 0 {return Err(())};

    let mut ty: Type = args.pop().unwrap();
    while let Some(a) = args.pop() {
        ty = pair(a, ty);
    }
    Ok((convert.subtract(start), ty))
}

fn parse_or(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Type), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut args: Vec<Type> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_and("arg", convert, ignored) {
            convert.update(range);
            args.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    if args.len() == 0 {return Err(())};

    let mut ty: Type = args.pop().unwrap();
    while let Some(a) = args.pop() {
        ty = or(a, ty);
    }
    Ok((convert.subtract(start), ty))
}

fn parse_and(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Type), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut args: Vec<Type> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_ty("arg", convert, ignored) {
            convert.update(range);
            args.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    if args.len() == 0 {return Err(())};

    let mut ty: Type = args.pop().unwrap();
    while let Some(a) = args.pop() {
        ty = and(a, ty);
    }
    Ok((convert.subtract(start), ty))
}

fn parse_ty_var(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Type), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut name: Option<Arc<String>> = None;
    let mut sym: bool = false;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = convert.meta_string("name") {
            convert.update(range);
            name = Some(val);
        } else if let Ok((range, val)) = convert.meta_bool("sym") {
            convert.update(range);
            sym = val;
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let name = name.ok_or(())?;
    let ty = if sym {Type::Sym(name)} else {Type::Ty(name)};
    Ok((convert.subtract(start), ty))
}

fn parse_app(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, (Type, Vec<Type>)), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut left: Option<Type> = None;
    let mut args: Vec<Type> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_ty("left", convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_ty("arg", convert, ignored) {
            convert.update(range);
            args.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let left = left.ok_or(())?;
    Ok((convert.subtract(start), (left, args)))
}

fn parse_bin(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Type), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut left: Option<Type> = None;
    let mut right: Option<Type> = None;
    let mut op: Option<Op> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_ty("left", convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_ty("right", convert, ignored) {
            convert.update(range);
            right = Some(val);
        } else if let Ok((range, _)) = convert.meta_bool("eq") {
            convert.update(range);
            op = Some(Op::Eq);
        } else if let Ok((range, _)) = convert.meta_bool("pow_eq") {
            convert.update(range);
            op = Some(Op::PowEq);
        } else if let Ok((range, _)) = convert.meta_bool("pow") {
            convert.update(range);
            op = Some(Op::Pow);
        } else if let Ok((range, _)) = convert.meta_bool("fun") {
            convert.update(range);
            op = Some(Op::Fun);
        } else if let Ok((range, _)) = convert.meta_bool("imply") {
            convert.update(range);
            op = Some(Op::Imply);
        } else if let Ok((range, _)) = convert.meta_bool("sd") {
            convert.update(range);
            op = Some(Op::Sd);
        } else if let Ok((range, _)) = convert.meta_bool("jud") {
            convert.update(range);
            op = Some(Op::Jud);
        } else if let Ok((range, _)) = convert.meta_bool("comp") {
            convert.update(range);
            op = Some(Op::Comp);
        } else if let Ok((range, _)) = convert.meta_bool("q") {
            convert.update(range);
            op = Some(Op::Q);
        } else if let Ok((range, _)) = convert.meta_bool("qi") {
            convert.update(range);
            op = Some(Op::Qi);
        } else if let Ok((range, _)) = convert.meta_bool("pair") {
            convert.update(range);
            op = Some(Op::Pair);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    if right.is_none() {
        let ty = left.ok_or(())?;
        return Ok((convert.subtract(start), ty));
    }

    let left = left.ok_or(())?;
    let right = right.ok_or(())?;
    let op = op.ok_or(())?;
    let ty = match op {
        Op::Eq => eq(left, right),
        Op::PowEq => pow_eq(left, right),
        Op::Pow => pow(left, right),
        Op::Fun => fun(left, right),
        Op::Imply => imply(left, right),
        Op::Sd => sd(left, right),
        Op::Jud => jud(left, right),
        Op::Comp => comp(left, right),
        Op::Q => q(left, right),
        Op::Qi => qi(left, right),
        Op::Pair => pair(left, right),
        _ => return Err(()),
    };
    Ok((convert.subtract(start), ty))
}

fn parse_un(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Type), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut arg: Option<Type> = None;
    let mut op: Option<Op> = None;
    let mut sym: Option<Arc<String>> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_ty("arg", convert, ignored) {
            convert.update(range);
            arg = Some(val);
        } else if let Ok((range, _)) = convert.meta_bool("not") {
            convert.update(range);
            op = Some(Op::Not);
        } else if let Ok((range, _)) = convert.meta_bool("all") {
            convert.update(range);
            op = Some(Op::All);
        } else if let Ok((range, _)) = convert.meta_bool("nec") {
            convert.update(range);
            op = Some(Op::Nec);
        } else if let Ok((range, _)) = convert.meta_bool("pos") {
            convert.update(range);
            op = Some(Op::Pos);
        } else if let Ok((range, _)) = convert.meta_bool("excm") {
            convert.update(range);
            op = Some(Op::Excm);
        } else if let Ok((range, _)) = convert.meta_bool("qu") {
            convert.update(range);
            op = Some(Op::Qu);
        } else if let Ok((range, val)) = convert.meta_string("sym") {
            convert.update(range);
            op = Some(Op::SymBlock);
            sym = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let arg = arg.ok_or(())?;
    let op = op.ok_or(())?;
    let ty = match op {
        Op::Not => not(arg),
        Op::All => all(arg),
        Op::Nec => nec(arg),
        Op::Pos => pos(arg),
        Op::Excm => excm(arg),
        Op::Qu => qu(arg),
        Op::SymBlock => {
            let sym = sym.ok_or(())?;
            sym_block(sym, arg)
        }
        _ => return Err(()),
    };
    Ok((convert.subtract(start), ty))
}

lazy_static! {
    static ref TYPE_SYNTAX: Arc<String> = Arc::new(include_str!("../assets/syntax.txt").into());

    static ref TYPE_SYNTAX_RULES: Result<Syntax, String> = syntax_errstr(&*TYPE_SYNTAX);
}

/// Parses a type string.
pub fn parse_ty_str(data: &str, meta_cache: &MetaCache) -> Result<Type, String> {
    use piston_meta::{parse_errstr};
    use crate::meta_cache::Key;

    let mut meta_data = vec![];
    let key = Key {
        source: Arc::new(data.into()),
        syntax: TYPE_SYNTAX.clone(),
    };
    if let Some(res) = meta_cache.get(&key) {
        meta_data = res?;
    } else {
        let syntax = TYPE_SYNTAX_RULES.as_ref().map_err(|err| err.clone())?;
        match parse_errstr(&syntax, &data, &mut meta_data) {
            Ok(()) => {
                meta_cache.insert(key, Ok(meta_data.clone()));
            }
            Err(err) => {
                meta_cache.insert(key, Err(err.clone()));
                return Err(err);
            }
        }
    }

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_ty("type", convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}

lazy_static! {
    static ref SCRIPT_SYNTAX: Arc<String> =
        Arc::new(include_str!("../assets/syntax-script.txt").into());

    static ref SCRIPT_SYNTAX_RULES: Result<Syntax, String> = syntax_errstr(&*SCRIPT_SYNTAX);
}

/// Executes a string as script.
pub fn run_str(
    file: &str,
    ctx: &mut Context,
    data: &str,
    search: &mut Search,
    loader: &mut Loader,
    meta_cache: &MetaCache,
) -> Result<Option<(bool, Arc<String>)>, String> {
    use piston_meta::{parse_errstr, ParseErrorHandler};
    use crate::meta_cache::Key;

    let mut meta_data = vec![];
    let key = Key {
        source: Arc::new(data.into()),
        syntax: SCRIPT_SYNTAX.clone(),
    };
    if let Some(data) = meta_cache.get(&key) {
        meta_data = data?;
    } else {
        let syntax = SCRIPT_SYNTAX_RULES.as_ref().map_err(|err| err.clone())?;
        match parse_errstr(&syntax, &data, &mut meta_data) {
            Ok(()) => {
                meta_cache.insert(key, Ok(meta_data.clone()));
            }
            Err(err) => {
                meta_cache.insert(key, Err(err.clone()));
                return Err(err);
            }
        }
    }

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match run_ctx(file, meta_cache, ctx, search, loader, "script", convert, &mut ignored) {
        Err((range, err)) => {
            let (range, _) = meta_data[range.offset].clone().decouple();
            let mut handler = ParseErrorHandler::new(data);
            let mut buf: Vec<u8> = vec![];
            handler.write_msg(&mut buf, range, &err).unwrap();
            Err(String::from_utf8(buf).unwrap())
        }
        Ok((_, expr)) => Ok(expr),
    }
}

lazy_static! {
    static ref LIB_SYNTAX: Arc<String> = Arc::new(include_str!("../assets/syntax-lib.txt").into());

    static ref LIB_SYNTAX_RULES: Result<Syntax, String> = syntax_errstr(&*LIB_SYNTAX);
}

/// Parses library format.
pub fn lib_str(
    data: &str,
    meta_cache: &MetaCache,
) -> Result<LibInfo, String> {
    use piston_meta::parse_errstr;
    use crate::meta_cache::Key;

    let mut meta_data = vec![];
    let key = Key {
        source: Arc::new(data.into()),
        syntax: LIB_SYNTAX.clone(),
    };
    if let Some(data) = meta_cache.get(&key) {
        meta_data = data?;
    } else {
        let syntax = LIB_SYNTAX_RULES.as_ref().map_err(|err| err.clone())?;
        match parse_errstr(&syntax, &data, &mut meta_data) {
            Ok(()) => {
                meta_cache.insert(key, Ok(meta_data.clone()));
            }
            Err(err) => {
                meta_cache.insert(key, Err(err.clone()));
                return Err(err);
            }
        }
    }

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_lib(meta_cache, "lib", convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}
