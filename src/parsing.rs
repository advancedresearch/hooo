use crate::*;

use piston_meta::{syntax_errstr, Convert, Range, Syntax};
use lazy_static::lazy_static;

fn parse_lib(
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
    let mut functions: HashMap<Arc<String>, Type> = HashMap::new();
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
        } else if let Ok((range, (name, _, ty))) = parse_var("fun", convert, ignored) {
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
    ctx: &mut Context,
    search: &mut Search,
    loader: &mut Loader,
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, Option<Arc<String>>), (Range, String)> {
    let start = convert;
    let start_range = convert.start_node(node)
        .map_err(|()| (convert.ignore(), format!("Expected start node {}", node)))?;
    convert.update(start_range);

    let mut ret: Option<Arc<String>> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        }
       
        match parse_var("axiom", convert, ignored) {
            Ok((range, (name, args, ty))) => {
                convert.update(range);
                if loader.run {
                    if args.len() == 0 {
                        ctx.new_term((name, Term::Axiom(ty)), search).map_err(|err| (range, err))?;
                    } else {
                        return Err((range, "Parsing axiom".into()));
                    }
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        } 
 
        match parse_var("var", convert, ignored) {
            Ok((range, (name, args, ty))) => {
                convert.update(range);
                if loader.run {
                    if args.len() == 0 {
                        ctx.new_term((name, Term::Var(ty)), search).map_err(|err| (range, err))?;
                    } else {
                        return Err((range, "Parsing variable".into()));
                    }
                }
                continue;
            }
            Err(Some(err)) => return Err((start_range, err)),
            Err(None) => {}
        }

        if let Ok((range, (name, args, ty))) = parse_var("app", convert, ignored) {
            convert.update(range);
            if loader.run {
                if args.len() >= 1 {
                    ctx.new_term((name, Term::App(args[0].clone(), args[1..].into(), ty)), search)
                        .map_err(|err| (range, err))?;
                } else {
                    return Err((range, "Parsing application: Expected arguments".into()));
                }
            }
            continue;
        } else if let Ok((range, (name, args, ty))) = parse_var("match", convert, ignored) {
            convert.update(range);
            if loader.run {
                if args.len() == 3 || args.len() == 1 {
                    ctx.new_term((name, Term::Match(args, ty)), search).map_err(|err| (range, err))?;
                } else {
                    return Err((range, "Parsing application".into()));
                }
            }
            continue;
        } else if let Ok((range, (name, _, ty))) = parse_var("check", convert, ignored) {
            convert.update(range);
            if loader.run {
                ctx.new_term((name, Term::Check(ty)), search).map_err(|err| (range, err))?;
            }
            continue;
        } else if let Ok((range, val)) = convert.meta_string("prove") {
            convert.update(range);
            if loader.run {
                let ty: Type = (&**val).try_into().map_err(|err| (range, err))?;
                let res = ctx.prove(ty, search);
                if !res {
                    return Err((range, format!("{}", val)));
                }
            }
            continue;
        }

        match parse_var("fun_decl", convert, ignored) {
            Ok((range, (name, _, ty))) => {
                convert.update(range);
                if loader.run {
                    let n = loader.trace.len();
                    loader.trace.push(name.clone());
                    if !loader.silent {println!("fn {}", name)};
                    ctx.fun(range, name.clone(), ty.clone(), search, |ctx, search| {
                        match run_ctx(ctx, search, loader, "script", convert, ignored) {
                            Ok((range, ret)) => {
                                convert.update(range);
                                if let Some(ret) = ret {
                                    if let Type::Pow(ab) = &ty {
                                        if ctx.has_term_ty(&ret, &ab.0) {
                                            ctx.add_proof(ty.clone());
                                        }
                                    }
                                }
                                Ok(())
                            }
                            Err(err) => Err(err),
                        }
                    })?;
                    loader.trace.truncate(n);
                } else {
                    if let Type::Pow(_) = &ty {
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

        if let Ok((range, (name, _, ty))) = parse_var("lam_decl", convert, ignored) {
            convert.update(range);
            if loader.run {
                if !loader.silent {println!("lam {}", name)};
                ctx.lam(range, name.clone(), ty.clone(), search, |ctx, search| {
                    match run_ctx(ctx, search, loader, "script", convert, ignored) {
                        Ok((range, ret)) => {
                            convert.update(range);
                            if let Some(ret) = ret {
                                if let Type::Imply(ab) = &ty {
                                    if ctx.has_term_ty(&ret, &ab.1) {
                                        ctx.add_proof(ty.clone());
                                    }
                                }
                            }
                            Ok(())
                        }
                        Err(err) => Err(err),
                    }
                })?;
            }
        } else if let Ok((range, val)) = convert.meta_string("return") {
            convert.update(range);
            if loader.run {
                if !ctx.has_term(&val) {return Err((range, format!("Could not find `{}`", val)))};

                ret = Some(val);
            }
        } else if let Ok((range, (ns, fun))) = parse_use("use", convert, ignored) {
            convert.update(range);
            if loader.run {
                let ty = loader.load_fun(&ns, &fun).map_err(|err| (range, err))?;
                ctx.new_term((fun, Term::FunDecl(ty)), search).map_err(|err| (range, err))?;
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
            ty = Some((&**val).try_into().map_err(|err| Some(format!("```\n{}\n```\n{}", val, err)))?);
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
        } else if let Ok((range, val)) = parse_bin("imply", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, val)) = parse_bin("pow", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, val)) = parse_bin("eq", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, val)) = parse_bin("sd", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, val)) = parse_or("or", convert, ignored) {
            convert.update(range);
            ty = Some(val);
        } else if let Ok((range, (f, args))) = parse_app("app", convert, ignored) {
            convert.update(range);
            let mut val = f;
            for arg in args.into_iter() {
                val = app(val, arg);
            }
            ty = Some(val);
        } else if let Ok((range, val)) = parse_un("not", convert, ignored) {
            convert.update(range);
            ty = Some(Type::Imply(Box::new((val, Type::False))));
        } else if let Ok((range, val)) = parse_un("excm", convert, ignored) {
            convert.update(range);
            ty = Some(or(val.clone(), not(val)));    
        } else if let Ok((range, val)) = parse_un("all", convert, ignored) {
            convert.update(range);
            ty = Some(Type::All(Box::new(val.lift())));
        } else if let Ok((range, _)) = convert.meta_bool("true") {
            convert.update(range);
            ty = Some(Type::True);
        } else if let Ok((range, _)) = convert.meta_bool("false") {
            convert.update(range);
            ty = Some(Type::False);
        } else if let Ok((range, val)) = convert.meta_string("sym") {
            convert.update(range);
            ty = Some(Type::Sym(val));
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
        } else if let Ok((range, _)) = convert.meta_bool("imply") {
            convert.update(range);
            op = Some(Op::Imply);
        } else if let Ok((range, _)) = convert.meta_bool("sd") {
            convert.update(range);
            op = Some(Op::Sd);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let left = left.ok_or(())?;
    let right = right.ok_or(())?;
    let op = op.ok_or(())?;
    let ty = match op {
        Op::Eq => eq(left, right),
        Op::PowEq => pow_eq(left, right),
        Op::Pow => pow(left, right),
        Op::Imply => imply(left, right),
        Op::Sd => sd(left, right),
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
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_ty("arg", convert, ignored) {
            convert.update(range);
            arg = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let arg = arg.ok_or(())?;
    Ok((convert.subtract(start), arg))
}

lazy_static! {
    static ref TYPE_SYNTAX_RULES: Result<Syntax, String> = {
        let syntax = include_str!("../assets/syntax.txt");
        syntax_errstr(syntax)
    };
}

/// Parses a type string.
pub fn parse_ty_str(data: &str) -> Result<Type, String> {
    use piston_meta::{parse_errstr};

    let syntax = TYPE_SYNTAX_RULES.as_ref().map_err(|err| err.clone())?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_ty("type", convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}

lazy_static! {
    static ref SCRIPT_SYNTAX_RULES: Result<Syntax, String> = {
        let syntax = include_str!("../assets/syntax-script.txt");
        syntax_errstr(syntax)
    };
}

/// Executes a string as script.
pub fn run_str(
    ctx: &mut Context,
    data: &str,
    search: &mut Search,
    loader: &mut Loader,
) -> Result<Option<Arc<String>>, String> {
    use piston_meta::{parse_errstr, ParseErrorHandler};

    let syntax = SCRIPT_SYNTAX_RULES.as_ref().map_err(|err| err.clone())?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match run_ctx(ctx, search, loader, "script", convert, &mut ignored) {
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
    static ref LIB_SYNTAX_RULES: Result<Syntax, String> = {
        let syntax = include_str!("../assets/syntax-lib.txt");
        syntax_errstr(syntax)
    };
}

/// Parses library format.
pub fn lib_str(
    data: &str,
) -> Result<LibInfo, String> {
    use piston_meta::parse_errstr;

    let syntax = LIB_SYNTAX_RULES.as_ref().map_err(|err| err.clone())?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_lib("lib", convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}
