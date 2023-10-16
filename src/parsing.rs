use crate::*;

use piston_meta::{Convert, Range};

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
            functions.insert(name, ty);
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
        } else if let Ok((range, (name, args, ty))) = parse_var("axiom", convert, ignored) {
            convert.update(range);
            if loader.run {
                if args.len() == 0 {
                    ctx.new_term((name, Term::Axiom(ty)), search).map_err(|err| (range, err))?;
                } else {
                    return Err((range, "Parsing axiom".into()));
                }
            }
        } else if let Ok((range, (name, args, ty))) = parse_var("var", convert, ignored) {
            convert.update(range);
            if loader.run {
                if args.len() == 0 {
                    ctx.new_term((name, Term::Var(ty)), search).map_err(|err| (range, err))?;
                } else {
                    return Err((range, "Parsing variable".into()));
                }
            }
        } else if let Ok((range, (name, args, ty))) = parse_var("app", convert, ignored) {
            convert.update(range);
            if loader.run {
                if args.len() >= 1 {
                    ctx.new_term((name, Term::App(args[0].clone(), args[1..].into(), ty)), search)
                        .map_err(|err| (range, err))?;
                } else {
                    return Err((range, "Parsing application: Expected arguments".into()));
                }
            }
        } else if let Ok((range, (name, args, ty))) = parse_var("match", convert, ignored) {
            convert.update(range);
            if loader.run {
                if args.len() == 3 || args.len() == 1 {
                    ctx.new_term((name, Term::Match(args, ty)), search).map_err(|err| (range, err))?;
                } else {
                    return Err((range, "Parsing application".into()));
                }
            }
        } else if let Ok((range, (name, _, ty))) = parse_var("check", convert, ignored) {
            convert.update(range);
            if loader.run {
                ctx.new_term((name, Term::Check(ty)), search).map_err(|err| (range, err))?;
            }
        } else if let Ok((range, val)) = convert.meta_string("prove") {
            convert.update(range);
            if loader.run {
                let ty: Type = (&**val).try_into().map_err(|err| (range, err))?;
                let res = ctx.prove(ty, search);
                if !res {
                    return Err((range, format!("{}", val)));
                }
            }
        } else if let Ok((range, (name, _, ty))) = parse_var("fun_decl", convert, ignored) {
            convert.update(range);
            if loader.run {
                let n = loader.trace.len();
                loader.trace.push(name.clone());
                println!("fn {}", name);
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
        } else if let Ok((range, (name, _, ty))) = parse_var("lam_decl", convert, ignored) {
            convert.update(range);
            if loader.run {
                println!("lam {}", name);
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
) -> Result<(Range, (Arc<String>, Vec<Arc<String>>, Type)), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
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
            ty = Some((&**val).try_into().map_err(|_| ())?);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let name = name.ok_or(())?;
    let ty = ty.ok_or(())?;
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
            ty = Some(Type::Imply(Box::new(val)));
        } else if let Ok((range, val)) = parse_bin("pow", convert, ignored) {
            convert.update(range);
            ty = Some(Type::Pow(Box::new(val)));
        } else if let Ok((range, val)) = parse_bin("and", convert, ignored) {
            convert.update(range);
            ty = Some(Type::And(Box::new(val)));
        } else if let Ok((range, val)) = parse_bin("or", convert, ignored) {
            convert.update(range);
            ty = Some(Type::Or(Box::new(val)));
        } else if let Ok((range, val)) = parse_bin("eq", convert, ignored) {
            convert.update(range);
            ty = Some(eq(val.0, val.1));
        } else if let Ok((range, val)) = parse_un("not", convert, ignored) {
            convert.update(range);
            ty = Some(Type::Imply(Box::new((val, Type::False))));
        } else if let Ok((range, val)) = parse_un("excm", convert, ignored) {
            convert.update(range);
            ty = Some(or(val.clone(), not(val)));    
        } else if let Ok((range, val)) = parse_un("all", convert, ignored) {
            convert.update(range);
            ty = Some(val.lift());
        } else if let Ok((range, _)) = convert.meta_bool("true") {
            convert.update(range);
            ty = Some(Type::True);
        } else if let Ok((range, _)) = convert.meta_bool("false") {
            convert.update(range);
            ty = Some(Type::False);
        } else if let Ok((range, val)) = convert.meta_string("name") {
            convert.update(range);
            ty = Some(Type::Ty(val));
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let ty = ty.ok_or(())?;
    Ok((convert.subtract(start), ty))
}

fn parse_bin(
    node: &str,
    mut convert: Convert,
    ignored: &mut Vec<Range>
) -> Result<(Range, (Type, Type)), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut left: Option<Type> = None;
    let mut right: Option<Type> = None;
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
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let left = left.ok_or(())?;
    let right = right.ok_or(())?;
    Ok((convert.subtract(start), (left, right)))
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

/// Parses a type string.
pub fn parse_ty_str(data: &str) -> Result<Type, String> {
    use piston_meta::{parse_errstr, syntax_errstr};

    let syntax_src = include_str!("../assets/syntax.txt");
    let syntax = syntax_errstr(syntax_src)?;

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

/// Executes a string as script.
pub fn run_str(
    ctx: &mut Context,
    data: &str,
    search: &mut Search,
    loader: &mut Loader,
) -> Result<Option<Arc<String>>, String> {
    use piston_meta::{parse_errstr, syntax_errstr, ParseErrorHandler};

    let syntax_src = include_str!("../assets/syntax-script.txt");
    let syntax = syntax_errstr(syntax_src)?;

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


/// Parses library format.
pub fn lib_str(
    data: &str,
) -> Result<LibInfo, String> {
    use piston_meta::{parse_errstr, syntax_errstr};

    let syntax_src = include_str!("../assets/syntax-lib.txt");
    let syntax = syntax_errstr(syntax_src)?;

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
