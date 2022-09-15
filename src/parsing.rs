//! Parsing

use crate::*;

use piston_meta::{Convert, Range};

fn parse_expr(node: &str, dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut expr: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_subst("subst", dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_app("app", dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_neg("neg", dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_bin("bin", dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, val)) = parse_un("un", dirs, convert, ignored) {
            convert.update(range);
            expr = Some(val);
        } else if let Ok((range, _)) = convert.meta_bool("⋀") {
            convert.update(range);
            expr = Some(And);
        } else if let Ok((range, _)) = convert.meta_bool("⋁") {
            convert.update(range);
            expr = Some(Or);
        } else if let Ok((range, _)) = convert.meta_bool("=") {
            convert.update(range);
            expr = Some(Eq);
        } else if let Ok((range, _)) = convert.meta_bool(":") {
            convert.update(range);
            expr = Some(Ty);
        } else if let Ok((range, _)) = convert.meta_bool("→") {
            convert.update(range);
            expr = Some(Imply);
        } else if let Ok((range, _)) = convert.meta_bool("←") {
            convert.update(range);
            expr = Some(Rimply);
        } else if let Ok((range, _)) = convert.meta_bool("↞") {
            convert.update(range);
            expr = Some(App);
        } else if let Ok((range, _)) = convert.meta_bool("^") {
            convert.update(range);
            expr = Some(Pow);
        } else if let Ok((range, _)) = convert.meta_bool("□") {
            convert.update(range);
            expr = Some(Sq);
        } else if let Ok((range, _)) = convert.meta_bool("◇") {
            convert.update(range);
            expr = Some(Di);
        } else if let Ok((range, _)) = convert.meta_bool("~~") {
            convert.update(range);
            expr = Some(Qual);
        } else if let Ok((range, _)) = convert.meta_bool("~◇~") {
            convert.update(range);
            expr = Some(Wave);
        } else if let Ok((range, _)) = convert.meta_bool("⊤") {
            convert.update(range);
            expr = Some(Tr);
        } else if let Ok((range, _)) = convert.meta_bool("⊥") {
            convert.update(range);
            expr = Some(Fa);
        } else if let Ok((range, val)) = convert.meta_string("var") {
            convert.update(range);
            expr = Some(match &**val {
                "A" => A,
                "B" => B,
                "X" => X,
                "Y" => Y,
                "_wave" => Wave,
                "left" => Left,
                "right" => Right,
                "fst" => Fst,
                "snd" => Snd,
                "swap_or" => SwapOr,
                "tauto" => Tauto,
                "para" => Para,
                "uniform" => Uniform,
                "theory" => Theory,
                "True" => Tr,
                "False" => Fa,
                _ => Var(val),
            });
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let expr = expr.ok_or(())?;
    Ok((convert.subtract(start), expr))
}

fn parse_neg(node: &str, dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut arg: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("arg", dirs, convert, ignored) {
            convert.update(range);
            arg = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let arg = arg.ok_or(())?;
    Ok((convert.subtract(start), imply(arg, Fa)))
}

fn parse_subst(node: &str, dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut f: Option<Expr> = None;
    let mut var: Option<Expr> = None;
    let mut arg: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("f", dirs, convert, ignored) {
            convert.update(range);
            f = Some(val);
        } else if let Ok((range, val)) = parse_expr("var", dirs, convert, ignored) {
            convert.update(range);
            var = Some(val);
        } else if let Ok((range, val)) = parse_expr("arg", dirs, convert, ignored) {
            convert.update(range);
            arg = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let f = f.ok_or(())?;
    let var = var.ok_or(())?;
    let arg = arg.ok_or(())?;
    Ok((convert.subtract(start), Subst(Box::new((f, var, arg)))))
}

fn parse_app(node: &str, dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut f: Option<Expr> = None;
    let mut args: Vec<Expr> = vec![];
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("f", dirs, convert, ignored) {
            convert.update(range);
            f = Some(val);
        } else if let Ok((range, val)) = parse_expr("arg", dirs, convert, ignored) {
            convert.update(range);
            args.push(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let f = f.ok_or(())?;
    let mut arg = f;
    for a in args.into_iter() {
        arg = app(arg, a)
    }
    Ok((convert.subtract(start), arg))
}

fn parse_un(node: &str, dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut op: Option<Expr> = None;
    let mut arg: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, _)) = convert.meta_bool("~") {
            convert.update(range);
            op = Some(Qubit);
        } else if let Ok((range, val)) = parse_expr("arg", dirs, convert, ignored) {
            convert.update(range);
            arg = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let op = op.ok_or(())?;
    let arg = arg.ok_or(())?;
    Ok((convert.subtract(start), Un(Box::new((op, arg)))))
}

fn parse_bin(node: &str, dirs: &[String], mut convert: Convert, ignored: &mut Vec<Range>) -> Result<(Range, Expr), ()> {
    let start = convert;
    let start_range = convert.start_node(node)?;
    convert.update(start_range);

    let mut op: Option<Expr> = None;
    let mut left: Option<Expr> = None;
    let mut right: Option<Expr> = None;
    loop {
        if let Ok(range) = convert.end_node(node) {
            convert.update(range);
            break;
        } else if let Ok((range, val)) = parse_expr("left", dirs, convert, ignored) {
            convert.update(range);
            left = Some(val);
        } else if let Ok((range, val)) = parse_expr("op", dirs, convert, ignored) {
            convert.update(range);
            op = Some(val);
        } else if let Ok((range, val)) = parse_expr("right", dirs, convert, ignored) {
            convert.update(range);
            right = Some(val);
        } else {
            let range = convert.ignore();
            convert.update(range);
            ignored.push(range);
        }
    }

    let left = left.ok_or(())?;
    let op = op.ok_or(())?;
    let right = right.ok_or(())?;
    Ok((convert.subtract(start), Bin(Box::new((op, left, right)))))
}

/// Parses an expression string.
pub fn parse_str(data: &str, dirs: &[String]) -> Result<Expr, String> {
    use piston_meta::{parse_errstr, syntax_errstr};

    let syntax_src = include_str!("../assets/syntax.txt");
    let syntax = syntax_errstr(syntax_src)?;

    let mut meta_data = vec![];
    parse_errstr(&syntax, &data, &mut meta_data)?;

    // piston_meta::json::print(&meta_data);

    let convert = Convert::new(&meta_data);
    let mut ignored = vec![];
    match parse_expr("expr", dirs, convert, &mut ignored) {
        Err(()) => Err("Could not convert meta data".into()),
        Ok((_, expr)) => Ok(expr),
    }
}

/// Parses an expression source file.
pub fn parse(source: &str, dirs: &[String]) -> Result<Expr, String> {
    use std::fs::File;
    use std::io::Read;

    let mut data_file = File::open(source).map_err(|err|
        format!("Could not open `{}`, {}", source, err))?;
    let mut data = String::new();
    data_file.read_to_string(&mut data).unwrap();

    parse_str(&data, dirs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        let a: Expr = parse_str(r#"⊤"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "⊤".to_string());

        let a: Expr = parse_str(r#"⊥"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "⊥".to_string());

        let a: Expr = parse_str(r#"(⊤ ⋀ ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ ⋀ ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊤ ⋁ ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ ⋁ ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊤ = ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ = ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊤ : ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ : ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊤ → ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ → ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊤ ← ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ ← ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊤ ↞ ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ ↞ ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊤ ^ ⊥)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊤ ^ ⊥)".to_string());

        let a: Expr = parse_str(r#"(⊥ ^ '^')"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊥ ^ '^')".to_string());

        let a: Expr = parse_str(r#"fst"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "fst".to_string());

        let a: Expr = parse_str(r#"snd"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "snd".to_string());

        let a: Expr = parse_str(r#"left"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "left".to_string());

        let a: Expr = parse_str(r#"right"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "right".to_string());

        let a: Expr = parse_str(r#"A"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "A".to_string());

        let a: Expr = parse_str(r#"B"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "B".to_string());

        let a: Expr = parse_str(r#"X"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "X".to_string());

        let a: Expr = parse_str(r#"Y"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "Y".to_string());

        let a: Expr = parse_str(r#"(A □ B)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(A □ B)".to_string());

        let a: Expr = parse_str(r#"(A ◇ B)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(A ◇ B)".to_string());

        let a: Expr = parse_str(r#"(A ~◇~ B)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(A ~◇~ B)".to_string());

        let a: Expr = parse_str(r#"(A _wave B)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(A ~◇~ B)".to_string());

        let a: Expr = parse_str(r#"swap_or"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "swap_or".to_string());

        let a: Expr = parse_str(r#"False^'_sq'"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊥ ^ '□')".to_string());

        let a: Expr = parse_str(r#"False^'_di'"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(⊥ ^ '◇')".to_string());

        let a: Expr = parse_str(r#"~a"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "~a".to_string());

        let a: Expr = parse_str(r#"(a ~~ b)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(a ~~ b)".to_string());

        let a: Expr = parse_str(r#"(tauto ↞ a)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(tauto ↞ a)".to_string());

        let a: Expr = parse_str(r#"(para ↞ a)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(para ↞ a)".to_string());

        let a: Expr = parse_str(r#"(uniform ↞ a)"#, &[]).unwrap();
        assert_eq!(format!("{}", a), "(uniform ↞ a)".to_string());
    }
}
