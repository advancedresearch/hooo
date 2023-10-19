use hooo::*;

use std::sync::Arc;
use rayon::prelude::*;

fn main() {
    println!("==== Hooo 0.2 ====");
    let file = std::env::args_os()
        .nth(1)
        .and_then(|s| s.into_string().ok());
    if let Some(file) = file {
        use std::path::Path;

        let path = Path::new(&file);
        if path.is_dir() {
            let ref mut loader = match Loader::new(Arc::new(file.clone())) {
                Ok(x) => x,
                Err(err) => {
                    eprintln!("ERROR:\n{}", err);
                    return;
                }
            };
            match lib_check(loader) {
                Ok(()) => {}
                Err(err) => {
                    eprintln!("\nERROR:\n{}", err);
                    return;
                }
            }
        } else {
            let dir: String = path.parent().unwrap().to_str().unwrap().into();
            let ref mut loader = match Loader::new(Arc::new(dir)) {
                Ok(x) => x,
                Err(err) => {
                    eprintln!("ERROR:\n{}", err);
                    return;
                }
            };
            match proof_check(file, loader) {
                Ok(()) => {}
                Err(err) => {
                    eprintln!("ERROR:\n{}", err);
                    return;
                }
            }
        }
    } else {
        eprintln!("hooo <file.hooo>");
    }
}

fn lib_check(loader: &mut Loader) -> Result<(), String> {
    use std::fmt::Write;
    use std::path::Path;
    use std::fs::File;
    use std::io::Write as OtherWrite;
    use std::sync::Mutex;

    let path = Path::new(&**loader.dir).join("Hooo.config");
    let lib: Option<LibInfo> = loader.load_info()?;
  
    let files = loader.files.clone(); 
 
    loader.silent = true;
    let error: Arc<Mutex<Result<(), String>>> = Arc::new(Ok(()).into());
    let _ = (0..files.len()).into_par_iter().map(|i| {
        if let Err(err) = proof_check(files[i].clone(), &mut loader.clone()) {
            let mut error = error.lock().unwrap();
            *error = Err(format!("In `{}`:\n{}", files[i], err));
            None
        } else {Some(i)}
    }).while_some().max();
    let error = error.lock().unwrap();
    let _ = error.as_ref().map_err(|err| err.clone())?;

    let mut s = String::new();
    // Extract functions and generate library format.
    let mut functions: Vec<(Arc<String>, Type)> = loader.functions.iter()
        .map(|(name, ty)| (name.clone(), ty.clone())).collect();
    functions.sort();

    let name: &str = if let Some(lib) = &lib {
        &**lib.name
    } else {
        Path::new(&**loader.dir).file_stem().unwrap().to_str().unwrap()
    };
    let version: &str = if let Some(lib) = &lib {
        &**lib.version
    } else {
        "0.1.0"
    };
    let desc: &str = if let Some(lib) = &lib {
        &**lib.description
    } else {
        "add your description here"
    };
 
    writeln!(s, "name: {};", json(name)).unwrap();
    writeln!(s, "version: {};", json(version)).unwrap();   
    writeln!(s, "description: {};", json(desc)).unwrap();
 
    writeln!(s, "functions {{").unwrap();
    let top = true;
    for (name, ty) in functions {
        writeln!(s, "  {} : {};", name, ty.to_str(top, None)).unwrap();
    }
    writeln!(s, "}}").unwrap();

    writeln!(s, "dependencies {{").unwrap();
    if let Some(lib) = &lib {
        for dep in &lib.dependencies {
            match dep {
                Dep::Path(p) => {
                    writeln!(s, "  path({});", json(&p)).unwrap();
                }
            }
        }
    }
    writeln!(s, "}}").unwrap();

    println!("");
    println!("=== New Hooo.config ===");
    println!("{}", s);
    if path.exists() {
        println!("");
        println!("The file `{}` will be overwritten.", path.to_str().unwrap());
        println!("Type `Y` and Enter to continue.");
        let stdin = std::io::stdin();
        let mut input = String::new();
        stdin.read_line(&mut input).unwrap();
        match input.trim() {
            "Y" => {}
            _ => {
                println!("Overwriting cancelled.");
                return Ok(());
            }
        };
    }
    
    let mut file = File::create(path).unwrap();
    file.write(s.as_bytes()).unwrap();
    Ok(())
}

fn json(s: &str) -> String {
    use piston_meta::json::write_string; 
    
    let mut buf: Vec<u8> = vec![];
    write_string(&mut buf, s).unwrap();
    String::from_utf8(buf).unwrap()
}

fn proof_check(file: String, loader: &mut Loader) -> Result<(), String> {
    println!("=== Proof check of `{}` ===", file);
    let _ = loader.load_info()?;
    let mut ctx = Context::new();
    let mut search = Search::new();
    let _ = ctx.run(&file, &mut search, loader)?;
    if !loader.silent {
        println!("\nProof check completed successfully.");
        println!("Search effort: {}", search.n);
    }
    Ok(())
}

