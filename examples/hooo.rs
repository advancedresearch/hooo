/*

Hooo type checker

Usage:

```
> hooo <file.hooo>
```

To type check a whole project:

```
> hooo <project directory>
```

Flags:

```
--overwrite         Automatically overwrite old `Hooo.config` file
--no_overwrite      Do not overwrite old `Hooo.config` file
```

*/

use hooo::*;
use hooo::meta_cache::MetaCache;

use rustc_hash::FxHashSet as HashSet;

use std::sync::Arc;
use rayon::prelude::*;

fn main() {
    println!("==== Hooo 0.10 ====");
    let file = std::env::args_os()
        .nth(1)
        .and_then(|s| s.into_string().ok());
    let overwrite = std::env::args_os()
        .nth(2)
        .and_then(|s| s.into_string().ok());
    let overwrite: Option<bool> = match overwrite.as_ref().map(|n| &**n) {
        Some("--overwrite") => Some(true),
        Some("--no_overwrite") => Some(false),
        _ => None,
    };

    if let Some(file) = file {
        use std::path::Path;

        let meta_store_file = "hooo-meta_store.bin";
        let path = Path::new(&file);
        let mut meta_cache = MetaCache::restore(meta_store_file);
        if path.is_dir() {
            match lib_check(file, &mut meta_cache, overwrite) {
                Ok(()) => {}
                Err(err) => {
                    eprintln!("\nERROR:\n{}", err);
                    return;
                }
            }
        } else {
            let dir: String = path.parent().unwrap().to_str().unwrap().into();
            let ref mut loader = match Loader::new(
                Arc::new(dir),
                &mut meta_cache,
                None,
                None,
            ) {
                Ok(x) => x,
                Err(err) => {
                    eprintln!("ERROR:\n{}", err);
                    return;
                }
            };
            match proof_check(file, loader, &mut meta_cache) {
                Ok(()) => {}
                Err(err) => {
                    eprintln!("ERROR:\n{}", err);
                    return;
                }
            }
        }

        match meta_cache.store(meta_store_file) {
            Ok(()) => {}
            Err(err) => eprintln!("ERROR:\n{}", err),
        }
    } else {
        eprintln!("hooo <file.hooo>");
    }
}

fn lib_check(
    file: String,
    meta_cache: &MetaCache,
    overwrite: Option<bool>,
) -> Result<(), String> {
    use std::path::Path;
    use std::fs::File;
    use std::io::Write as OtherWrite;
    use std::sync::Mutex;

    let (tx_cycle, rx_cycle) = std::sync::mpsc::channel();
    let (tx_grade, rx_grade) = std::sync::mpsc::channel();
    let tx_grade_copy = tx_grade.clone();
    let mut loader = Loader::new(
        Arc::new(file.clone()),
        meta_cache,
        Some(tx_cycle),
        Some(tx_grade),
    )?;

    let path = Path::new(&**loader.dir).join("Hooo.config");
    let lib: Option<LibInfo> = loader.load_info(meta_cache)?;

    if let Some(lib) = &lib {
        let ref mut sent: HashSet<Arc<String>> = HashSet::default();
        sent.insert(lib.name.clone());
        let dir = std::path::Path::new(&**loader.dir).into();
        lib.send_external_unique_gradings(dir, &tx_grade_copy, sent, meta_cache);
    }
    drop(tx_grade_copy);

    let files = loader.files.clone();

    loader.silent = true;
    let error: Arc<Mutex<Result<(), String>>> = Arc::new(Ok(()).into());
    let _ = (0..files.len()).into_par_iter().map(|i| {
        if let Err(err) = proof_check(
            files[i].clone(),
            &mut loader.clone(),
            &meta_cache
        ) {
            let mut error = error.lock().unwrap();
            *error = Err(format!("In `{}`:\n{}", files[i], err));
            None
        } else {Some(i)}
    }).while_some().max();
    let error = error.lock().unwrap();
    let _ = error.as_ref().map_err(|err| err.clone())?;

    // Detect cycle, if any.
    // First, drop cycle and grade check senders to terminate channels.
    loader.cycle_check = None;
    loader.grade_check = None;
    let cycle_detector = hooo::cycle_detector::CycleDetector::new(&loader, rx_cycle);
    if let Some(cycles) = cycle_detector.cycles() {
        use std::fmt::Write;

        let mut names = vec![None; cycle_detector.ids.len()];
        for name in cycle_detector.ids.keys() {
            names[*cycle_detector.ids.get(name).unwrap()] = Some(name);
        }
        let mut err = String::new();
        writeln!(err, "Cycles detected:\n").unwrap();
        for &(a, b) in &cycles {
            writeln!(err, "  {} -> {}",
                names[a].map(|n| &n.1).unwrap(), names[b].map(|n| &n.1).unwrap()).unwrap();
        }
        return Err(err);
    }
    // Generate theorem grading report.
    let s_grade = hooo::grader::grade_report(rx_grade.iter(), &cycle_detector);
    let s = loader.to_library_format(&lib, &s_grade);

    println!("");
    println!("=== New Hooo.config ===");
    println!("{}", s);

    if overwrite == Some(false) {return Ok(())};
    if overwrite.is_none() && path.exists() {
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

fn proof_check(file: String, loader: &mut Loader, meta_cache: &MetaCache) -> Result<(), String> {
    println!("=== Proof check of `{}` ===", file);
    let _ = loader.load_info(meta_cache)?;
    let mut ctx = Context::new();
    let mut search = Search::new();
    let _ = ctx.run(&file, &mut search, loader, meta_cache)?;
    if !loader.silent {
        println!("\nProof check completed successfully.");
        println!("Search effort: {}", search.n);
    }
    Ok(())
}
