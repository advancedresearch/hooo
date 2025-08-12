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

use std::sync::Arc;
use rayon::prelude::*;

fn main() {
    println!("==== Hooo 0.9 ====");
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
            let (tx_cycle, rx_cycle) = std::sync::mpsc::channel();
            let (tx_grade, rx_grade) = std::sync::mpsc::channel();
            let mut loader = match Loader::new(
                Arc::new(file.clone()),
                &mut meta_cache,
                Some(tx_cycle),
                Some(tx_grade),
            ) {
                Ok(x) => x,
                Err(err) => {
                    eprintln!("ERROR:\n{}", err);
                    return;
                }
            };
            match lib_check(&mut loader, &mut meta_cache, overwrite) {
                Ok(()) => {
                    // Detect cycle, if any.
                    drop(loader);
                    let cycle_detector = hooo::cycle_detector::CycleDetector::new(rx_cycle);
                    if let Some(cycles) = cycle_detector.cycles() {
                        let mut names = vec![None; cycle_detector.ids.len()];
                        for name in cycle_detector.ids.keys() {
                            names[*cycle_detector.ids.get(name).unwrap()] = Some(name);
                        }
                        eprintln!("ERROR:");
                        eprintln!("Cycles detected:\n");
                        for &(a, b) in &cycles {
                            eprintln!("  {} -> {}",
                                names[a].unwrap(), names[b].unwrap());
                        }
                        eprintln!("");
                    }

                    let s = hooo::grader::grade_report(rx_grade.iter(), &cycle_detector);
                    println!("{}", s);
                }
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
    loader: &mut Loader,
    meta_cache: &MetaCache,
    overwrite: Option<bool>,
) -> Result<(), String> {
    use std::path::Path;
    use std::fs::File;
    use std::io::Write as OtherWrite;
    use std::sync::Mutex;

    let path = Path::new(&**loader.dir).join("Hooo.config");
    let lib: Option<LibInfo> = loader.load_info(meta_cache)?;

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

    let s = loader.to_library_format(&lib);

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
