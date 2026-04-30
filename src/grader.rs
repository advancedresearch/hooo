use crate::*;

use cycle_detector::CycleDetector;

pub(crate) type Name = (Vec<Arc<String>>, Arc<String>);

type Filter = HashMap<usize, Vec<Arc<String>>>;

pub fn grade_report<I: Iterator<Item = (Arc<String>, Vec<Vec<Name>>, bool)>>(
    iter: I,
    cycle_detector: &CycleDetector,
) -> String {
    use std::fmt::Write;

    let mut s = String::new();
    writeln!(&mut s, "grades {{").unwrap();
    let mut grades: HashMap<Arc<String>, Grader> = HashMap::default();
    let mut filter: Filter = HashMap::default();
    for (name, args, external) in iter {
        let insert = if let Some(grader) = grades.get_mut(&name) {
            if grader.external != external {
                eprintln!("ERROR:\nGrade `{}` is declared externally", name);
                !external
            } else if external {
                for (grader_args, arg) in grader.args.iter_mut().zip(args.into_iter()) {
                    grader_args.extend(arg.into_iter());
                }
                continue
            } else {false}
        } else {true};

        if insert {
            let grader = Grader {name: name.clone(), args, external};

            // Remember theorem gradient specified locally,
            // so that they can be filtered out of other theorem grades.
            if !grader.external {
                for n in grader.args.iter() {
                    for m in n {
                        if let Some(id) = cycle_detector.ids.get(m) {
                            if let Some(names) = filter.get_mut(id) {
                                names.push(name.clone());
                            } else {
                                filter.insert(*id, vec![name.clone()]);
                            }
                        }
                    }
                }
            }

            grades.insert(name, grader);
        }
    }
    let mut grades: Vec<&Grader> = grades.values().collect();
    grades.sort_by_key(|n| &n.name);
    for grader in grades {
        grader.report(&mut s, cycle_detector, &mut filter);
    }
    writeln!(&mut s, "}}").unwrap();
    s
}

pub struct Grader {
    pub name: Arc<String>,
    pub args: Vec<Vec<Name>>,
    pub external: bool,
}

fn ns_name(name: &(Vec<Arc<String>>, Arc<String>)) -> String {
    let mut s = String::new();
    for n in &name.0 {
        s.push_str(n);
        s.push_str("::");
    }
    s.push_str(&name.1);
    s
}

impl Grader {
    pub fn report(
        &self,
        s: &mut String,
        cycle_detector: &CycleDetector,
        filter: &mut Filter,
    ) {
        use std::fmt::Write;

        // Stores grades and whether they are locked.
        let mut grades: HashMap<usize, (usize, bool)> = HashMap::default();

        for (gr, args) in self.args.iter().enumerate() {
            for arg in args {
                if let Some(id) = cycle_detector.ids.get(arg) {
                    grades.insert(*id, (gr, true));
                } else if !self.external {
                    eprintln!("ERROR:\n");
                    eprintln!("Grader check error #100:");
                    eprintln!("Could not find function `{}`", ns_name(arg));
                }
            }
        }

        loop {
            let mut changed = false;
            for (a, b) in &cycle_detector.edges {
                // Filter out other locally declared theorem grading axioms.
                if let Some(n) = filter.get(a) {
                    if !n.iter().any(|n| *n == self.name) {continue};
                }

                let gr_a = grades.get(a);
                let new_gr: (usize, bool) = match (gr_a, grades.get(b)) {
                    (Some((gr_a, false)), Some((gr_b, _))) => ((*gr_a).max(*gr_b), false),
                    (Some((gr_a, true)), _) => (*gr_a, true),
                    (Some((gr_a, locked)), None) => (*gr_a, *locked),
                    (None, Some((gr_b, _))) => (*gr_b, false),
                    (None, None) => continue,
                };
                if Some(&new_gr) != gr_a {
                    grades.insert(*a, new_gr);
                    changed = true;
                }
            }
            if !changed {break}
        }

        // Don't output empty theorem grading.
        if grades.len() == 0 {return}
        let mut any = false;
        'outer: for gr in 0..self.args.len() {
            for (gr_key, (gr_val, _)) in &grades {
                if *gr_val == gr {
                    for (name, id) in &cycle_detector.ids {
                        if id == gr_key && name.0.len() == 0 {
                            any = true;
                            break 'outer;
                        }
                    }
                }
            }
        }
        if !any {return}

        writeln!(s, "    {}: {{", self.name).unwrap();
        for gr in 0..self.args.len() {
            let mut fns: Vec<Name> = vec![];
            for (gr_key, (gr_val, _)) in &grades {
                if *gr_val == gr {
                    for (name, id) in &cycle_detector.ids {
                        if id == gr_key {
                            fns.push(name.clone());
                            break;
                        }
                    }
                }
            }

            fns.sort();
            write!(s, "        {}: [", gr + 1).unwrap();
            let mut any: u8 = 0;
            for (ns, _) in &fns {
                if ns.len() != 0 {continue};

                any = 2.min(any + 1);
                if any == 2 {break};
            }
            if any == 2 {
                for (ns, f) in &fns {
                    if ns.len() != 0 {continue};

                    write!(s, "\n            {},", f).unwrap();
                }
            } else if any == 1 {
                for (ns, f) in &fns {
                    if ns.len() != 0 {continue};

                    write!(s, "{}", f).unwrap();
                }
            }
            if any == 2 {
                writeln!(s, "\n        ];").unwrap();
            } else {
                writeln!(s, "];").unwrap();
            }
        }
        writeln!(s, "    }};").unwrap();
    }
}
