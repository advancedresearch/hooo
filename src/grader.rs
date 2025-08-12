use crate::*;

use cycle_detector::CycleDetector;
use std::collections::HashMap;

pub fn grade_report<I: Iterator<Item = (Arc<String>, Vec<Arc<String>>)>>(
    iter: I,
    cycle_detector: &CycleDetector,
) -> String {
    use std::fmt::Write;

    let mut s = String::new();
    writeln!(&mut s, "grades {{").unwrap();
    for (name, args) in iter {
        Grader {name, args, cycle_detector}.report(&mut s);
    }
    writeln!(&mut s, "}}").unwrap();
    s
}

pub struct Grader<'a> {
    pub name: Arc<String>,
    pub args: Vec<Arc<String>>,
    pub cycle_detector: &'a CycleDetector,
}

impl<'a> Grader<'a> {
    pub fn report(&self, s: &mut String) {
        use std::fmt::Write;

        // Stores grades and whether they are locked.
        let mut grades: HashMap<usize, (usize, bool)> = HashMap::new();

        for (gr, arg) in self.args.iter().enumerate() {
            if let Some(id) = self.cycle_detector.ids.get(arg) {
                grades.insert(*id, (gr, true));
            } else {
                eprintln!("ERROR:\n");
                eprintln!("Grader check error #100:");
                eprintln!("Could not find function `{}`", arg);
            }
        }

        loop {
            let mut changed = false;
            for (a, b) in &self.cycle_detector.edges {
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

        writeln!(s, "    {}: {{", self.name).unwrap();
        for gr in 0..self.args.len() {
            let mut fns: Vec<Arc<String>> = vec![];
            for (gr_key, (gr_val, _)) in &grades {
                if *gr_val == gr {
                    for (name, id) in &self.cycle_detector.ids {
                        if id == gr_key {
                            fns.push(name.clone());
                            break;
                        }
                    }
                }
            }

            fns.sort();
            write!(s, "        {}: [", gr + 1).unwrap();
            let mut first = true;
            for f in &fns {
                if !first {
                    write!(s, ", ").unwrap();
                } else {
                    first = false;
                }
                write!(s, "{}", f).unwrap();
            }
            writeln!(s, "];").unwrap();
        }
        writeln!(s, "    }};").unwrap();
    }
}
