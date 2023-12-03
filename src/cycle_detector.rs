use crate::*;

use std::sync::mpsc::Receiver;

pub struct CycleDetector {
    pub ids: HashMap<Arc<String>, usize>,
    pub edges: Vec<(usize, usize)>,
}

impl CycleDetector {
    /// Constructs cycle detector from receiver.
    ///
    /// Remember to drop the last sender before calling this.
    pub fn new(rc: Receiver<(Arc<String>, Arc<String>)>) -> CycleDetector {
        let mut ids = HashMap::default();
        let mut edges = vec![];
        for (a, b) in rc.iter() {
            let a_id = if !ids.contains_key(&a) {
                let id = ids.len();
                ids.insert(a, id);
                id
            } else {*ids.get(&a).unwrap()};
            let b_id = if !ids.contains_key(&b) {
                let id = ids.len();
                ids.insert(b, id);
                id
            } else {*ids.get(&b).unwrap()};
            edges.push((a_id, b_id));
        }
        edges.sort();
        edges.dedup();
        CycleDetector {
            ids,
            edges,
        }
    }

    /// Detects cycles, if any.
    pub fn cycles(&self) -> Option<Vec<(usize, usize)>> {
        /*
        let mut trace = vec![];
        for &(a, b) in &self.edges {
            trace.clear();
            trace.push(a);
            trace.push(b);
            loop {
                let mut changed = false;
                for &(c, d) in &self.edges {
                    if c == *trace.last().unwrap() {
                        if trace.iter().any(|&n| n == d) {
                            trace.push(d);
                            return Some(trace);
                        }
                        trace.push(d);
                        changed = true;
                    }
                }
                if !changed {break}
            }
        }
        */
        let mut visited = vec![false; self.ids.len()];
        // Mark all leaves.
        for &(a, b) in &self.edges {
            if !self.edges.iter().any(|&(_, d)| d == a) {
                visited[a] = true;
            }
            if !self.edges.iter().any(|&(c, _)| c == b) {
                visited[b] = true;
            }
        }
        loop {
            let mut changed = false;
            for &(a, b) in &self.edges {
                if !visited[a] {
                    if self.edges.iter().all(|&(c, d)| a != c || visited[d]) {
                        visited[a] = true;
                        changed = true;
                    }
                }
                if !visited[b] {
                    if self.edges.iter().all(|&(c, d)| b != d || visited[c]) {
                        visited[b] = true;
                        changed = true;
                    }
                }
            }
            if !changed {break}
        }

        let mut cycles = vec![];
        for &(a, b) in &self.edges {
            if !visited[a] && !visited[b] {cycles.push((a, b))}
        }
        if cycles.len() == 0 {None} else {Some(cycles)}
    }
}

