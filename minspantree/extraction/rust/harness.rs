// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    loop { let n = t.uint(); let m = t.uint(); if n == 0 && m == 0 { break; }
        let (mut us, mut vs, mut ws) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..m { us.push(t.uint()); vs.push(t.uint()); ws.push(t.int()); }
        let result = run()(n, submission_io::ints(us.clone()), submission_io::ints(vs.clone()), submission_io::ints(ws));
        match &*result {
            option::None {} => { writeln!(out, "Impossible").unwrap(); },
            option::Some(pair) => {
                let pair: &(_, _) = pair;
                let (cost, indices) = pair;
                writeln!(out, "{}", submission_io::decoded(*cost)).unwrap();
                let mut edges = (0..indices.length()).map(|i| {
                    let j = *indices.get(i) as usize; (us[j].min(vs[j]), us[j].max(vs[j]))
                }).collect::<Vec<_>>();
                edges.sort();
                for (u, v) in edges { writeln!(out, "{} {}", u, v).unwrap(); }
            }
        }
    }
    out
}); }
