// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    loop { let n = t.uint(); if n == 0 { break; }
        let (mut xs, mut ys) = (Vec::new(), Vec::new());
        for _ in 0..n { xs.push(t.int()); ys.push(t.int()); }
        let result = run()(submission_io::ints(xs.clone()), submission_io::ints(ys.clone()));
        writeln!(out, "{}", result.length()).unwrap();
        for i in 0..result.length() { let j = *result.get(i) as usize;
            writeln!(out, "{} {}", submission_io::decoded(xs[j]), submission_io::decoded(ys[j])).unwrap();
        }
    }
    out
}); }
