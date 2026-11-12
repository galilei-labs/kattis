// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    loop { let n = t.uint(); if n == 0 { break; }
        let (mut xs, mut ys) = (Vec::new(), Vec::new());
        for _ in 0..n { xs.push(t.int()); ys.push(t.int()); }
        let twice = submission_io::decoded(run()(submission_io::ints(xs), submission_io::ints(ys)));
        writeln!(out, "{} {}.{}", if twice < 0 { "CW" } else { "CCW" },
                 twice.abs() / 2, if twice.abs() % 2 == 0 { 0 } else { 5 }).unwrap();
    }
    out
}); }
