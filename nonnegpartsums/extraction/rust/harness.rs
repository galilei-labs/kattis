// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 512;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    loop { let n = t.uint(); if n == 0 { break; }
        writeln!(out, "{}", run()(t.signed_ints(n))).unwrap();
    }
    out
}); }
