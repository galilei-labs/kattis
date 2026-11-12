// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let result = run()(t.signed_ints(n.parse().unwrap()));
        writeln!(out, "{}", result.length()).unwrap();
        writeln!(out, "{}", submission_io::numbers((0..result.length()).map(|i| *result.get(i)))).unwrap();
    }
    out
}); }
