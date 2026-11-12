// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    for _ in 0..t.uint() {
        let n = t.uint(); let a = t.signed_ints(n + 1);
        let m = t.uint(); let b = t.signed_ints(m + 1);
        let result = run()(a, b);
        writeln!(out, "{}", n + m).unwrap();
        writeln!(out, "{}", submission_io::numbers((0..result.length()).map(|i|
            submission_io::decoded(*result.get(i))))).unwrap();
    }
    out
}); }
