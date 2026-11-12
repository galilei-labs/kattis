// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut lines = input.lines(); let mut out = String::new();
    while let Some(text) = lines.next() {
        let result = run()(submission_io::string(text));
        let mut t = submission_io::Tokens::new(lines.next().unwrap()); let n = t.uint();
        writeln!(out, "{}", submission_io::numbers((0..n).map(|_| *result.get(t.uint())))).unwrap();
    }
    out
}); }
