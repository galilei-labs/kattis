// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    while let Some(c) = t.optional() {
        let n = t.uint(); let (mut values, mut weights) = (Vec::new(), Vec::new());
        for _ in 0..n { values.push(t.uint()); weights.push(t.uint()); }
        let result = run()(c.parse().unwrap(), submission_io::ints(values), submission_io::ints(weights));
        let pair: &(_, _) = &result;
        let (_, indices) = pair;
        writeln!(out, "{}", indices.length()).unwrap();
        writeln!(out, "{}", submission_io::numbers((0..indices.length()).map(|i| *indices.get(i)))).unwrap();
    }
    out
}); }
