// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 512;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    let n = t.uint(); let q = t.uint();
    let (mut ops, mut a, mut b) = (Vec::new(), Vec::new(), Vec::new());
    for _ in 0..q { ops.push(t.next() == "="); a.push(t.uint()); b.push(t.uint()); }
    let result = run()(n, submission_io::array(ops.clone(), false), submission_io::ints(a), submission_io::ints(b));
    for (i, is_union) in ops.iter().enumerate() { if !is_union {
        writeln!(out, "{}", if *result.get(i as u64) { "yes" } else { "no" }).unwrap();
    } }
    out
}); }
