// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    for case in 1..=t.uint() { let n = t.uint();
        writeln!(out, "Case #{}: {}", case, run()(t.uints(n))).unwrap();
    }
    out
}); }
