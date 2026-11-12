// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let input = input.replace(':', " ");
    let mut t = Tokens::new(&input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n = n.parse().unwrap(); if n == 0 { break; }
        out.push_str(if run()(t.uints(n)) { "yes\n" } else { "no\n" });
    }
    out
}
fn main() { entry(solve); }
