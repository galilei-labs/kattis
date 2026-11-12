// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() { let n = n.parse().unwrap(); if n == 0 { break; } out.push_str(&format!("{}\n",run()(n))); }
    out
}
fn main() { entry(solve); }
