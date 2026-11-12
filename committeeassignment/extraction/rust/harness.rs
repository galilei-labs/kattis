// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n: u64 = n.parse().unwrap(); let m = t.uint(); if n == 0 && m == 0 { break; }
        let mut a = Vec::new(); let mut b = Vec::new();
        for _ in 0..m { a.push(string(t.next())); b.push(string(t.next())); }
        out.push_str(&format!("{}\n", run()(n, array(a, string("")), array(b, string("")))));
    }
    out
}
fn main() { entry(solve); }
