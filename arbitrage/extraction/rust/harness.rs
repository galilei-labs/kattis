// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let input = input.replace(':', " "); let mut t = Tokens::new(&input); let mut out = String::new();
    while let Some(c) = t.optional() {
        let c: u64 = c.parse().unwrap(); if c == 0 { break; }
        let mut index = std::collections::HashMap::new();
        for i in 0..c { index.insert(t.next(), i); }
        let r = t.uint(); let mut src = Vec::new(); let mut dst = Vec::new(); let mut a = Vec::new(); let mut b = Vec::new();
        for _ in 0..r { src.push(index[t.next()]); dst.push(index[t.next()]); a.push(t.uint()); b.push(t.uint()); }
        out.push_str(if run()(c, ints(src), ints(dst), ints(a), ints(b)) { "Arbitrage\n" } else { "Ok\n" });
    }
    out
}
fn main() { entry(solve); }
