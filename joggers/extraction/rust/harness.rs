// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let s = t.uint();
    let mut a = Vec::new(); let mut b = Vec::new(); let mut d = Vec::new();
    for _ in 0..n-1 { a.push(t.uint()); b.push(t.uint()); d.push(t.uint()); }
    let k = t.uint(); let l = t.uints(k);
    format!("{}\n", run()(n, s, ints(a), ints(b), ints(d), l))
}
fn main() { entry(solve); }
