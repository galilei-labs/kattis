// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint();
    let mut a = Vec::new(); let mut b = Vec::new();
    for _ in 0..n { a.push(t.uint()); b.push(t.uint()); }
    let r = run()(ints(a), ints(b));
    format!("{}\n{}", r.length(), lines(values(&r)))
}
fn main() { entry(solve); }
