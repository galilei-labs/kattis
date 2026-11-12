// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let ss = words(&mut t, n);
    let mut a = Vec::new(); let mut b = Vec::new();
    for _ in 0..n-1 { a.push(t.uint()); b.push(t.uint()); }
    format!("{}\n", text(&run()(ss, ints(a), ints(b))))
}
fn main() { entry(solve); }
