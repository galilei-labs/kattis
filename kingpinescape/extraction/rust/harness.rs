// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let h = t.uint(); let mut a = Vec::new(); let mut b = Vec::new();
    for _ in 0..n-1 { a.push(t.uint()); b.push(t.uint()); }
    let result = run()(n, h, ints(a), ints(b)); let (xs, ys) = &result;
    let mut out = format!("{}\n", xs.length());
    for (x, y) in values(xs).into_iter().zip(values(ys)) { out.push_str(&format!("{x} {y}\n")); }
    out
}
fn main() { entry(solve); }
