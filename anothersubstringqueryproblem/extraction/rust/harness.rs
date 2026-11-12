// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let s = string(t.next()); let q = t.uint();
    let mut ts = Vec::new(); let mut ks = Vec::new();
    for _ in 0..q { ts.push(string(t.next())); ks.push(t.uint()); }
    lines(values(&run()(s, array(ts, string("")), ints(ks))).into_iter().map(decoded))
}
fn main() { entry(solve); }
