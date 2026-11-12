// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let time = t.uint();
    let mut cash = Vec::new(); let mut deadlines = Vec::new();
    for _ in 0..n { cash.push(t.uint()); deadlines.push(t.uint()); }
    format!("{}\n", run()(time, ints(cash), ints(deadlines)))
}
fn main() { entry(solve); }
