// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let m = t.uint();
    let mut ks = Vec::new(); let mut wins = Vec::new(); let mut ls = Vec::new();
    for _ in 0..m { ks.push(t.uint()); wins.push(t.next() == ">"); ls.push(t.uint()); }
    if run()(n, ints(ks), array(wins, false), ints(ls)) { "consistent\n" } else { "inconsistent\n" }.into()
}
fn main() { entry(solve); }
