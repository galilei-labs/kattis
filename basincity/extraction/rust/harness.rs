// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let k = t.uint(); let n = t.uint();
    let rows = (0..n).map(|_| { let n = t.uint(); t.uints(n) }).collect();
    if run()(k, array(rows, ints(vec![]))) { "possible\n" } else { "impossible\n" }.into()
}
fn main() { entry(solve); }
