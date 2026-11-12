// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let l = t.uint();
    let rows = (0..n).map(|_| t.uints(n)).collect();
    if run()(array(rows, ints(vec![])), l) { "possible\n" } else { "impossible\n" }.into()
}
fn main() { entry(solve); }
