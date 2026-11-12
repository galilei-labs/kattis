// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 512;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint();
    if run()(t.uints(n)) { "canonical\n" } else { "non-canonical\n" }.into()
}
fn main() { entry(solve); }
