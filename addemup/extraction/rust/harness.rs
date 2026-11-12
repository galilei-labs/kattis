// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input);
    let n = t.uint(); let target = t.uint();
    if run()(target, t.uints(n)) { "YES\n" } else { "NO\n" }.into()
}
fn main() { entry(solve); }
