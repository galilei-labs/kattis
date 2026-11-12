// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let result = run()(t.uints(n));
    let (x, y) = &result; format!("{x} {y}\n")
}
fn main() { entry(solve); }
