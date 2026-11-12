// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let result = run()(string(input.trim())); let (i, j) = &result; format!("{i} {j}\n")
}
fn main() { entry(solve); }
