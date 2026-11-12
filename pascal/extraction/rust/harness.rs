// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String { format!("{}\n", run()(Tokens::new(input).uint())) }
fn main() { entry(solve); }
