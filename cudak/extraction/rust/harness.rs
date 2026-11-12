// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let result = run()(t.uint(), t.uint(), t.uint());
    let (count, minimum) = &result; format!("{count}\n{minimum}\n")
}
fn main() { entry(solve); }
