// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); format!("{}\n", numbers(values(&run()(n, t.signed_ints(n+1))).into_iter().map(decoded)))
}
fn main() { entry(solve); }
