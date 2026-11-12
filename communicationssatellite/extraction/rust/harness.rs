// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let [x,y,r] = columns(&mut t, n, true);
    format!("{:.10}\n", run()(x,y,r))
}
fn main() { entry(solve); }
