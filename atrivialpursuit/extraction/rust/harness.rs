// I/O adapter ported from the historical Rust survey; no algorithm changes.
// Debug frames need more stack; preserve the historical optimized setting.
#[cfg(debug_assertions)]
const STACK_MIB: usize = 768;
#[cfg(not(debug_assertions))]
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input);
    let p = t.uint(); let n = t.uint(); let m = t.uint();
    let gs = t.uints(n); let ls = t.uints(m);
    format!("{}\n", run()(p, gs, ls))
}
fn main() { entry(solve); }
