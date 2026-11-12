// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let cases = t.uint(); let mut out = String::new();
    for i in 1..=cases { out.push_str(&format!("Case #{i}: {}\n", run()(t.uint(), t.uint(), t.uint()))); }
    out
}
fn main() { entry(solve); }
