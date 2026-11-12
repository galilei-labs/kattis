// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    let mut t = submission_io::Tokens::new(input);
    let n = t.uint();
    format!("{}\n", run()(t.uints(n)))
}); }
