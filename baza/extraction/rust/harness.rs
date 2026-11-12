// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint();
    let db = array((0..n).map(|_| string(t.next())).collect(), string(""));
    let n = t.uint();
    let queries = array((0..n).map(|_| string(t.next())).collect(), string(""));
    lines(values(&run()(db, queries)))
}
fn main() { entry(solve); }
