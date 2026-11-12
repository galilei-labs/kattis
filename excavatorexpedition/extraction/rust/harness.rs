// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let v = t.uint(); let e = t.uint();
    let sites = string(t.next()); assert_eq!(rocq_string::length(&sites), v);
    let mut src = Vec::new(); let mut dst = Vec::new();
    for _ in 0..e { src.push(t.uint()); dst.push(t.uint()); }
    format!("{}\n", decoded(run()(sites, ints(src), ints(dst))))
}
fn main() { entry(solve); }
