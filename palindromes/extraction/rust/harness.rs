// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let s = string(t.next()); let m = t.uint(); let mut ls = Vec::new(); let mut rs = Vec::new();
    for _ in 0..m { ls.push(t.uint()); rs.push(t.uint()); }
    lines(values(&run()(s, ints(ls), ints(rs))))
}
fn main() { entry(solve); }
