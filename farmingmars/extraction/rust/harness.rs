// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let m = t.uint();
    let ph = array((0..n).map(|_| t.next().parse::<f64>().unwrap()).collect(), 0.0);
    let mut ls = Vec::new(); let mut rs = Vec::new();
    for _ in 0..m { ls.push(t.uint()); rs.push(t.uint()); }
    lines(values(&run()(ph, ints(ls), ints(rs))).into_iter().map(|b| if b { "usable" } else { "unusable" }))
}
fn main() { entry(solve); }
