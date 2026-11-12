// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n: u64 = n.parse().unwrap(); let mut x1 = Vec::new(); let mut y1 = Vec::new(); let mut x2 = Vec::new(); let mut y2 = Vec::new();
        for _ in 0..n { x1.push(t.int()); y1.push(t.int()); x2.push(t.int()); y2.push(t.int()); }
        out.push_str(if run()(ints(x1), ints(y1), ints(x2), ints(y2)) { "1\n" } else { "0\n" });
    }
    out
}
fn main() { entry(solve); }
