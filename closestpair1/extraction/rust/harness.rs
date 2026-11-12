// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n: u64 = n.parse().unwrap(); if n == 0 { break; }
        let mut xs = Vec::new(); let mut ys = Vec::new(); let mut original = Vec::new();
        for _ in 0..n { let x = t.next(); let y = t.next(); xs.push(x.parse().unwrap()); ys.push(y.parse().unwrap()); original.push((x,y)); }
        let result = run()(array(xs, 0.0), array(ys, 0.0)); let (i, j) = &result;
        let (x, y) = original[*i as usize]; let (u, v) = original[*j as usize]; out.push_str(&format!("{x} {y} {u} {v}\n"));
    }
    out
}
fn main() { entry(solve); }
