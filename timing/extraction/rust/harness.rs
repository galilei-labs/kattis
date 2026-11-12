// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let cases = t.uint(); let mut out = String::new();
    for _ in 0..cases {
        let n = t.uint(); let l = t.uint(); let time = t.uint();
        let u = array((0..n).map(|_| t.next().parse::<f64>().unwrap()).collect(),0.0);
        let mut src = Vec::new(); let mut dst = Vec::new(); let mut frac = Vec::new();
        for _ in 0..l { src.push(t.uint()); dst.push(t.uint()); frac.push(t.next().parse::<f64>().unwrap()); }
        out.push_str(&format!("{:.9}\n",run()(time,u,ints(src),ints(dst),array(frac,0.0))));
    }
    out
}
fn main() { entry(solve); }
