// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n: u64 = n.parse().unwrap(); let m = t.uint(); let q = t.uint(); let s = t.uint();
        if n == 0 && m == 0 && q == 0 && s == 0 { break; }
        let [u,v,w] = columns(&mut t,m,true); let qs = t.uints(q);
        if !out.is_empty() { out.push('\n'); }
        out.push_str(&lines(values(&run()(n,s,u,v,w,qs)).iter().map(|item| match item.as_ref() {
            answer::Dist { distance: d } => decoded(*d).to_string(), answer::Impossible { } => "Impossible".into(), answer::MinusInfinity { } => "-Infinity".into(),
        })));
    }
    out
}
fn main() { entry(solve); }
