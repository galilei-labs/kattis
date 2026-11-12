// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let mut src = Vec::new(); let mut dst = Vec::new();
    for _ in 0..n { src.push(string(t.next())); dst.push(string(t.next())); }
    let result = run()(array(src,string("")),array(dst,string("")));
    let (groups, avoid) = &result; let mut out = String::new();
    for group in values(groups) { out.push_str(&format!("okay {}\n",values(&group).iter().map(text).collect::<Vec<_>>().join(" "))); }
    if avoid.length() > 0 { out.push_str(&format!("avoid {}\n",values(avoid).iter().map(text).collect::<Vec<_>>().join(" "))); }
    out
}
fn main() { entry(solve); }
