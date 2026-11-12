// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n: u64 = n.parse().unwrap(); if n == 0 { break; }
        let [ys,rs] = columns(&mut t,n,true); let m = t.uint(); let [qy,qx] = columns(&mut t,m,true);
        if !out.is_empty() { out.push('\n'); }
        out.push_str(&lines(values(&run()(ys,rs,qy,qx)).into_iter().map(|item| match item {
            answer::Ans_true { } => "true", answer::Ans_maybe { } => "maybe", answer::Ans_false { } => "false",
        })));
    }
    out
}
fn main() { entry(solve); }
