// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve_input(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n: u64 = n.parse().unwrap(); if n == 0 { break; }
        let mut row = || array((0..n).map(|_| t.next().parse::<f64>().unwrap()).collect(),0.0);
        let a = array((0..n).map(|_| row()).collect(),array(vec![],0.0)); let b = row();
        out.push_str(&match run()(n,a,b).as_ref() {
            outcome::Unique(x) => format!("{}\n", numbers(values(x))),
            outcome::Multiple { } => "multiple\n".into(), outcome::Inconsistent { } => "inconsistent\n".into(),
        });
    }
    out
}
fn main() { entry(solve_input); }
