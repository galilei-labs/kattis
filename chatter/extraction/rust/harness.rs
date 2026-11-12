// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let result = run()(n.parse().unwrap(), t.uint(), t.uint(), t.uint(), t.uint());
        let (g, a) = &result; out.push_str(&g.to_string());
        for item in values(a) {
            let (s, k) = &item;
            out.push_str(&format!(" {s}"));
            if *k > 1 { out.push_str(&format!("x{k}")); }
        }
        out.push('\n');
    }
    out
}
fn main() { entry(solve); }
