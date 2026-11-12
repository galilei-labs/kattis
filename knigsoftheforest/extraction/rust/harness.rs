// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let k = t.uint(); let n = t.uint(); let y = t.uint(); let p = t.uint();
    let mut ys = Vec::new(); let mut ps = Vec::new();
    for _ in 0..n+k-2 { ys.push(t.uint()); ps.push(t.uint()); }
    match run()(k, n, y, p, ints(ys), ints(ps)).as_ref() {
        option::None { } => "unknown\n".into(), option::Some(w) => format!("{w}\n"),
    }
}
fn main() { entry(solve); }
