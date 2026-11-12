// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let cases = t.uint(); let mut out = String::new();
    for _ in 0..cases {
        let n = t.uint(); let result = run()(words(&mut t, n));
        out.push_str(&match result.as_ref() {
            option::None { } => "***".into(),
            option::Some(a) => values(a).iter().map(text).collect::<Vec<_>>().join("."),
        });
        out.push('\n');
    }
    out
}
fn main() { entry(solve); }
