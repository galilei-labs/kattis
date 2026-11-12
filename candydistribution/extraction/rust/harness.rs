// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let cases = t.uint();
    lines((0..cases).map(|_| match run()(t.uint(), t.uint()).as_ref() {
        option::None { } => "IMPOSSIBLE".into(), option::Some(b) => b.to_string(),
    }))
}
fn main() { entry(solve); }
