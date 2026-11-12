// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let y = t.uint(); let x = t.uint(); let xi = t.uint();
    let result = run()(y, x, xi, words(&mut t, y));
    match result.as_ref() { option::None { } => "begin repairs\n".into(), option::Some(n) => format!("{n}\n") }
}
fn main() { entry(solve); }
