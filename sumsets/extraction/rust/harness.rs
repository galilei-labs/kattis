// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint();
    match run()(t.signed_ints(n)).as_ref() { option::None { } => "no solution\n".into(), option::Some(d) => format!("{}\n",decoded(*d)) }
}
fn main() { entry(solve); }
