// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let _n = t.uint(); let result = run()(string(t.next()));
    let (r, big) = &result; if *big { format!("{r:05}\n") } else { format!("{r}\n") }
}
fn main() { entry(solve); }
