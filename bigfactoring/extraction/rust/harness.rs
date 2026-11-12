// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let n = rocq_bigint::of_string(input.trim()).expect("invalid decimal integer");
    format!("{}\n", numbers(values(&run()(n))))
}
fn main() { entry(solve); }
