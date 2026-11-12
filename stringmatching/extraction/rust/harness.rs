// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut input_lines = input.lines(); let mut out = String::new();
    while let Some(pattern) = input_lines.next() {
        let txt = input_lines.next().unwrap_or(""); out.push_str(&format!("{}\n",numbers(values(&run()(string(pattern),string(txt))))));
    }
    out
}
fn main() { entry(solve); }
