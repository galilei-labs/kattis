// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = if cfg!(debug_assertions) { 16384 } else { 1024 };
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut input_lines = input.lines(); let mut out = String::new();
    while let Some(pattern) = input_lines.next() {
        let txt = input_lines.next().unwrap_or("");
        let (first, second) = run()(string(pattern), string(txt));
        let mut positions = values(&first);
        positions.extend(values(&second));
        out.push_str(&format!("{}\n", numbers(positions)));
    }
    out
}
fn main() { entry(solve); }
