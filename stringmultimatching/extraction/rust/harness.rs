// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut lines = input.lines(); let mut out = String::new();
    while let Some(count) = lines.next() {
        let n: usize = count.parse().unwrap();
        let patterns = (0..n).map(|_| submission_io::string(lines.next().unwrap())).collect();
        let text = submission_io::string(lines.next().unwrap());
        let result = run()(submission_io::array(patterns, submission_io::string("")), text);
        for i in 0..result.length() { let row = result.get(i);
            writeln!(out, "{}", submission_io::numbers((0..row.length()).map(|j| *row.get(j)))).unwrap();
        }
    }
    out
}); }
