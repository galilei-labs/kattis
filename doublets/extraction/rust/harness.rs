// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut input_lines = input.lines(); let mut dictionary = Vec::new();
    for line in input_lines.by_ref() { if line.trim().is_empty() { break; } dictionary.push(string(line.trim())); }
    let mut src = Vec::new(); let mut dst = Vec::new();
    for line in input_lines { if line.trim().is_empty() { continue; } let mut t = Tokens::new(line); src.push(string(t.next())); dst.push(string(t.next())); }
    let result = run()(array(dictionary,string("")),array(src,string("")),array(dst,string("")));
    let mut out = String::new();
    for (i, item) in values(&result).iter().enumerate() {
        if i > 0 { out.push('\n'); }
        match item.as_ref() { option::None { } => out.push_str("No solution.\n"), option::Some(a) => out.push_str(&lines(values(a).iter().map(text))) }
    }
    out
}
fn main() { entry(solve); }
