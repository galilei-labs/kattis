// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut input_lines = input.lines(); let mut english = Vec::new(); let mut foreign = Vec::new();
    for line in input_lines.by_ref() {
        if line.trim().is_empty() { break; }
        let mut t = Tokens::new(line); english.push(string(t.next())); foreign.push(string(t.next()));
    }
    let message = input_lines.flat_map(str::split_whitespace).map(string).collect();
    let result = run()(array(english, string("")), array(foreign, string("")), array(message, string("")));
    lines(values(&result).iter().map(|item| match item.as_ref() {
        option::None { } => "eh".into(), option::Some(s) => text(s),
    }))
}
fn main() { entry(solve); }
