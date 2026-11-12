// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 512;
use kattis_io::*;

fn solve(input: String, output: &mut dyn std::io::Write) {
    let mut input_lines = input.lines(); let q: usize = input_lines.next().unwrap().trim().parse().unwrap();
    let mut ids = Vec::with_capacity(q); let mut ops = Vec::with_capacity(q);
    let mut xs = Vec::with_capacity(q); let mut ys = Vec::with_capacity(q);
    // Optional arguments stop at a newline, exactly as in the OCaml wrapper.
    for line in input_lines.filter(|s| !s.trim().is_empty()).take(q) {
        let mut t = Tokens::new(line); ids.push(t.int());
        let op = t.next(); assert_eq!(op.len(),1); ops.push(op.as_bytes()[0] as u64);
        xs.push(t.optional().map(|s| signed(s.parse().unwrap())).unwrap_or(0));
        ys.push(t.optional().map(|s| signed(s.parse().unwrap())).unwrap_or(0));
    }
    drop(input);
    let result = run()(ints(ids),ints(ops),ints(xs),ints(ys));
    for i in 0..result.length() {
        match crate::rocq_array::get(&result, i).as_ref() {
            option::None { } => writeln!(output, "-").unwrap(),
            option::Some(v) => writeln!(output, "{}", decoded(*v)).unwrap(),
        }
    }
}
fn main() { entry_streaming(solve); }
