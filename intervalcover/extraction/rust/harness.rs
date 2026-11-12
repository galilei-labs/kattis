// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    while let Some(a) = t.optional() {
        let a: f64 = a.parse().unwrap(); let b: f64 = t.next().parse().unwrap();
        let n = t.uint(); let (mut left, mut right) = (Vec::new(), Vec::new());
        for _ in 0..n {
            left.push(t.next().parse::<f64>().unwrap());
            right.push(t.next().parse::<f64>().unwrap());
        }
        let result = run()(a, b, submission_io::array(left, 0.0), submission_io::array(right, 0.0));
        match result.as_ref() {
            option::None { .. } => writeln!(out, "impossible").unwrap(),
            option::Some(indices) => {
                writeln!(out, "{}", indices.length()).unwrap();
                writeln!(out, "{}", submission_io::numbers((0..indices.length()).map(|i| *indices.get(i)))).unwrap();
            }
        }
    }
    out
}); }
