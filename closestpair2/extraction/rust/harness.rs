// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

// Match the submitted exact-hundredths interface, not the old float variant.
fn hundredths(s: &str) -> u64 {
    let negative = s.starts_with('-');
    let s = s.trim_start_matches(['-', '+']);
    let (whole, fraction) = s.split_once('.').unwrap_or((s, ""));
    assert!(fraction.len() <= 2);
    let mut n: i64 = whole.parse::<i64>().unwrap() * 100;
    if !fraction.is_empty() { n += fraction.parse::<i64>().unwrap() * if fraction.len() == 1 { 10 } else { 1 }; }
    signed(if negative { -n } else { n })
}
fn solve_input(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(n) = t.optional() {
        let n: u64 = n.parse().unwrap(); if n == 0 { break; }
        let mut xs = Vec::new(); let mut ys = Vec::new();
        let mut original = Vec::new();
        for _ in 0..n { let x = t.next(); let y = t.next(); xs.push(hundredths(x)); ys.push(hundredths(y)); original.push((x, y)); }
        let result = run()(ints(xs), ints(ys));
        let (i, j) = &result;
        let (x, y) = original[*i as usize]; let (u, v) = original[*j as usize];
        out.push_str(&format!("{x} {y} {u} {v}\n"));
    }
    out
}
fn main() { entry(solve_input); }
