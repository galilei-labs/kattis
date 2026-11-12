// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    let text = submission_io::string(t.next()); let q = t.uint();
    let (mut ls, mut rs) = (Vec::new(), Vec::new());
    for _ in 0..q { ls.push(t.uint()); rs.push(t.uint()); }
    // Choose the polynomial-family key externally, as required by the source contract.
    use std::io::Read;
    let mut bytes = [0u8; 8];
    std::fs::File::open("/dev/urandom").unwrap().read_exact(&mut bytes).unwrap();
    let key = u64::from_ne_bytes(bytes) % ((1u64 << 61) - 1);
    let result = run()(key, text, submission_io::ints(ls), submission_io::ints(rs));
    for i in 0..result.length() { writeln!(out, "{}", result.get(i)).unwrap(); }
    out
}); }
