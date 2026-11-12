// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    use std::fmt::Write;
    let mut t = submission_io::Tokens::new(input); let mut out = String::new();
    loop { let n = t.uint(); let m = t.uint(); let q = t.uint();
        if n == 0 && m == 0 && q == 0 { break; }
        if !out.is_empty() { out.push('\n'); }
        let (mut us, mut vs, mut ws) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..m { us.push(t.uint()); vs.push(t.uint()); ws.push(t.int()); }
        let result = run()(n, submission_io::ints(us), submission_io::ints(vs), submission_io::ints(ws));
        for _ in 0..q { let u = t.uint(); let v = t.uint(); match &**result.get(u).get(v) {
            answer::Impossible {} => { writeln!(out, "Impossible").unwrap(); },
            answer::NegInfinity {} => { writeln!(out, "-Infinity").unwrap(); },
            answer::Distance(value) => { writeln!(out, "{}", submission_io::decoded(*value)).unwrap(); }
        } }
    }
    out
}); }
