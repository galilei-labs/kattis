// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint();
    let tokens = (0..n).map(|_| Rc::new(match t.next() {
        "(" => token::Open { }, ")" => token::Close { }, n => token::Num(n.parse().unwrap()),
    })).collect();
    format!("{}\n", run()(array(tokens, Rc::new(token::Open { }))))
}
fn main() { entry(solve); }
