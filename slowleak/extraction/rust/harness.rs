// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let m = t.uint(); let k = t.uint(); let d = t.uint();
    let st = t.uints(k); let [i,j,w] = columns(&mut t,m,false);
    match run()(n,d,st,i,j,w).as_ref() { option::None { } => "stuck\n".into(), option::Some(x) => format!("{x}\n") }
}
fn main() { entry(solve); }
