// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let p = t.uints(n); let [u,v,w] = columns(&mut t,n-1,false);
    format!("{}\n",run()(p,u,v,w))
}
fn main() { entry(solve); }
