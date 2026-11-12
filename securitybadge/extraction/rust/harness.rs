// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let l = t.uint(); let b = t.uint(); let s = t.uint(); let d = t.uint();
    let [a,z,x,y] = columns(&mut t,l,false); format!("{}\n",run()(n,b,s,d,a,z,x,y))
}
fn main() { entry(solve); }
