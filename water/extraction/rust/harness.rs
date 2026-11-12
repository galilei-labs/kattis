// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let p = t.uint(); let k = t.uint();
    let [pa,pb,pc] = columns(&mut t,p,false); let [ia,ib,ic] = columns(&mut t,k,false);
    lines(values(&run()(n,pa,pb,pc,ia,ib,ic)))
}
fn main() { entry(solve); }
