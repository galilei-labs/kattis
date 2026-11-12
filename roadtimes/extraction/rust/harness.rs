// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint();
    let dist = array((0..n).map(|_| t.signed_ints(n)).collect(),ints(vec![]));
    let r = t.uint(); let [rs,rd,rt] = columns(&mut t,r,false);
    let q = t.uint(); let [qs,qd] = columns(&mut t,q,false); let original = (values(&qs),values(&qd));
    let result = run()(dist,rs,rd,rt,qs,qd);
    lines(values(&result).iter().enumerate().map(|(i,item)| {
        let (lo, hi) = item; format!("{} {} {:.9} {:.9}",original.0[i],original.1[i],lo,hi)
    }))
}
fn main() { entry(solve); }
