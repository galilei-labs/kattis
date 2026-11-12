// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let m = t.uint();
    let mut read = |k| {
        let mut a = Vec::new(); let mut r = Vec::new(); let mut b = Vec::new();
        for _ in 0..k {
            a.push(string(t.next())); r.push(match t.next() { "is-a" => relkind::IsA { }, "has-a" => relkind::HasA { }, _ => panic!("unknown relation") }); b.push(string(t.next()));
        }
        (array(a,string("")),array(r,relkind::IsA { }),array(b,string("")))
    };
    let (a,r,b) = read(n); let (qa,qr,qb) = read(m);
    lines(values(&run()(a,r,b,qa,qr,qb)).into_iter().enumerate().map(|(i,b)| format!("Query {}: {}",i+1,b)))
}
fn main() { entry(solve); }
