// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let b = t.uint(); let h = t.uint(); let r = t.uint(); let c = t.uint();
    let rows = (0..r).map(|_| {
        let digits = t.next(); assert_eq!(digits.len(), c as usize);
        ints(digits.bytes().map(|x| (x - b'0') as u64).collect())
    }).collect();
    format!("{}\n", run()(b, h, array(rows, ints(vec![]))))
}
fn main() { entry(solve); }
