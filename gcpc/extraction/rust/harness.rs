// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint(); let m = t.uint();
    let mut teams = Vec::new(); let mut penalties = Vec::new();
    for _ in 0..m { teams.push(t.uint()); penalties.push(t.uint()); }
    lines(values(&run()(n, ints(teams), ints(penalties))))
}
fn main() { entry(solve); }
