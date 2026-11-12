// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut input_lines = input.lines().filter(|s| !s.trim().is_empty());
    let cases: u64 = input_lines.next().unwrap().trim().parse().unwrap(); let mut out = String::new();
    for _ in 0..cases {
        let mut t = Tokens::new(input_lines.next().unwrap()); let n = t.uint(); let m = t.uint();
        let default = Rc::new(literal::X(0));
        let clauses = (0..m).map(|_| {
            let lits = input_lines.next().unwrap().split('v').map(|s| {
                let s = s.trim(); let negative = s.starts_with('~');
                let v = s.trim_start_matches('~').trim_start_matches('X').parse::<u64>().unwrap();
                Rc::new(if negative { literal::NotX(v) } else { literal::X(v) })
            }).collect(); array(lits,default.clone())
        }).collect();
        out.push_str(if run()(n,array(clauses,array(vec![],default))) { "satisfiable\n" } else { "unsatisfiable\n" });
    }
    out
}
fn main() { entry(solve); }
