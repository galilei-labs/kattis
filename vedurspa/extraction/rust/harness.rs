// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut input_lines = input.lines(); let mut head = Tokens::new(input_lines.next().unwrap()); let n = head.uint(); let m = head.uint();
    input_lines.next().unwrap(); // column headings, as in the submitted wrapper
    let data = input_lines.collect::<Vec<_>>().join("\n"); let mut t = Tokens::new(&data);
    let mut ts = Vec::new(); let mut ds = Vec::new(); let mut ss = Vec::new(); let mut hs = Vec::new();
    fn float(s: &str) -> Rc<option<f64>> { Rc::new(if s == "-" { option::None { } } else { option::Some(s.parse().unwrap()) }) }
    fn uint(s: &str) -> Rc<option<u64>> { Rc::new(if s == "-" { option::None { } } else { option::Some(s.parse().unwrap()) }) }
    for _ in 0..n { ts.push(float(t.next())); ds.push(uint(t.next())); ss.push(float(t.next())); hs.push(uint(t.next())); }
    let result = run()(array(ts,float("-")),array(ds,uint("-")),array(ss,float("-")),array(hs,uint("-")),m);
    let (r, oh) = result; let (r, os) = r; let (ot, od) = r;
    fn pf(s: &Rc<option<f64>>) -> String { match s.as_ref() { option::None { } => "-".into(), option::Some(f) => { let s = format!("{f:.1}"); if s == "-0.0" { "0.0".into() } else { s } } } }
    fn pi(s: &Rc<option<u64>>) -> String { match s.as_ref() { option::None { } => "-".into(), option::Some(w) => w.to_string() } }
    lines((0..ot.length()).map(|i| format!("{} {} {} {}",pf(&rocq_array::get(&ot,i)),pi(&rocq_array::get(&od,i)),pf(&rocq_array::get(&os,i)),pi(&rocq_array::get(&oh,i)))))
}
fn main() { entry(solve); }
