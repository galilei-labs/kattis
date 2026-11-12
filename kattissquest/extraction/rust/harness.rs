// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let n = t.uint();
    let commands = (0..n).map(|_| Rc::new(if t.next() == "add" {
        command::Add { energy: t.uint(), gold: t.uint() }
    } else { command::Query { energy: t.uint() } })).collect();
    lines(values(&run()(array(commands,Rc::new(command::Query { energy: 0 })))))
}
fn main() { entry(solve); }
