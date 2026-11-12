// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let mut out = String::new();
    while let Some(name) = t.optional() {
        let s = match name { "RUBEN" => player::Ruben { }, "ALBERT" => player::Albert { }, _ => panic!("unknown player") };
        let n = t.uint(); let [x,y,z] = columns(&mut t,n,false);
        out.push_str(match run()(s,x,y,z) { player::Ruben { } => "RUBEN\n", player::Albert { } => "ALBERT\n" });
    }
    out
}
fn main() { entry(solve); }
