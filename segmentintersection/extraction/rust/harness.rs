// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

// The submitted wrapper rounds exact rationals half away from zero, with
// integer arithmetic and no negative zero (not binary64's tie-to-even).
fn hundredths(num: u64, den: u64) -> String {
    let n = decoded(num) as i128; let d = decoded(den) as i128;
    assert!(d > 0); let h = (200*n.abs()+d)/(2*d);
    format!("{}{}.{:02}",if h != 0 && n < 0 { "-" } else { "" },h/100,h%100)
}
fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let cases = t.uint();
    lines((0..cases).map(|_| {
        let result = run()(t.int(),t.int(),t.int(),t.int(),t.int(),t.int(),t.int(),t.int());
        match result.as_ref() {
            inter::Empty { } => "none".into(),
            inter::Point { x: px, y: py, denominator: d } => format!("{} {}",hundredths(*px,*d),hundredths(*py,*d)),
            inter::Segment { start_x: ax, start_y: ay, end_x: bx, end_y: by_ } => format!("{} {} {} {}",hundredths(*ax,1),hundredths(*ay,1),hundredths(*bx,1),hundredths(*by_,1)),
        }
    }))
}
fn main() { entry(solve); }
