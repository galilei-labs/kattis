// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn read_datetime(t: &mut Tokens<'_>) -> Rc<datetime<u64>> {
    let date: Vec<u64> = t.next().split('-').map(|x| x.parse().unwrap()).collect();
    let time: Vec<u64> = t.next().split(':').map(|x| x.parse().unwrap()).collect();
    Rc::new(datetime { year: date[0], month: date[1], day: date[2], hour: time[0], minute: time[1] })
}
fn solve(input: &str) -> String {
    let mut t = Tokens::new(input); let cases = t.uint(); let mut out = String::new();
    let zero = Rc::new(datetime { year: 0, month: 0, day: 0, hour: 0, minute: 0 });
    for _ in 0..cases {
        let b = t.uint(); let c = t.uint(); let mut arrivals = Vec::new(); let mut departures = Vec::new();
        for _ in 0..b { t.next(); arrivals.push(read_datetime(&mut t)); departures.push(read_datetime(&mut t)); }
        out.push_str(&format!("{}\n", run()(c, array(arrivals, zero.clone()), array(departures, zero.clone()))));
    }
    out
}
fn main() { entry(solve); }
