// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 256;
use kattis_io::*;

fn main() { submission_io::entry(|input| {
    let mut lines = input.lines(); let n: usize = lines.next().unwrap().parse().unwrap();
    let mut names = std::collections::BTreeMap::new(); let mut rows = Vec::new();
    for line in lines.take(n) {
        let mut row = std::collections::BTreeMap::<usize, i64>::new();
        let (mut side, mut sign) = (1, 1);
        for token in line.split_whitespace() { match token {
            "=" => { side = -1; sign = 1; }, "*" => sign = 1, "/" => sign = -1,
            "1" => {}, name => {
                let next = names.len(); let index = *names.entry(name.to_string()).or_insert(next);
                *row.entry(index).or_default() += side * sign;
            }
        } }
        rows.push(row);
    }
    let m = names.len();
    let equations = rows.into_iter().map(|row| submission_io::ints((0..m)
        .map(|i| submission_io::signed(*row.get(&i).unwrap_or(&0))).collect())).collect();
    let result = run()(m as u64, submission_io::array(equations, submission_io::ints(Vec::new())));
    format!("{}\n", if result { "valid" } else { "invalid" })
}); }
