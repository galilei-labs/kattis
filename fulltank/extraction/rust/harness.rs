// I/O-only adapter following the accepted Rust survey route.
use std::io::{Read, Write};
use std::rc::Rc as HostRc;

fn ints(values: Vec<u64>) -> HostRc<rocq_array::Array<u64>> {
    HostRc::new(rocq_array::Array::literal(0, values))
}

fn main() {
    // Historical stack allowance for extracted recursion.
    std::thread::Builder::new().stack_size(256 * 1024 * 1024).spawn(|| {
        let mut input = String::new();
        std::io::stdin().read_to_string(&mut input).unwrap();
        let mut tokens = input.split_whitespace().map(|s| s.parse::<u64>().unwrap());
        let n = tokens.next().unwrap();
        let m = tokens.next().unwrap();
        let prices = ints((0..n).map(|_| tokens.next().unwrap()).collect());
        let (mut us, mut vs, mut distances) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..m {
            us.push(tokens.next().unwrap());
            vs.push(tokens.next().unwrap());
            distances.push(tokens.next().unwrap());
        }
        let q = tokens.next().unwrap();
        let (mut capacities, mut starts, mut ends) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..q {
            capacities.push(tokens.next().unwrap());
            starts.push(tokens.next().unwrap());
            ends.push(tokens.next().unwrap());
        }
        let result = run()(n, prices, ints(us), ints(vs), ints(distances),
                           ints(capacities), ints(starts), ints(ends));
        let mut output = std::io::BufWriter::new(std::io::stdout().lock());
        for i in 0..result.length() {
            match rocq_array::get(&result, i).as_ref() {
                option::None => writeln!(output, "impossible").unwrap(),
                option::Some(f0) => writeln!(output, "{f0}").unwrap(),
            }
        }
    }).unwrap().join().unwrap();
}
