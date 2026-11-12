// I/O-only adapter following the accepted Rust survey route.
use std::io::{Read, Write};
use std::rc::Rc as HostRc;

fn main() {
    // Retain the accepted generic driver and its 256 MiB worker stack.
    std::thread::Builder::new().stack_size(256 * 1024 * 1024).spawn(|| {
        let mut input = String::new();
        std::io::stdin().read_to_string(&mut input).unwrap();
        let mut tokens = input.split_whitespace();
        let n: usize = tokens.next().unwrap().parse().unwrap();
        let (mut xs, mut ys) = (Vec::with_capacity(n), Vec::with_capacity(n));
        for _ in 0..n {
            xs.push(tokens.next().unwrap().parse::<f64>().unwrap());
            ys.push(tokens.next().unwrap().parse::<f64>().unwrap());
        }
        let xs = HostRc::new(rocq_array::Array::literal(0.0, xs));
        let ys = HostRc::new(rocq_array::Array::literal(0.0, ys));
        let tour = run()(xs, ys);
        let mut output = std::io::BufWriter::new(std::io::stdout().lock());
        for i in 0..tour.length() {
            writeln!(output, "{}", rocq_array::get(&tour, i)).unwrap();
        }
    }).unwrap().join().unwrap();
}
