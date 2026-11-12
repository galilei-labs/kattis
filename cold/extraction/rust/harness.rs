fn main() {
    use std::io::Read;
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().unwrap().parse().unwrap();
    let temperatures = (0..n).map(|_| {
        let value: i64 = tokens.next().unwrap().parse().unwrap();
        // Rocq signed Int63 uses two's complement in the low 63 bits.
        (value as u64) & ((1u64 << 63) - 1)
    }).collect();
    let array = std::rc::Rc::new(rocq_array::Array::literal(0u64, temperatures));
    println!("{}", run()(array));
}
