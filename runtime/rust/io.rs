// I/O and representation bridges only; algorithms remain in extracted code.
use std::rc::Rc;
pub type Array<T> = Rc<crate::rocq_array::Array<T>>;
pub fn array<T: Clone>(values: Vec<T>, default: T) -> Array<T> {
    Rc::new(crate::rocq_array::Array::literal(default, values))
}
pub fn ints(values: Vec<u64>) -> Array<u64> { array(values, 0) }
pub fn values<T: Clone>(a: &Array<T>) -> Vec<T> {
    (0..a.length()).map(|i| crate::rocq_array::get(a, i)).collect()
}
pub fn lines(values: impl IntoIterator<Item=impl std::fmt::Display>) -> String {
    values.into_iter().map(|x| format!("{x}\n")).collect()
}
pub fn signed(value: i64) -> u64 { (value as u64) & ((1u64 << 63) - 1) }
pub fn decoded(value: u64) -> i64 { ((value << 1) as i64) >> 1 }
pub fn string(value: &str) -> Rc<crate::rocq_string::RocqString> {
    Rc::new(crate::rocq_string::RocqString::from_bytes(value.as_bytes().to_vec()))
}
pub fn text(value: &Rc<crate::rocq_string::RocqString>) -> String {
    String::from_utf8((0..crate::rocq_string::length(value))
        .map(|i| crate::rocq_string::get(value, i) as u8).collect()).unwrap()
}
pub fn words(t: &mut Tokens<'_>, n: u64) -> Array<Rc<crate::rocq_string::RocqString>> {
    array((0..n).map(|_| string(t.next())).collect(), string(""))
}
pub fn columns<const N: usize>(t: &mut Tokens<'_>, n: u64, signed_values: bool) -> [Array<u64>; N] {
    let mut cols: [Vec<u64>; N] = std::array::from_fn(|_| Vec::new());
    for _ in 0..n {
        for col in &mut cols { col.push(if signed_values { t.int() } else { t.uint() }); }
    }
    cols.map(ints)
}
pub struct Tokens<'a>(std::str::SplitWhitespace<'a>);
impl<'a> Tokens<'a> {
    pub fn new(input: &'a str) -> Self { Self(input.split_whitespace()) }
    pub fn next(&mut self) -> &'a str { self.0.next().expect("missing input") }
    pub fn optional(&mut self) -> Option<&'a str> { self.0.next() }
    pub fn uint(&mut self) -> u64 { self.next().parse().unwrap() }
    pub fn int(&mut self) -> u64 { signed(self.next().parse().unwrap()) }
    pub fn uints(&mut self, n: u64) -> Array<u64> { ints((0..n).map(|_| self.uint()).collect()) }
    pub fn signed_ints(&mut self, n: u64) -> Array<u64> { ints((0..n).map(|_| self.int()).collect()) }
}
pub fn numbers<T: std::fmt::Display>(values: impl IntoIterator<Item=T>) -> String {
    values.into_iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")
}
pub fn entry(solve: fn(&str) -> String) {
    // Generated recursion is not guaranteed to become a Rust loop.
    std::thread::Builder::new().stack_size(STACK_MIB * 1024 * 1024).spawn(move || {
        use std::io::{Read, Write};
        let mut input = String::new();
        std::io::stdin().read_to_string(&mut input).unwrap();
        let output = solve(&input);
        std::io::BufWriter::new(std::io::stdout().lock()).write_all(output.as_bytes()).unwrap();
    }).unwrap().join().unwrap();
}
pub fn entry_streaming(solve: fn(String, &mut dyn std::io::Write)) {
    std::thread::Builder::new().stack_size(STACK_MIB * 1024 * 1024).spawn(move || {
        use std::io::{Read, Write};
        let mut input = String::new();
        std::io::stdin().read_to_string(&mut input).unwrap();
        let mut output = std::io::BufWriter::new(std::io::stdout().lock());
        solve(input, &mut output);
        output.flush().unwrap();
    }).unwrap().join().unwrap();
}
