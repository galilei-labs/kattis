// I/O adapter ported from the historical Rust survey; no algorithm changes.
const STACK_MIB: usize = 512;
use kattis_io::*;

fn solve(input: String, output: &mut dyn std::io::Write) {
    let mut input_lines = input.lines(); let q: usize = input_lines.next().unwrap().trim().parse().unwrap();
    let mut commands = Vec::with_capacity(q);
    for line in input_lines.filter(|s| !s.trim().is_empty()).take(q) {
        let mut t = Tokens::new(line); let id = t.uint();
        let operation = match t.next() {
            "a" => operation::CopyFrom { source: t.uint() },
            "?" => operation::FindKey { key: t.int() },
            "l" => operation::LowerBound { key: t.int() },
            "u" => operation::UpperBound { key: t.int() },
            "i" => operation::Insert { key: t.int(), value: t.int() },
            "e" => operation::Erase {},
            "f" => operation::First {},
            "b" => operation::Last {},
            ">" => operation::NextKey {},
            "<" => operation::PreviousKey {},
            "k" => operation::SelectRank { index: t.int() },
            "r" => operation::GetRank {},
            "g" => operation::GetValue {},
            "s" => operation::SetValue { value: t.int() },
            "z" => operation::GetSize {},
            _ => panic!("unknown command"),
        };
        commands.push((id, Rc::new(operation)));
    }
    drop(input);
    let result = run()(array(commands, (0, Rc::new(operation::GetSize {}))));
    for i in 0..result.length() {
        match crate::rocq_array::get(&result, i).as_ref() {
            option::None { } => writeln!(output, "-").unwrap(),
            option::Some(v) => writeln!(output, "{}", decoded(*v)).unwrap(),
        }
    }
}
fn main() { entry_streaming(solve); }
