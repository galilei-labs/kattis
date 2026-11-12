#!/usr/bin/env python3
"""Route checks for the standalone Rust submission assembler."""

import importlib.util
from pathlib import Path
import unittest
from compact_rust_source import compact, without_runtime_tests

spec = importlib.util.spec_from_file_location(
    "assembler", Path(__file__).with_name("assemble-submission-rust.py"))
assembler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(assembler)


def directives(module):
    return (f"From RustExtraction Require Import {module} Bool Inlining.\n"
            "Set Rust Extraction Copy On Write Arrays.\n")


class AssemblyTests(unittest.TestCase):
    def test_matching_routes(self):
        for route, module in (("cow", "Arrays"), ("strong-cow", "ArraysStrong")):
            assembler.check_route(directives(module), route)

    def test_mismatched_routes(self):
        for route, module in (("cow", "ArraysStrong"), ("strong-cow", "Arrays")):
            with self.assertRaises(ValueError):
                assembler.check_route(directives(module), route)

    def test_requires_shared_array_mode(self):
        for route, module in (("cow", "Arrays"), ("strong-cow", "ArraysStrong")):
            with self.assertRaises(ValueError):
                assembler.check_route(f"From RustExtraction Require Import {module}.", route)

    def test_rejects_ambiguous_imports_and_options(self):
        for source in (directives("Arrays ArraysStrong"),
                       directives("ArraysStrong") + "Unset Rust Extraction Copy On Write Arrays.",
                       "(* " + directives("ArraysStrong") + " *)"):
            with self.assertRaises(ValueError):
                assembler.check_route(source, "strong-cow")

    def test_nested_comments(self):
        source = ("(* outer (* From RustExtraction Require Import Arrays. *) end *)\n"
                  + directives("ArraysStrong"))
        assembler.check_route(source, "strong-cow")
        with self.assertRaises(ValueError):
            assembler.without_comments("(* unclosed")

    def test_optional_runtimes(self):
        args = ("tsp", "strong-cow", directives("ArraysStrong"),
                "fn run() { rocq_bigint::sub(); rocq_float64::add(); }",
                "fn main() {}", "// int63", "// arrays", "BSD-3-Clause\n")
        with self.assertRaisesRegex(ValueError, "missing required runtime"):
            assembler.assemble(*args)
        source = assembler.assemble(*args, extra_runtimes={
            "rocq_bigint": "// bigint", "rocq_float64": "// float64"})
        self.assertIn("mod rocq_bigint {", source)
        self.assertIn("mod rocq_float64 {", source)
        unused = assembler.assemble(*args[:3], "fn run() {}", *args[4:],
                                   extra_runtimes={"rocq_bigint": "// bigint"})
        self.assertNotIn("mod rocq_bigint {", unused)

    def test_shared_io_helpers_require_their_runtime(self):
        args = ("ada", "strong-cow", directives("ArraysStrong"), "fn run() {}",
                "const STACK_MIB: usize = 256; use kattis_io::*; fn main() {}",
                "// int63", "// arrays", "BSD-3-Clause\n")
        with self.assertRaisesRegex(ValueError, "missing shared I/O helpers"):
            assembler.assemble(*args)
        with self.assertRaisesRegex(ValueError, "missing required runtime: rocq_string"):
            assembler.assemble(*args, io_helpers="fn text() { rocq_string::get(); }")
        source = assembler.assemble(*args, io_helpers="fn text() { rocq_string::get(); }",
                                    extra_runtimes={"rocq_string": "// strings"})
        self.assertIn("mod kattis_io {", source)
        self.assertIn("use super::STACK_MIB;", source)
        self.assertIn("mod rocq_string {", source)

    def test_assembly_is_standalone_and_preserves_notice(self):
        source = assembler.assemble("cold", "strong-cow", directives("ArraysStrong"),
                                    "fn run() {}", "fn main() {}", "// int63",
                                    "// arrays", "BSD-3-Clause\nCopyright test\n")
        for expected in ("// BSD-3-Clause", "// Copyright test", "mod rocq_int63 {",
                         "mod rocq_array {", "fn run() {}", "fn main() {}",
                         "Array route: strong-cow"):
            self.assertIn(expected, source)
        self.assertNotIn("include!", source)

    def test_trivia_preserves_literals_and_token_separation(self):
        literals = ['"// not a comment"', 'r###"/* raw */"###', "' '", "'\\n'",
                    'b"// bytes"', 'br#"// raw bytes"#']
        for literal in literals:
            self.assertIn(literal, compact("const X = " + literal + "; // discard\n"))
        source = "// Copyright test\n// Full notice\nfn f<'a>() { a /* x */ b; + +; / *; }"
        output = compact(source)
        self.assertIn("// Copyright test\n// Full notice\n", output)
        self.assertRegex(output, r"a\s+b")
        for separated in ("+ +", "/ *"):
            self.assertIn(separated, output)
        self.assertNotIn("/* x */", output)
        for malformed in ('/* unclosed', 'r#"unclosed', '"unclosed'):
            with self.assertRaises(ValueError):
                compact(malformed)

    def test_runtime_test_omission_is_fail_closed(self):
        source = "// SPDX-License-Identifier: BSD-3-Clause\nfn f() {}\n"
        tests = "#[cfg(test)]\nmod tests {\n    #[test]\n    fn check() {}\n}\n"
        self.assertEqual(without_runtime_tests(source + tests), source)
        with self.assertRaises(ValueError):
            without_runtime_tests(source + tests + "fn after() {}\n")

    def test_source_size_limit(self):
        args = ("cold", "strong-cow", directives("ArraysStrong"), "fn run() {}",
                "fn main() {}", "// int63", "// arrays", "BSD-3-Clause\n")
        # Whitespace is compacted, whereas oversized literal contents are not changed.
        source = assembler.assemble(*args[:3], " " * 131073 + args[3], *args[4:])
        self.assertLessEqual(len(source.encode()), 131072)
        with self.assertRaisesRegex(ValueError, "exceeds 131072 bytes"):
            assembler.assemble(*args[:3], 'const S: &str = "' + 'x' * 131073 + '";', *args[4:])


if __name__ == "__main__":
    unittest.main()
