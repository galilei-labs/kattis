From Selfbalancingbst Require Import selfbalancingbst_implem.
From RustExtraction Require Import Arrays Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extraction NoInline exec.

Rust Extract "selfbalancingbst_extracted.rs" run_commands.
