From Timing Require Import timing_implem.
From RustExtraction Require Import ArraysStrong BigInts Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extract "timing_extracted.rs" timing.
