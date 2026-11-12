From Nonnegpartsums Require Import nonnegpartsums_implem.
From RustExtraction Require Import ArraysStrong Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extract "nonnegpartsums_extracted.rs" count_good_shifts.
