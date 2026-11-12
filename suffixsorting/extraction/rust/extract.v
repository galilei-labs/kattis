From Suffixsorting Require Import suffixsorting_implem.
From RustExtraction Require Import Arrays BigInts Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extract "suffixsorting_extracted.rs" suffix_array.
