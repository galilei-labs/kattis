From Magicsequence Require Import magicsequence_implem.
From RustExtraction Require Import Arrays BigInts Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extract "magicsequence_extracted.rs" magic.
