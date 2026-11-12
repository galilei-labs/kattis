From Baza Require Import baza_implem.
From RustExtraction Require Import ArraysStrong Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extract "baza_extracted.rs" baza.
