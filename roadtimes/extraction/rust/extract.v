From Roadtimes Require Import roadtimes_implem.
From RustExtraction Require Import ArraysStrong BigInts Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extract "roadtimes_extracted.rs" roadtimes.
