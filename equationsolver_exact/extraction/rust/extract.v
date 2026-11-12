From EquationsolverExact Require Import equationsolver_exact_implem.
From RustExtraction Require Import ArraysStrong BigInts Bool Strings Inlining Float64.
From Stdlib Require Import BinPos.

Set Rust Extraction Copy On Write Arrays.
Set Rust Extraction Short Runtime Paths.
Rust Extraction Inline ADT prod.
Rust Extraction Inline Pos.compare.

Rust Extract "equationsolver_exact_extracted.rs" solve.
