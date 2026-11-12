From Tsp Require Import tsp_implem.
From RustExtraction Require Import ArraysStrong Bool Inlining BigInts Float64.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.

(* Compatibility with the installed extractor predating Int63's Bool mappings. *)

Rust Extract "tsp_extracted.rs" tsp.
