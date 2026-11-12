From Fulltank Require Import fulltank_implem.
From RustExtraction Require Import ArraysStrong Bool Inlining.

Set Rust Extraction Copy On Write Arrays.
Rust Extraction Inline ADT prod.

(* Compatibility with the installed extractor predating Int63's Bool mappings. *)

Rust Extract "fulltank_extracted.rs" fulltank.
