(* Strong-CoW extraction, paired with submission-rust-strong-cow.dune.inc.
   Runtime mappings and the host adapter are trusted, not verified. *)
From Cold Require Import cold_implem.
From RustExtraction Require Import ArraysStrong Bool Inlining.
Set Rust Extraction Copy On Write Arrays.

(* Boolean comparison wrappers used by this implementation, as in the survey. *)

Rust Extract "cold_extracted.rs" count_negatives.
