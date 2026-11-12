(* Selected Kattis submission extraction route: arrays_bigint.
   Output: yatp_extracted_arrays_bigint.ml.
   Standard Rocq extraction with unverified mutable-array mappings;
   correctness of in-place updates relies on linear array use.
   Dune generates fresh OCaml code in _build and checks it against the
   checked-in references. The extracted code requires the separate
   Bigint runtime for the positive/N/Z mappings;
   standalone Kattis submissions embed the required runtime support.
*)

From Yatp Require Import yatp_implem.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOCamlInt63.
From Stdlib Require Import PArray.  (* PrimArray onto plain OCaml arrays (mapping originally materialized from
   tools/gen-extract-arrays.py).  The type
   target is "array": Rocq prints the type argument in front, so [array int]
   becomes [Uint63.t array].  Every primitive is an Extract INLINED Constant:
   the extractor pastes the lambda at each call site and the compiler
   beta-reduces it, so the extracted code reads [Array.unsafe_get a i] --
   no module boundary, no call, no bounds check, whatever the compiler
   (Kattis compiles without flambda).  Out of range is UNDEFINED BEHAVIOUR
   where Rocq's PArray returns the default: the implem's proofs are what
   make the check redundant, and the harness's agreement check against the
   baseline is the only net.  [default] itself cannot be answered and
   raises (no extracted program of the suite calls it).  [set] returns its
   array, as the extracted code threads it.  Same linearity caveat as
   extract_marray.v: writes are in place. *)
Extract Constant PrimArray.array "'a" => "array".
Extraction Inline PrimArray.array.

Extract Inlined Constant PrimArray.make =>
  "(fun n d -> Array.make (Uint63.hash n) d)".
Extract Inlined Constant PrimArray.get =>
  "(fun a i -> Array.unsafe_get a (Uint63.hash i))".
Extract Inlined Constant PrimArray.default =>
  "(fun _ -> invalid_arg ""PrimArray.default: a raw array carries no default"")".
Extract Inlined Constant PrimArray.set =>
  "(fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)".
Extract Inlined Constant PrimArray.length =>
  "(fun a -> Uint63.of_int (Array.length a))".
Extract Inlined Constant PrimArray.copy => "Array.copy".
Extract Inlined Constant PrimArray.max_length => "(Uint63.of_int 4194303)".

From StdGalilei.extraction.ocaml Require Import bigint.

Set Extraction Output Directory ".".

Extraction "yatp_extracted_arrays_bigint.ml" yatp.
