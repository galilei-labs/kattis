(* The `marray` route, an EXTRA, UNVERIFIED column: the same proven implem
   extracted with Rocq's persistent arrays mapped onto OCaml's MUTABLE
   arrays.

   Build: driven by the Makefile in this directory.
   Emits cold_extracted_marray.ml and .mli under _build, leaving the
   checked-in snapshots unchanged. Integer extraction uses
   Rocq's default representation; no external Bigint mappings are enabled.

   Everything is the header's setting (ExtrOcamlBasic
   ExtrOCamlInt63) EXCEPT ExtrOCamlPArray: instead of rocq-runtime's
   Parray (one shared buffer plus a chain of Updated diffs, 48 B allocated
   per set), PrimArray is mapped onto Marray (marray.ml in this directory,
   a verbatim copy of tools/marray.ml), whose [set] writes in place and
   returns the same array.

   This is UNSOUND in general -- an old version would observe later writes
   -- and correct exactly when the arrays are used linearly, which the spec
   demands (@forbid) but nothing checks.  The column measures what a
   linearity-aware extractor would buy; it is not the verified artefact. *)

From Cold Require Import cold_implem.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOCamlInt63.
From Stdlib Require Import PArray.  (* so PrimArray.* resolve even if the implem never touches arrays *)

(* Same shape as ExtrOCamlPArray, target module Marray.  The type target is
   "Marray.t" rather than "'a Marray.t": Rocq prints the type argument in
   front of the target anyway, and the "'a" form yields the ill-formed
   "Uint63.t 'a Marray.t" wherever [array int] occurs in real code. *)
Extract Constant PrimArray.array "'a" => "Marray.t".
Extraction Inline PrimArray.array.

Extract Constant PrimArray.make => "Marray.make".
Extract Constant PrimArray.get => "Marray.get".
Extract Constant PrimArray.default => "Marray.default".
Extract Constant PrimArray.set => "Marray.set".
Extract Constant PrimArray.length => "Marray.length".
Extract Constant PrimArray.copy => "Marray.copy".
Extract Constant PrimArray.max_length => "Marray.max_length".

Set Extraction Output Directory ".".

Extraction "cold_extracted_marray.ml" cold_implem.count_negatives.
