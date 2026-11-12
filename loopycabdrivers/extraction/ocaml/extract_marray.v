(* Selected Kattis submission extraction route: marray.
   Output: loopycabdrivers_extracted_marray.ml.
   Standard Rocq extraction with unverified mutable-array mappings;
   correctness of in-place updates relies on linear array use.
   Dune generates fresh OCaml code in _build and checks it against the
   checked-in references. The extracted code requires the separate
   Marray runtime;
   standalone Kattis submissions embed the required runtime support.
*)

From Loopycabdrivers Require Import loopycabdrivers_implem.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOCamlInt63 ExtrOCamlPString.
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

Extraction "loopycabdrivers_extracted_marray.ml" loopy_regions.
