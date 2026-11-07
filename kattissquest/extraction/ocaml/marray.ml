(* Marray: OCaml *mutable* arrays behind the interface of Rocq's PrimArray
   primitives, as a drop-in replacement for rocq-runtime's Parray in an
   extra, clearly labelled benchmark column ("marray"; "mutable" in the
   flavours run before 2026-10-08).

   THIS MAPPING IS UNSOUND IN GENERAL.  Rocq's [PArray.set t i x] is a pure
   function: it returns a new array and [t] keeps its old contents
   ([get_set_other], and [t.[i]] is unchanged).  [Marray.set] writes in
   place and returns the very same array, so any later read of the OLD
   version observes the write.  The two agree exactly when every array is
   used LINEARLY -- each version is consumed once, by the [set] (or the
   final read) that supersedes it, and never read again afterwards.  Every
   spec in this library demands that in its @forbid section, and every
   implementation follows it, but nothing CHECKS it: the column produced
   with this module is an unverified data point ("what would a
   linearity-checking extractor buy?"), never the verified artefact.

   This is the canonical file.  Every flavour built from template/ gets
   its benchmark/extracted/marray.ml from it: the flavour Makefile's
   `make extract` copies it there (the benchmark directories are separate
   dune projects and cannot read tools/), and the copy is generated,
   gitignored and never edited.  Flavours older than 2026-09-06 carry a
   hand-made copy of the un-annotated version, tracked in git.

   INLINING.  The primitives below carry [@@inline always].  That attribute
   only acts when this unit is compiled WITHOUT -opaque, i.e. in dune's
   release profile (the flavour Makefile exports DUNE_PROFILE=release);
   under the dev profile every call from the extracted code is a generic
   caml_applyN through the module block, and without the attribute flambda
   -O3 emits direct calls but does not inline get/set (its cost model
   credits a removed call with 5 against a body of size 45).  Inlined, the
   extracted loops run at 0.59x-0.80x of the opaque build; measured in
   microbench/ (README.md there), whose `make inspect` shows the call
   sites.  The results.txt run header of every flavour built from template/
   records which case the build was in (`marray: inlined|calls|opaque`,
   computed by tools/marray-tag from the built objects).

   The marray route always goes through this module.  The arrays_bigint
   route, built alongside for every problem, uses no module at all --
   Array.unsafe_get/unsafe_set pasted at every call site.  The ladder
   Marray-not-inlined / inlined / a.(i) / unsafe_get was measured
   suite-wide on 2026-09-14 (extraction_to_arrays/README.md): a.(i) is
   0.78x of inlined Marray, unsafe_get 0.90x of that.

   Out-of-range behaviour mirrors rocq-runtime/kernel/parray.ml: [get]
   outside the bounds returns the default, [set] outside the bounds is the
   identity, [make] truncates the size to [max_length]. *)

type 'a t = { data : 'a array; def : 'a }

let max_array_length32 = 4194303

let max_length = Uint63.of_int max_array_length32

let length_to_int i = snd (Uint63.to_int2 i) [@@inline always]

let trunc_size n =
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int max_array_length32)
  then length_to_int n
  else max_array_length32

let make n def = { data = Array.make (trunc_size n) def; def } [@@inline always]

let length p = Uint63.of_int (Array.length p.data) [@@inline always]

let get p n =
  let l = Array.length p.data in
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l)
  then Array.unsafe_get p.data (length_to_int n)
  else p.def
  [@@inline always]

let set p n e =
  let l = Array.length p.data in
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l)
  then Array.unsafe_set p.data (length_to_int n) e;
  p
  [@@inline always]

let default p = p.def [@@inline always]

let copy p = { data = Array.copy p.data; def = p.def }

(* Harness helpers, same names and meaning as Parray's. *)

let of_array a def = { data = Array.copy a; def }

let to_array p = (Array.copy p.data, p.def)
