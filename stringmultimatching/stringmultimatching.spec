(* @function        multimatch
   @signature       array PrimString.string -> PrimString.string
                    -> array (array uint)
   @math_signature  list string -> string -> list (list N)
   @summary         [multimatch patterns text] returns, for every pattern
                    patterns[i] and in ascending order, every position of
                    text at which patterns[i] occurs, overlapping
                    occurrences included
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of characters of text. *)
Definition slen (text : string) : N := N.of_nat (String.length text).

(* The k-th element of l, for k < len l (0, [] or "" outside, never
   relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.
Definition get_row (rows : list (list N)) (i : N) : list N :=
  nth (N.to_nat i) rows [].
Definition get_pattern (patterns : list string) (i : N) : string :=
  nth (N.to_nat i) patterns ""%string.

(* pattern occurs in text at position : text is pattern preceded by
   position characters and followed by any. *)
Definition occurs_at (pattern text : string) (position : N) : Prop :=
  exists before after,
    text = (before ++ pattern ++ after)%string /\ slen before = position.

(* The positions are listed in strictly ascending order. *)
Definition ascending (positions : list N) : Prop :=
  forall j k, j < k < len positions ->
    get_list_N positions j < get_list_N positions k.

(* The total length of the patterns. *)
Definition total_length (patterns : list string) : N :=
  N.of_nat (list_sum (map String.length patterns)).

(* The statement's bounds, for one test case. *)
Record valid_input (patterns : list string) (text : string) : Prop := {
  (* every pattern is non-empty *)
  vi_patterns : Forall (fun pattern => 1 <= slen pattern) patterns;
  (* the total length of all patterns is no more than 100000 *)
  vi_total : total_length patterns <= 10 ^ 5;
  (* a non-empty text of length at most 200000 *)
  vi_txt : 1 <= slen text <= 2 * 10 ^ 5;
}.

(* One row per pattern : the positions of its occurrences, each once, in
   ascending order. *)
Definition multimatch_spec (patterns : list string) (text : string)
                           (output : list (list N)) : Prop :=
  len output = len patterns /\
  forall i, i < len patterns ->
    ascending (get_row output i) /\
    forall position, In position (get_row output i) <->
      occurs_at (get_pattern patterns i) text position.

(* machine side : the only thing that gets extracted *)
Program multimatch : array PrimString.string -> PrimString.string ->
                       array (array uint).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification multimatch_correct :
  forall (patterns : list string) (text : string)
         (patterns_arr : array PrimString.string)
         (text_str : PrimString.string),
  valid_input patterns text -> repr patterns_arr patterns ->
  repr text_str text ->
  exists output : list (list N),
    repr (multimatch patterns_arr text_str) output /\
    multimatch_spec patterns text output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
