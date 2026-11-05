(* @function        multimatch
   @signature       array PrimString.string -> PrimString.string
                    -> array (array uint)
   @math_signature  list string -> string -> list (list N)
   @summary         [multimatch pats txt] returns, for every pattern
                    pats[i] and in ascending order, every position of txt
                    at which pats[i] occurs, overlapping occurrences
                    included
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of characters of s. *)
Definition slen (s : string) : N := N.of_nat (String.length s).

(* The t-th element of l, for t < len l (0, [] or "" outside, never
   relied on). *)
Definition get_list_N (l : list N) (t : N) : N := nth (N.to_nat t) l 0.
Definition get_row (rows : list (list N)) (i : N) : list N :=
  nth (N.to_nat i) rows [].
Definition get_pattern (pats : list string) (i : N) : string :=
  nth (N.to_nat i) pats ""%string.

(* pat occurs in txt at position p : txt is pat preceded by p characters
   and followed by any. *)
Definition occurs_at (pat txt : string) (p : N) : Prop :=
  exists pre post, txt = (pre ++ pat ++ post)%string /\ slen pre = p.

(* The positions are listed in strictly ascending order. *)
Definition ascending (ps : list N) : Prop :=
  forall t u, t < u < len ps -> get_list_N ps t < get_list_N ps u.

(* The total length of the patterns. *)
Definition total_length (pats : list string) : N :=
  N.of_nat (list_sum (map String.length pats)).

(* The statement's bounds, for one test case. *)
Record valid_input (pats : list string) (txt : string) : Prop := {
  (* every pattern is non-empty *)
  vi_patterns : Forall (fun pat => 1 <= slen pat) pats;
  (* the total length of all patterns is no more than 100000 *)
  vi_total : total_length pats <= 10 ^ 5;
  (* a non-empty text of length at most 200000 *)
  vi_txt : 1 <= slen txt <= 2 * 10 ^ 5;
}.

(* One row per pattern : the positions of its occurrences, each once, in
   ascending order. *)
Definition multimatch_spec (pats : list string) (txt : string)
                           (rows : list (list N)) : Prop :=
  len rows = len pats /\
  forall i, i < len pats ->
    ascending (get_row rows i) /\
    forall p, In p (get_row rows i) <-> occurs_at (get_pattern pats i) txt p.

(* machine side : the only thing that gets extracted *)
Program multimatch : array PrimString.string -> PrimString.string ->
                       array (array uint).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification multimatch_correct :
  forall (pats : list string) (txt : string)
         (xp : array PrimString.string) (xt : PrimString.string),
  valid_input pats txt -> repr xp pats -> repr xt txt ->
  exists rows : list (list N),
    repr (multimatch xp xt) rows /\ multimatch_spec pats txt rows.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
