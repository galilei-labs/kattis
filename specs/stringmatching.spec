(* @function        find_all
   @signature       PrimString.string -> PrimString.string -> array uint
   @math_signature  string -> string -> list N
   @summary         [find_all pat txt] returns, in ascending order, every
                    position of txt at which pat occurs, overlapping
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

(* The number of characters of s. *)
Definition slen (s : string) : N := N.of_nat (String.length s).

(* The t-th position listed in ps, for t < len ps (0 outside, never relied
   on). *)
Definition get_list_N (ps : list N) (t : N) : N := nth (N.to_nat t) ps 0.

(* pat occurs in txt at position i : txt is pat preceded by i characters
   and followed by any. *)
Definition occurs_at (pat txt : string) (i : N) : Prop :=
  exists pre post, txt = (pre ++ pat ++ post)%string /\ slen pre = i.

(* The positions are listed in strictly ascending order. *)
Definition ascending (ps : list N) : Prop :=
  forall t u, t < u < len ps -> get_list_N ps t < get_list_N ps u.

(* The statement's bounds, for one test case -- plus one bound that is NOT
   Kattis's, vi_txt_parray. *)
Record valid_input (pat txt : string) : Prop := {
  (* a non-empty pattern, a non-empty text *)
  vi_pat : 1 <= slen pat;
  vi_txt : 1 <= slen txt;
  (* the input file is not larger than 5 Mb *)
  vi_file : slen pat + slen txt <= 5 * 10 ^ 6;
  (* NOT THE KATTIS BOUND (2026-10-17). Kattis allows a text of 5 Mb, but
     the output is an [array uint] and a PArray has at most
     PArray.max_length = 4194303 cells, while a text of n characters can
     hold up to n occurrences (pattern "a", text "aaa..."): on such an
     input the contract would demand an output no array can represent and
     find_all_correct would be false. So the text is capped at what a
     PArray can hold; every answer then fits (at most
     slen txt - slen pat + 1 <= 4194303 positions). Kattis inputs with a
     longer text are outside this contract. *)
  vi_txt_parray : slen txt <= 4194303;
}.

(* The positions of the occurrences of pat in txt, each once, in ascending
   order. *)
Definition find_all_spec (pat txt : string) (ps : list N) : Prop :=
  ascending ps /\
  forall i, In i ps <-> occurs_at pat txt i.

(* machine side : the only thing that gets extracted *)
Program find_all : PrimString.string -> PrimString.string -> array uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification find_all_correct :
  forall (pat txt : string) (xp xt : PrimString.string),
  valid_input pat txt -> repr xp pat -> repr xt txt ->
  exists ps : list N, repr (find_all xp xt) ps /\ find_all_spec pat txt ps.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
