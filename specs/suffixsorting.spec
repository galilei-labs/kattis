(* @function        suffix_array
   @signature       PrimString.string -> array uint
   @math_signature  string -> list N
   @summary         [suffix_array s] returns the starting positions of the
                    suffixes of s, from the lexicographically smallest
                    suffix to the largest ; the harness answers the query
                    q with entry q
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String Permutation.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of characters of s. *)
Definition slen (s : string) : N := N.of_nat (String.length s).

(* The r-th element of l, for r < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (r : N) : N := nth (N.to_nat r) l 0.

(* The suffix of s starting at position i. *)
Definition suffix (s : string) (i : N) : string :=
  substring (N.to_nat i) (String.length s) s.

(* u comes strictly before v in lexicographic order : at the first
   position where they differ u has the smaller character code, or u is a
   proper prefix of v. *)
Definition lex_lt (u v : string) : Prop := String.compare u v = Lt.

(* The positions 0 .. n - 1 of s. *)
Definition positions (s : string) : list N :=
  map N.of_nat (seq 0 (String.length s)).

(* The statement's bounds, for one test case. *)
Record valid_input (s : string) : Prop := {
  (* a non-empty string of length at most 100000 *)
  vi_s : 1 <= slen s <= 10 ^ 5;
}.

(* Every position exactly once, each suffix before the next. *)
Definition suffix_array_spec (s : string) (sa : list N) : Prop :=
  Permutation sa (positions s) /\
  forall r, r + 1 < len sa ->
    lex_lt (suffix s (get_list_N sa r)) (suffix s (get_list_N sa (r + 1))).

(* machine side : the only thing that gets extracted *)
Program suffix_array : PrimString.string -> array uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification suffix_array_correct : forall (s : string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists sa : list N, repr (suffix_array x) sa /\ suffix_array_spec s sa.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
