(* @function        lis
   @signature       array sint -> array uint
   @math_signature  list Z -> list N
   @summary         [lis a] returns the positions in a, in ascending order,
                    of a longest strictly increasing subsequence of a ; any
                    one of them when several exist
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th value of the sequence a, for k < len a (0 outside, never
   relied on). *)
Definition get_list_Z (a : list Z) (k : N) : Z := nth (N.to_nat k) a 0%Z.

(* The t-th position listed in s, for t < len s (0 outside, never relied
   on). *)
Definition get_list_N (s : list N) (t : N) : N := nth (N.to_nat t) s 0.

(* Every listed position is a position of the sequence. *)
Definition indices_valid (a : list Z) (s : list N) : Prop :=
  forall t, t < len s -> get_list_N s t < len a.

(* The positions are listed in strictly ascending order. *)
Definition indices_ascending (s : list N) : Prop :=
  forall t u, t < u < len s -> get_list_N s t < get_list_N s u.

(* The values at the listed positions strictly increase. *)
Definition values_increasing (a : list Z) (s : list N) : Prop :=
  forall t u, t < u < len s ->
    (get_list_Z a (get_list_N s t) < get_list_Z a (get_list_N s u))%Z.

(* s is a strictly increasing subsequence of a, given by the positions of
   its elements. *)
Definition increasing_subseq (a : list Z) (s : list N) : Prop :=
  indices_valid a s /\ indices_ascending s /\ values_increasing a s.

(* The statement's bounds on one test case. *)
Record valid_input (a : list Z) : Prop := {
  (* 1 <= n <= 10^5 *)
  vi_length : 1 <= len a <= 10 ^ 5;
  (* every value in [-2^31, 2^31) *)
  vi_values : Forall (fun v => (- 2 ^ 31 <= v < 2 ^ 31)%Z) a;
}.

(* The answer : an increasing subsequence of a that none is longer than. *)
Definition lis_spec (a : list Z) (s : list N) : Prop :=
  increasing_subseq a s /\
  forall s', increasing_subseq a s' -> len s' <= len s.

(* machine side : gets extracted *)
Program lis : array sint -> array uint.

(* Glue between machine and math worlds*)
Specification lis_correct : forall (a : list Z) (x : array sint),
  valid_input a -> repr x a ->
  exists s : list N, repr (lis x) s /\ lis_spec a s.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
