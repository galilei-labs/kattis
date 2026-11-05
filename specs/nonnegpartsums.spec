(* @function        count_good_shifts
   @signature       array sint -> uint
   @math_signature  list Z -> N
   @summary         [count_good_shifts a] returns the number of cyclic
                    shifts of a all of whose prefix sums are nonnegative
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0 l.

(* The cyclic shift of l by k positions : l[k], ..., l[n-1], l[0], ...,
   l[k-1]. *)
Definition rotate (k : nat) (l : list Z) : list Z :=
  skipn k l ++ firstn k l.

(* The sum of the first i elements is nonnegative for every 1 <= i <= n. *)
Definition nonneg_prefix_sums (l : list Z) : bool :=
  forallb (fun i => 0 <=? sum_Z (firstn i l)) (seq 1 (List.length l)).

Definition good_shift (a : list Z) (k : nat) : bool :=
  nonneg_prefix_sums (rotate k a).

(* The shifts k in [0, n - 1] whose prefix sums are all nonnegative. *)
Definition good_shifts (a : list Z) : list nat :=
  filter (good_shift a) (seq 0 (List.length a)).

(* The statement's bounds, for one test case. *)
Record valid_input (a : list Z) : Prop := {
  (* 1 <= n <= 10^6 *)
  vi_length : (1 <= len a <= 10 ^ 6)%N;
  (* -1000 <= a_i <= 1000 *)
  vi_values : Forall (fun v => - 1000 <= v <= 1000) a;
}.

(* The result is the number of good shifts. *)
Definition count_good_shifts_spec (a : list Z) (c : N) : Prop :=
  c = len (good_shifts a).

(* machine side : the only thing that gets extracted *)
Program count_good_shifts : array sint -> uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification count_good_shifts_correct :
  forall (a : list Z) (x : array sint),
  valid_input a -> repr x a ->
  exists c : N, repr (count_good_shifts x) c /\ count_good_shifts_spec a c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
