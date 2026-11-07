(* @function        count_good_shifts
   @signature       array sint -> uint
   @math_signature  list Z -> N
   @summary         [count_good_shifts sequence] returns the number of
                    cyclic shifts of sequence all of whose prefix sums are
                    nonnegative
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0 l.

(* The cyclic shift of sequence by k positions : sequence[k], ...,
   sequence[n-1], sequence[0], ..., sequence[k-1]. *)
Definition rotate (k : nat) (sequence : list Z) : list Z :=
  skipn k sequence ++ firstn k sequence.

(* The sum of the first i elements is nonnegative for every 1 <= i <= n. *)
Definition nonneg_prefix_sums (sequence : list Z) : bool :=
  forallb (fun i => 0 <=? sum_Z (firstn i sequence))
          (seq 1 (List.length sequence)).

Definition good_shift (sequence : list Z) (k : nat) : bool :=
  nonneg_prefix_sums (rotate k sequence).

(* The shifts k in [0, n - 1] whose prefix sums are all nonnegative. *)
Definition good_shifts (sequence : list Z) : list nat :=
  filter (good_shift sequence) (seq 0 (List.length sequence)).

(* The statement's bounds, for one test case. *)
Record valid_input (sequence : list Z) : Prop := {
  (* 1 <= n <= 10^6 *)
  vi_length : (1 <= len sequence <= 10 ^ 6)%N;
  (* -1000 <= a_i <= 1000 *)
  vi_values : Forall (fun element => - 1000 <= element <= 1000) sequence;
}.

(* The result is the number of good shifts. *)
Definition count_good_shifts_spec (sequence : list Z) (output : N)
    : Prop :=
  output = len (good_shifts sequence).

(* machine side : the only thing that gets extracted *)
Program count_good_shifts : array sint -> uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification count_good_shifts_correct :
  forall (sequence : list Z) (sequence_arr : array sint),
  valid_input sequence -> repr sequence_arr sequence ->
  exists output : N,
    repr (count_good_shifts sequence_arr) output /\
    count_good_shifts_spec sequence output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
