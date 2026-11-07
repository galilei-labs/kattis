(** * Non-negative Partial Sums *)

(** ** Description *)

(** [count_good_shifts sequence] returns the number of cyclic shifts of
    sequence all of whose prefix sums are nonnegative. *)

(** [@kattis nonnegpartsums]
    - Difficulty: 6.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB *)

(** ** Examples *)

(** Kattis sample: text input and output. *)
(* 3
2 2 1
3
-1 1 1
1
-1
0 = 3
2
0 *)

(** ** [@hide] Environment *)
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

(** ** Definitions *)

(** Math side The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The [sum_Z] definition. *)
Definition sum_Z (l : list Z) : Z := fold_right Z.add 0 l.

(** The cyclic shift of sequence by k positions : sequence[k], ...,
    sequence[n-1], sequence[0], ..., sequence[k-1]. *)
Definition rotate (k : nat) (sequence : list Z) : list Z :=
  skipn k sequence ++ firstn k sequence.

(** The sum of the first i elements is nonnegative for every 1 <= i <=
    n. *)
Definition nonneg_prefix_sums (sequence : list Z) : bool :=
  forallb (fun i => 0 <=? sum_Z (firstn i sequence))
          (seq 1 (List.length sequence)).

(** The [good_shift] definition. *)
Definition good_shift (sequence : list Z)
  (k : nat) : bool :=
  nonneg_prefix_sums (rotate k sequence).

(** The shifts k in [0, n - 1] whose prefix sums are all nonnegative. *)
Definition good_shifts (sequence : list Z) : list nat :=
  filter (good_shift sequence) (seq 0 (List.length
    sequence)).

(** [@inside count_good_shifts_correct] The statement's bounds, for one
    test case. *)
Record valid_input (sequence : list Z) : Prop := {
  (* 1 <= n <= 10^6 *)
  vi_length : (1 <= len sequence <= 10 ^ 6)%N;
  (* -1000 <= a_i <= 1000 *)
  vi_values : Forall (fun element => - 1000 <= element <=
    1000) sequence;
}.

(** ** Correctness *)

(** [@requirement] [@short The result is the number of good shifts.] The
    result is the number of good shifts. *)
Definition count_good_shifts_spec (sequence : list Z)
  (output : N)
    : Prop :=
  output = len (good_shifts sequence).

(** ** Interface *)

(** The [count_good_shifts] program on machine values.
    - Input [sequence]:
    - Output [output]: *)
Program count_good_shifts : array sint -> uint.

(** ** Bridge *)

(** [@requirement count_good_shifts_spec] [@fold full correctness
    statement] On valid represented inputs, [count_good_shifts]
    returns a represented output satisfying
    [count_good_shifts_spec]. *)
Specification count_good_shifts_correct :
  forall (sequence : list Z) (sequence_arr : array sint),
  valid_input sequence -> repr sequence_arr sequence ->
  exists output : N,
    repr (count_good_shifts sequence_arr) output /\
    count_good_shifts_spec sequence output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
