(** * Longest Increasing Subsequence *)

(** ** Description *)

(** Return the positions of a longest strictly increasing subsequence.

    [@kattis longincsubseq]
    - Difficulty: 3.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 100000 entries.
    - Signed 32-bit integer values. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
10
1 2 3 4 5 6 7 8 9 10
10
1 1 1 1 1 1 1 1 1 1
10
5 19 5 81 50 28 29 1 83 23
Output:
10
0 1 2 3 4 5 6 7 8 9
1
7
5
0 1 5 6 8
*)

(** ** [@hide] Environment *)
(* @function        lis
   @signature       array sint -> array uint
   @math_signature  list Z -> list N
   @summary         [lis sequence] returns the positions in sequence, in
                    ascending order, of a longest strictly increasing
                    subsequence of sequence ; any one of them when several
                    exist
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th value of the sequence, for k < len sequence (0 outside,
    never relied on). *)
Definition get_list_Z (sequence : list Z) (k : N) : Z :=
  nth (N.to_nat k) sequence 0%Z.

(** The t-th position listed in positions, for t < len positions (0
    outside, never relied on). *)
Definition get_list_N (positions : list N) (t : N) : N :=
  nth (N.to_nat t) positions 0.

(** Every listed position is a position of the sequence. *)
Definition indices_valid (sequence : list Z)
  (positions : list N) : Prop :=
  forall t, t < len positions ->
    get_list_N positions t < len sequence.

(** The positions are listed in strictly ascending order. *)
Definition indices_ascending (positions : list N) : Prop :=
  forall t u, t < u < len positions ->
    get_list_N positions t < get_list_N positions u.

(** The values at the listed positions strictly increase. *)
Definition values_increasing (sequence : list Z)
  (positions : list N)
    : Prop :=
  forall t u, t < u < len positions ->
    (get_list_Z sequence (get_list_N positions t) <
     get_list_Z sequence (get_list_N positions u))%Z.

(** positions is a strictly increasing subsequence of sequence, given by
    the positions of its elements. *)
Definition increasing_subseq (sequence : list Z)
  (positions : list N)
    : Prop :=
  indices_valid sequence positions /\ indices_ascending
    positions /\
  values_increasing sequence positions.

(** [@inside lis_correct] The statement's bounds on one test case. *)
Record valid_input (sequence : list Z) : Prop := {
  (* 1 <= n <= 10^5 *)
  vi_length : 1 <= len sequence <= 10 ^ 5;
  (* every value in [-2^31, 2^31) *)
  vi_values : Forall (fun value => (- 2 ^ 31 <= value < 2 ^
    31)%Z) sequence;
}.

(** ** Correctness *)

(** [@requirement] [@short The answer output : an increasing subsequence
    of sequence that none    is longer than.] The answer output : an
    increasing subsequence of sequence that none is longer than. *)
Definition lis_spec (sequence : list Z)
  (output : list N) : Prop :=
  increasing_subseq sequence output /\
  forall subsequence', increasing_subseq sequence
    subsequence' ->
    len subsequence' <= len output.

(** ** Interface *)

(** The [lis] program on machine values.
    - Input [sequence]:
    - Output [output]: *)
Program lis : array sint -> array uint.

(** ** Bridge *)

(** [@requirement lis_spec] [@fold full correctness statement] On valid
    represented inputs, [lis] returns a represented output
    satisfying [lis_spec]. *)
Specification lis_correct :
  forall (sequence : list Z) (sequence_arr : array sint),
  valid_input sequence -> repr sequence_arr sequence ->
  exists output : list N,
    repr (lis sequence_arr) output /\ lis_spec sequence
      output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
