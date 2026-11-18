(** * Longest Increasing Subsequence *)

(** ** Description *)

(** Return the positions of a longest strictly increasing subsequence.

    [@kattis longincsubseq]
    - Difficulty: 3.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Entry count: $1 \le n \le 10^{5}$.
    - Signed $32$-bit integer values. *)

(** ** Examples *)

(** - Input convention: Per case: sequence length followed by its integer values; input ends at EOF.
    - Output convention: Subsequence length, followed by increasing 0-based indices of a longest increasing subsequence. *)
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
                    It runs in at most c1 * n * (log2 n + 1) + c2 steps of
                    the cost model, n the length of the array, for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [sequence], or zero beyond the end. *)
Definition get_list_Z (sequence : list Z) (k : N) : Z :=
  nth (N.to_nat k) sequence 0%Z.

(** The entry at zero-based index [t] in [positions], or zero beyond the end. *)
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

(** [positions] lists strictly increasing valid indices whose values in [sequence]
    also strictly increase. *)
Definition increasing_subseq (sequence : list Z)
  (positions : list N)
    : Prop :=
  indices_valid sequence positions /\ indices_ascending
    positions /\
  values_increasing sequence positions.

(** [@inside lis_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sequence : list Z) : Prop := {
  (* 1 <= n <= 10^5 *)
  vi_length : 1 <= len sequence <= 10 ^ 5;
  (* every value x satisfies -2^31 <= x < 2^31 *)
  vi_values : Forall (fun value => (- 2 ^ 31 <= value < 2 ^
    31)%Z) sequence;
}.

(** ** Correctness *)

(** [@requirement]
    The output is an increasing sequence of input indices identifying a longest strictly
    increasing subsequence. *)
Definition lis_spec (sequence : list Z)
  (output : list N) : Prop :=
  increasing_subseq sequence output /\
  forall subsequence', increasing_subseq sequence
    subsequence' ->
    len subsequence' <= len output.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the sequence length. *)
Definition lis_time_spec (c1 c2 n_sequence steps : nat) : Prop :=
  (steps <= c1 * (n_sequence * (Nat.log2 (n_sequence) + 1)) + c2)%nat.

(** ** Interface *)

(** Return the positions of a longest strictly increasing subsequence.
    - Input [sequence]: Integer sequence in which to find an increasing subsequence.
    - Output [output]: The output is an increasing sequence of input indices identifying a longest strictly increasing subsequence. *)
Program lis : array sint -> array uint.

(** [@example lis]
    - Sample: 1
    - Case: 1
    - Input [sequence]: [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%Z
    - Output [output]: [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]
*)

(** [@example lis]
    - Sample: 1
    - Case: 2
    - Input [sequence]: [1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%Z
    - Output [output]: [7]
*)

(** [@example lis]
    - Sample: 1
    - Case: 3
    - Input [sequence]: [5; 19; 5; 81; 50; 28; 29; 1; 83; 23]%Z
    - Output [output]: [0; 1; 5; 6; 8]
*)

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

(** ** Complexity *)

(** [@hide] [lis_cost] is the cost translation of [lis] (the judge
    recomputes it and compares) ... *)
Complexity lis_cost for lis.

(** [@fold complexity bound] ... and runs in at most c1 * n * (log2 n + 1) + c2 steps of the cost model, n the length of the array, for two constants
    quantified before the input. [@requirement lis_time_spec] *)
Specification lis_time : exists c1 c2 : nat, forall sequence_arr : array sint,
  lis_time_spec c1 c2 (size sequence_arr) (cost1 lis_cost sequence_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
