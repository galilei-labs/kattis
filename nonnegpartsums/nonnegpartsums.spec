(** * Non-negative Partial Sums *)

(** ** Description *)

(** Count cyclic shifts of an integer sequence whose every prefix has a
    nonnegative sum.

    [@kattis nonnegpartsums]
    - Difficulty: 6.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Sequence length: $1 \le n \le 10^{6}$; each value: $-10^{3} \le a_i \le 10^{3}$. *)

(** ** Examples *)

(** - Input convention: Per case: sequence length followed by its integers; a zero length ends input.
    - Output convention: One count of cyclic shifts with nonnegative prefix sums per case. *)
(* Input:
3
2 2 1
3
-1 1 1
1
-1
0
Output:
3
2
0
*)

(** ** [@hide] Environment *)
(* @function        count_good_shifts
   @signature       array sint -> uint
   @math_signature  list Z -> N
   @summary         [count_good_shifts sequence] returns the number of
                    cyclic shifts of sequence all of whose prefix sums are
                    nonnegative
                    It runs in at most c1 * (n + 1) + c2 steps of the cost
                    model on a valid input, n the length of the sequence
                    (the deque sweep is linear: every element is pushed and
                    popped at most once), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The sum of the integer entries, with value zero for an empty list. *)
Fixpoint sum_Z (l : list Z) : Z :=
  match l with
  | [] => 0
  | value :: rest => value + sum_Z rest
  end.

(** Rotate [sequence] left by [k] entries, moving the preceding entries to the end. *)
Definition rotate (k : nat) (sequence : list Z) : list Z :=
  skipn k sequence ++ firstn k sequence.

(** Every nonempty prefix of [sequence] has a nonnegative sum. *)
Definition nonneg_prefix_sums (sequence : list Z) : bool :=
  forallb (fun i => 0 <=? sum_Z (firstn i sequence))
          (seq 1 (List.length sequence)).

(** Test whether rotating [sequence] by [k] positions makes every prefix sum
    nonnegative. *)
Definition good_shift (sequence : list Z)
  (k : nat) : bool :=
  nonneg_prefix_sums (rotate k sequence).

(** The zero-based rotation offsets that make every nonempty prefix sum nonnegative. *)
Definition good_shifts (sequence : list Z) : list nat :=
  filter (good_shift sequence) (seq 0 (List.length
    sequence)).

(** [@inside count_good_shifts_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sequence : list Z) : Prop := {
  (* 1 <= n <= 10^6 *)
  vi_length : (1 <= len sequence <= 10 ^ 6)%N;
  (* -10^3 <= a_i <= 10^3 *)
  vi_values : Forall (fun element => - 1000 <= element <=
    1000) sequence;
}.

(** ** Correctness *)

(** [@requirement]
    The output counts cyclic shifts for which every prefix sum is nonnegative. *)
Definition count_good_shifts_spec (sequence : list Z)
  (output : N)
    : Prop :=
  output = len (good_shifts sequence).

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the sequence length. *)
Definition count_good_shifts_time_spec (c1 c2 n_sequence steps : nat) : Prop :=
  (steps <= c1 * (n_sequence + 1) + c2)%nat.

(** ** Interface *)

(** Count cyclic shifts of an integer sequence whose every prefix has a nonnegative sum.
    - Input [sequence]: Integer sequence whose cyclic shifts are tested.
    - Output [output]: The output counts cyclic shifts for which every prefix sum is nonnegative. *)
Program count_good_shifts : array sint -> uint.

(** [@example count_good_shifts]
    - Sample: 1
    - Case: 1
    - Input [sequence]: [2; 2; 1]%Z
    - Output [output]: 3
*)

(** [@example count_good_shifts]
    - Sample: 1
    - Case: 2
    - Input [sequence]: [-1; 1; 1]%Z
    - Output [output]: 2
*)

(** [@example count_good_shifts]
    - Sample: 1
    - Case: 3
    - Input [sequence]: [-1]%Z
    - Output [output]: 0
*)

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

(** ** Complexity *)

(** [@hide] [count_good_shifts_cost] is the cost translation of [count_good_shifts] (the judge
    recomputes it and compares) ... *)
Complexity count_good_shifts_cost for count_good_shifts.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) + c2 steps of the cost model on a valid input, n the length of the sequence (the deque sweep is linear: every element is pushed and popped at most once), for two constants
    quantified before the inputs, on every valid input. [@requirement count_good_shifts_time_spec] *)
Specification count_good_shifts_time : exists c1 c2 : nat,
  forall (sequence : list Z) (sequence_arr : array sint),
  valid_input sequence -> repr sequence_arr sequence ->
  count_good_shifts_time_spec c1 c2 (size sequence_arr) (cost1 count_good_shifts_cost sequence_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
