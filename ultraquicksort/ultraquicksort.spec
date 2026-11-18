(** * Ultra-QuickSort *)

(** ** Description *)

(** Count inversions in a sequence: pairs of positions where the earlier
    value is larger than the later value.

    [@kattis ultraquicksort]
    - Difficulty: 4.0
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Distinct integer count: $1 \le n \le 5 \times 10^{5}$.
    - Values: $0 \le a_i \le 10^{9} - 1$. *)

(** ** Examples *)

(** - Input convention: Sequence length, followed by one integer value per line.
    - Output convention: A single integer giving the inversion count. *)
(* Input:
5
9
1
0
5
4
Output:
6
*)

(** ** [@hide] Environment *)

(* @function        inversions
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [inversions sequence] returns the number of pairs of
                    positions i < j of sequence such that
                    sequence[j] < sequence[i]
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

(** The number of entries in [values] strictly smaller than [pivot]. *)
Definition count_lt (pivot : N) (values : list N) : nat :=
  List.length (filter (fun value => value <? pivot) values).

(** The number of index pairs in increasing position order whose entries in the list
    are strictly decreasing. *)
Fixpoint inv_list (values : list N) : nat :=
  match values with
  | [] => 0%nat
  | first :: rest => (count_lt first rest + inv_list rest)
    %nat
  end.

(** [@inside inversions_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sequence : list N) : Prop := {
  (* 1 <= n <= 5 * 10^5 *)
  vi_length : 1 <= len sequence <= 5 * 10 ^ 5;
  (* 0 <= a[i] <= 10^9 - 1 *)
  vi_values : Forall (fun element => element <= 10 ^ 9 - 1)
    sequence;
  (* the integers are distinct *)
  vi_distinct : NoDup sequence;
}.

(** ** Correctness *)

(** [@requirement]
    The output counts index pairs for which the earlier value is strictly greater than
    the later value. *)
Definition inversions_spec
  (sequence : list N)
  (output : N)
  : Prop :=
  output = N.of_nat (inv_list sequence).

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the sequence length. *)
Definition inversions_time_spec (c1 c2 n_sequence steps : nat) : Prop :=
  (steps <= c1 * (n_sequence * (Nat.log2 (n_sequence) + 1)) + c2)%nat.

(** ** Interface *)

(** Count inversions in a sequence: pairs of positions where the earlier value is larger
    than the later value.
    - Input [sequence]: Integer sequence whose inversions are counted.
    - Output [output]: The output counts index pairs for which the earlier value is strictly greater than the later value. *)
Program inversions : array uint -> uint.

(** [@example inversions]
    - Sample: 1
    - Input [sequence]: [9; 1; 0; 5; 4]
    - Output [output]: 6
*)

(** ** Bridge *)

(** [@requirement inversions_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [inversions_spec]. *)
Specification inversions_correct :
  forall (sequence : list N) (sequence_arr : array uint),
  valid_input sequence -> repr sequence_arr sequence ->
  exists output : N,
    repr (inversions sequence_arr) output /\
    inversions_spec sequence output.

(** ** Complexity *)

(** [@hide] [inversions_cost] is the cost translation of [inversions] (the judge
    recomputes it and compares) ... *)
Complexity inversions_cost for inversions.

(** [@fold complexity bound] ... and runs in at most c1 * n * (log2 n + 1) + c2 steps of the cost model, n the length of the array, for two constants
    quantified before the input. [@requirement inversions_time_spec] *)
Specification inversions_time : exists c1 c2 : nat, forall sequence_arr : array uint,
  inversions_time_spec c1 c2 (size sequence_arr) (cost1 inversions_cost sequence_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
