(** * Ultra-QuickSort *)

(** ** Description *)

(** Count inversions in a sequence: pairs of positions where the earlier
    value is larger than the later value.

    [@kattis ultraquicksort]
    - Difficulty: 4.0
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 500,000 distinct integers.
    - Values from 0 to 999,999,999. *)

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
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of elements of values smaller than pivot. *)
Definition count_lt (pivot : N) (values : list N) : nat :=
  List.length (filter (fun value => value <? pivot) values).

(** The number of pairs of positions i < j whose values
    are in decreasing order. *)
Fixpoint inv_list (values : list N) : nat :=
  match values with
  | [] => 0%nat
  | first :: rest => (count_lt first rest + inv_list rest)
    %nat
  end.

(** [@inside inversions_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sequence : list N) : Prop := {
  (* 1 <= n <= 500000 *)
  vi_length : 1 <= len sequence <= 5 * 10 ^ 5;
  (* 0 <= a[i] <= 999999999 *)
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

(** ** Interface *)

(** Count inversions in a sequence: pairs of positions where the earlier value is larger
    than the later value.
    - Input [sequence]:
    - Output [output]: *)
Program inversions : array uint -> uint.

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

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
