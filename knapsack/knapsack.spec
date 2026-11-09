(** * Knapsack *)

(** ** Description *)

(** Choose a subset of items with maximum total value subject to a weight
    capacity. Return its value and the selected item indices.

    [@kattis knapsack]
    - Difficulty: 3.1
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Capacity and item count in $[1, 2{,}000]$.
    - Integer weights and values in $[1, 10{,}000]$. *)

(** ** Examples *)

(** - Input convention: Per case: capacity and item count, followed by value-weight pairs.
    - Output convention: Selected-item count, followed by their 0-based indices in any order. *)
(* Input:
5 3
1 5
10 5
100 5
6 4
5 4
4 3
3 2
2 1
Output:
1
2
3
1 2 3
*)

(** ** [@hide] Environment *)
(* @function        knapsack
   @signature       uint -> array uint -> array uint -> uint * array uint
   @math_signature  N -> list N -> list N -> N * list N
   @summary         [knapsack capacity values weights] returns the greatest
                    total value of a set of items whose total weight is at
                    most capacity, and the indices of such a set ; any one
                    when several exist
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. Item i has value values[i] and weight weights[i]. The
    number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** The sum of amounts[item] over the items of items. *)
Fixpoint total (amounts : list N) (items : list N) : N :=
  match items with
  | [] => 0
  | item :: rest => get_list_N amounts item + total amounts
    rest
  end.

(** items is a set of items : distinct indices in [0, n - 1]. *)
Definition selection (values : list N)
  (items : list N) : Prop :=
  NoDup items /\ Forall (fun item => item < len values)
    items.

(** The items of items fit in the knapsack. *)
Definition fits (capacity : N) (weights : list N)
  (items : list N) : Prop :=
  total weights items <= capacity.

(** [@inside knapsack_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (capacity : N)
  (values weights : list N) : Prop := {
  (* 1 <= C <= 2000 *)
  vi_capacity : 1 <= capacity <= 2000;
  (* 1 <= n <= 2000 *)
  vi_items : 1 <= len values <= 2000;
  (* one value and one weight per item *)
  vi_weights_length : len weights = len values;
  (* values and weights are integers between 1 and 10000 *)
  vi_values : Forall (fun value => 1 <= value <= 10000)
    values;
  vi_weights : Forall (fun weight => 1 <= weight <= 10000)
    weights;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives a maximum achievable total value and a corresponding subset of item
    indices whose total weight does not exceed the capacity. *)
Definition knapsack_spec (capacity : N)
  (values weights : list N)
    (output : N * list N) : Prop :=
  match output with
  | (best_value, chosen) =>
      selection values chosen /\
      fits capacity weights chosen /\
      best_value = total values chosen /\
      forall items, selection values items ->
        fits capacity weights items ->
        total values items <= best_value
  end.

(** ** Interface *)

(** Choose a subset of items with maximum total value subject to a weight capacity. Return
    its value and the selected item indices.
    - Input [capacity]: Maximum permitted total weight.
    - Input [values]: Value of each available item.
    - Input [weights]: Weight of each corresponding item.
    - Output [output]: The output gives a maximum achievable total value and a corresponding subset of item indices whose total weight does not exceed the capacity. *)
Program knapsack : uint -> array uint -> array uint -> uint
  * array uint.

(** ** Bridge *)

(** [@requirement knapsack_spec] [@fold full correctness statement] On
    valid represented inputs, [knapsack] returns a represented
    output satisfying [knapsack_spec]. *)
Specification knapsack_correct :
  forall (capacity : N) (values weights : list N)
         (capacity_int : uint) (values_arr weights_arr :
           array uint),
  valid_input capacity values weights ->
  repr capacity_int capacity -> repr values_arr values ->
  repr weights_arr weights ->
  exists output : N * list N,
    repr (knapsack capacity_int values_arr weights_arr)
      output /\
    knapsack_spec capacity values weights output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
