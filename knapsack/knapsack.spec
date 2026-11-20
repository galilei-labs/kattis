(** * Knapsack *)

(** ** Description *)

(** Choose a subset of items with maximum total value subject to a weight
    capacity. Return its value and the selected item indices.

    [@kattis knapsack]
    - Difficulty: 3.1
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Capacity and item count: $1 \le C, n \le 2 \times 10^{3}$.
    - Integer weights and values: $1 \le w_i, v_i \le 10^{4}$. *)

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
                    It runs in at most c1 * (n + 1) * (C + 1) + c2 steps of
                    the cost model, n the number of items, for two constants
                    c1, c2.
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

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** The sum of the entries of [amounts] selected by the indices in [items]. *)
Fixpoint total (amounts : list N) (items : list N) : N :=
  match items with
  | [] => 0
  | item :: rest => get_list_N amounts item + total amounts
    rest
  end.

(** [items] lists distinct valid zero-based item indices. *)
Definition selection (values : list N)
  (items : list N) : Prop :=
  NoDup items /\ Forall (fun item => item < len values)
    items.

(** The total weight of the selected [items] does not exceed [capacity]. *)
Definition fits (capacity : N) (weights : list N)
  (items : list N) : Prop :=
  total weights items <= capacity.

(** [@inside knapsack_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (capacity : N)
  (values weights : list N) : Prop := {
  (* 1 <= C <= 2 * 10^3 *)
  vi_capacity : 1 <= capacity <= 2000;
  (* 1 <= n <= 2 * 10^3 *)
  vi_items : 1 <= len values <= 2000;
  (* one value and one weight per item *)
  vi_weights_length : len weights = len values;
  (* values and weights are integers between 1 and 10^4 *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O((n+1)(C+1))$ steps, where $n$ is the number of items and $C$ the capacity. *)
Definition knapsack_time_spec (c1 c2 n_values n_capacity steps : nat) : Prop :=
  (steps <= c1 * ((n_values + 1) * (n_capacity + 1)) + c2)%nat.

(** ** Interface *)

(** Choose a subset of items with maximum total value subject to a weight capacity. Return
    its value and the selected item indices.
    - Input [capacity]: Maximum permitted total weight.
    - Input [values]: Value of each available item.
    - Input [weights]: Weight of each corresponding item.
    - Output [output]: The output gives a maximum achievable total value and a corresponding subset of item indices whose total weight does not exceed the capacity. *)
Program knapsack : uint -> array uint -> array uint -> uint
  * array uint.

(** [@example knapsack]
    - Sample: 1
    - Case: 1
    - Input [capacity]: 5
    - Input [values]: [1; 10; 100]
    - Input [weights]: [5; 5; 5]
    - Output [output]: (100, [2])
*)

(** [@example knapsack]
    - Sample: 1
    - Case: 2
    - Input [capacity]: 6
    - Input [values]: [5; 4; 3; 2]
    - Input [weights]: [4; 3; 2; 1]
    - Output [output]: (9, [1; 2; 3])
*)

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

(** ** Complexity *)

(** [@hide] [knapsack_cost] is the cost translation of [knapsack] (the judge
    recomputes it and compares) ... *)
Complexity knapsack_cost for knapsack.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (C + 1) + c2 steps of the cost model, n the number of items, for two constants
    quantified before the inputs. [@requirement knapsack_time_spec] *)
Specification knapsack_time : exists c1 c2 : nat, forall (capacity_int : uint) (values_arr weights_arr : array uint),
  knapsack_time_spec c1 c2 (size values_arr) (size capacity_int) (cost3 knapsack_cost capacity_int values_arr weights_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
