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

(* Math side.  Item i has value values[i] and weight weights[i]. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* The sum of amounts[item] over the items of items. *)
Fixpoint total (amounts : list N) (items : list N) : N :=
  match items with
  | [] => 0
  | item :: rest => get_list_N amounts item + total amounts rest
  end.

(* items is a set of items : distinct indices in [0, n - 1]. *)
Definition selection (values : list N) (items : list N) : Prop :=
  NoDup items /\ Forall (fun item => item < len values) items.

(* The items of items fit in the knapsack. *)
Definition fits (capacity : N) (weights : list N) (items : list N) : Prop :=
  total weights items <= capacity.

(* The statement's bounds, for one test case. *)
Record valid_input (capacity : N) (values weights : list N) : Prop := {
  (* 1 <= C <= 2000 *)
  vi_capacity : 1 <= capacity <= 2000;
  (* 1 <= n <= 2000 *)
  vi_items : 1 <= len values <= 2000;
  (* one value and one weight per item *)
  vi_weights_length : len weights = len values;
  (* values and weights are integers between 1 and 10000 *)
  vi_values : Forall (fun value => 1 <= value <= 10000) values;
  vi_weights : Forall (fun weight => 1 <= weight <= 10000) weights;
}.

(* The result output = (best_value, chosen) : chosen is a set of items
   that fits, best_value is its total value, and no set of items that fits
   has a greater total value. *)
Definition knapsack_spec (capacity : N) (values weights : list N)
    (output : N * list N) : Prop :=
  match output with
  | (best_value, chosen) =>
      selection values chosen /\
      fits capacity weights chosen /\
      best_value = total values chosen /\
      forall items, selection values items -> fits capacity weights items ->
        total values items <= best_value
  end.

(* machine side : the only thing that gets extracted *)
Program knapsack : uint -> array uint -> array uint -> uint * array uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification knapsack_correct :
  forall (capacity : N) (values weights : list N)
         (capacity_int : uint) (values_arr weights_arr : array uint),
  valid_input capacity values weights ->
  repr capacity_int capacity -> repr values_arr values ->
  repr weights_arr weights ->
  exists output : N * list N,
    repr (knapsack capacity_int values_arr weights_arr) output /\
    knapsack_spec capacity values weights output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
