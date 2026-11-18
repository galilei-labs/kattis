(** * Knapsack in a Globalized World *)

(** ** Description *)

(** Decide whether a target size is a nonnegative integer combination of the
    given item sizes, with unlimited copies of each item.

    [@kattis knapsack2]
    - Difficulty: 5.8
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Item size count: $1 \le n \le 20$; each size: $1 \le g_i \le 10^{3}$.
    - Target size: $1 \le k \le 10^{18}$. *)

(** ** Examples *)

(** - Input convention: Item-type count and target size, followed by the available item sizes.
    - Output convention: possible if the target can be filled exactly; impossible otherwise. *)
(* Input:
2 10000000000
3 6
Output:
impossible
*)

(** ** [@hide] Environment *)
(* @function        fillable
   @signature       uint -> array uint -> bool
   @math_signature  N -> list N -> bool
   @summary         [fillable knapsack_size item_sizes] returns whether
                    items of the sizes item_sizes, in unlimited supply, can
                    fill a knapsack of size knapsack_size exactly
                    It runs in at most c1 * (n + 1) * (G + 1) + c2 steps of
                    the cost model on a valid input, n the number of item
                    sizes and G the largest of them ([max_size]; the
                    residue-class closure costs the smallest size per item,
                    plus a gcd), for two constants c1, c2.
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

(** [items] lists valid zero-based item-type indices, allowing repetitions. *)
Definition bag (item_sizes : list N)
  (items : list N) : Prop :=
  Forall (fun item => item < len item_sizes) items.

(** The sum of the sizes of the item types listed in [items], counting repetitions. *)
Fixpoint total_size (item_sizes : list N)
  (items : list N) : N :=
  match items with
  | [] => 0
  | item :: rest => get_list_N item_sizes item + total_size
    item_sizes rest
  end.

(** Some bag of items has total size exactly [knapsack_size]. *)
Definition exact_filling (item_sizes : list N)
  (knapsack_size : N) : Prop :=
  exists items, bag item_sizes items /\
    total_size item_sizes items = knapsack_size.

(** [@inside fillable_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (knapsack_size : N)
  (item_sizes : list N) : Prop := {
  (* 1 <= n <= 20 *)
  vi_types : 1 <= len item_sizes <= 20;
  (* 1 <= k <= 10^18 *)
  vi_size : 1 <= knapsack_size <= 10 ^ 18;
  (* 1 <= g_i <= 10^3 *)
  vi_item_sizes : Forall (fun item_size => 1 <= item_size <=
    1000) item_sizes;
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when the target size is a nonnegative integer combination
    of the available item sizes. *)
Definition fillable_spec (knapsack_size : N)
  (item_sizes : list N)
    (output : bool) : Prop :=
  output = true <-> exact_filling item_sizes knapsack_size.

(** ** Complexity *)

(** [@requirement] Runs in $O((n+1)(M+1))$ steps, where $n$ is the number of item sizes and $M$ the largest item size. *)
Definition fillable_time_spec (c1 c2 n_item_sizes max_item_sizes steps : nat) : Prop :=
  (steps <= c1 * ((n_item_sizes + 1) * (max_item_sizes + 1)) + c2)%nat.

(** ** Interface *)

(** Decide whether a target size is a nonnegative integer combination of the given item
    sizes, with unlimited copies of each item.
    - Input [knapsack_size]: Target size to fill exactly.
    - Input [item_sizes]: Available item sizes; each can be used any number of times.
    - Output [output]: The output is true exactly when the target size is a nonnegative integer combination of the available item sizes. *)
Program fillable : uint -> array uint -> bool.

(** [@example fillable]
    - Sample: 1
    - Input [knapsack_size]: 10000000000
    - Input [item_sizes]: [3; 6]
    - Output [output]: false
*)

(** ** Bridge *)

(** [@requirement fillable_spec] [@fold full correctness statement] On
    valid represented inputs, [fillable] returns a represented
    output satisfying [fillable_spec]. *)
Specification fillable_correct :
  forall (knapsack_size : N) (item_sizes : list N)
         (knapsack_size_int : uint) (item_sizes_arr : array
           uint),
  valid_input knapsack_size item_sizes ->
  repr knapsack_size_int knapsack_size ->
    repr item_sizes_arr item_sizes ->
  exists output : bool,
    repr (fillable knapsack_size_int item_sizes_arr) output
      /\
    fillable_spec knapsack_size item_sizes output.

(** ** Complexity *)

(** [@hide] [fillable_cost] is the cost translation of [fillable] (the judge
    recomputes it and compares) ... *)
Complexity fillable_cost for fillable.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (G + 1) + c2 steps of the cost model on a valid input, n the number of item sizes and G the largest of them ([max_size]; the residue-class closure costs the smallest size per item, plus a gcd), for two constants
    quantified before the inputs, on every valid input. [@requirement fillable_time_spec] *)
Specification fillable_time : exists c1 c2 : nat,
  forall (knapsack_size : N) (item_sizes : list N)
  (knapsack_size_int : uint) (item_sizes_arr : array
  uint),
  valid_input knapsack_size item_sizes ->
  repr knapsack_size_int knapsack_size ->
  repr item_sizes_arr item_sizes ->
  fillable_time_spec c1 c2 (size item_sizes_arr) (max_size item_sizes_arr) (cost2 fillable_cost knapsack_size_int item_sizes_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
