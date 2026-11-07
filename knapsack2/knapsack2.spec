(** * Knapsack in a Globalized World *)

(** ** Description *)

(** Decide whether a target size is a nonnegative integer combination of the
    given item sizes, with unlimited copies of each item.

    [@kattis knapsack2]
    - Difficulty: 5.9
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 20 item sizes, each from 1 to 1000.
    - Target size from 1 to 10^18. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** items is a bag of items : type indices in [0, n - 1], repetitions
    allowed. *)
Definition bag (item_sizes : list N)
  (items : list N) : Prop :=
  Forall (fun item => item < len item_sizes) items.

(** The total size of the items of items. *)
Fixpoint total_size (item_sizes : list N)
  (items : list N) : N :=
  match items with
  | [] => 0
  | item :: rest => get_list_N item_sizes item + total_size
    item_sizes rest
  end.

(** Some bag of items has total size exactly knapsack_size. *)
Definition exact_filling (item_sizes : list N)
  (knapsack_size : N) : Prop :=
  exists items, bag item_sizes items /\
    total_size item_sizes items = knapsack_size.

(** [@inside fillable_correct] The statement's bounds. *)
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

(** [@requirement] [@short The result output is true exactly when an
    exact filling exists.] The result output is true exactly when an
    exact filling exists. *)
Definition fillable_spec (knapsack_size : N)
  (item_sizes : list N)
    (output : bool) : Prop :=
  match output with
  | true => exact_filling item_sizes knapsack_size
  | false => ~ exact_filling item_sizes knapsack_size
  end.

(** ** Interface *)

(** The [fillable] program on machine values.
    - Input [knapsack_size]:
    - Input [item_sizes]:
    - Output [output]: *)
Program fillable : uint -> array uint -> bool.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
