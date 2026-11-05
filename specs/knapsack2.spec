(* @function        fillable
   @signature       uint -> array uint -> bool
   @math_signature  N -> list N -> bool
   @summary         [fillable k g] returns whether items of the sizes g, in
                    unlimited supply, can fill a knapsack of size k exactly
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* l is a bag of items : type indices in [0, n - 1], repetitions allowed. *)
Definition bag (g : list N) (l : list N) : Prop :=
  Forall (fun i => i < len g) l.

(* The total size of the items of l. *)
Fixpoint total_size (g : list N) (l : list N) : N :=
  match l with
  | [] => 0
  | i :: l' => get_list_N g i + total_size g l'
  end.

(* Some bag of items has total size exactly k. *)
Definition exact_filling (g : list N) (k : N) : Prop :=
  exists l, bag g l /\ total_size g l = k.

(* The statement's bounds. *)
Record valid_input (k : N) (g : list N) : Prop := {
  (* 1 <= n <= 20 *)
  vi_types : 1 <= len g <= 20;
  (* 1 <= k <= 10^18 *)
  vi_size : 1 <= k <= 10 ^ 18;
  (* 1 <= g_i <= 10^3 *)
  vi_item_sizes : Forall (fun s => 1 <= s <= 1000) g;
}.

(* The result is true exactly when an exact filling exists. *)
Definition fillable_spec (k : N) (g : list N) (b : bool) : Prop :=
  b = true <-> exact_filling g k.

(* machine side : the only thing that gets extracted *)
Program fillable : uint -> array uint -> bool.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification fillable_correct :
  forall (k : N) (g : list N) (xk : uint) (xg : array uint),
  valid_input k g -> repr xk k -> repr xg g ->
  exists b : bool, repr (fillable xk xg) b /\ fillable_spec k g b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
