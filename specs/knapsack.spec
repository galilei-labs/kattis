(* @function        knapsack
   @signature       uint -> array uint -> array uint -> uint * array uint
   @math_signature  N -> list N -> list N -> N * list N
   @summary         [knapsack C values weights] returns the greatest total
                    value of a set of items whose total weight is at most
                    C, and the indices of such a set ; any one when several
                    exist
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

(* The sum of a[i] over the indices i of l. *)
Fixpoint total (a : list N) (l : list N) : N :=
  match l with
  | [] => 0
  | i :: l' => get_list_N a i + total a l'
  end.

(* l is a set of items : distinct indices in [0, n - 1]. *)
Definition selection (values : list N) (l : list N) : Prop :=
  NoDup l /\ Forall (fun i => i < len values) l.

(* The items of l fit in the knapsack. *)
Definition fits (C : N) (weights : list N) (l : list N) : Prop :=
  total weights l <= C.

(* The statement's bounds, for one test case. *)
Record valid_input (C : N) (values weights : list N) : Prop := {
  (* 1 <= C <= 2000 *)
  vi_capacity : 1 <= C <= 2000;
  (* 1 <= n <= 2000 *)
  vi_items : 1 <= len values <= 2000;
  (* one value and one weight per item *)
  vi_weights_length : len weights = len values;
  (* values and weights are integers between 1 and 10000 *)
  vi_values : Forall (fun v => 1 <= v <= 10000) values;
  vi_weights : Forall (fun w => 1 <= w <= 10000) weights;
}.

(* The result (v, l) : l is a set of items that fits, v is its total value,
   and no set of items that fits has a greater total value. *)
Definition knapsack_spec (C : N) (values weights : list N) (r : N * list N)
  : Prop :=
  selection values (snd r) /\
  fits C weights (snd r) /\
  fst r = total values (snd r) /\
  forall l, selection values l -> fits C weights l -> total values l <= fst r.

(* machine side : the only thing that gets extracted *)
Program knapsack : uint -> array uint -> array uint -> uint * array uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification knapsack_correct :
  forall (C : N) (values weights : list N)
         (xC : uint) (xv xw : array uint),
  valid_input C values weights ->
  repr xC C -> repr xv values -> repr xw weights ->
  exists r : N * list N,
    repr (knapsack xC xv xw) r /\ knapsack_spec C values weights r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
