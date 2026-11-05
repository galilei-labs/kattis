(* @function        count_negatives
   @signature       array sint -> uint
   @math_signature  list Z -> N
   @summary         [count_negatives l] returns the number of elements of
                    l that are strictly below zero
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* t is strictly below zero. *)
Definition is_negative (t : Z) : bool := t <? 0.

(* The statement's bounds. *)
Record valid_input (l : list Z) : Prop := {
  (* 1 <= n <= 100 *)
  vi_length : (1 <= len l <= 100)%N;
  (* -10^6 <= t <= 10^6 *)
  vi_values : Forall (fun t => - 10 ^ 6 <= t <= 10 ^ 6) l;
}.

(* The result is the number of negative entries. *)
Definition count_negatives_spec (l : list Z) (c : N) : Prop :=
  c = len (filter is_negative l).

(* machine side : the only thing that gets extracted *)
Program count_negatives : array sint -> uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification count_negatives_correct : forall (l : list Z) (x : array sint),
  valid_input l -> repr x l ->
  exists c : N, repr (count_negatives x) c /\ count_negatives_spec l c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
