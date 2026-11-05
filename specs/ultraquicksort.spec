(* @function        inversions
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [inversions l] returns the number of pairs of
                    positions i < j of l such that l[j] < l[i]
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of elements of l smaller than x. *)
Definition count_lt (x : N) (l : list N) : nat :=
  List.length (filter (fun y => y <? x) l).

(* The number of pairs of positions i < j whose values are in decreasing
   order. *)
Fixpoint inv_list (l : list N) : nat :=
  match l with
  | [] => 0%nat
  | x :: l' => (count_lt x l' + inv_list l')%nat
  end.

(* The statement's bounds. *)
Record valid_input (l : list N) : Prop := {
  (* 1 <= n <= 500000 *)
  vi_length : 1 <= len l <= 5 * 10 ^ 5;
  (* 0 <= a[i] <= 999999999 *)
  vi_values : Forall (fun a => a <= 10 ^ 9 - 1) l;
  (* the integers are distinct *)
  vi_distinct : NoDup l;
}.

(* The result is the number of inversions. *)
Definition inversions_spec (l : list N) (c : N) : Prop :=
  c = N.of_nat (inv_list l).

(* machine side : the only thing that gets extracted *)
Program inversions : array uint -> uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification inversions_correct : forall (l : list N) (a : array uint),
  valid_input l -> repr a l ->
  exists c : N, repr (inversions a) c /\ inversions_spec l c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
