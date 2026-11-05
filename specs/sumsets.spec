(* @function        sumsets
   @signature       array sint -> option sint
   @math_signature  list Z -> option Z
   @summary         [sumsets s] takes the set S of distinct integers and
                    returns [Some d] for the largest d such that
                    a + b + c = d where a, b, c and d are distinct elements
                    of S, and [None] ("no solution") when no such d exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  S is the list of its elements, in input order.  The elements
   are signed (the statement allows negatives) : sint / Z. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* d is a + b + c for elements a, b, c of S, the four being distinct
   elements of S. *)
Definition sum_of_three (s : list Z) (d : Z) : Prop :=
  exists a b c,
    In a s /\ In b s /\ In c s /\ In d s /\
    a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
    a + b + c = d.

(* The statement's bounds. *)
Record valid_input (s : list Z) : Prop := {
  (* 1 <= N <= 4 000, the number of elements in S *)
  vi_n : (1 <= len s <= 4000)%N;
  (* each element of S is a distinct integer *)
  vi_distinct : NoDup s;
  (* ... between -536 870 912 and +536 870 911, inclusive *)
  vi_range : Forall (fun x => -536870912 <= x <= 536870911) s;
}.

(* Some d : d is such a sum and no such sum is larger ; None : no element of
   S is such a sum ("no solution"). *)
Definition sumsets_spec (s : list Z) (o : option Z) : Prop :=
  match o with
  | Some d => sum_of_three s d /\ forall d', sum_of_three s d' -> d' <= d
  | None => forall d, ~ sum_of_three s d
  end.

Program sumsets : array sint -> option sint.

Specification sumsets_correct : forall (s : list Z) (x : array sint),
  valid_input s -> repr x s ->
  exists o : option Z, repr (sumsets x) o /\ sumsets_spec s o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
