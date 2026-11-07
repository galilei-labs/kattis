(* @function        sumsets
   @signature       array sint -> option sint
   @math_signature  list Z -> option Z
   @summary         [sumsets elements] takes the set S of distinct integers
                    and returns [Some target] for the largest target such
                    that first + second + third = target where first,
                    second, third and target are distinct elements of S,
                    and [None] ("no solution") when no such target exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  S is the list elements of its elements, in input order.  The
   elements are signed (the statement allows negatives) : sint / Z. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* target is first + second + third for elements first, second, third of
   S, the four being distinct elements of S. *)
Definition sum_of_three (elements : list Z) (target : Z) : Prop :=
  exists first second third,
    In first elements /\ In second elements /\ In third elements /\
    In target elements /\
    first <> second /\ first <> third /\ first <> target /\
    second <> third /\ second <> target /\ third <> target /\
    first + second + third = target.

(* The statement's bounds. *)
Record valid_input (elements : list Z) : Prop := {
  (* 1 <= N <= 4 000, the number of elements in S *)
  vi_n : (1 <= len elements <= 4000)%N;
  (* each element of S is a distinct integer *)
  vi_distinct : NoDup elements;
  (* ... between -536 870 912 and +536 870 911, inclusive *)
  vi_range : Forall (fun element => -536870912 <= element <= 536870911)
               elements;
}.

(* Some target : target is such a sum and no such sum is larger ; None : no
   element of S is such a sum ("no solution"). *)
Definition sumsets_spec (elements : list Z) (output : option Z) : Prop :=
  match output with
  | Some target =>
      sum_of_three elements target /\
      forall target', sum_of_three elements target' -> target' <= target
  | None => forall target, ~ sum_of_three elements target
  end.

Program sumsets : array sint -> option sint.

Specification sumsets_correct :
  forall (elements : list Z) (elements_arr : array sint),
  valid_input elements -> repr elements_arr elements ->
  exists output : option Z,
    repr (sumsets elements_arr) output /\
    sumsets_spec elements output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
