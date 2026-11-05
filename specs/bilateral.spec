(* @function        bilateral
   @signature       array uint -> array uint -> array uint
   @math_signature  list N -> list N -> list N
   @summary         [bilateral st lo] takes the m two-person teams, team k
                    being the Stockholm employee st_k and the London
                    employee lo_k, and returns the IDs of a smallest set of
                    employees containing at least one member of every team.
                    Among the smallest such sets it returns one containing
                    the friend, employee 1009, whenever one exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Employees are their IDs; the teams are two parallel lists,
   one per column of the input. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* Your friend has ID 1009. *)
Definition friend : N := 1009.

(* The teams, as (Stockholm member, London member) pairs. *)
Definition teams (st lo : list N) : list (N * N) := combine st lo.

(* c lists distinct employees and includes at least one person from each
   project. *)
Definition invitation (st lo c : list N) : Prop :=
  NoDup c /\ Forall (fun t => In (fst t) c \/ In (snd t) c) (teams st lo).

(* c is an invitation with the smallest number of employees. *)
Definition smallest (st lo c : list N) : Prop :=
  invitation st lo c /\ forall c', invitation st lo c' -> len c <= len c'.

(* The statement's bounds. *)
Record valid_input (st lo : list N) : Prop := {
  (* 1 <= m <= 10 000, the number of teams *)
  vi_m : 1 <= len st <= 10000;
  (* the following m lines each contain two integers i, j *)
  vi_pairs : len lo = len st;
  (* Stockholm employees have IDs in the range 1000 to 1999 *)
  vi_st : Forall (fun i => 1000 <= i <= 1999) st;
  (* London employees have IDs in the range 2000 to 2999 *)
  vi_lo : Forall (fun j => 2000 <= j <= 2999) lo;
  (* there cannot be several teams consisting of the same pair of
     employees *)
  vi_distinct : NoDup (teams st lo);
}.

(* The invitees: a smallest invitation, which contains the friend whenever
   some smallest invitation does.  Any such list, in any order. *)
Definition bilateral_spec (st lo c : list N) : Prop :=
  smallest st lo c /\
  ((exists c', smallest st lo c' /\ In friend c') -> In friend c).

Program bilateral : array uint -> array uint -> array uint.

Specification bilateral_correct :
  forall (st lo : list N) (x y : array uint),
  valid_input st lo -> repr x st -> repr y lo ->
  exists c : list N, repr (bilateral x y) c /\ bilateral_spec st lo c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
