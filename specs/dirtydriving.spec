(* @function        dirtydriving
   @signature       uint -> array uint -> uint
   @math_signature  N -> list N -> N
   @summary         [dirtydriving p d] is the minimum distance D you must keep
                    to the car directly in front, the cars ahead of you being
                    at the distinct distances d (in any order): moving yourself
                    so that the nearest car is at distance D, every car x must
                    then be at distance at least p * (k + 1), k being the
                    number of cars between you and x.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A car ahead is its current distance to you. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of cars between you and the car at distance x: the cars
   strictly closer than x. *)
Definition cars_between (d : list N) (x : N) : N :=
  len (filter (fun y => y <? x) d).

(* Keeping distance D to the car directly in front (the car at distance y,
   with no car between), every car x of d, then at distance D + (x - y),
   is at distance at least p * (cars_between x + 1). *)
Definition keeps_distance (p : N) (d : list N) (D : N) : Prop :=
  forall x y, In x d -> In y d -> cars_between d y = 0 ->
    p * (cars_between d x + 1) + y <= D + x.

(* The statement's bounds, for one test case; n is len d. *)
Record valid_input (p : N) (d : list N) : Prop := {
  (* 1 <= n <= 100 000 - the number of cars ahead of you *)
  vi_n : 1 <= len d <= 100000;
  (* 1 <= p <= 20 - the deceleration constant *)
  vi_p : 1 <= p <= 20;
  (* each of these integers are in the interval [1, 10^7] *)
  vi_d : Forall (fun x => 1 <= x <= 10 ^ 7) d;
  (* a single line with n unique integers *)
  vi_unique : NoDup d;
}.

(* The answer is the least distance that keeps every car far enough. *)
Definition dirtydriving_spec (p : N) (d : list N) (D : N) : Prop :=
  keeps_distance p d D /\
  forall D', keeps_distance p d D' -> D <= D'.

Program dirtydriving : uint -> array uint -> uint.

Specification dirtydriving_correct :
  forall (p : N) (d : list N) (x : uint) (y : array uint),
  valid_input p d -> repr x p -> repr y d ->
  exists D : N, repr (dirtydriving x y) D /\ dirtydriving_spec p d D.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
