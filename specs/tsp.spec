(* @function        tsp
   @signature       array float -> array float -> array uint
   @math_signature  list R -> list R -> list N
   @summary         [tsp xs ys] takes the n >= 1 points (xs_k, ys_k) of
                    the plane and returns a tour: the indices 0 .. n-1, each
                    exactly once, in the order the points are visited, the
                    tour closing from the last back to the first. Its
                    length, with exact Euclidean distances over the reals
                    the floats denote, is at most twice that of any tour.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The points are two parallel lists, one per column of the
   input lines "x y"; a coordinate is the real its float denotes. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th coordinate (0 outside, never relied on). *)
Definition get_list_R (l : list R) (k : N) : R := nth (N.to_nat k) l 0%R.

(* A tour of n points: n indices, each below n, pairwise distinct, so every
   point is visited exactly once. *)
Definition is_tour (n : N) (t : list N) : Prop :=
  len t = n /\ Forall (fun v => v < n) t /\ NoDup t.

(* The exact Euclidean distance between points i and j.  Not rounded to
   the nearest integer as in the statement's scoring: the guarantee below
   is a property of the exact distances (rounding breaks the triangle
   inequality). *)
Definition dist (xs ys : list R) (i j : N) : R :=
  let dx := (get_list_R xs i - get_list_R xs j)%R in
  let dy := (get_list_R ys i - get_list_R ys j)%R in
  sqrt ((dx * dx + dy * dy)%R).

(* f 0 + f 1 + ... + f (m - 1). *)
Fixpoint sum_below (f : nat -> R) (m : nat) : R :=
  match m with
  | O => 0%R
  | S m' => (sum_below f m' + f m')%R
  end.

(* The length of the closed tour t: the sum over k of the distance from the
   k-th visited point to the next one, the last one going back to the
   first. *)
Definition tour_length (xs ys : list R) (t : list N) : R :=
  let m := List.length t in
  sum_below (fun k => dist xs ys (nth k t 0) (nth ((k + 1) mod m) t 0)) m.

(* The statement's bounds on one test case. *)
Record valid_input (xs ys : list R) : Prop := {
  (* 1 <= N <= 1000, the number of points *)
  vi_n : 1 <= len xs <= 1000;
  (* the following N lines each contain a pair of real numbers x, y *)
  vi_ys : len ys = len xs;
  (* all numbers in the input have absolute value bounded by 10^6 *)
  vi_x : Forall (fun c => (Rabs c <= 1000000)%R) xs;
  vi_y : Forall (fun c => (Rabs c <= 1000000)%R) ys;
}.

(* The answer: a tour of the n points, at most twice as long as any tour
   (hence as a shortest one).  Any such tour. *)
Definition tsp_spec (xs ys : list R) (t : list N) : Prop :=
  is_tour (len xs) t /\
  forall u, is_tour (len xs) u ->
    (tour_length xs ys t <= 2 * tour_length xs ys u)%R.

Program tsp : array float -> array float -> array uint.

Specification tsp_correct :
  forall (xs ys : list R) (x y : array float),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists t : list N, repr (tsp x y) t /\ tsp_spec xs ys t.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
