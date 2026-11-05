(* @function        largest_triangle
   @signature       array uint -> array uint -> float
   @math_signature  list N -> list N -> R
   @summary         [largest_triangle xs ys] takes the N points
                    (xs_k, ys_k) and returns the largest area of a triangle
                    whose three corners are three of the N points (three
                    distinct indices; coincident or collinear corners give
                    area 0, so the answer is 0 when no proper triangle
                    exists), as a finite float within 10^-5 of that area.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The points are two parallel lists, one per column of the
   input lines "x y". *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th coordinate, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* Three of the N points: three distinct indices; two indices may hold the
   same point ("the points are not necessarily distinct"). *)
Definition is_triple (xs : list N) (i j k : N) : Prop :=
  i < len xs /\ j < len xs /\ k < len xs /\ i <> j /\ j <> k /\ i <> k.

(* The area of the triangle with corners the points i, j, k: half the
   absolute value of the cross product (P_j - P_i) x (P_k - P_i). *)
Definition area (xs ys : list N) (i j k : N) : R :=
  let X t := Z.of_N (get_list_N xs t) in
  let Y t := Z.of_N (get_list_N ys t) in
  (Rabs (IZR ((X j - X i) * (Y k - Y i) - (X k - X i) * (Y j - Y i))) / 2)%R.

(* a is the largest area over all triples of points: attained by one, at
   least that of every one. *)
Definition is_largest_area (xs ys : list N) (a : R) : Prop :=
  (exists i j k, is_triple xs i j k /\ area xs ys i j k = a) /\
  (forall i j k, is_triple xs i j k -> (area xs ys i j k <= a)%R).

(* The statement's bounds. *)
Record valid_input (xs ys : list N) : Prop := {
  (* 3 <= N <= 5 000 *)
  vi_n : 3 <= len xs <= 5000;
  (* each of the next N lines contains two integers x and y *)
  vi_ys : len ys = len xs;
  (* 0 <= x, y <= 4 * 10^7 *)
  vi_x : Forall (fun c => c <= 4 * 10 ^ 7) xs;
  vi_y : Forall (fun c => c <= 4 * 10 ^ 7) ys;
}.

(* The answer: within an absolute error of at most 10^-5 of the largest
   area. *)
Definition largest_triangle_spec (xs ys : list N) (r : R) : Prop :=
  exists a, is_largest_area xs ys a /\ (Rabs (r - a) <= / 100000)%R.

Program largest_triangle : array uint -> array uint -> float.

Specification largest_triangle_correct :
  forall (xs ys : list N) (x y : array uint),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists r : R, repr (largest_triangle x y) r /\
                  largest_triangle_spec xs ys r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
