(** * Travelling Salesperson 2D *)

(** ** Description *)

(** Construct a closed tour visiting every point exactly once, with total
    Euclidean length at most twice the optimum.

    [@kattis tsp]
    - Difficulty: 1.5
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 1000 points.
    - Coordinate absolute values are at most 1000000. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
10
95.0129 61.5432
23.1139 79.1937
60.6843 92.1813
48.5982 73.8207
89.1299 17.6266
76.2097 40.5706
45.6468 93.5470
1.8504 91.6904
82.1407 41.0270
44.4703 89.3650
Output:
0
8
5
4
3
9
6
2
1
7
*)

(** ** [@hide] Environment *)

(* @function        tsp
   @signature       array float -> array float -> array uint
   @math_signature  list R -> list R -> list N
   @summary         [tsp x_coords y_coords] takes the point_count >= 1
                    points (x_coords_k, y_coords_k) of the plane and returns
                    a tour: the indices 0 .. point_count-1, each exactly
                    once, in the order the points are visited, the tour
                    closing from the last back to the first. Its length,
                    with exact Euclidean distances over the reals the floats
                    denote, is at most twice that of any tour.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. The points are two parallel lists, one per
   column of the input lines "x y" ; a coordinate is the
   real its float denotes. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th coordinate (0 outside, never relied on). *)
Definition get_list_R (l : list R) (k : N) : R :=
  nth (N.to_nat k) l 0%R.

(** A tour of point_count points: point_count indices,
    each below point_count, pairwise distinct, so every
    point is visited exactly once. *)
Definition is_tour (point_count : N) (tour : list N) : Prop
  :=
  len tour = point_count /\ Forall
    (fun index => index < point_count) tour /\
  NoDup tour.

(** The exact Euclidean distance between points i and j.
    Not rounded to the nearest integer as in the
    statement's scoring: the guarantee below is a
    property of the exact distances (rounding breaks the
    triangle inequality). *)
Definition dist (x_coords y_coords : list R) (i j : N) : R
  :=
  let delta_x :=
    (get_list_R x_coords i - get_list_R x_coords j)%R in
  let delta_y :=
    (get_list_R y_coords i - get_list_R y_coords j)%R in
  sqrt ((delta_x * delta_x + delta_y * delta_y)%R).

(** term 0 + term 1 + ... + term (count - 1). *)
Fixpoint sum_below (term : nat -> R) (count : nat) : R :=
  match count with
  | O => 0%R
  | S count' => (sum_below term count' + term count')%R
  end.

(** The length of the closed tour: the sum over k of the
    distance from the k-th visited point to the next one,
    the last one going back to the first. *)
Definition tour_length (x_coords y_coords : list R)
  (tour : list N) : R :=
  let stop_count := List.length tour in
  sum_below
    (fun k => dist x_coords y_coords (nth k tour 0)
                (nth ((k + 1) mod stop_count) tour 0))
    stop_count.

(** [@inside tsp_correct] The statement's bounds on one
    test case. *)
Record valid_input (x_coords y_coords : list R) : Prop := {
  (* 1 <= N <= 1000, the number of points *)
  vi_n : 1 <= len x_coords <= 1000;
  (* the following N lines each contain a pair of real
     numbers x, y *)
  vi_ys : len y_coords = len x_coords;
  (* all numbers in the input have absolute value bounded
     by 10^6 *)
  vi_x : Forall (fun coord => (Rabs coord <= 1000000)%R)
    x_coords;
  vi_y : Forall (fun coord => (Rabs coord <= 1000000)%R)
    y_coords;
}.

(** ** Correctness *)

(** [@requirement] [@short Return a tour through all
    points whose length is at most twice the length of
    any tour, using exact Euclidean distances for the
    specification.] The answer: a tour of the point_count
    points, at most twice as long as any tour (hence as a
    shortest one). Any such tour. *)
Definition tsp_spec
  (x_coords y_coords : list R )
  (output : list N )
  : Prop :=
  is_tour (len x_coords) output /\
  forall other_tour, is_tour (len x_coords) other_tour ->
    (tour_length x_coords y_coords output <=
     2 * tour_length x_coords y_coords other_tour)%R.

(** ** Interface *)

(** Return a tour through all points whose length is at
    most twice the length of any tour, using exact
    Euclidean distances for the specification.
    - Input [x_coords]:
    - Input [y_coords]:
    - Output [output]: *)
Program tsp : array float -> array float -> array uint.

(** ** Bridge *)

(** [@requirement tsp_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying [tsp_spec]. *)
Specification tsp_correct :
  forall (x_coords y_coords : list R ) (x_coords_arr
    y_coords_arr : array float ),
    valid_input x_coords y_coords ->
    repr x_coords_arr x_coords -> repr y_coords_arr y_coords
      ->
    exists output : list N,
      repr (tsp x_coords_arr y_coords_arr) output /\
      tsp_spec x_coords y_coords output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
