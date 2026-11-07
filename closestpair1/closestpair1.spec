(** * Closest Pair (Uniform) *)

(** ** Description *)

(** Find two distinct points with minimum Euclidean distance, comparing the
    exact real values represented by their floating-point coordinates.

    [@kattis closestpair1]
    - Difficulty: 3.4

    **Kattis Bounds**
    - 2 to 100,000 points.
    - Each coordinate has absolute value at most 100,000. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
2
1.12 0
0 0.51
3
158 12
123 15
1859 -1489
3
21.12 -884.2
18.18 43.34
21.12 -884.2
0
Output:
0.0 0.51 1.12 0.00
123 15 158 12.00
21.12 -884.20 21.12 -884.20
*)

(** ** [@hide] Environment *)

(* @function        closestpair
   @signature       array float -> array float -> uint * uint
   @math_signature  list R -> list R -> N * N
   @summary         One test case: [closestpair x_coordinates y_coordinates]
                    takes the n >= 2 points (x_coordinates_k, y_coordinates_k)
                    of the case and returns the indices i, j of two distinct
                    points that no pair of distinct points is strictly closer
                    than, exactly over the reals the floats denote; any such
                    pair, in either order. The harness prints
                    x_coordinates_i y_coordinates_i x_coordinates_j
                    y_coordinates_j.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The points are two parallel lists, one per
  column of the
   input lines "x y"; a coordinate is the real its float
     denotes. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th coordinate, for k < len l (0 outside, never
    relied on). *)
Definition get_list_R (l : list R) (k : N) : R :=
  nth (N.to_nat k) l 0%R.

(** i and j are two distinct points of the input:
    distinct indices; two indices may hold the same
    point, at distance 0 (third sample case). *)
Definition point_pair (x_coordinates : list R)
  (i j : N) : Prop :=
  i < len x_coordinates /\ j < len x_coordinates /\ i <> j.

(** The squared Euclidean distance between points i and
    j. *)
Definition dist2 (x_coordinates y_coordinates : list R)
  (i j : N) : R :=
  let delta_x :=
    (get_list_R x_coordinates i - get_list_R x_coordinates
      j)%R in
  let delta_y :=
    (get_list_R y_coordinates i - get_list_R y_coordinates
      j)%R in
  (delta_x * delta_x + delta_y * delta_y)%R.

(** [@inside closestpair_correct] The statement's bounds
    on one test case. "At most 2 decimals" is a property
    of the input text, gone once parsed: the contract is
    exact on the reals the parsed floats denote.
    "Generated uniformly at random" is a distribution,
    not a property of one input: the contract holds on
    every input below. *)
Record valid_input
  (x_coordinates y_coordinates : list R) : Prop := {
  (* 2 <= n <= 100 000 *)
  vi_n : 2 <= len x_coordinates <= 100000;
  (* n points, each of the form x y *)
  vi_ys : len y_coordinates = len x_coordinates;
  (* coordinates ... absolute value bounded by 100 000 *)
  vi_x : Forall (fun coordinate =>
    (Rabs coordinate <= 100000)%R)
           x_coordinates;
  vi_y : Forall (fun coordinate =>
    (Rabs coordinate <= 100000)%R)
           y_coordinates;
}.

(** ** Correctness *)

(** [@requirement] [@short must return a pair of points
    at minimum distance.] The answer: two distinct
    points that no pair of distinct points is strictly
    closer than, exactly. *)
Definition closestpair_spec
  (x_coordinates y_coordinates : list R)
  (output : N * N) : Prop :=
  match output with
  | (first, second) =>
      point_pair x_coordinates first second /\
      forall i j, point_pair x_coordinates i j ->
        (dist2 x_coordinates y_coordinates first second
         <= dist2 x_coordinates y_coordinates i j)%R
  end.

(** ** Interface *)

(** The machine-level interface.
    - Input [x_coordinates]:
    - Input [y_coordinates]:
    - Output [output]: *)
Program closestpair : array float -> array float
  -> uint * uint.

(** ** Bridge *)

(** [@requirement closestpair_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [closestpair_spec]. *)
Specification closestpair_correct :
  forall (x_coordinates y_coordinates : list R)
         (x_coordinates_arr y_coordinates_arr : array
           float),
    valid_input x_coordinates y_coordinates ->
    repr x_coordinates_arr x_coordinates ->
    repr y_coordinates_arr y_coordinates ->
    exists output : N * N,
      repr (closestpair x_coordinates_arr y_coordinates_arr)
        output /\
      closestpair_spec x_coordinates y_coordinates output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals
    rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
