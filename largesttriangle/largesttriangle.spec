(** * Largest Triangle *)

(** ** Description *)

(** Find the maximum area of a triangle formed by three input points,
    returning zero if all such triangles are degenerate.

    [@kattis largesttriangle]
    - Difficulty: 6.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 3 to 5,000 points.
    - Integer coordinates from 0 to 40,000,000. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
7
0 0
0 5
7 7
0 10
0 0
20 0
10 10
Output:
100.00000
*)

(** ** [@hide] Environment *)
(* @function        largest_triangle
   @signature       array uint -> array uint -> float
   @math_signature  list N -> list N -> R
   @summary         [largest_triangle x_coordinates y_coordinates] takes the
                    N points (x_coordinates_k, y_coordinates_k) and returns
                    the largest area of a triangle whose three corners are
                    three of the N points (three distinct indices;
                    coincident or collinear corners give area 0, so the
                    answer is 0 when no proper triangle exists), as a
                    finite float within 10^-5 of that area.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The points are two parallel lists, one per column of the
    input lines "x y". The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th coordinate, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** Three of the N points: three distinct indices; two indices may hold
    the same point ("the points are not necessarily distinct"). *)
Definition is_triple (x_coordinates : list N)
  (i j k : N) : Prop :=
  i < len x_coordinates /\ j < len x_coordinates /\ k < len
    x_coordinates /\
  i <> j /\ j <> k /\ i <> k.

(** The area of the triangle with corners the points i, j, k: half the
    absolute value of the cross product (P_j - P_i) x (P_k - P_i). *)
Definition area (x_coordinates y_coordinates : list N)
  (i j k : N) : R :=
  let x_of index :=
    Z.of_N (get_list_N x_coordinates index) in
  let y_of index :=
    Z.of_N (get_list_N y_coordinates index) in
  (Rabs (IZR ((x_of j - x_of i) * (y_of k - y_of i)
              - (x_of k - x_of i) * (y_of j - y_of i))) /
                2)%R.

(** largest_area is the largest area over all triples of points:
    attained by one, at least that of every one. *)
Definition is_largest_area
  (x_coordinates y_coordinates : list N)
    (largest_area : R) : Prop :=
  (exists i j k, is_triple x_coordinates i j k /\
     area x_coordinates y_coordinates i j k = largest_area)
       /\
  (forall i j k, is_triple x_coordinates i j k ->
     (area x_coordinates y_coordinates i j k <=
       largest_area)%R).

(** [@inside largest_triangle_correct] The statement's bounds. *)
Record valid_input
  (x_coordinates y_coordinates : list N) : Prop := {
  (* 3 <= N <= 5 000 *)
  vi_n : 3 <= len x_coordinates <= 5000;
  (* each of the next N lines contains two integers x and
     y *)
  vi_ys : len y_coordinates = len x_coordinates;
  (* 0 <= x, y <= 4 * 10^7 *)
  vi_x : Forall (fun coordinate => coordinate <= 4 * 10 ^ 7)
    x_coordinates;
  vi_y : Forall (fun coordinate => coordinate <= 4 * 10 ^ 7)
    y_coordinates;
}.

(** ** Correctness *)

(** [@requirement] [@short The answer output: within an absolute error
    of at most 10^-5 of    the largest area.] The answer output:
    within an absolute error of at most 10^-5 of the largest area. *)
Definition largest_triangle_spec
  (x_coordinates y_coordinates : list N)
    (output : R) : Prop :=
  exists largest_area,
    is_largest_area x_coordinates y_coordinates largest_area
      /\
    (Rabs (output - largest_area) <= / 100000)%R.

(** ** Interface *)

(** The [largest_triangle] program on machine values.
    - Input [x_coordinates]:
    - Input [y_coordinates]:
    - Output [output]: *)
Program largest_triangle : array uint -> array uint ->
  float.

(** ** Bridge *)

(** [@requirement largest_triangle_spec] [@fold full correctness
    statement] On valid represented inputs, [largest_triangle]
    returns a represented output satisfying [largest_triangle_spec]. *)
Specification largest_triangle_correct :
  forall (x_coordinates y_coordinates : list N)
         (x_coordinates_arr y_coordinates_arr : array uint),
    valid_input x_coordinates y_coordinates ->
    repr x_coordinates_arr x_coordinates ->
    repr y_coordinates_arr y_coordinates ->
    exists output : R,
      repr (largest_triangle x_coordinates_arr
        y_coordinates_arr)
        output /\
      largest_triangle_spec x_coordinates y_coordinates
        output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
