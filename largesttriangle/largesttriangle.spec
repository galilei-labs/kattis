(** * Largest Triangle *)

(** ** Description *)

(** Find the maximum area of a triangle formed by three input points,
    returning zero if all such triangles are degenerate.

    [@kattis largesttriangle]
    - Difficulty: 6.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Point count: $3 \le n \le 5 \times 10^{3}$.
    - Integer coordinates: $0 \le x_i, y_i \le 4 \times 10^{7}$. *)

(** ** Examples *)

(** - Input convention: Point count, followed by integer coordinate pairs.
    - Output convention: Maximum triangle area, with absolute error at most $10^{-5}$. *)
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
                    It runs in at most c1 * (N + 1) * (N + log2 N + 1) + c2
                    steps of the cost model on a valid input, N the number
                    of points (the sort and the hull in N log N, then the
                    two-pointer sweep over the h hull vertices in h^2 <=
                    N^2), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** Three distinct valid input indices. The corresponding point coordinates need not
    be distinct. *)
Definition is_triple (x_coordinates : list N)
  (i j k : N) : Prop :=
  i < len x_coordinates /\ j < len x_coordinates /\ k < len
    x_coordinates /\
  i <> j /\ j <> k /\ i <> k.

(** The area of the triangle at indices [i], [j], and [k]: half the absolute cross
    product of its edge vectors. *)
Definition area (x_coordinates y_coordinates : list N)
  (i j k : N) : R :=
  let x_of index :=
    Z.of_N (get_list_N x_coordinates index) in
  let y_of index :=
    Z.of_N (get_list_N y_coordinates index) in
  (Rabs (IZR ((x_of j - x_of i) * (y_of k - y_of i)
              - (x_of k - x_of i) * (y_of j - y_of i))) /
                2)%R.

(** [largest_area] is attained by a triple of points and is at least the area
    of every other triple. *)
Definition is_largest_area
  (x_coordinates y_coordinates : list N)
    (largest_area : R) : Prop :=
  (exists i j k, is_triple x_coordinates i j k /\
     area x_coordinates y_coordinates i j k = largest_area)
       /\
  (forall i j k, is_triple x_coordinates i j k ->
     (area x_coordinates y_coordinates i j k <=
       largest_area)%R).

(** [@inside largest_triangle_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (x_coordinates y_coordinates : list N) : Prop := {
  (* 3 <= N <= 5 * 10^3 *)
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

(** [@requirement]
    The output approximates the maximum area of a triangle formed by input points, with
    absolute error at most $10^{-5}$. *)
Definition largest_triangle_spec
  (x_coordinates y_coordinates : list N)
    (output : R) : Prop :=
  exists largest_area,
    is_largest_area x_coordinates y_coordinates largest_area
      /\
    (Rabs (output - largest_area) <= / 100000)%R.

(** ** Complexity *)

(** [@requirement] Runs in $O(n^2)$ steps, where $n$ is the number of points. *)
Definition largest_triangle_time_spec (c1 c2 n_x_coordinates steps : nat) : Prop :=
  (steps <= c1 * ((n_x_coordinates + 1) * (n_x_coordinates + Nat.log2 (n_x_coordinates) + 1)) + c2)%nat.

(** ** Interface *)

(** Find the maximum area of a triangle formed by three input points, returning zero if all
    such triangles are degenerate.
    - Input [x_coordinates]: Horizontal coordinates of the input points.
    - Input [y_coordinates]: Vertical coordinates of the corresponding points.
    - Output [output]: The output approximates the maximum area of a triangle formed by input points, with absolute error at most $10^{-5}$. *)
Program largest_triangle : array uint -> array uint ->
  float.

(** [@example largest_triangle]
    - Sample: 1
    - Input [x_coordinates]: [0; 0; 7; 0; 0; 20; 10]
    - Input [y_coordinates]: [0; 5; 7; 10; 0; 0; 10]
    - Output [output]: 100%R
*)

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

(** ** Complexity *)

(** [@hide] [largest_triangle_cost] is the cost translation of [largest_triangle] (the judge
    recomputes it and compares) ... *)
Complexity largest_triangle_cost for largest_triangle.

(** [@fold complexity bound] ... and runs in at most c1 * (N + 1) * (N + log2 N + 1) + c2 steps of the cost model on a valid input, N the number of points (the sort and the hull in N log N, then the two-pointer sweep over the h hull vertices in h^2 <= N^2), for two constants
    quantified before the inputs, on every valid input. [@requirement largest_triangle_time_spec] *)
Specification largest_triangle_time : exists c1 c2 : nat,
  forall (x_coordinates y_coordinates : list N)
  (x_coordinates_arr y_coordinates_arr : array uint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  largest_triangle_time_spec c1 c2 (size x_coordinates_arr) (cost2 largest_triangle_cost x_coordinates_arr y_coordinates_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
