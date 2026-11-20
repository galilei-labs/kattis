(** * Closest Pair (Uniform) *)

(** ** Description *)

(** Find two distinct points with minimum Euclidean distance, comparing the
    exact real values represented by their floating-point coordinates.

    [@kattis closestpair1]
    - Difficulty: 3.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Point count: $2 \le n \le 10^{5}$.
    - Each coordinate has absolute value at most $10^{5}$. *)

(** ** Examples *)

(** - Input convention: Per case: point count and coordinate pairs; a zero count ends input.
    - Output convention: Four coordinates x1 y1 x2 y2 describing any closest pair, one line per case. *)
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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* The points are two parallel lists, one per
  column of the
   input lines "x y"; a coordinate is the real its float
     denotes. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_R (l : list R) (k : N) : R :=
  nth (N.to_nat k) l 0%R.

(** [i] and [j] are distinct valid input indices. Their coordinates may coincide,
    giving distance zero. *)
Definition point_pair (x_coordinates : list R)
  (i j : N) : Prop :=
  i < len x_coordinates /\ j < len x_coordinates /\ i <> j.

(** The squared Euclidean distance between the points at indices [i] and [j]. *)
Definition dist2 (x_coordinates y_coordinates : list R)
  (i j : N) : R :=
  let delta_x :=
    (get_list_R x_coordinates i - get_list_R x_coordinates
      j)%R in
  let delta_y :=
    (get_list_R y_coordinates i - get_list_R y_coordinates
      j)%R in
  (delta_x * delta_x + delta_y * delta_y)%R.

(** [@inside closestpair_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (x_coordinates y_coordinates : list R) : Prop := {
  (* 2 <= n <= 10^5 *)
  vi_n : 2 <= len x_coordinates <= 100000;
  (* n points, each of the form x y *)
  vi_ys : len y_coordinates = len x_coordinates;
  (* coordinates ... absolute value bounded by 10^5 *)
  vi_x : Forall (fun coordinate =>
    (Rabs coordinate <= 100000)%R)
           x_coordinates;
  vi_y : Forall (fun coordinate =>
    (Rabs coordinate <= 100000)%R)
           y_coordinates;
}.

(** ** Correctness *)

(** [@requirement]
    The output identifies two distinct input positions attaining the minimum Euclidean
    distance, evaluated on the exact real values of the coordinates. *)
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

(** Find two distinct points with minimum Euclidean distance, comparing the exact real
    values represented by their floating-point coordinates.
    - Input [x_coordinates]: Horizontal coordinates of the input points.
    - Input [y_coordinates]: Vertical coordinates of the corresponding points.
    - Output [output]: The output identifies two distinct input positions attaining the minimum Euclidean distance, evaluated on the exact real values of the coordinates. *)
Program closestpair : array float -> array float
  -> uint * uint.

(** [@example closestpair]
    - Sample: 1
    - Case: 1
    - Input [x_coordinates]: [fval 1.12%float; 0]%R
    - Input [y_coordinates]: [0; fval 0.51%float]%R
    - Output [output]: (1, 0)
*)

(** [@example closestpair]
    - Sample: 1
    - Case: 2
    - Input [x_coordinates]: [158; 123; 1859]%R
    - Input [y_coordinates]: [12; 15; -1489]%R
    - Output [output]: (1, 0)
*)

(** [@example closestpair]
    - Sample: 1
    - Case: 3
    - Input [x_coordinates]: [fval 21.12%float; fval 18.18%float; fval 21.12%float]
    - Input [y_coordinates]: [fval (-884.2)%float; fval 43.34%float; fval (-884.2)%float]
    - Output [output]: (0, 2)
*)

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
    rest on: the specification is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
