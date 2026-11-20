(** * Polygon Area *)

(** ** Description *)

(** Compute twice a polygon's signed area: positive for counterclockwise
    vertex order and negative for clockwise order.

    [@kattis polygonarea]
    - Difficulty: 1.8
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $3 \le n \le 10^{3}$.
    - Integer coordinates with absolute value at most $10^{4}$. *)

(** ** Examples *)

(** - Input convention: Per case: vertex count and polygon coordinates in boundary order; a zero count ends input.
    - Output convention: CW or CCW followed by the unsigned area with one decimal place. *)
(* Input:
3
0 0
10 0
0 10
5
41 -6
-24 -74
-51 -6
73 17
-30 -34
0
Output:
CCW 50.0
CW 3817.5
*)

(** ** [@hide] Environment *)
(* @function        signed_area2
   @signature       array sint -> array sint -> sint
   @math_signature  list Z -> list Z -> Z
   @summary         [signed_area2 x_coordinates y_coordinates] returns twice
                    the signed area of the polygon whose vertices are
                    (x_coordinates[i], y_coordinates[i]) in order :
                    positive when they are given counterclockwise, negative
                    when clockwise.  The harness prints the direction from
                    the sign and the area, half the absolute value, with
                    one decimal
                    It runs in at most c1 * (|x| + |y| + 1) + c2 steps of
                    the cost model (one pass over the vertices), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_Z (l : list Z) (k : N) : Z :=
  nth (N.to_nat k) l 0.

(** The vertex index following [i], wrapping from the last vertex to zero. *)
Definition next (vertex_count i : N) : N :=
  ((i + 1) mod vertex_count)%N.

(** The sum of [term] over zero-based indices below [count]. *)
Fixpoint sum_below (term : N -> Z) (count : nat) : Z :=
  match count with
  | O => 0
  | S below => sum_below term below + term (N.of_nat below)
  end.

(** Twice the signed polygon area, computed by the shoelace formula. The sign is
    positive for counterclockwise vertex order. *)
Definition shoelace
  (x_coordinates y_coordinates : list Z) : Z :=
  let vertex_count := len x_coordinates in
  sum_below
    (fun i => get_list_Z x_coordinates i
                * get_list_Z y_coordinates (next
                  vertex_count i)
              - get_list_Z x_coordinates (next vertex_count
                i)
                * get_list_Z y_coordinates i)
    (N.to_nat vertex_count).

(** [@inside signed_area2_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (x_coordinates y_coordinates : list Z) : Prop := {
  (* 3 <= n <= 10^3 *)
  vi_n : (3 <= len x_coordinates <= 1000)%N;
  (* one y per x *)
  vi_ys_length : len y_coordinates = len x_coordinates;
  (* coordinates are integers with absolute value bounded
     by 10^4 *)
  vi_xs : Forall (fun coordinate => - 10000 <= coordinate <=
    10000)
            x_coordinates;
  vi_ys : Forall (fun coordinate => - 10000 <= coordinate <=
    10000)
            y_coordinates;
}.

(** ** Correctness *)

(** [@requirement]
    The output is twice the polygon's signed area, positive for counterclockwise order
    and negative for clockwise order. *)
Definition signed_area2_spec
  (x_coordinates y_coordinates : list Z)
    (output : Z) : Prop :=
  output = shoelace x_coordinates y_coordinates.

(** ** Complexity *)

(** [@requirement] Runs in $O(n_x+n_y+1)$ steps, where $n_x$ and $n_y$ are the lengths of the two coordinate arrays. *)
Definition signed_area2_time_spec (c1 c2 n_x_coordinates n_y_coordinates steps : nat) : Prop :=
  (steps <= c1 * (n_x_coordinates + n_y_coordinates + 1) + c2)%nat.

(** ** Interface *)

(** Compute twice a polygon's signed area: positive for counterclockwise vertex order and
    negative for clockwise order.
    - Input [x_coordinates]: Horizontal coordinates of polygon vertices in boundary order.
    - Input [y_coordinates]: Vertical coordinates of the corresponding polygon vertices.
    - Output [output]: The output is twice the polygon's signed area, positive for counterclockwise order and negative for clockwise order. *)
Program signed_area2 : array sint -> array sint -> sint.

(** [@example signed_area2]
    - Sample: 1
    - Case: 1
    - Input [x_coordinates]: [0; 10; 0]%Z
    - Input [y_coordinates]: [0; 0; 10]%Z
    - Output [output]: 100%Z
*)

(** [@example signed_area2]
    - Sample: 1
    - Case: 2
    - Input [x_coordinates]: [41; -24; -51; 73; -30]%Z
    - Input [y_coordinates]: [-6; -74; -6; 17; -34]%Z
    - Output [output]: (-7635)%Z
*)

(** ** Bridge *)

(** [@requirement signed_area2_spec] [@fold full correctness statement]
    On valid represented inputs, [signed_area2] returns a
    represented output satisfying [signed_area2_spec]. *)
Specification signed_area2_correct :
  forall (x_coordinates y_coordinates : list Z)
         (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  exists output : Z,
    repr (signed_area2 x_coordinates_arr y_coordinates_arr)
      output /\
    signed_area2_spec x_coordinates y_coordinates output.

(** ** Complexity *)

(** [@hide] [signed_area2_cost] is the cost translation of [signed_area2] (the judge
    recomputes it and compares) ... *)
Complexity signed_area2_cost for signed_area2.

(** [@fold complexity bound] ... and runs in at most c1 * (|x| + |y| + 1) + c2 steps of the cost model (one pass over the vertices), for two constants
    quantified before the inputs, on every valid input (the accepted
    program computes [length x - 1], which wraps on an empty array;
    [valid_input] has at least three vertices). [@requirement signed_area2_time_spec] *)
Specification signed_area2_time : exists c1 c2 : nat,
  forall (x_coordinates y_coordinates : list Z)
         (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  signed_area2_time_spec c1 c2 (size x_coordinates_arr) (size y_coordinates_arr) (cost2 signed_area2_cost x_coordinates_arr y_coordinates_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
