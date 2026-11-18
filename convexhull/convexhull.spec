(** * Convex Hull *)

(** ** Description *)

(** Return the vertices of a point set's convex hull in counterclockwise
    order, omitting collinear intermediate vertices.

    [@kattis convexhull]
    - Difficulty: 2.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Point count: $1 \le n \le 10^{4}$.
    - Integer coordinates with absolute value at most $10^{4}$. *)

(** ** Examples *)

(** - Input convention: Per case: point count and integer coordinate pairs; a zero count ends input.
    - Output convention: Hull vertex count followed by counterclockwise coordinates, excluding collinear intermediate vertices. *)
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
2
50 50
50 50
0
Output:
3
0 0
10 0
0 10
3
-24 -74
73 17
-51 -6
1
50 50
*)

(** ** [@hide] Environment *)

(* @function        convex_hull
   @signature       array sint -> array sint -> array uint
   @math_signature  list Z -> list Z -> list N
   @summary         [convex_hull x_coordinates y_coordinates] returns the
                    indices, in counterclockwise order, of the vertices of
                    the convex hull of the points (x_coordinates[i],
                    y_coordinates[i]), no three consecutive vertices
                    collinear ; any cyclic shift, and any index among
                    duplicates of a vertex
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of points (the sort; the two chain scans are linear,
                    every index pushed once and popped at most once), for
                    two constants c1, c2.
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

(** A point in the plane. *)
Definition point : Type := Z * Z.

(** The input point at zero-based index [i], using corresponding entries of the
    coordinate lists. *)
Definition get_point (x_coordinates y_coordinates : list Z)
  (i : N) : point :=
  (get_list_Z x_coordinates i, get_list_Z y_coordinates i).

(** The vertex at zero-based index [k] in [polygon], or [(0, 0)] beyond the end. *)
Definition get_pt (polygon : list point) (k : N) : point :=
  nth (N.to_nat k) polygon (0, 0).

(** The index following [k] in [polygon], wrapping from the last vertex to the
    first. *)
Definition next (polygon : list point) (k : N) : N :=
  ((k + 1) mod len polygon)%N.

(** Twice the signed area of the triangle with vertices [origin], [target], and
    [probe]. The value is positive when [probe] lies to the left of the directed
    line from [origin] to [target], and zero when the points are collinear. *)
Definition cross (origin target probe : point) : Z :=
  (fst target - fst origin) * (snd probe - snd origin) -
  (snd target - snd origin) * (fst probe - fst origin).

(** [probe] lies on the closed segment from [origin] to [target]. *)
Definition on_segment
  (origin target probe : point) : Prop :=
  cross origin target probe = 0 /\
  Z.min (fst origin) (fst target) <= fst probe
    <= Z.max (fst origin) (fst target) /\
  Z.min (snd origin) (snd target) <= snd probe
    <= Z.max (snd origin) (snd target).

(** Every listed index is the index of an input point. *)
Definition indices_valid (x_coordinates : list Z)
  (hull_indices : list N)
  : Prop :=
  Forall (fun i => (i < len x_coordinates)%N) hull_indices.

(** The input points selected by [hull_indices], in the listed order. *)
Definition vertices (x_coordinates y_coordinates : list Z)
    (hull_indices : list N) : list point :=
  map (get_point x_coordinates y_coordinates) hull_indices.

(** Every consecutive triple of vertices makes a strict left turn, including triples
    that wrap around the polygon. *)
Definition strictly_convex_ccw
  (polygon : list point) : Prop :=
  forall k, (k < len polygon)%N ->
    0 < cross (get_pt polygon k) (get_pt polygon
      (next polygon k))
              (get_pt polygon (next polygon
                (next polygon k))).

(** Every input point is on or to the left of every
    directed edge of the polygon. *)
Definition left_of_edges
  (x_coordinates y_coordinates : list Z)
    (polygon : list point) : Prop :=
  forall k i, (k < len polygon)%N ->
    (i < len x_coordinates)%N ->
    0 <= cross (get_pt polygon k) (get_pt polygon
      (next polygon k))
               (get_point x_coordinates y_coordinates i).

(** All input points equal the sole vertex, lie on the segment between two vertices,
    or lie on or to the left of every directed polygon edge, according to the
    polygon size. *)
Definition encloses (x_coordinates y_coordinates : list Z)
    (polygon : list point) : Prop :=
  match polygon with
  | [vertex] => forall i, (i < len x_coordinates)%N ->
      get_point x_coordinates y_coordinates i = vertex
  | [vertex; vertex'] => forall i,
    (i < len x_coordinates)%N ->
      on_segment vertex vertex'
        (get_point x_coordinates y_coordinates i)
  | _ => left_of_edges x_coordinates y_coordinates polygon
  end.

(** [@inside convex_hull_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (x_coordinates y_coordinates : list Z) : Prop := {
  (* 1 <= n <= 10^4 *)
  vi_n : (1 <= len x_coordinates <= 10000)%N;
  (* one y per x *)
  vi_ys_length : len y_coordinates = len x_coordinates;
  (* coordinates are integers with absolute value bounded by
    10^4 *)
  vi_xs : Forall
    (fun x_coordinate => - 10000 <= x_coordinate <= 10000)
            x_coordinates;
  vi_ys : Forall
    (fun y_coordinate => - 10000 <= y_coordinate <= 10000)
            y_coordinates;
}.

(** ** Correctness *)

(** [@requirement]
    The output lists convex-hull vertices counterclockwise, without duplicate
    coordinates or intermediate collinear vertices, and encloses every input point. *)
Definition convex_hull_spec
  (x_coordinates y_coordinates : list Z)
    (output : list N) : Prop :=
  let polygon :=
    vertices x_coordinates y_coordinates output in
  (1 <= len output)%N /\
  indices_valid x_coordinates output /\
  NoDup polygon /\
  ((3 <= len polygon)%N -> strictly_convex_ccw polygon) /\
  encloses x_coordinates y_coordinates polygon.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of points. *)
Definition convex_hull_time_spec (c1 c2 n_x_coordinates steps : nat) : Prop :=
  (steps <= c1 * ((n_x_coordinates + 1) * (Nat.log2 (n_x_coordinates) + 1)) + c2)%nat.

(** ** Interface *)

(** Return the vertices of a point set's convex hull in counterclockwise order, omitting
    collinear intermediate vertices.
    - Input [x_coordinates]: Horizontal coordinates of the input points.
    - Input [y_coordinates]: Vertical coordinates of the corresponding points.
    - Output [output]: The output lists convex-hull vertices counterclockwise, without duplicate coordinates or intermediate collinear vertices, and encloses every input point. *)
Program convex_hull : array sint -> array sint
  -> array uint.

(** [@example convex_hull]
    - Sample: 1
    - Case: 1
    - Input [x_coordinates]: [0; 10; 0]%Z
    - Input [y_coordinates]: [0; 0; 10]%Z
    - Output [output]: [0; 1; 2]
*)

(** [@example convex_hull]
    - Sample: 1
    - Case: 2
    - Input [x_coordinates]: [41; -24; -51; 73; -30]%Z
    - Input [y_coordinates]: [-6; -74; -6; 17; -34]%Z
    - Output [output]: [1; 3; 2]
*)

(** [@example convex_hull]
    - Sample: 1
    - Case: 3
    - Input [x_coordinates]: [50; 50]%Z
    - Input [y_coordinates]: [50; 50]%Z
    - Output [output]: [0]
*)

(** ** Bridge *)

(** [@requirement convex_hull_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [convex_hull_spec]. *)
Specification convex_hull_correct :
  forall (x_coordinates y_coordinates : list Z)
         (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  exists output : list N,
    repr (convex_hull x_coordinates_arr y_coordinates_arr)
      output /\
    convex_hull_spec x_coordinates y_coordinates output.

(** ** Complexity *)

(** [@hide] [convex_hull_cost] is the cost translation of [convex_hull] (the judge
    recomputes it and compares) ... *)
Complexity convex_hull_cost for convex_hull.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of points (the sort; the two chain scans are linear, every index pushed once and popped at most once), for two constants
    quantified before the inputs, on every valid input. [@requirement convex_hull_time_spec] *)
Specification convex_hull_time : exists c1 c2 : nat,
  forall (x_coordinates y_coordinates : list Z)
  (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  convex_hull_time_spec c1 c2 (size x_coordinates_arr) (cost2 convex_hull_cost x_coordinates_arr y_coordinates_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
