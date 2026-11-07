(* @function        convex_hull
   @signature       array sint -> array sint -> array uint
   @math_signature  list Z -> list Z -> list N
   @summary         [convex_hull x_coordinates y_coordinates] returns the
                    indices, in counterclockwise order, of the vertices of
                    the convex hull of the points (x_coordinates[i],
                    y_coordinates[i]), no three consecutive vertices
                    collinear ; any cyclic shift, and any index among
                    duplicates of a vertex
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_Z (l : list Z) (k : N) : Z := nth (N.to_nat k) l 0.

Definition point : Type := Z * Z.

(* The i-th input point. *)
Definition get_point (x_coordinates y_coordinates : list Z) (i : N) : point :=
  (get_list_Z x_coordinates i, get_list_Z y_coordinates i).

(* The k-th vertex of the polygon, for k < len polygon ((0, 0) outside,
   never relied on). *)
Definition get_pt (polygon : list point) (k : N) : point :=
  nth (N.to_nat k) polygon (0, 0).

(* The position after k around the polygon. *)
Definition next (polygon : list point) (k : N) : N :=
  ((k + 1) mod len polygon)%N.

(* Twice the signed area of the triangle origin target probe : positive
   when probe is to the left of the directed line from origin to target,
   zero when the three points are collinear. *)
Definition cross (origin target probe : point) : Z :=
  (fst target - fst origin) * (snd probe - snd origin) -
  (snd target - snd origin) * (fst probe - fst origin).

(* probe lies on the segment from origin to target. *)
Definition on_segment (origin target probe : point) : Prop :=
  cross origin target probe = 0 /\
  Z.min (fst origin) (fst target) <= fst probe
    <= Z.max (fst origin) (fst target) /\
  Z.min (snd origin) (snd target) <= snd probe
    <= Z.max (snd origin) (snd target).

(* Every listed index is the index of an input point. *)
Definition indices_valid (x_coordinates : list Z) (hull_indices : list N)
  : Prop :=
  Forall (fun i => (i < len x_coordinates)%N) hull_indices.

(* The vertices named by hull_indices, as points. *)
Definition vertices (x_coordinates y_coordinates : list Z)
    (hull_indices : list N) : list point :=
  map (get_point x_coordinates y_coordinates) hull_indices.

(* Every turn of the polygon is strictly to the left : counterclockwise,
   and no three consecutive vertices collinear. *)
Definition strictly_convex_ccw (polygon : list point) : Prop :=
  forall k, (k < len polygon)%N ->
    0 < cross (get_pt polygon k) (get_pt polygon (next polygon k))
              (get_pt polygon (next polygon (next polygon k))).

(* Every input point is on or to the left of every directed edge of the
   polygon. *)
Definition left_of_edges (x_coordinates y_coordinates : list Z)
    (polygon : list point) : Prop :=
  forall k i, (k < len polygon)%N -> (i < len x_coordinates)%N ->
    0 <= cross (get_pt polygon k) (get_pt polygon (next polygon k))
               (get_point x_coordinates y_coordinates i).

(* The polygon encloses the input points : all equal to its single
   vertex, all on the segment between its two vertices, or all on or to
   the left of each of its edges. *)
Definition encloses (x_coordinates y_coordinates : list Z)
    (polygon : list point) : Prop :=
  match polygon with
  | [vertex] => forall i, (i < len x_coordinates)%N ->
      get_point x_coordinates y_coordinates i = vertex
  | [vertex; vertex'] => forall i, (i < len x_coordinates)%N ->
      on_segment vertex vertex' (get_point x_coordinates y_coordinates i)
  | _ => left_of_edges x_coordinates y_coordinates polygon
  end.

(* The statement's bounds, for one test case. *)
Record valid_input (x_coordinates y_coordinates : list Z) : Prop := {
  (* 1 <= n <= 10000 *)
  vi_n : (1 <= len x_coordinates <= 10000)%N;
  (* one y per x *)
  vi_ys_length : len y_coordinates = len x_coordinates;
  (* coordinates are integers with absolute value bounded by 10000 *)
  vi_xs : Forall (fun x_coordinate => - 10000 <= x_coordinate <= 10000)
            x_coordinates;
  vi_ys : Forall (fun y_coordinate => - 10000 <= y_coordinate <= 10000)
            y_coordinates;
}.

(* The answer : a non-empty polygon of distinct input points, strictly
   convex and counterclockwise when it has three vertices or more, that
   encloses every input point. *)
Definition convex_hull_spec (x_coordinates y_coordinates : list Z)
    (output : list N) : Prop :=
  let polygon := vertices x_coordinates y_coordinates output in
  (1 <= len output)%N /\
  indices_valid x_coordinates output /\
  NoDup polygon /\
  ((3 <= len polygon)%N -> strictly_convex_ccw polygon) /\
  encloses x_coordinates y_coordinates polygon.

(* machine side : the only thing that gets extracted *)
Program convex_hull : array sint -> array sint -> array uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification convex_hull_correct :
  forall (x_coordinates y_coordinates : list Z)
         (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  exists output : list N,
    repr (convex_hull x_coordinates_arr y_coordinates_arr) output /\
    convex_hull_spec x_coordinates y_coordinates output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
