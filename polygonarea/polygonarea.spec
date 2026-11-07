(** * Polygon Area *)

(** ** Description *)

(** [signed_area2 x_coordinates y_coordinates] returns twice the signed
    area of the polygon whose vertices are (x_coordinates[i],
    y_coordinates[i]) in order : positive when they are given
    counterclockwise, negative when clockwise. The harness prints
    the direction from the sign and the area, half the absolute
    value, with one decimal. *)

(** [@kattis polygonarea]
    - Difficulty: 1.8
    - CPU time limit: 1 second
    - Memory limit: 1024 MB *)

(** ** Examples *)

(** Kattis sample: text input and output. *)
(* 3
0 0
10 0
0 10
5
41 -6
-24 -74
-51 -6
73 17
-30 -34
0 = CCW 50.0
CW 3817.5 *)

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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** Math side The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_Z (l : list Z) (k : N) : Z :=
  nth (N.to_nat k) l 0.

(** The vertex after i, the last one being followed by the first. *)
Definition next (vertex_count i : N) : N :=
  ((i + 1) mod vertex_count)%N.

(** term 0 + term 1 + ... + term (count - 1). *)
Fixpoint sum_below (term : N -> Z) (count : nat) : Z :=
  match count with
  | O => 0
  | S below => sum_below term below + term (N.of_nat below)
  end.

(** The shoelace sum, twice the signed area : the sum over the vertices
    of x_i * y_(i+1) - x_(i+1) * y_i. *)
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

(** [@inside signed_area2_correct] The statement's bounds, for one test
    case. The statement also says the vertices are those of a simple
    polygon ; the shoelace sum does not need it, so it is not
    stated. *)
Record valid_input
  (x_coordinates y_coordinates : list Z) : Prop := {
  (* 3 <= n <= 1000 *)
  vi_n : (3 <= len x_coordinates <= 1000)%N;
  (* one y per x *)
  vi_ys_length : len y_coordinates = len x_coordinates;
  (* coordinates are integers with absolute value bounded
     by 10000 *)
  vi_xs : Forall (fun coordinate => - 10000 <= coordinate <=
    10000)
            x_coordinates;
  vi_ys : Forall (fun coordinate => - 10000 <= coordinate <=
    10000)
            y_coordinates;
}.

(** ** Correctness *)

(** [@requirement] [@short The answer : the shoelace sum.] The answer :
    the shoelace sum. *)
Definition signed_area2_spec
  (x_coordinates y_coordinates : list Z)
    (output : Z) : Prop :=
  output = shoelace x_coordinates y_coordinates.

(** ** Interface *)

(** The [signed_area2] program on machine values.
    - Input [x_coordinates]:
    - Input [y_coordinates]:
    - Output [output]: *)
Program signed_area2 : array sint -> array sint -> sint.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
