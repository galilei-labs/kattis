(** * Line Segment Intersection *)

(** ** Description *)

(** Compute the exact intersection of two closed line
    segments: no intersection, one rational point, or a
    shared segment.

    [@kattis segmentintersection]
    - Difficulty: 4.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB *)

(** ** [@hide] Environment *)

(* @function        intersect
   @signature       sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint
                    -> inter sint
   @math_signature  Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> inter Z
   @summary         [intersect x1 y1 x2 y2 x3 y3 x4 y4] computes, exactly, the
                    intersection of the closed segment (x1,y1)-(x2,y2) with the
                    closed segment (x3,y3)-(x4,y4) (either may be a single
                    point): [Empty], a single point [Point x y denominator]
                    standing for (x/denominator, y/denominator) with
                    denominator > 0, or a segment [Segment start_x start_y
                    end_x end_y] from (start_x,start_y) to (end_x,end_y), its
                    endpoints distinct, the one with the smaller x first (the
                    smaller y on a tie).
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The answer, on both sides (A = sint, A = Z). The
    answer is exact: a point is a rational
    (x/denominator, y/denominator), not a decimal; the
    rounding to 2 decimals is the printer's. *)
Inductive inter (A : Type) : Type :=
| Empty
| Point (x y denominator : A)
| Segment (start_x start_y end_x end_y : A).
Arguments Empty {A}.
Arguments Point {A} x y denominator.
Arguments Segment {A} start_x start_y end_x end_y.

Instance repr_inter A M `{Repr A M} : Repr (inter A)
  (inter M) :=
  fun machine math => match machine, math with
    | Empty, Empty => True
    | Point x y denominator, Point x' y' denominator' =>
        repr x x' /\ repr y y' /\ repr denominator
          denominator'
    | Segment start_x start_y end_x end_y,
      Segment start_x' start_y' end_x' end_y' =>
        repr start_x start_x' /\ repr start_y start_y' /\
        repr end_x end_x' /\ repr end_y end_y'
    | _, _ => False
    end.

(* Math side. *)

(** The rational point (point_x/denominator,
    point_y/denominator), denominator > 0, lies on the
    closed segment from (start_x,start_y) to
    (end_x,end_y): collinear with both ends and inside
    their box. *)
Definition on_seg (start_x start_y end_x end_y point_x
  point_y denominator : Z)
    : Prop :=
  (end_x - start_x) * (point_y - start_y * denominator) =
    (end_y - start_y) * (point_x - start_x * denominator) /\
  Z.min start_x end_x * denominator <= point_x
    <= Z.max start_x end_x * denominator /\
  Z.min start_y end_y * denominator <= point_y
    <= Z.max start_y end_y * denominator.

(** The rational point (point_x/denominator,
    point_y/denominator), denominator > 0, belongs to the
    answer. *)
Definition denotes (answer : inter Z)
  (point_x point_y denominator : Z)
    : Prop :=
  match answer with
  | Empty => False
  | Point other_x other_y other_denominator =>
      point_x * other_denominator = other_x * denominator /\
      point_y * other_denominator = other_y * denominator
  | Segment start_x start_y end_x end_y =>
      on_seg start_x start_y end_x end_y point_x point_y
        denominator
  end.

(** The well-formedness of an answer: a point has a
    positive denominator, a segment has distinct
    endpoints, the smaller x first, or the smaller y
    first when the x are equal. *)
Definition well_formed (answer : inter Z) : Prop :=
  match answer with
  | Empty => True
  | Point _ _ denominator => 0 < denominator
  | Segment start_x start_y end_x end_y =>
      start_x < end_x \/
        (start_x = end_x /\ start_y < end_y)
  end.

(** [@inside intersect_correct] The statement's bounds,
    for one test case. *)
Record valid_input (x1 y1 x2 y2 x3 y3 x4 y4 : Z) : Prop := {
  (* Coordinates have absolute value at most 10000. *)
  vi_coords : Forall
    (fun coordinate => Z.abs coordinate <= 10000)
                [x1; y1; x2; y2; x3; y3; x4; y4];
}.

(** ** Correctness *)

(** [@requirement] [@short Compute the exact intersection
    of two closed line segments: no intersection, one
    rational point, or a shared segment.] The answer is
    well formed, and its points are exactly the
    (rational) points on both segments. *)
Definition intersect_spec
  (x1 y1 x2 y2 x3 y3 x4 y4 : Z)
  (output : inter Z)
  : Prop :=
  well_formed output /\
  forall point_x point_y denominator, 0 < denominator ->
    (denotes output point_x point_y denominator <->
     on_seg x1 y1 x2 y2 point_x point_y denominator /\
     on_seg x3 y3 x4 y4 point_x point_y denominator).

(** ** Interface *)

(** Compute the exact intersection of two closed line
    segments: no intersection, one rational point, or a
    shared segment.
    - Input [x1]:
    - Input [y1]:
    - Input [x2]:
    - Input [y2]:
    - Input [x3]:
    - Input [y3]:
    - Input [x4]:
    - Input [y4]:
    - Output [output]: *)
Program intersect :
  sint -> sint -> sint -> sint -> sint -> sint -> sint ->
    sint -> inter sint.

(** ** Bridge *)

(** [@requirement intersect_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [intersect_spec]. *)
Specification intersect_correct :
  forall (x1 y1 x2 y2 x3 y3 x4 y4 : Z)
         (x1_int y1_int x2_int y2_int x3_int y3_int x4_int
           y4_int : sint),
  valid_input x1 y1 x2 y2 x3 y3 x4 y4 ->
  repr x1_int x1 -> repr y1_int y1 -> repr x2_int x2 -> repr
    y2_int y2 ->
  repr x3_int x3 -> repr y3_int y3 -> repr x4_int x4 -> repr
    y4_int y4 ->
  exists output : inter Z,
    repr (intersect x1_int y1_int x2_int y2_int x3_int
      y3_int x4_int y4_int)
      output /\
    intersect_spec x1 y1 x2 y2 x3 y3 x4 y4 output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
