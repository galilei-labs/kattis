(** * Line Segment Intersection *)

(** ** Description *)

(** Compute the exact intersection of two closed line segments: no
    intersection, one rational point, or a shared segment.

    [@kattis segmentintersection]
    - Difficulty: 4.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Coordinate absolute values are at most $10^{4}$. *)

(** ** Examples *)

(** - Input convention: Case count, followed by eight endpoint coordinates per segment pair.
    - Output convention: none, one point or two segment endpoints, with coordinates to two decimal places. *)
(* Input:
5
-10 0 10 0 0 -10 0 10
-10 0 10 0 -5 0 5 0
1 1 1 1 1 1 2 1
1 1 1 1 2 1 2 1
1871 5789 216 -517 189 -518 3851 1895
Output:
0.00 0.00
-5.00 0.00 5.00 0.00
1.00 1.00
none
221.33 -496.70
*)

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
                    It runs in at most a constant number c of steps of the
                    cost model (straight-line code).
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** An exact intersection represented as empty, a rational point or a segment. Decimal rounding is performed only when printing. *)
Inductive inter (A : Type) : Type :=
| Empty
| Point (x y denominator : A)
| Segment (start_x start_y end_x end_y : A).

(** [@hide] Constructor argument declarations and the representation relation
    between machine and mathematical intersections. *)
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

(** [@hide] The cost translation of [inter], for the bound below. *)
Elpi complexity inter.

(* Math side. *)

(** For positive [denominator], the rational point with numerators [point_x] and
    [point_y] lies on the closed segment from [(start_x, start_y)] to
    [(end_x, end_y)]. Denominator positivity is a precondition, not part of this
    predicate. *)
Definition on_seg (start_x start_y end_x end_y point_x
  point_y denominator : Z)
    : Prop :=
  (end_x - start_x) * (point_y - start_y * denominator) =
    (end_y - start_y) * (point_x - start_x * denominator) /\
  Z.min start_x end_x * denominator <= point_x
    <= Z.max start_x end_x * denominator /\
  Z.min start_y end_y * denominator <= point_y
    <= Z.max start_y end_y * denominator.

(** For positive [denominator], the rational point with numerators [point_x] and
    [point_y] belongs to the represented intersection. *)
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

(** [@inside intersect_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (x1 y1 x2 y2 x3 y3 x4 y4 : Z) : Prop := {
  (* Coordinates have absolute value at most 10^4. *)
  vi_coords : Forall
    (fun coordinate => Z.abs coordinate <= 10000)
                [x1; y1; x2; y2; x3; y3; x4; y4];
}.

(** ** Correctness *)

(** [@requirement]
    The output is a well-formed exact representation of the shared points of the two
    closed segments: empty, a point or a segment. *)
Definition intersect_spec
  (x1 y1 x2 y2 x3 y3 x4 y4 : Z)
  (output : inter Z)
  : Prop :=
  well_formed output /\
  forall point_x point_y denominator, 0 < denominator ->
    (denotes output point_x point_y denominator <->
     on_seg x1 y1 x2 y2 point_x point_y denominator /\
     on_seg x3 y3 x4 y4 point_x point_y denominator).

(** ** Complexity *)

(** [@requirement] Runs in $O(1)$ steps, independently of the coordinate values. *)
Definition intersect_time_spec (c steps : nat) : Prop :=
  (steps <= c)%nat.

(** ** Interface *)

(** Compute the exact intersection of two closed line segments: no intersection, one
    rational point, or a shared segment.
    - Input [x1]: Horizontal coordinate of the first endpoint of the first segment.
    - Input [y1]: Vertical coordinate of the first endpoint of the first segment.
    - Input [x2]: Horizontal coordinate of the second endpoint of the first segment.
    - Input [y2]: Vertical coordinate of the second endpoint of the first segment.
    - Input [x3]: Horizontal coordinate of the first endpoint of the second segment.
    - Input [y3]: Vertical coordinate of the first endpoint of the second segment.
    - Input [x4]: Horizontal coordinate of the second endpoint of the second segment.
    - Input [y4]: Vertical coordinate of the second endpoint of the second segment.
    - Output [output]: The output is a well-formed exact representation of the shared points of the two closed segments: empty, a point or a segment. *)
Program intersect :
  sint -> sint -> sint -> sint -> sint -> sint -> sint ->
    sint -> inter sint.

(** [@example intersect]
    - Sample: 1
    - Case: 1
    - Input [x1]: (-10)%Z
    - Input [y1]: 0%Z
    - Input [x2]: 10%Z
    - Input [y2]: 0%Z
    - Input [x3]: 0%Z
    - Input [y3]: (-10)%Z
    - Input [x4]: 0%Z
    - Input [y4]: 10%Z
    - Output [output]: (Point 0 0 1)%Z
*)

(** [@example intersect]
    - Sample: 1
    - Case: 2
    - Input [x1]: (-10)%Z
    - Input [y1]: 0%Z
    - Input [x2]: 10%Z
    - Input [y2]: 0%Z
    - Input [x3]: (-5)%Z
    - Input [y3]: 0%Z
    - Input [x4]: 5%Z
    - Input [y4]: 0%Z
    - Output [output]: (Segment (-5) 0 5 0)%Z
*)

(** [@example intersect]
    - Sample: 1
    - Case: 3
    - Input [x1]: 1%Z
    - Input [y1]: 1%Z
    - Input [x2]: 1%Z
    - Input [y2]: 1%Z
    - Input [x3]: 1%Z
    - Input [y3]: 1%Z
    - Input [x4]: 2%Z
    - Input [y4]: 1%Z
    - Output [output]: (Point 1 1 1)%Z
*)

(** [@example intersect]
    - Sample: 1
    - Case: 4
    - Input [x1]: 1%Z
    - Input [y1]: 1%Z
    - Input [x2]: 1%Z
    - Input [y2]: 1%Z
    - Input [x3]: 2%Z
    - Input [y3]: 1%Z
    - Input [x4]: 2%Z
    - Input [y4]: 1%Z
    - Output [output]: Empty
*)

(** [@example intersect]
    - Sample: 1
    - Case: 5
    - Input [x1]: 1871%Z
    - Input [y1]: 5789%Z
    - Input [x2]: 216%Z
    - Input [y2]: (-517)%Z
    - Input [x3]: 189%Z
    - Input [y3]: (-518)%Z
    - Input [x4]: 3851%Z
    - Input [y4]: 1895%Z
    - Output [output]: (Point 4227160607 (-9486462835) 19099057)%Z
*)

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

(** ** Complexity *)

(** [@hide] [intersect_cost] is the cost translation of [intersect] (the judge
    recomputes it and compares) ... *)
Complexity intersect_cost for intersect.

(** [@fold complexity bound] ... and runs in at most a constant number c of steps of the cost model (straight-line code), for a constant
    quantified before the inputs. [@requirement intersect_time_spec] *)
Specification intersect_time : exists c : nat, forall x1_int y1_int x2_int y2_int x3_int y3_int x4_int y4_int : sint,
  intersect_time_spec c (cost8 intersect_cost x1_int y1_int x2_int y2_int x3_int y3_int x4_int y4_int).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
