(* @function        intersect
   @signature       sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint
                    -> inter sint
   @math_signature  Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> inter Z
   @summary         [intersect x1 y1 x2 y2 x3 y3 x4 y4] computes, exactly, the
                    intersection of the closed segment (x1,y1)-(x2,y2) with the
                    closed segment (x3,y3)-(x4,y4) (either may be a single
                    point): [Empty], a single point [Point px py d] standing
                    for (px/d, py/d) with d > 0, or a segment [Segment ax ay bx
                    by] from (ax,ay) to (bx,by), its endpoints distinct, the
                    one with the smaller x first (the smaller y on a tie).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* The answer, on both sides (A = sint, A = Z).  The answer is exact: a
   point is a rational (px/d, py/d), not a decimal; the rounding to 2
   decimals is the printer's. *)
Inductive inter (A : Type) : Type :=
| Empty
| Point (px py d : A)
| Segment (ax ay bx by_ : A).
Arguments Empty {A}.
Arguments Point {A} px py d.
Arguments Segment {A} ax ay bx by_.

Instance repr_inter A M `{Repr A M} : Repr (inter A) (inter M) :=
  fun x i => match x, i with
             | Empty, Empty => True
             | Point a b c, Point a' b' c' => repr a a' /\ repr b b' /\ repr c c'
             | Segment a b c e, Segment a' b' c' e' =>
                 repr a a' /\ repr b b' /\ repr c c' /\ repr e e'
             | _, _ => False
             end.

(* Math side. *)

(* The rational point (px/d, py/d), d > 0, lies on the closed segment from
   (ax,ay) to (bx,by): collinear with both ends and inside their box. *)
Definition on_seg (ax ay bx by_ px py d : Z) : Prop :=
  (bx - ax) * (py - ay * d) = (by_ - ay) * (px - ax * d) /\
  Z.min ax bx * d <= px <= Z.max ax bx * d /\
  Z.min ay by_ * d <= py <= Z.max ay by_ * d.

(* The rational point (px/d, py/d), d > 0, belongs to the answer r. *)
Definition denotes (r : inter Z) (px py d : Z) : Prop :=
  match r with
  | Empty => False
  | Point qx qy e => px * e = qx * d /\ py * e = qy * d
  | Segment ax ay bx by_ => on_seg ax ay bx by_ px py d
  end.

(* The well-formedness of an answer: a point has a positive denominator, a
   segment has distinct endpoints, the smaller x first, or the smaller y
   first when the x are equal. *)
Definition well_formed (r : inter Z) : Prop :=
  match r with
  | Empty => True
  | Point _ _ e => 0 < e
  | Segment ax ay bx by_ => ax < bx \/ (ax = bx /\ ay < by_)
  end.

(* The statement's bounds, for one test case. *)
Record valid_input (x1 y1 x2 y2 x3 y3 x4 y4 : Z) : Prop := {
  (* Coordinates have absolute value at most 10000. *)
  vi_coords : Forall (fun c => Z.abs c <= 10000) [x1; y1; x2; y2; x3; y3; x4; y4];
}.

(* The answer is well formed, and its points are exactly the (rational)
   points on both segments. *)
Definition intersect_spec (x1 y1 x2 y2 x3 y3 x4 y4 : Z) (r : inter Z) : Prop :=
  well_formed r /\
  forall px py d, 0 < d ->
    (denotes r px py d <->
     on_seg x1 y1 x2 y2 px py d /\ on_seg x3 y3 x4 y4 px py d).

Program intersect :
  sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> inter sint.

Specification intersect_correct :
  forall (x1 y1 x2 y2 x3 y3 x4 y4 : Z)
         (a1 b1 a2 b2 a3 b3 a4 b4 : sint),
  valid_input x1 y1 x2 y2 x3 y3 x4 y4 ->
  repr a1 x1 -> repr b1 y1 -> repr a2 x2 -> repr b2 y2 ->
  repr a3 x3 -> repr b3 y3 -> repr a4 x4 -> repr b4 y4 ->
  exists r : inter Z,
    repr (intersect a1 b1 a2 b2 a3 b3 a4 b4) r /\
    intersect_spec x1 y1 x2 y2 x3 y3 x4 y4 r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
