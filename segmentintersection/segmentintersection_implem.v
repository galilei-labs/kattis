(* Executable implementation and its required termination dependencies.
   Correctness proofs are in segmentintersection_proofs.v. *)
(* Implementation of segmentintersection (segmentintersection.spec):
   CLRS 33.1-style exact intersection of two closed segments A-B and C-D,
   straight-line code on 63-bit words read through Sint63, no Z, no float,
   no division, no loop.

   Code ([isect_m]).  r = B - A, s = D - C, q = C - A,
   den = cross(r,s), tn = cross(q,s), un = cross(q,r).
   - den <> 0 (lines cross): sign-normalise (den, tn, un) so den > 0; the
     answer is Point (x1*den + tn*rx) (y1*den + tn*ry) den when
     0 <= tn <= den and 0 <= un <= den, else Empty.
   - den = 0 and A = B: Point A if A lies on C-D, else Empty;
     den = 0 and C = D: Point C if C lies on A-B, else Empty.
   - den = 0, both proper, un <> 0 (parallel distinct lines): Empty.
   - den = 0, un = 0 (collinear): sort each segment's ends
     lexicographically (x, then y), intersect [max lows, min highs]:
     Segment lo hi when lo < hi, Point lo when lo = hi, else Empty.
   Under |coordinate| <= 10^4 every value fits easily: |den|,|tn|,|un|
   <= 8*10^8, the point's numerators <= 2.4*10^13.

   Proof.  [isectZ] is the same algorithm over Z; [isectZ_ok] proves
   intersect_spec of it (crossing case: [param], the point is
   A + tn/den (B - A) and lies on a segment iff 0 <= tn <= den; collinear
   case: [line_seg], on a common line a segment is the lexicographic
   interval of its ends; degenerate and parallel cases directly), and
   [isect_m_repr] proves that the machine function computes it word for
   word (Sint63.to_Z_add/sub/mul under the bounds of valid_input). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith Lia Bool Uint63.
From Stdlib Require Sint63.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The program: the same algorithm on 63-bit words read through Sint63 *)
(* ------------------------------------------------------------------ *)

Section Machine.
  Local Open Scope uint63_scope.

  Definition lexle_m (ux uy vx vy : sint) : bool :=
    Sint63.ltb ux vx || ((ux =? vx) && Sint63.leb uy vy).
  Definition lexlt_m (ux uy vx vy : sint) : bool :=
    Sint63.ltb ux vx || ((ux =? vx) && Sint63.ltb uy vy).

  Definition finish_m (lox loy hix hiy : sint) : inter sint :=
    if lexlt_m lox loy hix hiy then Segment lox loy hix hiy
    else if (lox =? hix) && (loy =? hiy) then Point lox loy 1
    else Empty.

  Definition coll2_m (p1x p1y p2x p2y p3x p3y p4x p4y : sint) : inter sint :=
    if lexle_m p1x p1y p3x p3y then
      (if lexle_m p2x p2y p4x p4y then finish_m p3x p3y p2x p2y else finish_m p3x p3y p4x p4y)
    else
      (if lexle_m p2x p2y p4x p4y then finish_m p1x p1y p2x p2y else finish_m p1x p1y p4x p4y).

  Definition coll1_m (p1x p1y p2x p2y x3 y3 x4 y4 : sint) : inter sint :=
    if lexle_m x3 y3 x4 y4 then coll2_m p1x p1y p2x p2y x3 y3 x4 y4
    else coll2_m p1x p1y p2x p2y x4 y4 x3 y3.

  Definition coll_m (x1 y1 x2 y2 x3 y3 x4 y4 : sint) : inter sint :=
    if lexle_m x1 y1 x2 y2 then coll1_m x1 y1 x2 y2 x3 y3 x4 y4
    else coll1_m x2 y2 x1 y1 x3 y3 x4 y4.

  Definition onseg_m (ax ay bx by_ px py : sint) : bool :=
    ((bx - ax) * (py - ay) =? (by_ - ay) * (px - ax))
    && ((Sint63.leb ax px && Sint63.leb px bx) || (Sint63.leb bx px && Sint63.leb px ax))
    && ((Sint63.leb ay py && Sint63.leb py by_) || (Sint63.leb by_ py && Sint63.leb py ay)).

  Definition cross_fin_m (x1 y1 rx ry den tn un : sint) : inter sint :=
    if Sint63.leb 0 tn && Sint63.leb tn den && Sint63.leb 0 un && Sint63.leb un den
    then Point (x1 * den + tn * rx) (y1 * den + tn * ry) den
    else Empty.

  Definition crossing_m (x1 y1 rx ry den tn un : sint) : inter sint :=
    if Sint63.ltb den 0 then cross_fin_m x1 y1 rx ry (0 - den) (0 - tn) (0 - un)
    else cross_fin_m x1 y1 rx ry den tn un.

  Definition isect_m (x1 y1 x2 y2 x3 y3 x4 y4 : sint) : inter sint :=
    let rx := x2 - x1 in let ry := y2 - y1 in
    let sx := x4 - x3 in let sy := y4 - y3 in
    let qx := x3 - x1 in let qy := y3 - y1 in
    let den := rx * sy - ry * sx in
    let un := qx * ry - qy * rx in
    if den =? 0 then
      if (rx =? 0) && (ry =? 0) then
        (if onseg_m x3 y3 x4 y4 x1 y1 then Point x1 y1 1 else Empty)
      else if (sx =? 0) && (sy =? 0) then
        (if onseg_m x1 y1 x2 y2 x3 y3 then Point x3 y3 1 else Empty)
      else if un =? 0 then coll_m x1 y1 x2 y2 x3 y3 x4 y4
      else Empty
    else crossing_m x1 y1 rx ry den (qx * sy - qy * sx) un.
End Machine.

(* ------------------------------------------------------------------ *)
(* The program computes isectZ                                          *)
(* ------------------------------------------------------------------ *)

Notation sZ := Sint63.to_Z.

Definition intersect : sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint
                       -> inter sint := isect_m.
