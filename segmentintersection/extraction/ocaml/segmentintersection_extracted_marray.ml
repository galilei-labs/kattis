
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

(** val lesb : Uint63.t -> Uint63.t -> bool **)

let lesb = Uint63.les

type sint = Uint63.t

type 'a inter =
| Empty
| Point of 'a * 'a * 'a
| Segment of 'a * 'a * 'a * 'a

(** val lexle_m : sint -> sint -> sint -> sint -> bool **)

let lexle_m ux uy vx vy =
  (||) (ltsb ux vx) ((&&) (eqb ux vx) (lesb uy vy))

(** val lexlt_m : sint -> sint -> sint -> sint -> bool **)

let lexlt_m ux uy vx vy =
  (||) (ltsb ux vx) ((&&) (eqb ux vx) (ltsb uy vy))

(** val finish_m : sint -> sint -> sint -> sint -> sint inter **)

let finish_m lox loy hix hiy =
  if lexlt_m lox loy hix hiy
  then Segment (lox, loy, hix, hiy)
  else if (&&) (eqb lox hix) (eqb loy hiy)
       then Point (lox, loy, (Uint63.of_int (1)))
       else Empty

(** val coll2_m :
    sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter **)

let coll2_m p1x p1y p2x p2y p3x p3y p4x p4y =
  if lexle_m p1x p1y p3x p3y
  then if lexle_m p2x p2y p4x p4y
       then finish_m p3x p3y p2x p2y
       else finish_m p3x p3y p4x p4y
  else if lexle_m p2x p2y p4x p4y
       then finish_m p1x p1y p2x p2y
       else finish_m p1x p1y p4x p4y

(** val coll1_m :
    sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter **)

let coll1_m p1x p1y p2x p2y x3 y3 x4 y4 =
  if lexle_m x3 y3 x4 y4
  then coll2_m p1x p1y p2x p2y x3 y3 x4 y4
  else coll2_m p1x p1y p2x p2y x4 y4 x3 y3

(** val coll_m :
    sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter **)

let coll_m x1 y1 x2 y2 x3 y3 x4 y4 =
  if lexle_m x1 y1 x2 y2
  then coll1_m x1 y1 x2 y2 x3 y3 x4 y4
  else coll1_m x2 y2 x1 y1 x3 y3 x4 y4

(** val onseg_m : sint -> sint -> sint -> sint -> sint -> sint -> bool **)

let onseg_m ax ay bx by_ px py =
  (&&)
    ((&&) (eqb (mul (sub bx ax) (sub py ay)) (mul (sub by_ ay) (sub px ax)))
      ((||) ((&&) (lesb ax px) (lesb px bx)) ((&&) (lesb bx px) (lesb px ax))))
    ((||) ((&&) (lesb ay py) (lesb py by_)) ((&&) (lesb by_ py) (lesb py ay)))

(** val cross_fin_m :
    sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter **)

let cross_fin_m x1 y1 rx ry den tn un =
  if (&&)
       ((&&) ((&&) (lesb (Uint63.of_int (0)) tn) (lesb tn den))
         (lesb (Uint63.of_int (0)) un))
       (lesb un den)
  then Point ((add (mul x1 den) (mul tn rx)), (add (mul y1 den) (mul tn ry)),
         den)
  else Empty

(** val crossing_m :
    sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter **)

let crossing_m x1 y1 rx ry den tn un =
  if ltsb den (Uint63.of_int (0))
  then cross_fin_m x1 y1 rx ry (sub (Uint63.of_int (0)) den)
         (sub (Uint63.of_int (0)) tn) (sub (Uint63.of_int (0)) un)
  else cross_fin_m x1 y1 rx ry den tn un

(** val isect_m :
    sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint inter **)

let isect_m x1 y1 x2 y2 x3 y3 x4 y4 =
  let rx = sub x2 x1 in
  let ry = sub y2 y1 in
  let sx = sub x4 x3 in
  let sy = sub y4 y3 in
  let qx = sub x3 x1 in
  let qy = sub y3 y1 in
  let den = sub (mul rx sy) (mul ry sx) in
  let un = sub (mul qx ry) (mul qy rx) in
  if eqb den (Uint63.of_int (0))
  then if (&&) (eqb rx (Uint63.of_int (0))) (eqb ry (Uint63.of_int (0)))
       then if onseg_m x3 y3 x4 y4 x1 y1
            then Point (x1, y1, (Uint63.of_int (1)))
            else Empty
       else if (&&) (eqb sx (Uint63.of_int (0))) (eqb sy (Uint63.of_int (0)))
            then if onseg_m x1 y1 x2 y2 x3 y3
                 then Point (x3, y3, (Uint63.of_int (1)))
                 else Empty
            else if eqb un (Uint63.of_int (0))
                 then coll_m x1 y1 x2 y2 x3 y3 x4 y4
                 else Empty
  else crossing_m x1 y1 rx ry den (sub (mul qx sy) (mul qy sx)) un

module SegmentintersectionImpl =
 struct
  (** val intersect :
      sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint -> sint
      inter **)

  let intersect =
    isect_m
 end
