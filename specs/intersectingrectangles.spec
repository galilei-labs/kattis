(* @function        intersecting_rectangles
   @signature       array sint -> array sint -> array sint -> array sint -> bool
   @math_signature  list Z -> list Z -> list Z -> list Z -> bool
   @summary         Rectangle i has lower left corner (x1_i, y1_i) and upper
                    right corner (x2_i, y2_i).  The answer is true exactly
                    when two distinct rectangles have boundaries with a
                    common point of the real plane (a rectangle nested
                    strictly inside another does not count).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Types : the coordinates are signed (sint / Z) ; the n input lines
   x1 y1 x2 y2 are four parallel arrays / lists, one per column.  The
   answer 1 / 0 is the bool true / false. *)

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The i-th entry of a column (rectangle i's coordinate), and the same as
   a real number. *)
Definition entry (c : list Z) (i : N) : Z := nth (N.to_nat i) c 0.
Definition coord (c : list Z) (i : N) : R := IZR (entry c i).

(* The point (p, q) lies on the boundary of rectangle i : in the closed
   rectangle, and on one of its four sides. *)
Definition on_boundary (x1 y1 x2 y2 : list Z) (i : N) (p q : R) : Prop :=
  (coord x1 i <= p <= coord x2 i)%R /\ (coord y1 i <= q <= coord y2 i)%R /\
  (p = coord x1 i \/ p = coord x2 i \/ q = coord y1 i \/ q = coord y2 i).

(* The boundaries of rectangles i and j have a common point. *)
Definition intersect (x1 y1 x2 y2 : list Z) (i j : N) : Prop :=
  exists p q : R,
    on_boundary x1 y1 x2 y2 i p q /\ on_boundary x1 y1 x2 y2 j p q.

(* Some pair of distinct rectangles intersect. *)
Definition some_pair_intersects (x1 y1 x2 y2 : list Z) : Prop :=
  exists i j : N, (i < j < len x1)%N /\ intersect x1 y1 x2 y2 i j.

(* The statement's bounds, for one test case. *)
Record valid_input (x1 y1 x2 y2 : list Z) : Prop := {
  (* 1 <= n <= 10^5, n the number of rectangles *)
  vi_n : (1 <= len x1 <= 10 ^ 5)%N;
  (* each of the next n lines contains four integers x1 y1 x2 y2 *)
  vi_y1_len : len y1 = len x1;
  vi_x2_len : len x2 = len x1;
  vi_y2_len : len y2 = len x1;
  (* -10^9 <= x1, y1, x2, y2 <= 10^9 *)
  vi_x1 : Forall (fun c => - 10 ^ 9 <= c <= 10 ^ 9) x1;
  vi_y1 : Forall (fun c => - 10 ^ 9 <= c <= 10 ^ 9) y1;
  vi_x2 : Forall (fun c => - 10 ^ 9 <= c <= 10 ^ 9) x2;
  vi_y2 : Forall (fun c => - 10 ^ 9 <= c <= 10 ^ 9) y2;
  (* x1 < x2, y1 < y2 *)
  vi_x_order : forall i, (i < len x1)%N -> entry x1 i < entry x2 i;
  vi_y_order : forall i, (i < len x1)%N -> entry y1 i < entry y2 i;
  (* all x values will be distinct *)
  vi_x_distinct : NoDup (x1 ++ x2);
  (* all y values will be distinct *)
  vi_y_distinct : NoDup (y1 ++ y2);
}.

(* The answer : 1 (true) iff some pair of rectangles intersect. *)
Definition intersecting_rectangles_spec (x1 y1 x2 y2 : list Z) (b : bool)
  : Prop :=
  b = true <-> some_pair_intersects x1 y1 x2 y2.

Program intersecting_rectangles :
  array sint -> array sint -> array sint -> array sint -> bool.

Specification intersecting_rectangles_correct :
  forall (x1 y1 x2 y2 : list Z) (ax1 ay1 ax2 ay2 : array sint),
  valid_input x1 y1 x2 y2 ->
  repr ax1 x1 -> repr ay1 y1 -> repr ax2 x2 -> repr ay2 y2 ->
  exists b : bool,
    repr (intersecting_rectangles ax1 ay1 ax2 ay2) b /\
    intersecting_rectangles_spec x1 y1 x2 y2 b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
