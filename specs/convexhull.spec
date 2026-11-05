(* @function        convex_hull
   @signature       array sint -> array sint -> array uint
   @math_signature  list Z -> list Z -> list N
   @summary         [convex_hull xs ys] returns the indices, in
                    counterclockwise order, of the vertices of the convex
                    hull of the points (xs[i], ys[i]), no three consecutive
                    vertices collinear ; any cyclic shift, and any index
                    among duplicates of a vertex
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
Definition get_point (xs ys : list Z) (i : N) : point :=
  (get_list_Z xs i, get_list_Z ys i).

(* The t-th vertex of the polygon p, for t < len p ((0, 0) outside, never
   relied on). *)
Definition get_pt (p : list point) (t : N) : point := nth (N.to_nat t) p (0, 0).

(* The position after t around the polygon p. *)
Definition next (p : list point) (t : N) : N := ((t + 1) mod len p)%N.

(* Twice the signed area of the triangle a b c : positive when c is to the
   left of the directed line from a to b, zero when the three points are
   collinear. *)
Definition cross (a b c : point) : Z :=
  (fst b - fst a) * (snd c - snd a) - (snd b - snd a) * (fst c - fst a).

(* q lies on the segment from a to b. *)
Definition on_segment (a b q : point) : Prop :=
  cross a b q = 0 /\
  Z.min (fst a) (fst b) <= fst q <= Z.max (fst a) (fst b) /\
  Z.min (snd a) (snd b) <= snd q <= Z.max (snd a) (snd b).

(* Every listed index is the index of an input point. *)
Definition indices_valid (xs : list Z) (h : list N) : Prop :=
  Forall (fun i => (i < len xs)%N) h.

(* The vertices named by h, as points. *)
Definition vertices (xs ys : list Z) (h : list N) : list point :=
  map (get_point xs ys) h.

(* Every turn of the polygon p is strictly to the left : counterclockwise,
   and no three consecutive vertices collinear. *)
Definition strictly_convex_ccw (p : list point) : Prop :=
  forall t, (t < len p)%N ->
    0 < cross (get_pt p t) (get_pt p (next p t)) (get_pt p (next p (next p t))).

(* Every input point is on or to the left of every directed edge of p. *)
Definition left_of_edges (xs ys : list Z) (p : list point) : Prop :=
  forall t i, (t < len p)%N -> (i < len xs)%N ->
    0 <= cross (get_pt p t) (get_pt p (next p t)) (get_point xs ys i).

(* The polygon p encloses the input points : all equal to its single
   vertex, all on the segment between its two vertices, or all on or to
   the left of each of its edges. *)
Definition encloses (xs ys : list Z) (p : list point) : Prop :=
  match p with
  | [a] => forall i, (i < len xs)%N -> get_point xs ys i = a
  | [a; b] => forall i, (i < len xs)%N -> on_segment a b (get_point xs ys i)
  | _ => left_of_edges xs ys p
  end.

(* The statement's bounds, for one test case. *)
Record valid_input (xs ys : list Z) : Prop := {
  (* 1 <= n <= 10000 *)
  vi_n : (1 <= len xs <= 10000)%N;
  (* one y per x *)
  vi_ys_length : len ys = len xs;
  (* coordinates are integers with absolute value bounded by 10000 *)
  vi_xs : Forall (fun x => - 10000 <= x <= 10000) xs;
  vi_ys : Forall (fun y => - 10000 <= y <= 10000) ys;
}.

(* The answer : a non-empty polygon of distinct input points, strictly
   convex and counterclockwise when it has three vertices or more, that
   encloses every input point. *)
Definition convex_hull_spec (xs ys : list Z) (h : list N) : Prop :=
  let p := vertices xs ys h in
  (1 <= len h)%N /\
  indices_valid xs h /\
  NoDup p /\
  ((3 <= len p)%N -> strictly_convex_ccw p) /\
  encloses xs ys p.

(* machine side : the only thing that gets extracted *)
Program convex_hull : array sint -> array sint -> array uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification convex_hull_correct : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists h : list N, repr (convex_hull x y) h /\ convex_hull_spec xs ys h.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
