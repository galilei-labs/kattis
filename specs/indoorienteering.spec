(* @function        indoorienteering
   @signature       array (array uint) -> uint -> bool
   @math_signature  list (list N) -> N -> bool
   @summary         [indoorienteering d L] decides whether the n control
                    points, whose pairwise distances form the n x n matrix
                    d, can be visited each exactly once in some order,
                    returning directly to the first one, with a total race
                    length of exactly L. It returns true ("possible") iff
                    such an order exists, false ("impossible") otherwise.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The control points are 0 .. n-1 (the statement's 1 .. n);
   row i of d is the i-th line of the matrix. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* d_ij, the distance between control points i and j. *)
Definition dist (d : list (list N)) (i j : N) : N :=
  nth (N.to_nat j) (nth (N.to_nat i) d []) 0.

(* p lists every control point 0 .. n-1 exactly once. *)
Definition visiting_order (d : list (list N)) (p : list N) : Prop :=
  NoDup p /\ forall i, In i p <-> i < len d.

(* The sum of the distances between consecutive points of p. *)
Fixpoint path_length (d : list (list N)) (p : list N) : N :=
  match p with
  | x :: ((y :: _) as t) => dist d x y + path_length d t
  | _ => 0
  end.

(* The race along p, then directly back from its last point to its first. *)
Definition race_length (d : list (list N)) (p : list N) : N :=
  match p with
  | [] => 0
  | x :: _ => path_length d p + dist d (last p x) x
  end.

(* The statement's bounds, for one test case. *)
Record valid_input (d : list (list N)) (L : N) : Prop := {
  (* 2 <= n <= 14, the number of control points *)
  vi_n : 2 <= len d <= 14;
  (* 1 <= L <= 10^15, the desired length of the race *)
  vi_L : 1 <= L <= 10 ^ 15;
  (* n lines with n integers each *)
  vi_rows : Forall (fun r => len r = len d) d;
  (* d_ii = 0 *)
  vi_diag : forall i, i < len d -> dist d i i = 0;
  (* 1 <= d_ij <= L for i <> j *)
  vi_dist : forall i j, i < len d -> j < len d -> i <> j ->
    1 <= dist d i j <= L;
  (* d_ij = d_ji *)
  vi_sym : forall i j, i < len d -> j < len d -> dist d i j = dist d j i;
  (* d_ij <= d_ik + d_kj *)
  vi_tri : forall i j k, i < len d -> j < len d -> k < len d ->
    dist d i j <= dist d i k + dist d k j;
}.

(* "possible" (true) iff some order visits every control point once and
   returns to the first one with a total distance of exactly L. *)
Definition indoorienteering_spec (d : list (list N)) (L : N) (b : bool) : Prop :=
  b = true <-> exists p, visiting_order d p /\ race_length d p = L.

Program indoorienteering : array (array uint) -> uint -> bool.

Specification indoorienteering_correct :
  forall (d : list (list N)) (L : N) (x : array (array uint)) (y : uint),
  valid_input d L -> repr x d -> repr y L ->
  exists b : bool, repr (indoorienteering x y) b /\
                   indoorienteering_spec d L b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
