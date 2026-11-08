(** * Indoorienteering *)

(** ** Description *)

(** Decide whether a tour can visit every vertex exactly once, return to its
    start, and have exactly a specified total length.

    [@kattis indoorienteering]
    - Difficulty: 6.6
    - CPU time limit: 8 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 2 to 14 vertices; target length from 1 to $10^{15}$.
    - Distances are symmetric, zero on the diagonal, and otherwise from 1 to
      the target length; they satisfy the triangle inequality. *)

(** ** Examples *)

(** - Input convention: Vertex count and target tour length, followed by a square distance matrix.
    - Output convention: possible if a tour of exactly the requested length exists; impossible otherwise. *)
(* Input:
4 10
0 3 2 1
3 0 1 3
2 1 0 2
1 3 2 0
Output:
possible
*)

(** ** [@hide] Environment *)
(* @function        indoorienteering
   @signature       array (array uint) -> uint -> bool
   @math_signature  list (list N) -> N -> bool
   @summary         [indoorienteering distances desired_length] decides
                    whether the n control points, whose pairwise distances
                    form the n x n matrix distances, can be visited each
                    exactly once in some order, returning directly to the
                    first one, with a total race length of exactly
                    desired_length. It returns true ("possible") iff such
                    an order exists, false ("impossible") otherwise.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** d_ij, the distance between control points i and j. *)
Definition dist (distances : list (list N)) (i j : N) : N :=
  nth (N.to_nat j) (nth (N.to_nat i) distances []) 0.

(** order lists every control point 0 .. n-1 exactly once. *)
Definition visiting_order (distances : list (list N))
  (order : list N)
    : Prop :=
  NoDup order /\ forall point, In point order <-> point <
    len distances.

(** The sum of the distances between consecutive points of order. *)
Fixpoint path_length (distances : list (list N))
  (order : list N) : N :=
  match order with
  | point :: ((next :: _) as rest) =>
      dist distances point next + path_length distances rest
  | _ => 0
  end.

(** The race along order, then directly back from its last point to its
    first. *)
Definition race_length (distances : list (list N))
  (order : list N) : N :=
  match order with
  | [] => 0
  | start :: _ =>
      path_length distances order + dist distances (last
        order start) start
  end.

(** [@inside indoorienteering_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (distances : list (list N))
  (desired_length : N)
    : Prop := {
  (* 2 <= n <= 14, the number of control points *)
  vi_n : 2 <= len distances <= 14;
  (* 1 <= L <= 10^15, the desired length of the race
     (desired_length) *)
  vi_L : 1 <= desired_length <= 10 ^ 15;
  (* n lines with n integers each *)
  vi_rows : Forall (fun row => len row = len distances)
    distances;
  (* d_ii = 0 *)
  vi_diag : forall i, i < len distances ->
    dist distances i i = 0;
  (* 1 <= d_ij <= L for i <> j *)
  vi_dist : forall i j, i < len distances ->
    j < len distances -> i <> j ->
    1 <= dist distances i j <= desired_length;
  (* d_ij = d_ji *)
  vi_sym : forall i j, i < len distances ->
    j < len distances ->
    dist distances i j = dist distances j i;
  (* d_ij <= d_ik + d_kj *)
  vi_tri : forall i j k,
    i < len distances -> j < len distances ->
      k < len distances ->
    dist distances i j <= dist distances i k + dist
      distances k j;
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when a tour visits every vertex once, returns to its
    start and has the specified total length. *)
Definition indoorienteering_spec (distances : list (list N))
    (desired_length : N) (output : bool) : Prop :=
  match output with
  | true =>
      exists order, visiting_order distances order /\
            race_length distances order =
            desired_length
  | false =>
      ~ exists order, visiting_order distances order /\
            race_length distances order =
            desired_length
  end.

(** ** Interface *)

(** Decide whether a tour can visit every vertex exactly once, return to its start, and have
    exactly a specified total length.
    - Input [distances]:
    - Input [desired_length]:
    - Output [output]: *)
Program indoorienteering : array
  (array uint) -> uint -> bool.

(** ** Bridge *)

(** [@requirement indoorienteering_spec] [@fold full correctness
    statement] On valid represented inputs, [indoorienteering]
    returns a represented output satisfying [indoorienteering_spec]. *)
Specification indoorienteering_correct :
  forall (distances : list (list N)) (desired_length : N)
         (distances_arr : array (array uint))
           (desired_length_int : uint),
  valid_input distances desired_length ->
  repr distances_arr distances ->
    repr desired_length_int desired_length ->
  exists output : bool,
    repr (indoorienteering distances_arr desired_length_int)
      output /\
    indoorienteering_spec distances desired_length output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
