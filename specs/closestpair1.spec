(* @function        closestpair
   @signature       array float -> array float -> uint * uint
   @math_signature  list R -> list R -> N * N
   @summary         One test case: [closestpair xs ys] takes the n >= 2
                    points (xs_k, ys_k) of the case and returns the indices
                    i, j of two distinct points that no pair of distinct
                    points is strictly closer than, exactly over the reals
                    the floats denote; any such pair, in either order. The
                    harness prints xs_i ys_i xs_j ys_j.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The points are two parallel lists, one per column of the
   input lines "x y"; a coordinate is the real its float denotes. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th coordinate, for k < len l (0 outside, never relied on). *)
Definition get_list_R (l : list R) (k : N) : R := nth (N.to_nat k) l 0%R.

(* i and j are two distinct points of the input: distinct indices; two
   indices may hold the same point, at distance 0 (third sample case). *)
Definition point_pair (xs : list R) (i j : N) : Prop :=
  i < len xs /\ j < len xs /\ i <> j.

(* The squared Euclidean distance between points i and j. *)
Definition dist2 (xs ys : list R) (i j : N) : R :=
  let dx := (get_list_R xs i - get_list_R xs j)%R in
  let dy := (get_list_R ys i - get_list_R ys j)%R in
  (dx * dx + dy * dy)%R.

(* The statement's bounds on one test case.  "At most 2 decimals" is a
   property of the input text, gone once parsed: the contract is exact on
   the reals the parsed floats denote.  "Generated uniformly at random" is
   a distribution, not a property of one input: the contract holds on
   every input below. *)
Record valid_input (xs ys : list R) : Prop := {
  (* 2 <= n <= 100 000 *)
  vi_n : 2 <= len xs <= 100000;
  (* n points, each of the form x y *)
  vi_ys : len ys = len xs;
  (* coordinates ... absolute value bounded by 100 000 *)
  vi_x : Forall (fun c => (Rabs c <= 100000)%R) xs;
  vi_y : Forall (fun c => (Rabs c <= 100000)%R) ys;
}.

(* The answer: two distinct points that no pair of distinct points is
   strictly closer than, exactly. *)
Definition closestpair_spec (xs ys : list R) (r : N * N) : Prop :=
  point_pair xs (fst r) (snd r) /\
  forall p q, point_pair xs p q ->
    (dist2 xs ys (fst r) (snd r) <= dist2 xs ys p q)%R.

Program closestpair : array float -> array float -> uint * uint.

Specification closestpair_correct :
  forall (xs ys : list R) (x y : array float),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists r : N * N, repr (closestpair x y) r /\ closestpair_spec xs ys r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
