(* @function        roberthood
   @signature       array sint -> array sint -> float
   @math_signature  list Z -> list Z -> R
   @summary         [roberthood xs ys] takes the arrows hitting the target,
                    arrow k at the integer point (xs_k, ys_k), and returns
                    the longest Euclidean distance between any pair of
                    arrows, as a float whose absolute or relative error is
                    less than 10^-6.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  The list of coordinate pairs is two parallel lists, one per
   column of the input lines "x y"; a coordinate is signed (sint / Z). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th coordinate, for k < len l (0 outside, never relied on). *)
Definition get_list_Z (l : list Z) (k : N) : Z := nth (N.to_nat k) l 0.

(* i and j are two distinct arrows of the input. *)
Definition arrow_pair (xs : list Z) (i j : N) : Prop :=
  (i < len xs)%N /\ (j < len xs)%N /\ i <> j.

(* The Euclidean distance between arrows i and j, over the reals. *)
Definition dist (xs ys : list Z) (i j : N) : R :=
  let dx := get_list_Z xs i - get_list_Z xs j in
  let dy := get_list_Z ys i - get_list_Z ys j in
  R_sqrt.sqrt (IZR (dx * dx + dy * dy)).

(* d is the longest distance between any pair of arrows: attained by a
   pair, and no pair is farther apart. *)
Definition is_longest (xs ys : list Z) (d : R) : Prop :=
  (exists i j, arrow_pair xs i j /\ dist xs ys i j = d) /\
  (forall i j, arrow_pair xs i j -> (dist xs ys i j <= d)%R).

(* r has an absolute or a relative error to d of less than 10^-6. *)
Definition within_tolerance (r d : R) : Prop :=
  (Rabs (r - d) < / 1000000 \/ Rabs (r - d) < d / 1000000)%R.

(* The statement's bounds. *)
Record valid_input (xs ys : list Z) : Prop := {
  (* a single positive integer C, 2 <= C <= 100 000, the number of shots *)
  vi_n : (2 <= len xs <= 100000)%N;
  (* each following line contains a pair of integer coordinates *)
  vi_ys : len ys = len xs;
  (* the absolute value of any coordinate does not exceed 1 000 *)
  vi_x : Forall (fun c => Z.abs c <= 1000) xs;
  vi_y : Forall (fun c => Z.abs c <= 1000) ys;
}.

(* The answer: within the statement's tolerance of the longest distance. *)
Definition roberthood_spec (xs ys : list Z) (r : R) : Prop :=
  exists d, is_longest xs ys d /\ within_tolerance r d.

Program roberthood : array sint -> array sint -> float.

Specification roberthood_correct :
  forall (xs ys : list Z) (x y : array sint),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists r : R, repr (roberthood x y) r /\ roberthood_spec xs ys r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
