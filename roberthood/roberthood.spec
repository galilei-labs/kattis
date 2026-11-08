(** * Robert Hood *)

(** ** Description *)

(** Find the greatest Euclidean distance between any two input points.

    [@kattis roberthood]
    - Difficulty: 2.8
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 2 to 100,000 points.
    - Integer coordinates with absolute value at most 1,000. *)

(** ** Examples *)

(** - Input convention: Point count, followed by integer coordinate pairs.
    - Output convention: Maximum pairwise distance, with absolute or relative error below $10^{-6}$. *)
(* Input:
2
2 2
-1 -2
Output:
5.0
*)

(** ** [@hide] Environment *)

(* @function        roberthood
   @signature       array sint -> array sint -> float
   @math_signature  list Z -> list Z -> R
   @summary         [roberthood abscissas ordinates] takes the arrows
                    hitting the target, arrow k at the integer point
                    (abscissas_k, ordinates_k), and returns
                    the longest Euclidean distance between any pair of
                    arrows, as a float whose absolute or relative error is
                    less than 10^-6.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side. The list of coordinate pairs is two
   parallel lists, one per column of the input lines "x
   y" ; a coordinate is signed (sint / Z). *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th coordinate, for k < [len] l (0 outside,
    never relied on). *)
Definition get_list_Z (l : list Z) (k : N) : Z :=
  nth (N.to_nat k) l 0.

(** i and j are two distinct arrows of the input. *)
Definition arrow_pair (abscissas : list Z) (i j : N) : Prop
  :=
  (i < len abscissas)%N /\ (j < len abscissas)%N /\ i <> j.

(** The Euclidean distance between arrows i and j, over
    the reals. *)
Definition dist (abscissas ordinates : list Z) (i j : N) : R
  :=
  let delta_x :=
    get_list_Z abscissas i - get_list_Z abscissas j in
  let delta_y :=
    get_list_Z ordinates i - get_list_Z ordinates j in
  R_sqrt.sqrt (IZR (delta_x * delta_x + delta_y * delta_y)).

(** longest is the longest distance between any pair of
    arrows: attained by a pair, and no pair is farther
    apart. *)
Definition is_longest (abscissas ordinates : list Z)
  (longest : R) : Prop :=
  (exists i j, arrow_pair abscissas i j /\
     dist abscissas ordinates i j = longest) /\
  (forall i j, arrow_pair abscissas i j ->
     (dist abscissas ordinates i j <= longest)%R).

(** approx has an absolute or a relative error to exact
    of less than 10^-6. *)
Definition within_tolerance (approx exact : R) : Prop :=
  (Rabs (approx - exact) < / 1000000 \/
   Rabs (approx - exact) < exact / 1000000)%R.

(** [@inside roberthood_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (abscissas ordinates : list Z) : Prop :=
  {
  (* a single positive integer C, 2 <= C <= 100 000, the
     number of shots *)
  vi_n : (2 <= len abscissas <= 100000)%N;
  (* each following line contains a pair of integer
     coordinates *)
  vi_ys : len ordinates = len abscissas;
  (* the absolute value of any coordinate does not exceed
     1 000 *)
  vi_x : Forall (fun coordinate => Z.abs coordinate <= 1000)
    abscissas;
  vi_y : Forall (fun coordinate => Z.abs coordinate <= 1000)
    ordinates;
}.

(** ** Correctness *)

(** [@requirement]
    The output approximates the maximum Euclidean distance between input points, within
    the specified absolute or relative tolerance. *)
Definition roberthood_spec
  (abscissas ordinates : list Z)
  (output : R)
  : Prop :=
  exists longest, is_longest abscissas ordinates longest /\
    within_tolerance output longest.

(** ** Interface *)

(** Find the greatest Euclidean distance between any two input points.
    - Input [abscissas]:
    - Input [ordinates]:
    - Output [output]: *)
Program roberthood : array sint -> array sint -> float.

(** ** Bridge *)

(** [@requirement roberthood_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [roberthood_spec]. *)
Specification roberthood_correct :
  forall (abscissas ordinates : list Z)
         (abscissas_arr ordinates_arr : array sint),
    valid_input abscissas ordinates ->
    repr abscissas_arr abscissas -> repr ordinates_arr
      ordinates ->
    exists output : R,
      repr (roberthood abscissas_arr ordinates_arr) output
        /\
      roberthood_spec abscissas ordinates output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
