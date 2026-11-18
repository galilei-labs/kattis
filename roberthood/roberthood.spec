(** * Robert Hood *)

(** ** Description *)

(** Arrows have landed at the given coordinates on a target. Find the
    greatest Euclidean distance between any two arrow landing points.

    [@kattis roberthood]
    - Difficulty: 2.8
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Arrow count: $2 \le n \le 10^{5}$.
    - Integer coordinates with absolute value at most $10^{3}$. *)

(** ** Examples *)

(** - Input convention: Arrow count, followed by integer landing-coordinate pairs.
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
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of points (the sort; the hull scans and the rotating
                    calipers are linear), for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(* The list of coordinate pairs is two
   parallel lists, one per column of the input lines "x
   y" ; a coordinate is signed (sint / Z). *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_Z (l : list Z) (k : N) : Z :=
  nth (N.to_nat k) l 0.

(** [i] and [j] are distinct valid input-arrow indices. *)
Definition arrow_pair (abscissas : list Z) (i j : N) : Prop
  :=
  (i < len abscissas)%N /\ (j < len abscissas)%N /\ i <> j.

(** The exact real-valued Euclidean distance between arrows [i] and [j]. *)
Definition dist (abscissas ordinates : list Z) (i j : N) : R
  :=
  let delta_x :=
    get_list_Z abscissas i - get_list_Z abscissas j in
  let delta_y :=
    get_list_Z ordinates i - get_list_Z ordinates j in
  R_sqrt.sqrt (IZR (delta_x * delta_x + delta_y * delta_y)).

(** [longest] is attained by a pair of arrows, and no pair is farther apart. *)
Definition is_longest (abscissas ordinates : list Z)
  (longest : R) : Prop :=
  (exists i j, arrow_pair abscissas i j /\
     dist abscissas ordinates i j = longest) /\
  (forall i j, arrow_pair abscissas i j ->
     (dist abscissas ordinates i j <= longest)%R).

(** [approx] has absolute or relative error strictly less than $10^{-6}$ from
    [exact]. *)
Definition within_tolerance (approx exact : R) : Prop :=
  (Rabs (approx - exact) < / 1000000 \/
   Rabs (approx - exact) < exact / 1000000)%R.

(** [@inside roberthood_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (abscissas ordinates : list Z) : Prop :=
  {
  (* a single positive integer C, 2 <= C <= 10^5, the
     number of shots *)
  vi_n : (2 <= len abscissas <= 100000)%N;
  (* each following line contains a pair of integer
     coordinates *)
  vi_ys : len ordinates = len abscissas;
  (* the absolute value of any coordinate does not exceed
     10^3 *)
  vi_x : Forall (fun coordinate => Z.abs coordinate <= 1000)
    abscissas;
  vi_y : Forall (fun coordinate => Z.abs coordinate <= 1000)
    ordinates;
}.

(** ** Correctness *)

(** [@requirement]
    The output approximates the maximum Euclidean distance between arrow landing points, within
    the specified absolute or relative tolerance. *)
Definition roberthood_spec
  (abscissas ordinates : list Z)
  (output : R)
  : Prop :=
  exists longest, is_longest abscissas ordinates longest /\
    within_tolerance output longest.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of points. *)
Definition roberthood_time_spec (c1 c2 n_abscissas steps : nat) : Prop :=
  (steps <= c1 * ((n_abscissas + 1) * (Nat.log2 (n_abscissas) + 1)) + c2)%nat.

(** ** Interface *)

(** Find the greatest Euclidean distance between any two arrow landing points.
    - Input [abscissas]: Horizontal landing coordinate of each arrow.
    - Input [ordinates]: Vertical landing coordinate of each corresponding arrow.
    - Output [output]: Maximum distance between two arrows, within the specified absolute or relative tolerance. *)
Program roberthood : array sint -> array sint -> float.

(** [@example roberthood]
    - Sample: 1
    - Input [abscissas]: [2; -1]%Z
    - Input [ordinates]: [2; -2]%Z
    - Output [output]: 5%R
*)

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

(** ** Complexity *)

(** [@hide] [roberthood_cost] is the cost translation of [roberthood] (the judge
    recomputes it and compares) ... *)
Complexity roberthood_cost for roberthood.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of points (the sort; the hull scans and the rotating calipers are linear), for two constants
    quantified before the inputs, on every valid input. [@requirement roberthood_time_spec] *)
Specification roberthood_time : exists c1 c2 : nat,
  forall (abscissas ordinates : list Z)
  (abscissas_arr ordinates_arr : array sint),
  valid_input abscissas ordinates ->
  repr abscissas_arr abscissas -> repr ordinates_arr
  ordinates ->
  roberthood_time_spec c1 c2 (size abscissas_arr) (cost2 roberthood_cost abscissas_arr ordinates_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
