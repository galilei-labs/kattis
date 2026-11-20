(** * Dirty Driving *)

(** ** Description *)

(** Given the current distances to cars ahead, move your own car while
    keeping the distances between those cars unchanged. Find the smallest
    gap to the nearest car for which the car of rank $k$ is at least $kp$
    away, where $p$ is the spacing constant (called [deceleration] in the
    mathematical interface) and ranks begin at one.

    The input gives the number of cars ahead, $n$, and the spacing constant
    $p$, followed by exactly $n$ distinct current distances, one per car,
    in any order.

    [@kattis dirtydriving]
    - Difficulty: 3.3
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Distinct distance count: $1 \le n \le 10^{5}$; each distance: $1 \le d_i \le 10^{7}$.
    - Spacing constant: $1 \le p \le 20$. *)

(** ** Examples *)

(** - Input convention: Car count n and spacing constant p (the mathematical input deceleration), followed by exactly n distinct current distances, one per car, in any order.
    - Output convention: The minimum required distance to the nearest car. *)
(* Input:
3 1
1 2 4
Output:
1
*)

(** ** [@hide] Environment *)

(* @function        dirtydriving
   @signature       uint -> array uint -> uint
   @math_signature  N -> list N -> N
   @summary         [dirtydriving deceleration distances] is the minimum
                    distance D you must keep to the car directly in front,
                    the cars ahead of you being at the distinct distances
                    [distances] (in any order): moving yourself so that the
                    nearest car is at distance D, every car x must then be
                    at distance at least deceleration * (k + 1), k being the
                    number of cars between you and x.
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of cars (the merge sort), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A car ahead is its current distance to you.
  *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of cars at distances strictly smaller than [car]. *)
Definition cars_between (distances : list N)
  (car : N) : N :=
  len (filter (fun other => other <? car) distances).

(** Moving your car to leave [gap] to the nearest car, without changing the
    distances between the cars ahead, puts every car at least [deceleration]
    times its rank away. Ranks start at one for the nearest car. *)
Definition keeps_distance (deceleration : N)
  (distances : list N) (gap : N)
    : Prop :=
  forall car front_car, In car distances
    -> In front_car distances ->
    cars_between distances front_car = 0 ->
    deceleration *
      (cars_between distances car + 1) + front_car <= gap +
      car.

(** [@inside dirtydriving_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (deceleration : N)
  (distances : list N) : Prop := {
  (* 1 <= n <= 10^5 - the number of cars ahead of you *)
  vi_n : 1 <= len distances <= 100000;
  (* 1 <= p <= 20 - the deceleration constant *)
  vi_p : 1 <= deceleration <= 20;
  (* each distance d_i satisfies 1 <= d_i <= 10^7 *)
  vi_d : Forall
    (fun distance => 1 <= distance <= 10 ^ 7) distances;
  (* a single line with n unique integers *)
  vi_unique : NoDup distances;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the minimum gap to the nearest car such that every car is at
    least its rank times [deceleration] away, preserving all distances between
    the cars ahead. Ranks begin at one. *)
Definition dirtydriving_spec (deceleration : N)
  (distances : list N)
    (output : N) : Prop :=
  keeps_distance deceleration distances output /\
  forall output', keeps_distance deceleration distances
    output'
    -> output <= output'.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of distances. *)
Definition dirtydriving_time_spec (c1 c2 n_distances steps : nat) : Prop :=
  (steps <= c1 * ((n_distances + 1) * (Nat.log2 (n_distances) + 1)) + c2)%nat.

(** ** Interface *)

(** Find the smallest gap to the nearest car that meets the rank-based spacing
    rule, moving only your own car and keeping the cars ahead fixed relative
    to one another.
    - Input [deceleration]: The spacing constant p; the car of rank k must be at least k times p away. Ranks start at one for the nearest car.
    - Input [distances]: Distinct current distances to the cars ahead, in any order.
    - Output [output]: Minimum new gap to the nearest car such that every car is at least its rank times [deceleration] away. *)
Program dirtydriving : uint -> array uint -> uint.

(** [@example dirtydriving]
    - Sample: 1
    - Input [deceleration]: 1
    - Input [distances]: [1; 2; 4]
    - Output [output]: 1
*)

(** ** Bridge *)

(** [@requirement dirtydriving_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [dirtydriving_spec]. *)
Specification dirtydriving_correct :
  forall (deceleration : N) (distances : list N)
         (deceleration_int : uint)
           (distances_arr : array uint),
  valid_input deceleration distances ->
  repr deceleration_int deceleration
    -> repr distances_arr distances ->
  exists output : N,
    repr (dirtydriving deceleration_int distances_arr)
      output /\
    dirtydriving_spec deceleration distances output.

(** ** Complexity *)

(** [@hide] [dirtydriving_cost] is the cost translation of [dirtydriving] (the judge
    recomputes it and compares) ... *)
Complexity dirtydriving_cost for dirtydriving.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of cars (the merge sort), for two constants
    quantified before the inputs, on every valid input. [@requirement dirtydriving_time_spec] *)
Specification dirtydriving_time : exists c1 c2 : nat,
  forall (deceleration : N) (distances : list N)
  (deceleration_int : uint)
  (distances_arr : array uint),
  valid_input deceleration distances ->
  repr deceleration_int deceleration
  -> repr distances_arr distances ->
  dirtydriving_time_spec c1 c2 (size distances_arr) (cost2 dirtydriving_cost deceleration_int distances_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
