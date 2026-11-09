(** * Dirty Driving *)

(** ** Description *)

(** Given distinct distances to objects ahead and a spacing constant p, find
    the smallest new distance to the nearest object such that the k-th
    nearest object is at least k * p away.

    [@kattis dirtydriving]
    - Difficulty: 3.3
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1\text{ to }100{,}000$ distinct distances, each in $[1, 10^{7}]$.
    - Spacing constant in $[1, 20]$. *)

(** ** Examples *)

(** - Input convention: Object count and spacing constant, followed by distinct current distances.
    - Output convention: The minimum required distance to the nearest object. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A car ahead is its current distance to you.
  *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of objects at distances strictly smaller than [car]. *)
Definition cars_between (distances : list N)
  (car : N) : N :=
  len (filter (fun other => other <? car) distances).

(** Keeping distance gap to the car directly in front
    (the car at distance front_car, with no car
    between), every car of distances, then at distance
    gap + (car - front_car), is at distance at least
    deceleration * (cars_between car + 1). *)
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
  (* 1 <= n <= 100 000 - the number of cars ahead of you *)
  vi_n : 1 <= len distances <= 100000;
  (* 1 <= p <= 20 - the deceleration constant *)
  vi_p : 1 <= deceleration <= 20;
  (* each of these integers are in the interval [1, 10^7] *)
  vi_d : Forall
    (fun distance => 1 <= distance <= 10 ^ 7) distances;
  (* a single line with n unique integers *)
  vi_unique : NoDup distances;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the minimum distance to the nearest object for which the k-th nearest
    object is at least k times the spacing constant away. *)
Definition dirtydriving_spec (deceleration : N)
  (distances : list N)
    (output : N) : Prop :=
  keeps_distance deceleration distances output /\
  forall output', keeps_distance deceleration distances
    output'
    -> output <= output'.

(** ** Interface *)

(** Given distinct distances to objects ahead and a spacing constant p, find the smallest
    new distance to the nearest object such that the k-th nearest object is at least k *
    p away.
    - Input [deceleration]: Required spacing per position in the distance order.
    - Input [distances]: Current distances to the objects ahead.
    - Output [output]: The output is the minimum distance to the nearest object for which the k-th nearest object is at least k times the spacing constant away. *)
Program dirtydriving : uint -> array uint -> uint.

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

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
