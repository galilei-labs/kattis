(** * Candy Distribution *)

(** ** Description *)

(** Given positive integers K and C, find a positive B no greater than
    1000000000 such that C * B = K * X + 1 for some positive integer X, or
    report that no solution exists.

    [@kattis candydistribution]
    - Difficulty: 4.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1 \le K, C \le 10^{9}$.
    - The returned B must be at most $10^{9}$. *)

(** ** Examples *)

(** - Input convention: Case count, followed by one pair K C per case.
    - Output convention: A valid bag count, or IMPOSSIBLE, on one line per case. *)
(* Input:
5
10 5
10 7
1337 23
123454321 42
999999937 142857133
Output:
IMPOSSIBLE
3
872
14696943
166666655
*)

(** ** [@hide] Environment *)

(* @function        candydistribution
   @signature       uint -> uint -> option uint
   @math_signature  N -> N -> option N
   @summary         [candydistribution kid_count bag_size], for kid_count
                    kids and bags of bag_size candies each, returns
                    [Some bag_count] where buying bag_count bags, at most
                    10^9 of them, gives exactly kid_count * share + 1
                    candies for some positive natural number share, and
                    [None] ("IMPOSSIBLE") exactly when no such number of
                    bags exists. When several bag_count work, any of them
                    may be returned.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(** ** Definitions *)

(** The upper bound of $10^9$ on the bag count. *)
Definition max_bags : N := 10 ^ 9.

(** Buying bag_count bags of bag_size candies, within
    the bag limit, gives (kid_count * share) + 1 candies
    for a positive natural number share: a fair
    distribution of share candies to each of the
    kid_count kids, plus exactly one spare candy. *)
Definition fair_bags
  (kid_count bag_size bag_count : N) : Prop :=
  1 <= bag_count <= max_bags /\
  exists share : N, 1 <= share
    /\ bag_count * bag_size = kid_count * share + 1.

(** [@inside candydistribution_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (kid_count bag_size : N) : Prop := {
  (* "1 <= K, C <= 10^9" *)
  vi_k : 1 <= kid_count <= 10 ^ 9;
  vi_c : 1 <= bag_size <= 10 ^ 9;
}.

(** ** Correctness *)

(** [@requirement]
    The output is a positive bag count satisfying the divisibility, positive-share and
    upper-bound constraints, or None exactly when no such count exists. *)
Definition candydistribution_spec (kid_count bag_size : N)
  (output : option N) : Prop :=
  match output with
  | Some bag_count => fair_bags kid_count bag_size bag_count
  | None => ~
    exists bag_count, fair_bags kid_count bag_size bag_count
  end.

(** ** Interface *)

(** Given positive integers K and C, find a positive B no greater than 1000000000 such that
    C * B = K * X + 1 for some positive integer X, or report that no solution exists.
    - Input [kid_count]: Number of equal positive shares required.
    - Input [bag_size]: Number of units in each bag.
    - Output [output]: The output is a positive bag count satisfying the divisibility, positive-share and upper-bound constraints, or None exactly when no such count exists. *)
Program candydistribution : uint -> uint -> option uint.

(** ** Bridge *)

(** [@requirement candydistribution_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [candydistribution_spec]. *)
Specification candydistribution_correct :
  forall (kid_count bag_size : N)
    (kid_count_int bag_size_int : uint),
  valid_input kid_count bag_size ->
  repr kid_count_int kid_count
    -> repr bag_size_int bag_size ->
  exists output : option N,
    repr (candydistribution kid_count_int bag_size_int)
      output /\
    candydistribution_spec kid_count bag_size output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
