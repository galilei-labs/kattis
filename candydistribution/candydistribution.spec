(** * Candy Distribution *)

(** ** Description *)

(** Buy candy for $K$ children in bags containing $C$ candies each. Every
    child must receive the same positive number of candies, with exactly one
    spare candy left over. Find a positive number of bags $B$, no greater
    than $10^{9}$, that makes this possible, or report that none exists.
    Equivalently, require $CB = KX + 1$ for some positive integer share $X$.

    [@kattis candydistribution]
    - Difficulty: 4.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1 \le K, C \le 10^{9}$.
    - The returned $B$ must be at most $10^{9}$. *)

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
                    It runs in at most c1 * (log2 K + log2 C + 1) + c2 steps
                    of the cost model, for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The upper bound of $10^9$ on the bag count. *)
Definition max_bags : N := 10 ^ 9.

(** [bag_count] bags of [bag_size] candies respect the bag limit and provide an
    equal positive share for each of [kid_count] children, with exactly one candy
    left over. *)
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
    The output is a positive bag count no greater than $10^{9}$ that gives
    every child an equal positive share and leaves exactly one spare candy,
    or [None] exactly when no such bag count exists. *)
Definition candydistribution_spec (kid_count bag_size : N)
  (output : option N) : Prop :=
  match output with
  | Some bag_count => fair_bags kid_count bag_size bag_count
  | None => ~
    exists bag_count, fair_bags kid_count bag_size bag_count
  end.

(** ** Complexity *)

(** [@requirement] Runs in $O(\log(K+2)+\log(C+2))$ steps, where $K$ is the number of children and $C$ the bag size. *)
Definition candydistribution_time_spec (c1 c2 n_kid_count n_bag_size steps : nat) : Prop :=
  (steps <= c1 * (Nat.log2 (n_kid_count) + Nat.log2 (n_bag_size) + 1) + c2)%nat.

(** ** Interface *)

(** Buy whole bags so every child receives an equal positive share of candy
    and exactly one candy remains spare, using at most $10^{9}$ bags.
    - Input [kid_count]: Number of children sharing the candy.
    - Input [bag_size]: Candies in each bag.
    - Output [output]: [Some] valid positive bag count, or [None] exactly when no count within the limit works. *)
Program candydistribution : uint -> uint -> option uint.

(** [@example candydistribution]
    - Sample: 1
    - Case: 1
    - Input [kid_count]: 10
    - Input [bag_size]: 5
    - Output [output]: None
*)

(** [@example candydistribution]
    - Sample: 1
    - Case: 2
    - Input [kid_count]: 10
    - Input [bag_size]: 7
    - Output [output]: Some 3
*)

(** [@example candydistribution]
    - Sample: 1
    - Case: 3
    - Input [kid_count]: 1337
    - Input [bag_size]: 23
    - Output [output]: Some 872
*)

(** [@example candydistribution]
    - Sample: 1
    - Case: 4
    - Input [kid_count]: 123454321
    - Input [bag_size]: 42
    - Output [output]: Some 14696943
*)

(** [@example candydistribution]
    - Sample: 1
    - Case: 5
    - Input [kid_count]: 999999937
    - Input [bag_size]: 142857133
    - Output [output]: Some 166666655
*)

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

(** ** Complexity *)

(** [@hide] [candydistribution_cost] is the cost translation of [candydistribution] (the judge
    recomputes it and compares) ... *)
Complexity candydistribution_cost for candydistribution.

(** [@fold complexity bound] ... and runs in at most c1 * (log2 K + log2 C + 1) + c2 steps of the cost model, for two constants
    quantified before the inputs. [@requirement candydistribution_time_spec] *)
Specification candydistribution_time : exists c1 c2 : nat, forall kid_count_int bag_size_int : uint,
  candydistribution_time_spec c1 c2 (size kid_count_int) (size bag_size_int) (cost2 candydistribution_cost kid_count_int bag_size_int).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
