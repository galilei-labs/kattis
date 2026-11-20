(** * Tug of War *)

(** ** Description *)

(** Divide all the people at a picnic into two tug-of-war teams. Every
    person must join exactly one team, and the team sizes may differ by at
    most one person. Make the teams' total weights as close as possible,
    and report the two totals with the smaller first.

    [@kattis tugofwar]
    - Difficulty: 5.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Weight count: $1 \le n \le 100$; each integer weight: $1 \le w_i \le 450$. *)

(** ** Examples *)

(** - Input convention: Weight count, followed by one integer weight per line.
    - Output convention: The two group totals on one line, with the smaller total first. *)
(* Input:
3
100
90
200
Output:
190 200
*)

(** ** [@hide] Environment *)

(* @function        tugofwar
   @signature       array uint -> uint * uint
   @math_signature  list N -> N * N
   @summary         [tugofwar weights] divides the people of weights weights
                    into two teams whose numbers of people differ by at most
                    one, so that the total weights of the two teams are as
                    nearly equal as possible, and returns the two totals,
                    the lesser first.
                    It runs in at most c1 * (n + 1)^2 * (S + 1) + c2 steps
                    of the cost model on a valid input, n the number of
                    people and S the total weight ([sizes]; the reachability
                    table over team sizes and partial sums, one pass per
                    person), for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* Person k has weight weights_k; a division
   into two teams is a list assignment of booleans,
   assignment_k telling whether person k is on the first
   team. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The sum of the entries in [l], with value zero for an empty list. *)
Fixpoint sum (l : list N) : N :=
  match l with
  | [] => 0
  | weight :: rest => weight + sum rest
  end.

(** The weights of the people that [assignment] places on the first team. *)
Definition team (weights : list N) (assignment : list bool)
  : list N :=
  map fst (filter snd (combine weights assignment)).

(** The [weights] of the people on the other [team]. *)
Definition other_team (weights : list N)
  (assignment : list bool)
  : list N :=
  team weights (map negb assignment).

(** [assignment] assigns each person to one of two teams whose sizes differ by at
    most one. *)
Definition division (weights : list N)
  (assignment : list bool) : Prop :=
  len assignment = len weights /\
  (Z.abs (Z.of_N (len (team weights assignment)) -
          Z.of_N (len (other_team weights assignment)) ) <=
            1)%Z.

(** The difference between the total [weights] of the two
    teams. *)
Definition gap (weights : list N) (assignment : list bool) :
  Z :=
  Z.abs (Z.of_N (sum (team weights assignment)) -
         Z.of_N (sum (other_team weights assignment))).

(** [@inside tugofwar_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (weights : list N) : Prop := {
  (* There is at least 1 and at most 100 people at the
     picnic. *)
  vi_n : 1 <= len weights <= 100;
  (* Each weight is an integer between 1 and 450. *)
  vi_w : Forall (fun weight => 1 <= weight <= 450) weights;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the two team weights, smaller first, assigning every
    person to one team, with team sizes differing by at most one and the
    difference between total weights as small as possible. *)
Definition tugofwar_spec
  (weights : list N)
  (output : N * N)
  : Prop :=
  match output with
  | (lighter_total, heavier_total) =>
      lighter_total <= heavier_total /\
      exists assignment,
        division weights assignment /\
        sum (team weights assignment) = lighter_total /\
        sum (other_team weights assignment) = heavier_total
          /\
        forall assignment', division weights assignment' ->
          (gap weights assignment <= gap weights
        assignment')
            %Z
  end.

(** ** Complexity *)

(** [@requirement] Runs in $O((n+1)^2(W+1))$ steps, where $n$ is the number of weights and $W$ their sum. *)
Definition tugofwar_time_spec (c1 c2 n_weights total_weights steps : nat) : Prop :=
  (steps <= c1 * ((n_weights + 1) * (n_weights + 1) * (total_weights + 1)) + c2)%nat.

(** ** Interface *)

(** Form two tug-of-war teams with sizes differing by at most one person,
    minimizing the difference between their total weights.
    - Input [weights]: Weight of each person, who must be assigned to exactly one team.
    - Output [output]: Team weight totals, smaller first, for an optimal division. *)
Program tugofwar : array uint -> uint * uint.

(** [@example tugofwar]
    - Sample: 1
    - Input [weights]: [100; 90; 200]
    - Output [output]: (190, 200)
*)

(** ** Bridge *)

(** [@requirement tugofwar_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [tugofwar_spec]. *)
Specification tugofwar_correct :
  forall (weights : list N) (weights_arr : array uint),
  valid_input weights -> repr weights_arr weights ->
  exists output : N * N,
    repr (tugofwar weights_arr) output /\
    tugofwar_spec weights output.

(** ** Complexity *)

(** [@hide] [tugofwar_cost] is the cost translation of [tugofwar] (the judge
    recomputes it and compares) ... *)
Complexity tugofwar_cost for tugofwar.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1)^2 * (S + 1) + c2 steps of the cost model on a valid input, n the number of people and S the total weight ([sizes]; the reachability table over team sizes and partial sums, one pass per person), for two constants
    quantified before the inputs, on every valid input. [@requirement tugofwar_time_spec] *)
Specification tugofwar_time : exists c1 c2 : nat,
  forall (weights : list N) (weights_arr : array uint),
  valid_input weights -> repr weights_arr weights ->
  tugofwar_time_spec c1 c2 (size weights_arr) (sizes weights_arr) (cost1 tugofwar_cost weights_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
