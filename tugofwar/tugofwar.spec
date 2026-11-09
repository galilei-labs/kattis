(** * Tug of War *)

(** ** Description *)

(** Partition a sequence of weights into two groups whose sizes differ by at
    most one, minimizing the difference between their total weights.

    [@kattis tugofwar]
    - Difficulty: 5.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Weight count: $1 \le n \le 100$, each an integer in $[1, 450]$. *)

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
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. Person k has weight weights_k; a division
   into two teams is a list assignment of booleans,
   assignment_k telling whether person k is on the first
   team. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The [sum] of the elements of l. *)
Definition sum (l : list N) : N := fold_right N.add 0 l.

(** The [weights] of the people that assignment puts on
    the first [team]. *)
Definition team (weights : list N) (assignment : list bool)
  : list N :=
  map fst (filter snd (combine weights assignment)).

(** The [weights] of the people on the other [team]. *)
Definition other_team (weights : list N)
  (assignment : list bool)
  : list N :=
  team weights (map negb assignment).

(** assignment puts each person on one [team] or the
    other, and the numbers of people on the two teams do
    not differ by more than 1. *)
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
    The output gives the group totals in ascending order for a partition whose group
    sizes differ by at most one and whose total-weight difference is minimal. *)
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

(** ** Interface *)

(** Partition a sequence of weights into two groups whose sizes differ by at most one,
    minimizing the difference between their total weights.
    - Input [weights]: Weights to partition into two balanced groups.
    - Output [output]: The output gives the group totals in ascending order for a partition whose group sizes differ by at most one and whose total-weight difference is minimal. *)
Program tugofwar : array uint -> uint * uint.

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

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
