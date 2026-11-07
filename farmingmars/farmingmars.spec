(** * Farming Mars *)

(** ** Description *)

(** For each interval of a sequence, decide whether one value occurs in
    strictly more than half its positions.

    [@kattis farmingmars]
    - Difficulty: 5.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 10000 values and 1 to 10000 queries.
    - Values from 0 to 14; each query is a nonempty interval within the
      sequence. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
8 4
7.000000
8.314634
7.000001
7.000000
2.581236
7.000000
2.581236
7.000000
1 8
1 3
4 8
5 7
Output:
unusable
unusable
usable
usable
*)

(** ** [@hide] Environment *)
(* @function        farmingmars
   @signature       array float -> array uint -> array uint -> array bool
   @math_signature  list R -> list N -> list N -> list bool
   @summary         [farmingmars ph_values left_ends right_ends] answers the
                    m queries [left_ends_j, right_ends_j] (acres numbered
                    from 1, both ends included) on the strip whose acre i
                    has pH ph_values_i: answer j is true ("usable") exactly
                    when some pH value is shared by a strict majority,
                    floor((r-l+1)/2) + 1, of the acres l..r, and false
                    ("unusable") otherwise. pH values are compared exactly,
                    as the reals they denote.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The pH of an acre is the real its float denotes; the
    queries are two parallel lists, one per column of the lines "l
    r". The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of values, for k < len values (0 outside, never
    relied on). *)
Definition get_list_N (values : list N) (k : N) : N :=
  nth (N.to_nat k) values 0.

(** The acres first_acre..last_acre of the strip, acres numbered from 1. *)
Definition acres (ph_values : list R)
  (first_acre last_acre : N) : list R :=
  firstn (N.to_nat (last_acre - first_acre + 1))
    (skipn (N.to_nat (first_acre - 1)) ph_values).

(** The number of acres of the list whose pH is exactly target. *)
Definition count_ph (target : R) (acre_phs : list R) : N :=
  len (filter (fun acre_ph => if Req_EM_T acre_ph target
    then true else false)
         acre_phs).

(** Some pH value is shared by a strict majority
    floor((last_acre-first_acre+1)/2) + 1 of the acres
    first_acre..last_acre. *)
Definition usable (ph_values : list R)
  (first_acre last_acre : N) : Prop :=
  exists shared_ph : R,
    (last_acre - first_acre + 1) / 2 + 1 <=
    count_ph shared_ph (acres ph_values first_acre
      last_acre).

(** [@inside farmingmars_correct] The statement's bounds. "Exactly six
    decimal digits" is a property of the input text, gone once
    parsed: the contract is exact on the reals the parsed floats
    denote. *)
Record valid_input (ph_values : list R)
  (left_ends right_ends : list N)
    : Prop := {
  (* 1 <= n <= 10 000: the size of the strip of land *)
  vi_n : 1 <= len ph_values <= 10000;
  (* 1 <= m <= 10 000: the number of queries *)
  vi_m : 1 <= len left_ends <= 10000;
  (* m lines containing two space-separated integers each *)
  vi_rs : len right_ends = len left_ends;
  (* Each pH value lies between 0.000000 and 14.000000,
     inclusive *)
  vi_ph : Forall (fun ph => (0 <= ph <= 14)%R) ph_values;
  (* 1 <= l_j <= r_j <= n *)
  vi_lr : forall j, j < len left_ends ->
    1 <= get_list_N left_ends j <= get_list_N right_ends j
      /\
    get_list_N right_ends j <= len ph_values;
}.

(** ** Correctness *)

(** [@requirement] [@short One answer per query, in query order: true
    iff the interval is usable.] One answer per query, in query
    order: true iff the interval is usable. *)
Definition farmingmars_spec (ph_values : list R)
  (left_ends right_ends
    : list N) (output : list bool) : Prop :=
  len output = len left_ends /\
  forall j, j < len left_ends ->
    (nth (N.to_nat j) output false = true <->
     usable ph_values (get_list_N left_ends j) (get_list_N
       right_ends j)).

(** ** Interface *)

(** The [farmingmars] program on machine values.
    - Input [ph_values]:
    - Input [left_ends]:
    - Input [right_ends]:
    - Output [output]: *)
Program farmingmars : array float -> array uint -> array
  uint -> array bool.

(** ** Bridge *)

(** [@requirement farmingmars_spec] [@fold full correctness statement]
    On valid represented inputs, [farmingmars] returns a represented
    output satisfying [farmingmars_spec]. *)
Specification farmingmars_correct :
  forall (ph_values : list R) (left_ends right_ends : list
    N)
         (ph_values_arr : array float)
         (left_ends_arr right_ends_arr : array uint),
    valid_input ph_values left_ends right_ends ->
    repr ph_values_arr ph_values ->
      repr left_ends_arr left_ends ->
    repr right_ends_arr right_ends ->
    exists output : list bool,
      repr (farmingmars ph_values_arr left_ends_arr
        right_ends_arr)
        output /\
      farmingmars_spec ph_values left_ends right_ends
        output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
