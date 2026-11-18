(** * Farming Mars *)

(** ** Description *)

(** A Martian colony has a strip of farmland with a measured soil pH for
    each acre. A potato variety thrives at one specific pH, and developing
    it is worthwhile only if strictly more than half the acres in a proposed
    planting interval share that exact pH. For each queried interval, decide
    whether such a majority pH exists. Matching acres need not be consecutive.

    [@kattis farmingmars]
    - Difficulty: 5.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Value count: $1 \le n \le 10^{4}$ and Query count: $1 \le q \le 10^{4}$.
    - Values: $0 \le a_i \le 14$; each query is a nonempty interval within the
      sequence. *)

(** ** Examples *)

(** - Input convention: Value and query counts, one decimal value per line, then inclusive 1-based query intervals.
    - Output convention: usable if the interval has a strict majority value; unusable otherwise. *)
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
                    It runs in at most c1 * (n + m + 1) * (sqrt n + log2 (n
                    + m) + 1) + c2 steps of the cost model on a valid input,
                    n the number of acres and m of queries (the sorts, then
                    Mo's order: the window ends travel (n + m) sqrt n cells
                    in all), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [values], or zero beyond the end. *)
Definition get_list_N (values : list N) (k : N) : N :=
  nth (N.to_nat k) values 0.

(** The pH values from one-based acre [first_acre] through [last_acre], inclusive. *)
Definition acres (ph_values : list R)
  (first_acre last_acre : N) : list R :=
  firstn (N.to_nat (last_acre - first_acre + 1))
    (skipn (N.to_nat (first_acre - 1)) ph_values).

(** The number of listed acres whose pH equals [target]. *)
Definition count_ph (target : R) (acre_phs : list R) : N :=
  len (filter (fun acre_ph => if Req_EM_T acre_ph target
    then true else false)
         acre_phs).

(** Some pH value occurs in strictly more than half of the acres from [first_acre]
    through [last_acre], inclusive. *)
Definition usable (ph_values : list R)
  (first_acre last_acre : N) : Prop :=
  exists shared_ph : R,
    (last_acre - first_acre + 1) / 2 + 1 <=
    count_ph shared_ph (acres ph_values first_acre
      last_acre).

(** [@inside farmingmars_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (ph_values : list R)
  (left_ends right_ends : list N)
    : Prop := {
  (* 1 <= n <= 10^4: the size of the strip of land *)
  vi_n : 1 <= len ph_values <= 10000;
  (* 1 <= m <= 10^4: the number of queries *)
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

(** [@requirement]
    Each output entry is true exactly when strictly more than half the acres
    in the corresponding inclusive interval share the same pH. *)
Definition farmingmars_spec (ph_values : list R)
  (left_ends right_ends
    : list N) (output : list bool) : Prop :=
  len output = len left_ends /\
  forall j, j < len left_ends ->
    (nth (N.to_nat j) output false = true <->
     usable ph_values (get_list_N left_ends j) (get_list_N
       right_ends j)).

(** ** Complexity *)

(** [@requirement] Runs in $O((n+q+1)(\sqrt{n}+\log(n+q+2)))$ steps, where $n$ is the number of pH values and $q$ the number of interval queries. *)
Definition farmingmars_time_spec (c1 c2 n_ph_values n_left_ends steps : nat) : Prop :=
  (steps <= c1 * ((n_ph_values + n_left_ends + 1) * (Nat.sqrt (n_ph_values) + Nat.log2 (n_ph_values + n_left_ends) + 1)) + c2)%nat.

(** ** Interface *)

(** Decide whether each proposed planting interval has a pH shared by
    strictly more than half its acres.
    - Input [ph_values]: Soil pH measurements in acre order along the strip.
    - Input [left_ends]: Inclusive one-based first acre of each query.
    - Input [right_ends]: Inclusive one-based last acre of each query.
    - Output [output]: One Boolean per query, true exactly when a strict majority of its acres have the same pH. *)
Program farmingmars : array float -> array uint -> array
  uint -> array bool.

(** [@example farmingmars]
    - Sample: 1
    - Input [ph_values]: [7; fval 8.314634%float; fval 7.000001%float; 7; fval 2.581236%float; 7; fval 2.581236%float; 7]%R
    - Input [left_ends]: [1; 1; 4; 5]
    - Input [right_ends]: [8; 3; 8; 7]
    - Output [output]: [false; false; true; true]
*)

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

(** ** Complexity *)

(** [@hide] [farmingmars_cost] is the cost translation of [farmingmars] (the judge
    recomputes it and compares) ... *)
Complexity farmingmars_cost for farmingmars.

(** [@fold complexity bound] ... and runs in at most c1 * (n + m + 1) * (sqrt n + log2 (n + m) + 1) + c2 steps of the cost model on a valid input, n the number of acres and m of queries (the sorts, then Mo's order: the window ends travel (n + m) sqrt n cells in all), for two constants
    quantified before the inputs, on every valid input. [@requirement farmingmars_time_spec] *)
Specification farmingmars_time : exists c1 c2 : nat,
  forall (ph_values : list R) (left_ends right_ends : list
  N)
  (ph_values_arr : array float)
  (left_ends_arr right_ends_arr : array uint),
  valid_input ph_values left_ends right_ends ->
  repr ph_values_arr ph_values ->
  repr left_ends_arr left_ends ->
  repr right_ends_arr right_ends ->
  farmingmars_time_spec c1 c2 (size ph_values_arr) (size left_ends_arr) (cost3 farmingmars_cost ph_values_arr left_ends_arr right_ends_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
