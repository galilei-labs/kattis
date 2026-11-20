(** * Interval Cover *)

(** ** Description *)

(** Find a smallest subset of given closed intervals whose union covers a
    target interval, or report that coverage is impossible.

    [@kattis intervalcover]
    - Difficulty: 4.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Interval count: $1 \le n \le 2 \times 10^{4}$; each left endpoint is no greater than its right
      endpoint.
    - Input coordinates have at most six digits after the decimal point. *)

(** ** Examples *)

(** - Input convention: Per case: target endpoints, interval count, then available interval endpoints.
    - Output convention: Minimum cover size and 0-based interval indices, or impossible if no cover exists. *)
(* Input:
-0.5 1
3
-0.9 -0.1
-0.2 2
-0.7 1
0 1
3
0 0.25
0.25 0.75
0.75 0.999
0 1
3
0 0.25
0.25 0.75
0.75 1
1 1
1
1 1
Output:
1
2
impossible
3
0 1 2
1
0
*)

(** ** [@hide] Environment *)
(* @function        cover
   @signature       float -> float -> array float -> array float
                    -> option (array uint)
   @math_signature  R -> R -> list R -> list R -> option (list N)
   @summary         [cover target_left target_right lefts rights] returns
                    the indices of a smallest selection of the intervals
                    [lefts_i, rights_i] whose union contains [target_left,
                    target_right], any one of them when several exist, or
                    None when no selection does ; the harness prints the
                    count then the indices, or "impossible"
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of intervals (the sort; the sweep is linear), for two
                    constants c1, c2.
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

(** The entry at zero-based index [i] in [endpoints], or zero beyond the end. *)
Definition get_list_R (endpoints : list R) (i : N) : R :=
  nth (N.to_nat i) endpoints 0%R.

(** The entry at zero-based index [k] in [chosen], or zero beyond the end. *)
Definition get_list_N (chosen : list N) (k : N) : N :=
  nth (N.to_nat k) chosen 0.

(** Every listed index is the index of an interval. *)
Definition indices_valid (lefts : list R)
  (chosen : list N) : Prop :=
  forall k, k < len chosen ->
    get_list_N chosen k < len lefts.

(** [point] lies between [low] and [high], inclusive. *)
Definition inside (low high point : R) : Prop :=
  (low <= point <= high)%R.

(** Every point between [target_left] and [target_right], inclusive, belongs to at
    least one listed interval. *)
Definition covers (target_left target_right : R)
  (lefts rights : list R)
    (chosen : list N) : Prop :=
  forall point : R, inside target_left target_right point ->
    exists k, k < len chosen /\
      inside (get_list_R lefts (get_list_N chosen k))
             (get_list_R rights (get_list_N chosen k))
               point.

(** [chosen] lists valid interval indices whose intervals cover the entire closed
    target interval. Repeated indices are not excluded by this predicate. *)
Definition covering (target_left target_right : R)
  (lefts rights : list R)
    (chosen : list N) : Prop :=
  indices_valid lefts chosen /\
  covers target_left target_right lefts rights chosen.

(** [@inside cover_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (target_left target_right : R)
  (lefts rights : list R)
    : Prop := {
  (* A <= B (target_left, target_right) *)
  vi_target : (target_left <= target_right)%R;
  (* 1 <= n <= 2 * 10^4 *)
  vi_length : 1 <= len lefts <= 2 * 10 ^ 4;
  (* one right endpoint per left endpoint *)
  vi_lengths : len rights = len lefts;
  (* a_i <= b_i (lefts, rights) *)
  vi_intervals : forall i, i < len lefts ->
    (get_list_R lefts i <= get_list_R rights i)%R;
  (* "at most 6 digits after the decimal point" : a
     property of the input text, gone once the harness
     parses it into binary64 (0.1 has no exact float), so
     it has no counterpart here. Nothing depends on it :
     the contract only compares the values, and parsing
     is monotone. *)
}.

(** ** Correctness *)

(** [@requirement]
    The output identifies a minimum-cardinality set of intervals covering the target
    interval, or None exactly when no cover exists. *)
Definition cover_spec (target_left target_right : R)
  (lefts rights : list R)
    (output : option (list N)) : Prop :=
  match output with
  | None =>
      forall chosen, ~ covering target_left target_right
        lefts rights chosen
  | Some chosen =>
      covering target_left target_right lefts rights chosen
        /\
      forall chosen',
        covering target_left target_right lefts rights
          chosen' ->
        len chosen <= len chosen'
  end.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of candidate intervals. *)
Definition cover_time_spec (c1 c2 n_lefts steps : nat) : Prop :=
  (steps <= c1 * ((n_lefts + 1) * (Nat.log2 (n_lefts) + 1)) + c2)%nat.

(** ** Interface *)

(** Find a smallest subset of given closed intervals whose union covers a target interval,
    or report that coverage is impossible.
    - Input [target_left]: Left endpoint of the interval to cover.
    - Input [target_right]: Right endpoint of the interval to cover.
    - Input [lefts]: Left endpoint of each available interval.
    - Input [rights]: Right endpoint of each available interval.
    - Output [output]: The output identifies a minimum-cardinality set of intervals covering the target interval, or None exactly when no cover exists. *)
Program cover :
  float -> float -> array float -> array float ->
    option (array uint).

(** [@example cover]
    - Sample: 1
    - Case: 1
    - Input [target_left]: fval (-0.5)%float
    - Input [target_right]: 1%R
    - Input [lefts]: [fval (-0.9)%float; fval (-0.2)%float; fval (-0.7)%float]
    - Input [rights]: [fval (-0.1)%float; 2; 1]%R
    - Output [output]: Some [2]
*)

(** [@example cover]
    - Sample: 1
    - Case: 2
    - Input [target_left]: 0%R
    - Input [target_right]: 1%R
    - Input [lefts]: [0; fval 0.25%float; fval 0.75%float]%R
    - Input [rights]: [fval 0.25%float; fval 0.75%float; fval 0.999%float]
    - Output [output]: None
*)

(** [@example cover]
    - Sample: 1
    - Case: 3
    - Input [target_left]: 0%R
    - Input [target_right]: 1%R
    - Input [lefts]: [0; fval 0.25%float; fval 0.75%float]%R
    - Input [rights]: [fval 0.25%float; fval 0.75%float; 1]%R
    - Output [output]: Some [0; 1; 2]
*)

(** [@example cover]
    - Sample: 1
    - Case: 4
    - Input [target_left]: 1%R
    - Input [target_right]: 1%R
    - Input [lefts]: [1]%R
    - Input [rights]: [1]%R
    - Output [output]: Some [0]
*)

(** ** Bridge *)

(** [@requirement cover_spec] [@fold full correctness statement] On
    valid represented inputs, [cover] returns a represented output
    satisfying [cover_spec]. *)
Specification cover_correct :
  forall (target_left target_right : R) (lefts rights : list
    R)
         (target_left_float target_right_float : float)
         (lefts_arr rights_arr : array float),
    valid_input target_left target_right lefts rights ->
    repr target_left_float target_left ->
    repr target_right_float target_right ->
    repr lefts_arr lefts -> repr rights_arr rights ->
    exists output : option (list N),
      repr (cover target_left_float target_right_float
        lefts_arr rights_arr)
        output /\
      cover_spec target_left target_right lefts rights
        output.

(** ** Complexity *)

(** [@hide] [cover_cost] is the cost translation of [cover] (the judge
    recomputes it and compares) ... *)
Complexity cover_cost for cover.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of intervals (the sort; the sweep is linear), for two constants
    quantified before the inputs, on every valid input. [@requirement cover_time_spec] *)
Specification cover_time : exists c1 c2 : nat,
  forall (target_left target_right : R) (lefts rights : list
  R)
  (target_left_float target_right_float : float)
  (lefts_arr rights_arr : array float),
  valid_input target_left target_right lefts rights ->
  repr target_left_float target_left ->
  repr target_right_float target_right ->
  repr lefts_arr lefts -> repr rights_arr rights ->
  cover_time_spec c1 c2 (size lefts_arr) (cost4 cover_cost target_left_float target_right_float lefts_arr rights_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
