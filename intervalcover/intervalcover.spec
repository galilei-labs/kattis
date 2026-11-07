(** * Interval Cover *)

(** ** Description *)

(** [cover target_left target_right lefts rights] returns the indices of
    a smallest selection of the intervals [lefts_i, rights_i] whose
    union contains [target_left, target_right], any one of them when
    several exist, or None when no selection does ; the harness
    prints the count then the indices, or "impossible". *)

(** [@kattis intervalcover]
    - Difficulty: 4.3
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB *)

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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. A float input is read as the real it denotes
    (repr_float), and the reals are compared exactly : this problem
    does no arithmetic on them, so there is no rounding and no
    tolerance. The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The i-th endpoint, for i < len endpoints (0 outside, never relied
    on). *)
Definition get_list_R (endpoints : list R) (i : N) : R :=
  nth (N.to_nat i) endpoints 0%R.

(** The k-th index listed in chosen, for k < len chosen (0 outside,
    never relied on). *)
Definition get_list_N (chosen : list N) (k : N) : N :=
  nth (N.to_nat k) chosen 0.

(** Every listed index is the index of an interval. *)
Definition indices_valid (lefts : list R)
  (chosen : list N) : Prop :=
  forall k, k < len chosen ->
    get_list_N chosen k < len lefts.

(** point lies in the closed interval [low, high]. *)
Definition inside (low high point : R) : Prop :=
  (low <= point <= high)%R.

(** Every point of [target_left, target_right] lies in one of the listed
    intervals. *)
Definition covers (target_left target_right : R)
  (lefts rights : list R)
    (chosen : list N) : Prop :=
  forall point : R, inside target_left target_right point ->
    exists k, k < len chosen /\
      inside (get_list_R lefts (get_list_N chosen k))
             (get_list_R rights (get_list_N chosen k))
               point.

(** chosen is a selection of intervals covering [target_left,
    target_right]. *)
Definition covering (target_left target_right : R)
  (lefts rights : list R)
    (chosen : list N) : Prop :=
  indices_valid lefts chosen /\
  covers target_left target_right lefts rights chosen.

(** [@inside cover_correct] The statement's bounds on one test case. *)
Record valid_input (target_left target_right : R)
  (lefts rights : list R)
    : Prop := {
  (* A <= B (target_left, target_right) *)
  vi_target : (target_left <= target_right)%R;
  (* 1 <= n <= 20 000 *)
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

(** [@requirement] [@short The answer : None when no selection covers
    [target_left, target_right],    otherwise a covering selection
    that none is shorter than.] The answer : None when no selection
    covers [target_left, target_right], otherwise a covering
    selection that none is shorter than. *)
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

(** ** Interface *)

(** The [cover] program on machine values.
    - Input [target_left]:
    - Input [target_right]:
    - Input [lefts]:
    - Input [rights]:
    - Output [output]: *)
Program cover :
  float -> float -> array float -> array float ->
    option (array uint).

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
