(** * Median *)

(** ** Description *)

(** [median values] is the median of the n >= 1 integers of values: once
    they are sorted, the middle one when n is odd, the mean of the
    two middle ones when n is even. The float returned denotes
    exactly that number (an integer or an integer plus one half); no
    tolerance. *)

(** [@kattis median]
    - Difficulty: 2.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB *)

(** ** Examples *)

(** Kattis sample: text input and output. *)
(* 7
5 4 3 1 6 7 2 = 4 *)

(** Kattis sample: text input and output. *)
(* 4
1 3 7 7 = 5 *)

(** ** [@hide] Environment *)
(* @function        median
   @signature       array uint -> float
   @math_signature  list N -> R
   @summary         [median values] is the median of the n >= 1 integers of
                    values: once they are sorted, the middle one when n is
                    odd, the mean of the two middle ones when n is even.  The
                    float returned denotes exactly that number (an integer or
                    an integer plus one half); no tolerance.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Stdlib Require Import Sorted Permutation.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The input is the list of the n integers, in input order.
    The output is a float because the mean of two integers need not
    be an integer (it is the real it denotes, exactly). The number
    of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The element at 0-based position k of l, as a real (0 outside, never
    relied on). *)
Definition elem (l : list N) (k : N) : R :=
  IZR (Z.of_N (nth (N.to_nat k) l 0)).

(** The median of a sorted list of value_count numbers: its element at
    0-based position value_count / 2 when value_count is odd, the
    mean of its elements at value_count / 2 - 1 and value_count / 2
    when value_count is even. *)
Definition median_of_sorted (sorted_values : list N) : R :=
  let value_count := len sorted_values in
  if N.odd value_count then elem sorted_values (value_count
    / 2)
  else ((elem sorted_values (value_count / 2 - 1)
         + elem sorted_values (value_count / 2)) / 2)%R.

(** [@inside median_correct] The statement's bounds. *)
Record valid_input (values : list N) : Prop := {
  (* a single integer, n, where 1 <= n <= 10^5 *)
  vi_n : 1 <= len values <= 10 ^ 5;
  (* each integer is between 0 and 10^9 (inclusive) *)
  vi_a : Forall (fun number => number <= 10 ^ 9) values;
}.

(** ** Correctness *)

(** [@requirement] [@short The answer: the median of the input once
    sorted (the sorted    rearrangement of the input exists and is
    unique).] The answer: the median of the input once sorted (the
    sorted rearrangement of the input exists and is unique). *)
Definition median_spec (values : list N)
  (output : R) : Prop :=
  forall sorted_values, Permutation values sorted_values ->
    Sorted N.le sorted_values ->
      output = median_of_sorted sorted_values.

(** ** Interface *)

(** The [median] program on machine values.
    - Input [values]:
    - Output [output]: *)
Program median : array uint -> float.

(** ** Bridge *)

(** [@requirement median_spec] [@fold full correctness statement] On
    valid represented inputs, [median] returns a represented output
    satisfying [median_spec]. *)
Specification median_correct :
  forall (values : list N) (values_arr : array uint),
  valid_input values -> repr values_arr values ->
  exists output : R,
    repr (median values_arr) output /\ median_spec values
      output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
