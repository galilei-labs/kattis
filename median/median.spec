(** * Median *)

(** ** Description *)

(** Compute the median of an integer sequence, averaging the two middle
    values when its length is even.

    [@kattis median]
    - Difficulty: 2.8
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Sequence length: $1 \le n \le 10^{5}$; each value: $0 \le a_i \le 10^{9}$. *)

(** ** Examples *)

(** - Input convention: Sequence length, followed by space-separated integer values.
    - Output convention: The median, averaging the two middle values for an even-length sequence. *)
(* Input:
7
5 4 3 1 6 7 2
Output:
4
*)

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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], embedded in the real numbers, or zero
    beyond the end. *)
Definition elem (l : list N) (k : N) : R :=
  IZR (Z.of_N (nth (N.to_nat k) l 0)).

(** The median of [sorted_values]: the middle entry for an odd length, or the mean
    of the two middle entries for an even length. *)
Definition median_of_sorted (sorted_values : list N) : R :=
  let value_count := len sorted_values in
  if N.odd value_count then elem sorted_values (value_count
    / 2)
  else ((elem sorted_values (value_count / 2 - 1)
         + elem sorted_values (value_count / 2)) / 2)%R.

(** [@inside median_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (values : list N) : Prop := {
  (* a single integer, n, where 1 <= n <= 10^5 *)
  vi_n : 1 <= len values <= 10 ^ 5;
  (* each integer is between 0 and 10^9 (inclusive) *)
  vi_a : Forall (fun number => number <= 10 ^ 9) values;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the exact median of the input values, averaging the two middle values
    when the sequence length is even. *)
Definition median_spec (values : list N)
  (output : R) : Prop :=
  forall sorted_values, Permutation values sorted_values ->
    Sorted N.le sorted_values ->
      output = median_of_sorted sorted_values.

(** ** Interface *)

(** Compute the median of an integer sequence, averaging the two middle values when its
    length is even.
    - Input [values]: Integer values whose median is required.
    - Output [output]: The output is the exact median of the input values, averaging the two middle values when the sequence length is even. *)
Program median : array uint -> float.

(** [@example median]
    - Sample: 1
    - Input [values]: [5; 4; 3; 1; 6; 7; 2]
    - Output [output]: 4%R
*)

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
