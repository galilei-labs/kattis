(** * Cudak *)

(** ** Description *)

(** Count integers in an inclusive interval with a specified decimal digit
    sum, and return the smallest such integer.

    [@kattis cudak]
    - Difficulty: 5.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Interval endpoints $a,b$: $1 \le a \le b < 10^{15}$.
    - Target digit sum in $[1, 135]$; at least one matching integer exists. *)

(** ** Examples *)

(** - Input convention: Lower bound, upper bound and required decimal digit sum.
    - Output convention: The qualifying count on the first line and smallest qualifying integer on the second. *)
(* Input:
1 9 5
Output:
1
5
*)

(** ** [@hide] Environment *)

(* @function        cudak
   @signature       uint -> uint -> uint -> uint * uint
   @math_signature  N -> N -> N -> N * N
   @summary         [cudak lower_bound upper_bound target_sum] answers
                    Bozo's two questions on the interval
                    [lower_bound, upper_bound]: how many integers x with
                    lower_bound <= x <= upper_bound have decimal digit sum
                    target_sum, and which is the smallest of them.  The
                    answer is the pair (count, smallest); the input
                    guarantees that at least one such integer exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** [digit_sum number total]: the decimal digits of
    number add up to total (the last digit is number mod
    10, the others are those of number / 10; 0 has digit
    sum 0). *)
Inductive digit_sum : N -> N -> Prop :=
| digit_sum_zero : digit_sum 0 0
| digit_sum_step : forall number total,
    0 < number -> digit_sum (number / 10) total ->
    digit_sum number (number mod 10 + total).

(** candidate is one of the integers Bozo asks about: in
    [lower_bound, upper_bound], digit sum target_sum. *)
Definition qualifies
  (lower_bound upper_bound target_sum candidate : N)
    : Prop :=
  lower_bound <= candidate <= upper_bound
    /\ digit_sum candidate target_sum.

(** Exactly amount integers satisfy property: they form
    a duplicate-free list of length amount. *)
Definition count_is (property : N -> Prop)
  (amount : N) : Prop :=
  exists witnesses : list N, NoDup witnesses /\
    (forall value, In value witnesses <-> property value) /\
    len witnesses = amount.

(** [@inside cudak_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (lower_bound upper_bound target_sum : N) : Prop := {
  (* 1 <= A <= B < 10^15 *)
  vi_a : 1 <= lower_bound <= upper_bound;
  vi_b : upper_bound < 10 ^ 15;
  (* 1 <= S <= 135 *)
  vi_s : 1 <= target_sum <= 135;
  (* the input data will guarantee that the first number
    (the count) is
     at least 1 *)
  vi_exists : exists candidate,
    qualifies lower_bound upper_bound target_sum candidate;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the number of integers in the inclusive interval with the required
    digit sum and the smallest such integer. *)
Definition cudak_spec
  (lower_bound upper_bound target_sum : N)
    (output : N * N) : Prop :=
  match output with
  | (match_count, smallest) =>
      count_is (qualifies lower_bound upper_bound
        target_sum) match_count /\
      qualifies lower_bound upper_bound target_sum smallest
        /\
      (forall candidate,
         qualifies lower_bound upper_bound target_sum
           candidate ->
         smallest <= candidate)
  end.

(** ** Interface *)

(** Count integers in an inclusive interval with a specified decimal digit sum, and return
    the smallest such integer.
    - Input [lower_bound]: Inclusive lower endpoint of the integer interval.
    - Input [upper_bound]: Inclusive upper endpoint of the integer interval.
    - Input [target_sum]: Required sum of decimal digits.
    - Output [output]: The output gives the number of integers in the inclusive interval with the required digit sum and the smallest such integer. *)
Program cudak : uint -> uint -> uint -> uint * uint.

(** ** Bridge *)

(** [@requirement cudak_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [cudak_spec]. *)
Specification cudak_correct :
  forall (lower_bound upper_bound target_sum : N)
         (lower_bound_int upper_bound_int target_sum_int :
           uint),
  valid_input lower_bound upper_bound target_sum ->
  repr lower_bound_int lower_bound
    -> repr upper_bound_int upper_bound ->
  repr target_sum_int target_sum ->
  exists output : N * N,
    repr (cudak lower_bound_int upper_bound_int
      target_sum_int)
      output /\
    cudak_spec lower_bound upper_bound target_sum output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
