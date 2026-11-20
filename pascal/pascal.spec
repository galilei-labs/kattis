(** * Pascal *)

(** ** Description *)

(** Starting at $n - 1$ and counting downward, stop at the first divisor of $n$.
    Return the number of candidate integers examined, including that divisor.
    For $n = 1$, there are no candidates and the result is zero.

    [@kattis pascal]
    - Difficulty: 3.5
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1 \le n \le 10^{9}$. *)

(** ** Examples *)

(** - Input convention: A single positive integer n.
    - Output convention: The number of descending divisor candidates examined. *)
(* Input:
1
Output:
0
*)

(** ** [@hide] Environment *)
(* @function        pascal
   @signature       uint -> uint
   @math_signature  N -> N
   @summary         [pascal number] is what Frane's Pascal program prints on
                    input number: the counter after the loop "for i :=
                    number-1 downto 1, add one to the counter, stop as soon
                    as number mod i = 0".
                    It runs in at most c1 * (sqrt n + 1) + c2 steps of the
                    cost model (trial division up to sqrt n), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Run the descending divisor-search loop from [divisor], with initial [counter].
    Count each candidate examined and stop at the first divisor of [number], or
    after reaching one. *)
Fixpoint frane_loop (number : N) (divisor : nat)
  (counter : N) : N :=
  match divisor with
  | O => counter
  | S smaller =>
      let counter' := counter + 1 in
      if number mod N.of_nat divisor =? 0 then counter'
      else frane_loop number smaller counter'
  end.

(** The counter printed by the divisor search, starting at [number - 1] with counter
    zero. *)
Definition frane_output (number : N) : N :=
  frane_loop number (N.to_nat (number - 1)) 0.

(** [@inside pascal_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (number : N) : Prop := {
  (* The first and only line of input contains the
     integer 1 <= N <= 10^9. *)
  vi_n : 1 <= number <= 10 ^ 9;
}.

(** ** Correctness *)

(** [@requirement]
    The output counts descending candidate divisors from n - 1 through the first divisor
    of n; for n = 1, it is zero. *)
Definition pascal_spec (number : N) (output : N) : Prop :=
  output = frane_output number.

(** ** Complexity *)

(** [@requirement] Runs in $O(\sqrt{N}+1)$ steps, where $N$ is the input number. *)
Definition pascal_time_spec (c1 c2 n_number steps : nat) : Prop :=
  (steps <= c1 * (Nat.sqrt (n_number) + 1) + c2)%nat.

(** ** Interface *)

(** Starting at [number - 1], count down to the first divisor of [number].
    Return the number of candidates examined, including that divisor;
    return zero when [number] is one.
    - Input [number]: Positive integer whose descending divisor search is counted.
    - Output [output]: Number of candidates examined by this descending search, or zero when [number] is one. *)
Program pascal : uint -> uint.

(** [@example pascal]
    - Sample: 1
    - Input [number]: 1
    - Output [output]: 0
*)

(** ** Bridge *)

(** [@requirement pascal_spec] [@fold full correctness statement] On
    valid represented inputs, [pascal] returns a represented output
    satisfying [pascal_spec]. *)
Specification pascal_correct : forall (number : N)
  (number_int : uint),
  valid_input number -> repr number_int number ->
  exists output : N,
    repr (pascal number_int) output /\ pascal_spec number
      output.

(** ** Complexity *)

(** [@hide] [pascal_cost] is the cost translation of [pascal] (the judge
    recomputes it and compares) ... *)
Complexity pascal_cost for pascal.

(** [@fold complexity bound] ... and runs in at most c1 * (sqrt n + 1) + c2 steps of the cost model (trial division up to sqrt n), for two constants
    quantified before the input, on every valid input (the loop's test
    [p * p <=? n] is exact only while p * p fits a word: for n above
    3037000499^2 the accepted program overruns sqrt n). [@requirement pascal_time_spec] *)
Specification pascal_time : exists c1 c2 : nat,
  forall (number : N) (number_int : uint),
  valid_input number -> repr number_int number ->
  pascal_time_spec c1 c2 (size number_int) (cost1 pascal_cost number_int).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
