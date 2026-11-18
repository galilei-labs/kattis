(** * Prime Powers *)

(** ** Description *)

(** For every prime $p$ in the inclusive interval from $L$ to $R$, take
    $p^E$. Return the product of these powers modulo $10^{9} + 7$.

    [@kattis primepower]
    - Difficulty: 4.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Exponent: $1 \le E \le 10^{6}$.
    - Interval endpoints: $1 \le L \le R \le 10^{6}$. *)

(** ** Examples *)

(** - Input convention: Exponent E and interval endpoints L and R, each on a separate line.
    - Output convention: The product of the prime powers modulo $10^9 + 7$. *)
(* Input:
3
6
10
Output:
343
*)

(** ** [@hide] Environment *)

(* @function        primepower
   @signature       uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N
   @summary         [primepower exponent low high] returns the product of
                    prime^exponent over all primes with
                    low <= prime <= high, reduced modulo 10^9 + 7.  The
                    three arguments are the three integers of the input, in
                    the order E, L, R; the result is the integer printed.
                    It runs in at most c1 * (R + 1) * (log2 R + log2 E + 1)
                    + c2 steps of the cost model on a valid input, R the
                    upper end of the range and E the exponent (the sieve up
                    to R, then one modular exponentiation per prime), for
                    two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Znumtheory.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The modulus used for the result, $10^9 + 7$. *)
Definition modulus : N := 1000000007.

(** Among the [remaining] consecutive integers beginning at [start], raise each
    prime to [exponent] and multiply the results. If none of these integers is
    prime, including when [remaining] is zero, the product is one. *)
Fixpoint prime_power_product_from (exponent start : N)
  (remaining : nat)
    : N :=
  match remaining with
  | O => 1
  | S remaining' =>
      (if prime_dec (Z.of_N start) then start ^ exponent
        else 1)
      * prime_power_product_from exponent (start + 1)
        remaining'
  end.

(** The product of $p^{\mathit{exponent}}$ over primes $p$ from [low] through
    [high], inclusive. *)
Definition prime_power_product (exponent low high : N) : N
  :=
  prime_power_product_from exponent low
    (N.to_nat (high + 1 - low)).

(** [@inside primepower_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (exponent low high : N) : Prop := {
  (* E (1 <= E <= 10^6) *)
  vi_e : 1 <= exponent <= 10 ^ 6;
  (* L and R (1 <= L <= R <= 10^6) *)
  vi_l : 1 <= low;
  vi_lr : low <= high;
  vi_r : high <= 10 ^ 6;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the product of the specified power of every prime in the inclusive
    interval, modulo $10^9 + 7$. *)
Definition primepower_spec
  (exponent low high : N)
  (output : N)
  : Prop :=
  output = prime_power_product exponent low high mod
    modulus.

(** ** Complexity *)

(** [@requirement] Runs in $O((H+1)(\log(H+2)+\log(k+2)))$ steps, where $H$ is the upper bound and $k$ the exponent. *)
Definition primepower_time_spec (c1 c2 n_high n_exponent steps : nat) : Prop :=
  (steps <= c1 * ((n_high + 1) * (Nat.log2 (n_high) + Nat.log2 (n_exponent) + 1)) + c2)%nat.

(** ** Interface *)

(** Raise every prime from [low] through [high], inclusive, to [exponent],
    multiply the results, and reduce modulo $10^9 + 7$.
    - Input [exponent]: Power applied to each prime.
    - Input [low]: Inclusive lower endpoint of the prime interval.
    - Input [high]: Inclusive upper endpoint of the prime interval.
    - Output [output]: The output is the product of the specified power of every prime in the inclusive interval, modulo $10^9 + 7$. *)
Program primepower : uint -> uint -> uint -> uint.

(** [@example primepower]
    - Sample: 1
    - Input [exponent]: 3
    - Input [low]: 6
    - Input [high]: 10
    - Output [output]: 343
*)

(** ** Bridge *)

(** [@requirement primepower_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [primepower_spec]. *)
Specification primepower_correct :
  forall (exponent low high : N) (exponent_int low_int
    high_int : uint),
  valid_input exponent low high ->
  repr exponent_int exponent -> repr low_int low -> repr
    high_int high ->
  exists output : N,
    repr (primepower exponent_int low_int high_int) output
      /\
    primepower_spec exponent low high output.

(** ** Complexity *)

(** [@hide] [primepower_cost] is the cost translation of [primepower] (the judge
    recomputes it and compares) ... *)
Complexity primepower_cost for primepower.

(** [@fold complexity bound] ... and runs in at most c1 * (R + 1) * (log2 R + log2 E + 1) + c2 steps of the cost model on a valid input, R the upper end of the range and E the exponent (the sieve up to R, then one modular exponentiation per prime), for two constants
    quantified before the inputs, on every valid input. [@requirement primepower_time_spec] *)
Specification primepower_time : exists c1 c2 : nat,
  forall (exponent low high : N) (exponent_int low_int
  high_int : uint),
  valid_input exponent low high ->
  repr exponent_int exponent -> repr low_int low -> repr
  high_int high ->
  primepower_time_spec c1 c2 (size high_int) (size exponent_int) (cost3 primepower_cost exponent_int low_int high_int).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
