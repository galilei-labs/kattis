(** * Prime Powers *)

(** ** Description *)

(** Compute the product of p^E over all primes p in a given inclusive
    interval, modulo 1000000007.

    [@kattis primepower]
    - Difficulty: 4.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Exponent: $1 \le E \le 10^6$.
    - Interval endpoints: $1 \le L \le R \le 10^6$. *)

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
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Znumtheory.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(** ** Definitions *)

(** The [modulus] of the [output], 10^9 + 7. *)
Definition modulus : N := 1000000007.

(** The product of prime^[exponent] over the primes of
    [start, start + remaining - 1] (1 when there are
    none). *)
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

(** The product of prime^[exponent] over the primes with
    [low] <= prime <= [high]. *)
Definition prime_power_product (exponent low high : N) : N
  :=
  prime_power_product_from exponent low
    (N.to_nat (high + 1 - low)).

(** [@inside primepower_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (exponent low high : N) : Prop := {
  (* E (1 <= E <= 1,000,000) *)
  vi_e : 1 <= exponent <= 10 ^ 6;
  (* L and R (1 <= L <= R <= 1,000,000) *)
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

(** ** Interface *)

(** Compute the product of p^E over all primes p in a given inclusive interval, modulo
    1000000007.
    - Input [exponent]: Power applied to each prime.
    - Input [low]: Inclusive lower endpoint of the prime interval.
    - Input [high]: Inclusive upper endpoint of the prime interval.
    - Output [output]: The output is the product of the specified power of every prime in the inclusive interval, modulo $10^9 + 7$. *)
Program primepower : uint -> uint -> uint -> uint.

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

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
