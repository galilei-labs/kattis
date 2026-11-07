(* @function        primepower
   @signature       uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N
   @summary         [primepower exponent low high] returns the product of
                    prime^exponent over all primes with
                    low <= prime <= high, reduced modulo 10^9 + 7.  The
                    three arguments are the three integers of the input, in
                    the order E, L, R; the result is the integer printed.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Znumtheory.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The modulus of the output, 10^9 + 7. *)
Definition modulus : N := 1000000007.

(* The product of prime^exponent over the primes of
   [start, start + remaining - 1] (1 when there are none). *)
Fixpoint prime_power_product_from (exponent start : N) (remaining : nat)
    : N :=
  match remaining with
  | O => 1
  | S remaining' =>
      (if prime_dec (Z.of_N start) then start ^ exponent else 1)
      * prime_power_product_from exponent (start + 1) remaining'
  end.

(* The product of prime^exponent over the primes with
   low <= prime <= high. *)
Definition prime_power_product (exponent low high : N) : N :=
  prime_power_product_from exponent low (N.to_nat (high + 1 - low)).

(* The statement's bounds. *)
Record valid_input (exponent low high : N) : Prop := {
  (* E (1 <= E <= 1,000,000) *)
  vi_e : 1 <= exponent <= 10 ^ 6;
  (* L and R (1 <= L <= R <= 1,000,000) *)
  vi_l : 1 <= low;
  vi_lr : low <= high;
  vi_r : high <= 10 ^ 6;
}.

(* The answer: the product modulo 10^9 + 7. *)
Definition primepower_spec (exponent low high : N) (output : N) : Prop :=
  output = prime_power_product exponent low high mod modulus.

Program primepower : uint -> uint -> uint -> uint.

Specification primepower_correct :
  forall (exponent low high : N) (exponent_int low_int high_int : uint),
  valid_input exponent low high ->
  repr exponent_int exponent -> repr low_int low -> repr high_int high ->
  exists output : N,
    repr (primepower exponent_int low_int high_int) output /\
    primepower_spec exponent low high output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
