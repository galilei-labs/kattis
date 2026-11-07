(* @function        bigfactoring
   @signature       Z -> array Z
   @math_signature  Z -> list Z
   @summary         [bigfactoring number] returns the prime factors of
                    number in ascending order, each one repeated as many
                    times as it occurs in number: a sorted list of primes
                    whose product is number.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Znumtheory Sorted.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Z in the signature, on both sides: number goes up to 10^24 (about 2^80),
   and so does a prime factor (number itself may be prime).  A bignum
   represents the integer it is. *)
Instance repr_Z : Repr Z Z := fun bignum value => bignum = value.

(* Math side. *)

(* The product of the elements of factors; 1 for the empty list. *)
Definition product (factors : list Z) : Z := fold_right Z.mul 1 factors.

(* The statement's bounds. *)
Record valid_input (number : Z) : Prop := {
  (* a positive integer 2 <= n <= 10^24 *)
  vi_n : 2 <= number <= 10 ^ 24;
}.

(* The prime factors of number, in ascending order, a factor occurring k
   times in number listed k times: every element is prime, the list is
   sorted, and the product is number.  By unique factorisation, exactly one
   list qualifies. *)
Definition bigfactoring_spec (number : Z) (output : list Z) : Prop :=
  Forall prime output /\ Sorted Z.le output /\
  product output = number.

(* machine side: the only thing that gets extracted *)
Program bigfactoring : Z -> array Z.

(* the one line: repr on the input (universal), repr on the output
   (existential) *)
Specification bigfactoring_correct : forall (number : Z) (number_int : Z),
  valid_input number -> repr number_int number ->
  exists output : list Z,
    repr (bigfactoring number_int) output /\
    bigfactoring_spec number output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
