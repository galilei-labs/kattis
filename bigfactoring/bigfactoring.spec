(** * Big Factoring *)

(** ** Description *)

(** Factor an integer into primes, listed in ascending order with
    multiplicity.

    [@kattis bigfactoring]
    - Difficulty: 7.2
    - CPU time limit: 4 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Integer in $[2, 10^{24}]$. *)

(** ** Examples *)

(** - Input convention: A single positive integer to factor.
    - Output convention: Prime factors in ascending order, including repeated factors. *)
(* Input:
166448
Output:
2 2 2 2 101 103
*)

(** ** [@hide] Environment *)

(* @function        bigfactoring
   @signature       Z -> array Z
   @math_signature  Z -> list Z
   @summary         [bigfactoring number] returns the prime factors of
                    number in ascending order, each one repeated as many
                    times as it occurs in number: a sorted list of primes
                    whose product is number.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Znumtheory Sorted.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** [@hide] Z in the signature, on both sides: number
    goes up to 10^24 (about 2^80), and so does a prime
    factor (number itself may be prime). A bignum
    represents the integer it is. *)
Instance repr_Z : Repr Z Z :=
  fun bignum value => bignum = value.

(* Math side. *)

(** The product of the elements of factors; 1 for the
    empty list. *)
Definition product (factors : list Z) : Z :=
  fold_right Z.mul 1 factors.

(** [@inside bigfactoring_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (number : Z) : Prop := {
  (* a positive integer 2 <= n <= 10^24 *)
  vi_n : 2 <= number <= 10 ^ 24;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the ascending list of prime factors whose product equals the input,
    including multiplicities. *)
Definition bigfactoring_spec (number : Z)
  (output : list Z) : Prop :=
  Forall prime output /\ Sorted Z.le output /\
  product output = number.

(** ** Interface *)

(** Factor an integer into primes, listed in ascending order with multiplicity.
    - Input [number]: Positive integer to factor into primes.
    - Output [output]: The output is the ascending list of prime factors whose product equals the input, including multiplicities. *)
Program bigfactoring : Z -> array Z.

(** ** Bridge *)

(** [@requirement bigfactoring_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [bigfactoring_spec]. *)
Specification bigfactoring_correct : forall (number : Z)
  (number_int : Z),
  valid_input number -> repr number_int number ->
  exists output : list Z,
    repr (bigfactoring number_int) output /\
    bigfactoring_spec number output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
