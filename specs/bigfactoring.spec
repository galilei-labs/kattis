(* @function        bigfactoring
   @signature       Z -> array Z
   @math_signature  Z -> list Z
   @summary         [bigfactoring n] returns the prime factors of n in
                    ascending order, each one repeated as many times as it
                    occurs in n: a sorted list of primes whose product is n.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Znumtheory Sorted.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Z in the signature, on both sides: n goes up to 10^24 (about 2^80), and
   so does a prime factor (n itself may be prime).  A bignum represents the
   integer it is. *)
Instance repr_Z : Repr Z Z := fun x i => x = i.

(* Math side. *)

(* The product of the elements of l; 1 for the empty list. *)
Definition product (l : list Z) : Z := fold_right Z.mul 1 l.

(* The statement's bounds. *)
Record valid_input (n : Z) : Prop := {
  (* a positive integer 2 <= n <= 10^24 *)
  vi_n : 2 <= n <= 10 ^ 24;
}.

(* The prime factors of n, in ascending order, a factor occurring k times
   in n listed k times: every element is prime, the list is sorted, and
   the product is n.  By unique factorisation, exactly one list qualifies. *)
Definition bigfactoring_spec (n : Z) (fs : list Z) : Prop :=
  Forall prime fs /\ Sorted Z.le fs /\ product fs = n.

(* machine side: the only thing that gets extracted *)
Program bigfactoring : Z -> array Z.

(* the one line: repr on the input (universal), repr on the output
   (existential) *)
Specification bigfactoring_correct : forall (n : Z) (x : Z),
  valid_input n -> repr x n ->
  exists fs : list Z, repr (bigfactoring x) fs /\ bigfactoring_spec n fs.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
