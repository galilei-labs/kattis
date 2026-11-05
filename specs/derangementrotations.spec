(* @function        derangement_rotations
   @signature       uint -> uint -> uint
   @math_signature  N -> N -> N
   @summary         [derangement_rotations n p] is, modulo the prime p, the
                    number of derangements D of {1, ..., n} such that exactly
                    n - 2 of the distinct rotations of D are again
                    derangements.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Permutation Znumtheory.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A sequence a_1, ..., a_n is a list, position i (from 0)
   holding a_(i+1). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The list 1, 2, ..., n. *)
Definition iota (n : N) : list N := map N.of_nat (List.seq 1 (N.to_nat n)).

(* l is a permutation of {1, 2, ..., n}. *)
Definition is_perm (n : N) (l : list N) : Prop := Permutation l (iota n).

(* A permutation of {1, ..., n} with p_i <> i for every i. *)
Definition derangement (n : N) (l : list N) : Prop :=
  is_perm n l /\ forall i, i < len l -> nth (N.to_nat i) l 0 <> i + 1.

(* The rotation with offset k (1 <= k <= n) : a_k, ..., a_n, a_1, ..., a_(k-1). *)
Definition rotation (l : list N) (k : N) : list N :=
  skipn (N.to_nat (k - 1)) l ++ firstn (N.to_nat (k - 1)) l.

Definition is_rotation_of (l q : list N) : Prop :=
  exists k, 1 <= k <= len l /\ q = rotation l k.

(* Exactly c distinct values satisfy P. *)
Definition has_count {A : Type} (P : A -> Prop) (c : N) : Prop :=
  exists L : list A, NoDup L /\ (forall x, In x L <-> P x) /\ len L = c.

(* f(D) = c : exactly c distinct rotations of D are derangements. *)
Definition f_is (n : N) (D : list N) (c : N) : Prop :=
  has_count (fun q => is_rotation_of D q /\ derangement n q) c.

(* The derangements D of {1, ..., n} with f(D) = n - 2. *)
Definition counted (n : N) (D : list N) : Prop :=
  derangement n D /\ f_is n D (n - 2).

(* The statement's bounds. *)
Record valid_input (n p : N) : Prop := {
  (* 3 <= n <= 10^6 *)
  vi_n : 3 <= n <= 10 ^ 6;
  (* 10^8 <= p <= 10^9+7 *)
  vi_p : 10 ^ 8 <= p <= 10 ^ 9 + 7;
  (* p is a prime number *)
  vi_p_prime : prime (Z.of_N p);
}.

(* The answer : the number of counted derangements, reduced modulo p. *)
Definition derangement_rotations_spec (n p o : N) : Prop :=
  exists c, has_count (counted n) c /\ o = c mod p.

Program derangement_rotations : uint -> uint -> uint.

Specification derangement_rotations_correct : forall (n p : N) (x y : uint),
  valid_input n p -> repr x n -> repr y p ->
  exists o : N, repr (derangement_rotations x y) o /\
                derangement_rotations_spec n p o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
