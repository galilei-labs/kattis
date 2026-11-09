(** * Derangement Rotations *)

(** ** Description *)

(** Count permutations of 1 through n with no fixed points for which exactly
    n - 2 cyclic rotations also have no fixed points. Return the count
    modulo a given prime.

    [@kattis derangementrotations]
    - Difficulty: 6.2
    - CPU time limit: 1 second
    - Memory limit: 2048 MB

    **Kattis Bounds**
    - Permutation size: $3 \le n \le 10^6$.
    - Prime modulus in $[10^{8}, 1{,}000{,}000{,}007]$. *)

(** ** Examples *)

(** - Input convention: Permutation size n and prime modulus p.
    - Output convention: The qualifying derangement count modulo p. *)
(* Input:
3 1000000007
Output:
0
*)

(** ** [@hide] Environment *)

(* @function        derangement_rotations
   @signature       uint -> uint -> uint
   @math_signature  N -> N -> N
   @summary         [derangement_rotations perm_size prime_modulus] is,
                    modulo the prime prime_modulus, the number of
                    derangements D of {1, ..., perm_size} such that exactly
                    perm_size - 2 of the distinct rotations of D are again
                    derangements.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Permutation Znumtheory.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A sequence a_1, ..., a_n is a list, position
  i (from 0)
   holding a_(i+1). *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The list 1, 2, ..., last_value. *)
Definition iota (last_value : N) : list N :=
  map N.of_nat (List.seq 1 (N.to_nat last_value)).

(** sequence is a permutation of {1, 2, ..., perm_size}. *)
Definition is_perm (perm_size : N)
  (sequence : list N) : Prop :=
  Permutation sequence (iota perm_size).

(** A permutation of {1, ..., perm_size} with p_i <> i
    for every i. *)
Definition derangement (perm_size : N)
  (sequence : list N) : Prop :=
  is_perm perm_size sequence /\
  forall i, i < len sequence -> nth
    (N.to_nat i) sequence 0 <> i + 1.

(** The rotation with offset k (1 <= k <= n): a_k, ...,
    a_n, a_1, ..., a_(k-1). *)
Definition rotation (sequence : list N)
  (offset : N) : list N :=
  skipn (N.to_nat (offset - 1)) sequence ++
  firstn (N.to_nat (offset - 1)) sequence.

(** One list is a cyclic rotation of the other. *)
Definition is_rotation_of
  (sequence rotated : list N) : Prop :=
  exists offset, 1 <= offset <= len sequence /\
    rotated = rotation sequence offset.

(** Exactly amount distinct values satisfy property. *)
Definition has_count {A : Type} (property : A -> Prop)
  (amount : N) : Prop :=
  exists witnesses : list A, NoDup witnesses /\
    (forall value, In value witnesses <-> property value) /\
    len witnesses = amount.

(** f(candidate) = amount : exactly amount distinct
    rotations of candidate are derangements. *)
Definition f_is (perm_size : N) (candidate : list N)
  (amount : N) : Prop :=
  has_count
    (fun rotated => is_rotation_of candidate rotated /\
                            derangement perm_size rotated)
                              amount.

(** The derangements D of {1, ..., perm_size} with f(D)
    = perm_size - 2. *)
Definition counted (perm_size : N)
  (candidate : list N) : Prop :=
  derangement perm_size candidate /\
  f_is perm_size candidate (perm_size - 2).

(** [@inside derangement_rotations_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (perm_size prime_modulus : N) : Prop := {
  (* 3 <= n <= 10^6 *)
  vi_n : 3 <= perm_size <= 10 ^ 6;
  (* 10^8 <= p <= 10^9+7 *)
  vi_p : 10 ^ 8 <= prime_modulus <= 10 ^ 9 + 7;
  (* p is a prime number *)
  vi_p_prime : prime (Z.of_N prime_modulus);
}.

(** ** Correctness *)

(** [@requirement]
    The output counts derangements having exactly n - 2 cyclic rotations that are also
    derangements, modulo the given prime. *)
Definition derangement_rotations_spec
  (perm_size prime_modulus : N)
    (output : N) : Prop :=
  exists total, has_count (counted perm_size) total /\
    output = total mod prime_modulus.

(** ** Interface *)

(** Count permutations of 1 through n with no fixed points for which exactly n - 2 cyclic
    rotations also have no fixed points. Return the count modulo a given prime.
    - Input [perm_size]: Size of the permutations to count.
    - Input [prime_modulus]: Prime modulus used for the result.
    - Output [output]: The output counts derangements having exactly n - 2 cyclic rotations that are also derangements, modulo the given prime. *)
Program derangement_rotations : uint -> uint -> uint.

(** ** Bridge *)

(** [@requirement derangement_rotations_spec] [@fold
    full correctness statement] On valid represented
    inputs, the program returns a represented output
    satisfying [derangement_rotations_spec]. *)
Specification derangement_rotations_correct :
  forall (perm_size prime_modulus : N)
         (perm_size_int prime_modulus_int : uint),
  valid_input perm_size prime_modulus ->
  repr perm_size_int perm_size
    -> repr prime_modulus_int prime_modulus ->
  exists output : N,
    repr (derangement_rotations perm_size_int
      prime_modulus_int)
      output /\
    derangement_rotations_spec perm_size prime_modulus
      output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
