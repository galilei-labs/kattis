(** * Derangement Rotations *)

(** ** Description *)

(** A derangement is a permutation of $1$ through $n$ in which no entry equals
    its one-based position. Count derangements for which exactly $n - 2$
    distinct cyclic rotations are also derangements, including the original
    arrangement among the rotations. Return the count modulo a given prime.

    [@kattis derangementrotations]
    - Difficulty: 6.2
    - CPU time limit: 1 second
    - Memory limit: 2048 MB

    **Kattis Bounds**
    - Permutation size: $3 \le n \le 10^{6}$.
    - Prime modulus: $10^{8} \le p \le 10^{9} + 7$. *)

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
                    It runs in at most c1 * (n + 1) * (log2 n + log2 p + 1)
                    + c2 steps of the cost model on a valid input, n the
                    permutation size and p the modulus (one pass over d with
                    a gcd and a modular power each), for two constants c1,
                    c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Permutation Znumtheory.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A sequence a_1, ..., a_n is a list, position
  i (from 0)
   holding a_(i+1). *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The list 1, 2, ..., [last_value]. *)
Definition iota (last_value : N) : list N :=
  map N.of_nat (List.seq 1 (N.to_nat last_value)).

(** [sequence] is a permutation of the integers from one through [perm_size]. *)
Definition is_perm (perm_size : N)
  (sequence : list N) : Prop :=
  Permutation sequence (iota perm_size).

(** A permutation of the integers from one through [perm_size] with no entry equal
    to its one-based position. *)
Definition derangement (perm_size : N)
  (sequence : list N) : Prop :=
  is_perm perm_size sequence /\
  forall i, i < len sequence -> nth
    (N.to_nat i) sequence 0 <> i + 1.

(** Rotate [sequence] to begin at its one-based position [offset], wrapping the
    preceding entries to the end. *)
Definition rotation (sequence : list N)
  (offset : N) : list N :=
  skipn (N.to_nat (offset - 1)) sequence ++
  firstn (N.to_nat (offset - 1)) sequence.

(** [is_rotation_of sequence rotated] means that [rotated] is obtained from
    [sequence] by choosing one of its entries as the first and wrapping the
    preceding entries to the end, preserving their order. Choosing the first
    entry leaves [sequence] unchanged; an empty [sequence] has no such rotation. *)
Definition is_rotation_of
  (sequence rotated : list N) : Prop :=
  exists offset, 1 <= offset <= len sequence /\
    rotated = rotation sequence offset.

(** Exactly [amount] distinct values satisfy [property]. *)
Definition has_count {A : Type} (property : A -> Prop)
  (amount : N) : Prop :=
  exists witnesses : list A, NoDup witnesses /\
    (forall value, In value witnesses <-> property value) /\
    len witnesses = amount.

(** Exactly [amount] distinct cyclic rotations of [candidate] are derangements. *)
Definition f_is (perm_size : N) (candidate : list N)
  (amount : N) : Prop :=
  has_count
    (fun rotated => is_rotation_of candidate rotated /\
                            derangement perm_size rotated)
                              amount.

(** The derangements of size [perm_size] having exactly [perm_size - 2] distinct
    derangement rotations. *)
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
    The output counts derangements of size [perm_size] having exactly
    [perm_size - 2] cyclic rotations that are also derangements, modulo
    [prime_modulus]. *)
Definition derangement_rotations_spec
  (perm_size prime_modulus : N)
    (output : N) : Prop :=
  exists total, has_count (counted perm_size) total /\
    output = total mod prime_modulus.

(** ** Complexity *)

(** [@requirement] Runs in $O((n+1)(\log(n+2)+\log(p+2)))$ steps, where $n$ is the permutation size and $p$ the prime modulus. *)
Definition derangement_rotations_time_spec (c1 c2 n_perm_size n_prime_modulus steps : nat) : Prop :=
  (steps <= c1 * ((n_perm_size + 1) * (Nat.log2 (n_perm_size) + Nat.log2 (n_prime_modulus) + 1)) + c2)%nat.

(** ** Interface *)

(** Count derangements of size [perm_size] for which exactly [perm_size - 2]
    cyclic rotations are also derangements. Return the count modulo
    [prime_modulus].
    - Input [perm_size]: Size of the permutations to count.
    - Input [prime_modulus]: Prime modulus used for the result.
    - Output [output]: Number of such derangements, reduced modulo [prime_modulus]. *)
Program derangement_rotations : uint -> uint -> uint.

(** [@example derangement_rotations]
    - Sample: 1
    - Input [perm_size]: 3
    - Input [prime_modulus]: 1000000007
    - Output [output]: 0
*)

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

(** ** Complexity *)

(** [@hide] [derangement_rotations_cost] is the cost translation of [derangement_rotations] (the judge
    recomputes it and compares) ... *)
Complexity derangement_rotations_cost for derangement_rotations.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + log2 p + 1) + c2 steps of the cost model on a valid input, n the permutation size and p the modulus (one pass over d with a gcd and a modular power each), for two constants
    quantified before the inputs, on every valid input. [@requirement derangement_rotations_time_spec] *)
Specification derangement_rotations_time : exists c1 c2 : nat,
  forall (perm_size prime_modulus : N)
  (perm_size_int prime_modulus_int : uint),
  valid_input perm_size prime_modulus ->
  repr perm_size_int perm_size
  -> repr prime_modulus_int prime_modulus ->
  derangement_rotations_time_spec c1 c2 (size perm_size_int) (size prime_modulus_int) (cost2 derangement_rotations_cost perm_size_int prime_modulus_int).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
