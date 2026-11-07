(** * Magic Sequence *)

(** ** Description *)

(** Generate N integers by S[0] = A and S[i] = (S[i-1] * B + A) mod C, then
    sort them. Hash the sorted sequence by starting at zero and repeatedly
    replacing V with (V * X + value) mod Y.

    [@kattis magicsequence]
    - Difficulty: 7.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 <= N <= 1000000.
    - 1 <= A, B, C, X, Y <= 1000000000. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
3
7
7 7 12
1 20
7
16 1 15
1 14
7
2 5 6
1 19
Output:
0
1
8
*)

(** ** [@hide] Environment *)
(* @function        magic
   @signature       uint -> uint -> uint -> uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N -> N -> N -> N
   @summary         [magic sequence_length seed multiplier modulus hash_base
                    hash_modulus] generates the sequence S of
                    sequence_length integers S[0] = seed,
                    S[i] = (S[i-1] * multiplier + seed) mod modulus for
                    1 <= i < sequence_length, sorts it into R, and returns
                    the hash V obtained from V = 0 by
                    V := (V * hash_base + R[i]) mod hash_modulus for i from
                    0 to sequence_length - 1.  One test case per call.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Sorting.Sorted
  Sorting.Permutation.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The statement's A, B, C are seed, multiplier, modulus;
    its X, Y are hash_base, hash_modulus. The number of elements of
    l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** S[i] : S[0] = seed, S[i] = (S[i-1] * multiplier + seed) mod modulus. *)
Fixpoint term (seed multiplier modulus : N) (i : nat) : N :=
  match i with
  | O => seed
  | Datatypes.S k => (term seed multiplier modulus k *
    multiplier + seed)
            mod modulus
  end.

(** The sequence S[0], ..., S[sequence_length-1]. *)
Definition sequence
  (sequence_length seed multiplier modulus : N) : list N :=
  map (term seed multiplier modulus) (seq 0 (N.to_nat
    sequence_length)).

(** sorted_list is the sorted version of unsorted_list : the same
    elements, in non-decreasing order. *)
Definition sorted_version
  (sorted_list unsorted_list : list N) : Prop :=
  Permutation sorted_list unsorted_list /\ Sorted N.le
    sorted_list.

(** The value of V after "V = 0; for each element of terms in order : V
    = (V * hash_base + element) % hash_modulus". *)
Definition hash (hash_base hash_modulus : N)
  (terms : list N) : N :=
  fold_left (fun partial element => (partial * hash_base +
    element)
            mod hash_modulus)
            terms 0.

(** [@inside magic_correct] The statement's bounds, for one test case
    (TC, the number of test cases, is the harness's loop, not an
    argument). *)
Record valid_input
  (sequence_length seed multiplier modulus hash_base
            hash_modulus : N) : Prop := {
  (* 1 <= N <= 10^6 *)
  vi_n : 1 <= sequence_length <= 10 ^ 6;
  (* 1 <= A, B, C <= 10^9 *)
  vi_a : 1 <= seed <= 10 ^ 9;
  vi_b : 1 <= multiplier <= 10 ^ 9;
  vi_c : 1 <= modulus <= 10 ^ 9;
  (* 1 <= X, Y <= 10^9 *)
  vi_x : 1 <= hash_base <= 10 ^ 9;
  vi_y : 1 <= hash_modulus <= 10 ^ 9;
}.

(** ** Correctness *)

(** [@requirement] [@short The answer output is the hash of R =
    sorted_terms, the sorted version    of S (R is unique, so the
    answer is pinned).] The answer output is the hash of R =
    sorted_terms, the sorted version of S (R is unique, so the
    answer is pinned). *)
Definition magic_spec
  (sequence_length seed multiplier modulus hash_base
            hash_modulus : N) (output : N) : Prop
            :=
  exists sorted_terms,
    sorted_version sorted_terms
      (sequence sequence_length seed multiplier modulus) /\
    output = hash hash_base hash_modulus sorted_terms.

(** ** Interface *)

(** The [magic] program on machine values.
    - Input [sequence_length]:
    - Input [seed]:
    - Input [multiplier]:
    - Input [modulus]:
    - Input [hash_base]:
    - Input [hash_modulus]:
    - Output [output]: *)
Program magic : uint -> uint -> uint -> uint -> uint -> uint
  -> uint.

(** ** Bridge *)

(** [@requirement magic_spec] [@fold full correctness statement] On
    valid represented inputs, [magic] returns a represented output
    satisfying [magic_spec]. *)
Specification magic_correct :
  forall (sequence_length seed multiplier modulus hash_base
    hash_modulus : N)
         (sequence_length_int seed_int multiplier_int
           modulus_int
          hash_base_int hash_modulus_int : uint),
  valid_input sequence_length seed multiplier modulus
    hash_base
    hash_modulus ->
  repr sequence_length_int sequence_length ->
    repr seed_int seed ->
  repr multiplier_int multiplier ->
    repr modulus_int modulus ->
  repr hash_base_int hash_base ->
    repr hash_modulus_int hash_modulus ->
  exists output : N,
    repr (magic sequence_length_int seed_int multiplier_int
      modulus_int
            hash_base_int hash_modulus_int) output /\
    magic_spec sequence_length seed multiplier modulus
      hash_base
      hash_modulus output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
