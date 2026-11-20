(** * Magic Sequence *)

(** ** Description *)

(** Generate $N$ integers: $S_0 = A$ and
    $S_i = (S_{i-1}B + A) \bmod C$ for $1 \le i < N$. Sort the entries in
    nondecreasing order. Starting with hash $V = 0$, process each sorted
    entry $s$ by setting $V = (VX + s) \bmod Y$, and return the final hash.

    [@kattis magicsequence]
    - Difficulty: 7.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1 \le N \le 10^{6}$.
    - $1 \le A, B, C, X, Y \le 10^{9}$. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives N, generator parameters A B C and hash parameters X Y.
    - Output convention: One hash of the sorted generated sequence per case. *)
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
                    It runs in at most c1 * (n + 1) + c2 steps of the cost
                    model on a valid input, n the length of the sequence
                    (the generation, a radix sort of a fixed number of
                    counting passes over 2^16 buckets, the hash fold), for
                    two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Sorting.Sorted
  Sorting.Permutation.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at index [i] of the generated sequence: begin with [seed], then
    repeatedly multiply by [multiplier], add [seed], and reduce modulo [modulus]. *)
Fixpoint term (seed multiplier modulus : N) (i : nat) : N :=
  match i with
  | O => seed
  | S k => (term seed multiplier modulus k *
    multiplier + seed)
            mod modulus
  end.

(** The first [sequence_length] generated entries, beginning with [seed]. *)
Definition sequence
  (sequence_length seed multiplier modulus : N) : list N :=
  map (term seed multiplier modulus) (seq 0 (N.to_nat
    sequence_length)).

(** [sorted_list] contains the same elements as [unsorted_list], in
    nondecreasing order and with the same multiplicities. *)
Definition sorted_version
  (sorted_list unsorted_list : list N) : Prop :=
  Permutation sorted_list unsorted_list /\ Sorted N.le
    sorted_list.

(** Continue hashing [terms] from the current hash [partial]. *)
Fixpoint hash_from (hash_base hash_modulus : N)
  (terms : list N) (partial : N) : N :=
  match terms with
  | [] => partial
  | element :: rest =>
      hash_from hash_base hash_modulus rest
        ((partial * hash_base + element) mod hash_modulus)
  end.

(** Hash [terms] from left to right: begin at zero, then multiply by [hash_base],
    add the next entry, and reduce modulo [hash_modulus]. *)
Definition hash (hash_base hash_modulus : N)
  (terms : list N) : N :=
  hash_from hash_base hash_modulus terms 0.

(** [@inside magic_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
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

(** [@requirement]
    The output is the specified rolling hash of the generated sequence sorted in
    nondecreasing order. *)
Definition magic_spec
  (sequence_length seed multiplier modulus hash_base
            hash_modulus : N) (output : N) : Prop
            :=
  exists sorted_terms,
    sorted_version sorted_terms
      (sequence sequence_length seed multiplier modulus) /\
    output = hash hash_base hash_modulus sorted_terms.

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the generated sequence length. *)
Definition magic_time_spec (c1 c2 n_sequence_length steps : nat) : Prop :=
  (steps <= c1 * (n_sequence_length + 1) + c2)%nat.

(** ** Interface *)

(** Generate a sequence beginning with [seed], then repeatedly multiply the
    previous entry by [multiplier], add [seed], and reduce modulo [modulus].
    Sort the entries, then hash them from left to right, starting at zero:
    multiply the hash by [hash_base], add the next entry, and reduce modulo
    [hash_modulus]. Return the final hash.
    - Input [sequence_length]: Number of values to generate.
    - Input [seed]: Initial value and additive generator parameter.
    - Input [multiplier]: Multiplier used to generate the sequence.
    - Input [modulus]: Modulus used to generate the sequence.
    - Input [hash_base]: Multiplier used to hash the sorted sequence.
    - Input [hash_modulus]: Modulus used for the resulting hash.
    - Output [output]: The output is the specified rolling hash of the generated sequence sorted in nondecreasing order. *)
Program magic : uint -> uint -> uint -> uint -> uint -> uint
  -> uint.

(** [@example magic]
    - Sample: 1
    - Case: 1
    - Input [sequence_length]: 7
    - Input [seed]: 7
    - Input [multiplier]: 7
    - Input [modulus]: 12
    - Input [hash_base]: 1
    - Input [hash_modulus]: 20
    - Output [output]: 0
*)

(** [@example magic]
    - Sample: 1
    - Case: 2
    - Input [sequence_length]: 7
    - Input [seed]: 16
    - Input [multiplier]: 1
    - Input [modulus]: 15
    - Input [hash_base]: 1
    - Input [hash_modulus]: 14
    - Output [output]: 1
*)

(** [@example magic]
    - Sample: 1
    - Case: 3
    - Input [sequence_length]: 7
    - Input [seed]: 2
    - Input [multiplier]: 5
    - Input [modulus]: 6
    - Input [hash_base]: 1
    - Input [hash_modulus]: 19
    - Output [output]: 8
*)

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

(** ** Complexity *)

(** [@hide] [magic_cost] is the cost translation of [magic] (the judge
    recomputes it and compares) ... *)
Complexity magic_cost for magic.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) + c2 steps of the cost model on a valid input, n the length of the sequence (the generation, a radix sort of a fixed number of counting passes over 2^16 buckets, the hash fold), for two constants
    quantified before the inputs, on every valid input. [@requirement magic_time_spec] *)
Specification magic_time : exists c1 c2 : nat,
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
  magic_time_spec c1 c2 (size sequence_length_int) (cost6 magic_cost sequence_length_int seed_int multiplier_int modulus_int hash_base_int hash_modulus_int).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
