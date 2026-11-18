(** * Antiarithmetic? *)

(** ** Description *)

(** Decide whether a permutation contains no three entries, in their
    original order, that form an arithmetic progression.

    [@kattis antiarithmetic]
    - Difficulty: 6.3
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Entry count: $3 \le n \le 10^{4}$, forming a permutation of the integers $0 \le x < n$. *)

(** ** Examples *)

(** - Input convention: Each case gives n, a colon and a permutation of 0 through n - 1; 0 ends input.
    - Output convention: yes for an antiarithmetic permutation; no otherwise, one line per case. *)
(* Input:
3: 0 2 1
5: 2 0 1 3 4
6: 2 4 3 5 0 1
0
Output:
yes
no
yes
*)

(** ** [@hide] Environment *)

(* @function        antiarithmetic
   @signature       array uint -> bool
   @math_signature  list N -> bool
   @summary         [antiarithmetic permutation] decides whether the
                    permutation permutation of 0, 1, ..., n-1 (n its length)
                    is antiarithmetic: it returns true exactly when there
                    are no three indices 0 <= i < j < k < n such that
                    (p_i, p_j, p_k) forms an arithmetic progression, p_i
                    being the i-th value of permutation.  One call per test
                    case.
                    It runs in at most c1 * (n + 1) * (n / 63 + 1) + c2
                    steps of the cost model on a valid input, n the length
                    of the permutation (the bitset scan, one word of 63
                    steps at a time), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A permutation is the list of its values, p_0
  first. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [i] in [permutation], or zero beyond the end. *)
Definition get (permutation : list N) (i : N) : N :=
  nth (N.to_nat i) permutation 0.

(** [first], [second], and [third] have equal successive differences, computed as
    integers. *)
Definition progression (first second third : N) : Prop :=
  (Z.of_N first - Z.of_N second = Z.of_N second - Z.of_N
    third)%Z.

(** Three entries at strictly increasing indices form an arithmetic progression. *)
Definition has_progression (permutation : list N) : Prop :=
  exists i j k : N,
    i < j /\ j < k /\ k < len permutation /\
    progression (get permutation i) (get permutation j)
      (get permutation k).

(** [permutation] has no arithmetic-progression subsequence of length three or more. *)
Definition is_antiarithmetic
  (permutation : list N) : Prop :=
  ~ has_progression permutation.

(** [@inside antiarithmetic_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (permutation : list N) : Prop := {
  (* a natural number 3 <= n <= 10^4 *)
  vi_n : 3 <= len permutation <= 10000;
  (* all n numbers are nonnegative integers smaller than n
    *)
  vi_values : Forall
    (fun value => value < len permutation) permutation;
  (* followed by n distinct numbers *)
  vi_distinct : NoDup permutation;
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when no three entries in increasing index order form an
    arithmetic progression. *)
Definition antiarithmetic_spec (permutation : list N)
  (output : bool)
    : Prop :=
  output = true <-> is_antiarithmetic permutation.

(** ** Complexity *)

(** [@requirement] Runs in $O(n^2)$ steps, where $n$ is the permutation length; the formal bound retains the factor $\lfloor n/63\rfloor+1$. *)
Definition antiarithmetic_time_spec (c1 c2 n_permutation steps : nat) : Prop :=
  (steps <= c1 * ((n_permutation + 1) * (n_permutation / 63 + 1)) + c2)%nat.

(** ** Interface *)

(** Decide whether a permutation contains no three entries, in their original order, that
    form an arithmetic progression.
    - Input [permutation]: Permutation to test for a three-term arithmetic progression.
    - Output [output]: The output is true exactly when no three entries in increasing index order form an arithmetic progression. *)
Program antiarithmetic : array uint -> bool.

(** [@example antiarithmetic]
    - Sample: 1
    - Case: 1
    - Input [permutation]: [0; 2; 1]
    - Output [output]: true
*)

(** [@example antiarithmetic]
    - Sample: 1
    - Case: 2
    - Input [permutation]: [2; 0; 1; 3; 4]
    - Output [output]: false
*)

(** [@example antiarithmetic]
    - Sample: 1
    - Case: 3
    - Input [permutation]: [2; 4; 3; 5; 0; 1]
    - Output [output]: true
*)

(** ** Bridge *)

(** [@requirement antiarithmetic_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [antiarithmetic_spec]. *)
Specification antiarithmetic_correct :
  forall (permutation : list N)
    (permutation_arr : array uint),
  valid_input permutation
    -> repr permutation_arr permutation ->
  exists output : bool,
    repr (antiarithmetic permutation_arr) output /\
    antiarithmetic_spec permutation output.

(** ** Complexity *)

(** [@hide] [antiarithmetic_cost] is the cost translation of [antiarithmetic] (the judge
    recomputes it and compares) ... *)
Complexity antiarithmetic_cost for antiarithmetic.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (n / 63 + 1) + c2 steps of the cost model on a valid input, n the length of the permutation (the bitset scan, one word of 63 steps at a time), for two constants
    quantified before the inputs, on every valid input. [@requirement antiarithmetic_time_spec] *)
Specification antiarithmetic_time : exists c1 c2 : nat,
  forall (permutation : list N)
  (permutation_arr : array uint),
  valid_input permutation
  -> repr permutation_arr permutation ->
  antiarithmetic_time_spec c1 c2 (size permutation_arr) (cost1 antiarithmetic_cost permutation_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
