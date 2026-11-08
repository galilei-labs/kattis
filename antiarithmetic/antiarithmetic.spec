(** * Antiarithmetic? *)

(** ** Description *)

(** Decide whether a permutation contains no three entries, in their
    original order, that form an arithmetic progression.

    [@kattis antiarithmetic]
    - Difficulty: 6.3
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 3 to 10,000 entries, forming a permutation of 0 through n - 1. *)

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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A permutation is the list of its values, p_0
  first. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The i-th element of permutation (p_i); 0 beyond the
    end. *)
Definition get (permutation : list N) (i : N) : N :=
  nth (N.to_nat i) permutation 0.

(** (first, second, third) forms an arithmetic
    progression: there is a constant c with first -
    second = c and second - third = c, the differences
    taken in Z. *)
Definition progression (first second third : N) : Prop :=
  (Z.of_N first - Z.of_N second = Z.of_N second - Z.of_N
    third)%Z.

(** There are three indices 0 <= i < j < k < n such that
    (p_i, p_j, p_k) forms an arithmetic progression. *)
Definition has_progression (permutation : list N) : Prop :=
  exists i j k : N,
    i < j /\ j < k /\ k < len permutation /\
    progression (get permutation i) (get permutation j)
      (get permutation k).

(** permutation is antiarithmetic: no subsequence of it
    of length greater than 2 is an arithmetic
    progression. *)
Definition is_antiarithmetic
  (permutation : list N) : Prop :=
  ~ has_progression permutation.

(** [@inside antiarithmetic_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (permutation : list N) : Prop := {
  (* a natural number 3 <= n <= 10 000 *)
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
  match output with
  | true => is_antiarithmetic permutation
  | false => has_progression permutation
  end.

(** ** Interface *)

(** Decide whether a permutation contains no three entries, in their original order, that
    form an arithmetic progression.
    - Input [permutation]:
    - Output [output]: *)
Program antiarithmetic : array uint -> bool.

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

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
