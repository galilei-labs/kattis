(** * Odd Man Out *)

(** ** Description *)

(** Find the unique value occurring an odd number of times in a sequence.

    [@kattis oddmanout]
    - Difficulty: 1.5
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Entry count: $3 \le n \le 999$, each in $[1, 2^{31}-1]$.
    - Exactly one value has odd multiplicity. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives a sequence length and its integer values.
    - Output convention: Case #number: followed by the value with odd multiplicity. *)
(* Input:
3
3
1 2147483647 2147483647
5
3 4 7 4 3
5
2 10 2 10 5
Output:
Case #1: 1
Case #2: 7
Case #3: 5
*)

(** ** [@hide] Environment *)
(* @function        odd_one
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [odd_one codes] returns the element of codes that occurs
                    an odd number of times in codes, there being exactly one
                    such element
*)

From Stdlib Require Import ZArith NArith PeanoNat List
  Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of guests whose invitation code is [code]. *)
Definition occurrences (codes : list N) (code : N) : nat :=
  count_occ N.eq_dec codes code.

(** The [odd_occurrences] definition. *)
Definition odd_occurrences (codes : list N)
  (code : N) : Prop :=
  Nat.Odd (occurrences codes code).

(** Exactly one code, [code], has odd multiplicity. *)
Definition only_odd (codes : list N) (code : N) : Prop :=
  odd_occurrences codes code /\
  forall other, odd_occurrences codes other -> other = code.

(** [@inside odd_one_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (codes : list N) : Prop := {
  (* 3 <= G < 1000 *)
  vi_length : 3 <= len codes < 1000;
  (* 0 < C < 2^31 *)
  vi_codes : Forall (fun code => 0 < code < 2 ^ 31) codes;
  (* only couples were invited and exactly one guest came
     alone : one code occurs an odd number of times *)
  vi_one_alone : exists code, only_odd codes code;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the unique input value with odd multiplicity. *)
Definition odd_one_spec (codes : list N)
  (output : N) : Prop :=
  only_odd codes output.

(** ** Interface *)

(** Find the unique value occurring an odd number of times in a sequence.
    - Input [codes]: Integer values containing one value of odd multiplicity.
    - Output [output]: The output is the unique input value with odd multiplicity. *)
Program odd_one : array uint -> uint.

(** ** Bridge *)

(** [@requirement odd_one_spec] [@fold full correctness statement] On
    valid represented inputs, [odd_one] returns a represented output
    satisfying [odd_one_spec]. *)
Specification odd_one_correct :
  forall (codes : list N) (codes_arr : array uint),
  valid_input codes -> repr codes_arr codes ->
  exists output : N,
    repr (odd_one codes_arr) output /\ odd_one_spec codes
      output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
