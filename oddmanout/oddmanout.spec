(** * Odd Man Out *)

(** ** Description *)

(** Guests were invited to a party in couples, with a shared invitation
    code for each couple. One guest has arrived alone. Given the code reported
    by each guest, find the unpaired guest's code: the unique code occurring
    an odd number of times.

    [@kattis oddmanout]
    - Difficulty: 1.5
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Entry count: $3 \le n \le 999$; each value: $1 \le a_i \le 2^{31} - 1$.
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
                    It runs in at most c1 * n + c2 steps of the cost model,
                    n the number of codes, for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith PeanoNat List
  Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of guests whose invitation code is [code]. *)
Definition occurrences (codes : list N) (code : N) : nat :=
  count_occ N.eq_dec codes code.

(** [code] occurs an odd number of times in [codes]. *)
Definition odd_occurrences (codes : list N)
  (code : N) : Prop :=
  Nat.Odd (occurrences codes code).

(** Exactly one code, [code], has odd multiplicity. *)
Definition only_odd (codes : list N) (code : N) : Prop :=
  odd_occurrences codes code /\
  forall other, odd_occurrences codes other -> other = code.

(** [@inside odd_one_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (codes : list N) : Prop := {
  (* 3 <= G < 10^3 *)
  vi_length : 3 <= len codes < 1000;
  (* 0 < C < 2^31 *)
  vi_codes : Forall (fun code => 0 < code < 2 ^ 31) codes;
  (* only couples were invited and exactly one guest came
     alone : one code occurs an odd number of times *)
  vi_one_alone : exists code, only_odd codes code;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the unpaired guest's invitation code: the unique code
    reported an odd number of times. *)
Definition odd_one_spec (codes : list N)
  (output : N) : Prop :=
  only_odd codes output.

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the number of invitation codes. *)
Definition odd_one_time_spec (c1 c2 n_codes steps : nat) : Prop :=
  (steps <= c1 * n_codes + c2)%nat.

(** ** Interface *)

(** Identify the invitation code of the guest without a partner.
    - Input [codes]: Invitation code reported by each guest; exactly one code has odd multiplicity.
    - Output [output]: The unique invitation code occurring an odd number of times. *)
Program odd_one : array uint -> uint.

(** [@example odd_one]
    - Sample: 1
    - Case: 1
    - Input [codes]: [1; 2147483647; 2147483647]
    - Output [output]: 1
*)

(** [@example odd_one]
    - Sample: 1
    - Case: 2
    - Input [codes]: [3; 4; 7; 4; 3]
    - Output [output]: 7
*)

(** [@example odd_one]
    - Sample: 1
    - Case: 3
    - Input [codes]: [2; 10; 2; 10; 5]
    - Output [output]: 5
*)

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

(** ** Complexity *)

(** [@hide] [odd_one_cost] is the cost translation of [odd_one] (the judge
    recomputes it and compares) ... *)
Complexity odd_one_cost for odd_one.

(** [@fold complexity bound] ... and runs in at most c1 * n + c2 steps of the cost model, n the number of codes, for two constants
    quantified before the input. [@requirement odd_one_time_spec] *)
Specification odd_one_time : exists c1 c2 : nat, forall codes_arr : array uint,
  odd_one_time_spec c1 c2 (size codes_arr) (cost1 odd_one_cost codes_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
