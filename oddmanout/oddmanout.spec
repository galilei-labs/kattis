(* @function        odd_one
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [odd_one codes] returns the element of codes that occurs
                    an odd number of times in codes, there being exactly one
                    such element
*)

From Stdlib Require Import ZArith NArith PeanoNat List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of guests whose invitation code is [code]. *)
Definition occurrences (codes : list N) (code : N) : nat :=
  count_occ N.eq_dec codes code.

Definition odd_occurrences (codes : list N) (code : N) : Prop :=
  Nat.Odd (occurrences codes code).

(* Exactly one code, [code], has odd multiplicity. *)
Definition only_odd (codes : list N) (code : N) : Prop :=
  odd_occurrences codes code /\
  forall other, odd_occurrences codes other -> other = code.

(* The statement's bounds, for one test case. *)
Record valid_input (codes : list N) : Prop := {
  (* 3 <= G < 1000 *)
  vi_length : 3 <= len codes < 1000;
  (* 0 < C < 2^31 *)
  vi_codes : Forall (fun code => 0 < code < 2 ^ 31) codes;
  (* only couples were invited and exactly one guest came alone : one
     code occurs an odd number of times *)
  vi_one_alone : exists code, only_odd codes code;
}.

(* The result is the code that occurs an odd number of times. *)
Definition odd_one_spec (codes : list N) (output : N) : Prop :=
  only_odd codes output.

(* machine side : the only thing that gets extracted *)
Program odd_one : array uint -> uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification odd_one_correct :
  forall (codes : list N) (codes_arr : array uint),
  valid_input codes -> repr codes_arr codes ->
  exists output : N,
    repr (odd_one codes_arr) output /\ odd_one_spec codes output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
