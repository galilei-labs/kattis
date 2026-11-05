(* @function        odd_one
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [odd_one l] returns the element of l that occurs an
                    odd number of times in l, there being exactly one such
                    element
*)

From Stdlib Require Import ZArith NArith PeanoNat List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of guests whose invitation code is x. *)
Definition occurrences (l : list N) (x : N) : nat := count_occ N.eq_dec l x.

Definition odd_occurrences (l : list N) (x : N) : Prop :=
  Nat.Odd (occurrences l x).

(* Exactly one code x has odd multiplicity. *)
Definition only_odd (l : list N) (x : N) : Prop :=
  odd_occurrences l x /\ forall y, odd_occurrences l y -> y = x.

(* The statement's bounds, for one test case. *)
Record valid_input (l : list N) : Prop := {
  (* 3 <= G < 1000 *)
  vi_length : 3 <= len l < 1000;
  (* 0 < C < 2^31 *)
  vi_codes : Forall (fun c => 0 < c < 2 ^ 31) l;
  (* only couples were invited and exactly one guest came alone : one
     code occurs an odd number of times *)
  vi_one_alone : exists x, only_odd l x;
}.

(* The result is the code that occurs an odd number of times. *)
Definition odd_one_spec (l : list N) (x : N) : Prop := only_odd l x.

(* machine side : the only thing that gets extracted *)
Program odd_one : array uint -> uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification odd_one_correct : forall (l : list N) (a : array uint),
  valid_input l -> repr a l ->
  exists x : N, repr (odd_one a) x /\ odd_one_spec l x.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
