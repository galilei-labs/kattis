(* @function        purplerain
   @signature       PrimString.string -> uint * uint
   @math_signature  String.string -> N * N
   @summary         [purplerain s] takes the colours of sections 1 to n of
                    the peninsula (a string of 'R' and 'B') and returns the
                    first and last section (i, j), 1 <= i <= j <= n, of a
                    part maximising |#R - #B| over its sections.  Among all
                    maximising parts it returns the one with the smallest
                    i, and then the smallest j.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import PrimString String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Section k (1-based, West to East) has the colour of
   character k - 1 of s. *)

(* The number of sections. *)
Definition slen (s : String.string) : N := N.of_nat (String.length s).

(* The number of characters of t equal to c. *)
Fixpoint count (c : ascii) (t : String.string) : N :=
  match t with
  | EmptyString => 0
  | String a t' => (if Ascii.eqb a c then 1 else 0) + count c t'
  end.

(* (i, j) is a part of the peninsula: sections i to j, both included. *)
Definition is_part (s : String.string) (i j : N) : Prop :=
  1 <= i /\ i <= j /\ j <= slen s.

(* The colours of sections i to j. *)
Definition part (s : String.string) (i j : N) : String.string :=
  String.substring (N.to_nat (i - 1)) (N.to_nat (j - i + 1)) s.

(* The difference between the number of R and the number of B in sections
   i to j, in absolute value (sample 2: the answer BBRBB has more B). *)
Definition difference (s : String.string) (i j : N) : Z :=
  Z.abs (Z.of_N (count "R" (part s i j)) - Z.of_N (count "B" (part s i j))).

(* (i, j) is West of, or is, (i', j'): smaller start, then smaller end. *)
Definition west_or_equal (i j i' j' : N) : Prop :=
  i < i' \/ (i = i' /\ j <= j').

Record valid_input (s : String.string) : Prop := {
  (* a string of n characters (1 <= n <= 10^5) *)
  vi_n : 1 <= slen s <= 10 ^ 5;
  (* the string consists of uppercase ASCII letters 'R' and 'B' only *)
  vi_colors : forall k c, String.get k s = Some c ->
    c = "R"%char \/ c = "B"%char;
}.

(* The answer (i, j) is a part of maximal difference, and the Westernmost
   one among the parts of maximal difference. *)
Definition purplerain_spec (s : String.string) (o : N * N) : Prop :=
  let (i, j) := o in
  is_part s i j /\
  (forall i' j', is_part s i' j' -> (difference s i' j' <= difference s i j)%Z) /\
  (forall i' j', is_part s i' j' -> difference s i' j' = difference s i j ->
     west_or_equal i j i' j').

Program purplerain : PrimString.string -> uint * uint.

Specification purplerain_correct :
  forall (s : String.string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists o : N * N, repr (purplerain x) o /\ purplerain_spec s o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
