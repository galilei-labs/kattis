(* @function        purplerain
   @signature       PrimString.string -> uint * uint
   @math_signature  String.string -> N * N
   @summary         [purplerain colors] takes the colours of sections 1 to
                    n of the peninsula (a string of 'R' and 'B') and
                    returns the first and last section (west, east),
                    1 <= west <= east <= n, of a part maximising
                    |#R - #B| over its sections.  Among all maximising
                    parts it returns the one with the smallest west, and
                    then the smallest east.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import PrimString String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Section k (1-based, West to East) has the colour of
   character k - 1 of colors. *)

(* The number of sections. *)
Definition slen (colors : String.string) : N :=
  N.of_nat (String.length colors).

(* The number of characters of text equal to letter. *)
Fixpoint count (letter : ascii) (text : String.string) : N :=
  match text with
  | EmptyString => 0
  | String head rest =>
      (if Ascii.eqb head letter then 1 else 0) + count letter rest
  end.

(* (west, east) is a part of the peninsula: sections west to east, both
   included. *)
Definition is_part (colors : String.string) (west east : N) : Prop :=
  1 <= west /\ west <= east /\ east <= slen colors.

(* The colours of sections west to east. *)
Definition part (colors : String.string) (west east : N) : String.string :=
  String.substring (N.to_nat (west - 1)) (N.to_nat (east - west + 1))
    colors.

(* The difference between the number of R and the number of B in sections
   west to east, in absolute value (sample 2: the answer BBRBB has more
   B). *)
Definition difference (colors : String.string) (west east : N) : Z :=
  Z.abs (Z.of_N (count "R" (part colors west east))
         - Z.of_N (count "B" (part colors west east))).

(* (west, east) is West of, or is, (west', east'): smaller start, then
   smaller end. *)
Definition west_or_equal (west east west' east' : N) : Prop :=
  west < west' \/ (west = west' /\ east <= east').

Record valid_input (colors : String.string) : Prop := {
  (* a string of n characters (1 <= n <= 10^5) *)
  vi_n : 1 <= slen colors <= 10 ^ 5;
  (* the string consists of uppercase ASCII letters 'R' and 'B' only *)
  vi_colors : forall k color, String.get k colors = Some color ->
    color = "R"%char \/ color = "B"%char;
}.

(* The answer (west, east) is a part of maximal difference, and the
   Westernmost one among the parts of maximal difference. *)
Definition purplerain_spec (colors : String.string) (output : N * N)
    : Prop :=
  match output with
  | (west, east) =>
      is_part colors west east /\
      (forall west' east', is_part colors west' east' ->
         (difference colors west' east' <= difference colors west east)%Z) /\
      (forall west' east', is_part colors west' east' ->
         difference colors west' east' = difference colors west east ->
         west_or_equal west east west' east')
  end.

Program purplerain : PrimString.string -> uint * uint.

Specification purplerain_correct :
  forall (colors : String.string) (colors_str : PrimString.string),
  valid_input colors -> repr colors_str colors ->
  exists output : N * N,
    repr (purplerain colors_str) output /\
    purplerain_spec colors output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
