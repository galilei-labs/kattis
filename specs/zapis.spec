(* @function        zapis
   @signature       PrimString.string -> uint * bool
   @math_signature  String.string -> N * bool
   @summary         [zapis s] counts the ways to replace every '?' of s by a
                    character so that the result is a regular
                    bracket-sequence over ( ) [ ] { }, every other character
                    of s being kept. It returns that count modulo 100000
                    and whether the count is at least 100000: the answer
                    printed is the residue, padded with leading zeros to 5
                    digits when the flag is set (the last 5 digits).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray PrimString.
From Stdlib Require Import String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A string is a String.string, a character an ascii. *)

(* The number of characters of s. *)
Definition slen (s : string) : N := N.of_nat (String.length s).

(* [o] is the opening bracket that [c] closes. *)
Definition matching (o c : ascii) : Prop :=
     (o = "("%char /\ c = ")"%char)
  \/ (o = "["%char /\ c = "]"%char)
  \/ (o = "{"%char /\ c = "}"%char).

(* The statement's grammar: the empty string; (A), [A] and {A} for a
   regular A; AB for regular A and B. *)
Inductive regular : string -> Prop :=
  | regular_empty : regular ""
  | regular_wrap  : forall o c a, matching o c -> regular a ->
      regular (String o (a ++ String c ""))
  | regular_cat   : forall a b, regular a -> regular b -> regular (a ++ b).

(* t is s with each '?' replaced by some character: same length, and at
   every position s has '?' or the character of t. *)
Definition completion (s t : string) : Prop :=
  String.length t = String.length s /\
  forall k, (k < String.length s)%nat ->
    String.get k s = Some "?"%char \/ String.get k t = String.get k s.

(* The characters that can appear in the input string. *)
Definition input_char (c : ascii) : Prop :=
  In c ["("; ")"; "["; "]"; "{"; "}"; "?"]%char.

Record valid_input (s : string) : Prop := {
  (* an even integer N (2 <= N <= 200), the length of the string *)
  vi_len  : 2 <= slen s <= 200;
  vi_even : N.even (slen s) = true;
  (* the string is a bracket-sequence some of whose characters are
     illegible, represented by the '?' character *)
  vi_chars : forall k c, String.get k s = Some c -> input_char c;
}.

(* The answer: l lists, without repetition, exactly the regular completions
   of s; the output is their number modulo 100000 and whether that number
   is at least 100000, so that its last 5 digits are the residue written
   with 5 digits (leading zeros included) when the flag is set, and the
   residue itself (the whole number) otherwise.  The residue alone would
   print 05292 as 5292. *)
Definition zapis_spec (s : string) (o : N * bool) : Prop :=
  exists l : list string,
    NoDup l /\
    (forall t, In t l <-> completion s t /\ regular t) /\
    o = (N.of_nat (List.length l) mod 100000,
         100000 <=? N.of_nat (List.length l)).

Program zapis : PrimString.string -> uint * bool.

Specification zapis_correct : forall (s : string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists o : N * bool, repr (zapis x) o /\ zapis_spec s o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
