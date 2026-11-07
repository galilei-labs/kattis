(* @function        zapis
   @signature       PrimString.string -> uint * bool
   @math_signature  String.string -> N * bool
   @summary         [zapis sequence] counts the ways to replace every '?' of
                    sequence by a character so that the result is a regular
                    bracket-sequence over ( ) [ ] { }, every other character
                    of sequence being kept. It returns that count modulo
                    100000 and whether the count is at least 100000: the
                    answer printed is the residue, padded with leading zeros
                    to 5 digits when the flag is set (the last 5 digits).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray PrimString.
From Stdlib Require Import String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A string is a String.string, a character an ascii. *)

(* The number of characters of text. *)
Definition slen (text : string) : N := N.of_nat (String.length text).

(* [opening] is the opening bracket that [closing] closes. *)
Definition matching (opening closing : ascii) : Prop :=
     (opening = "("%char /\ closing = ")"%char)
  \/ (opening = "["%char /\ closing = "]"%char)
  \/ (opening = "{"%char /\ closing = "}"%char).

(* The statement's grammar: the empty string; (A), [A] and {A} for a
   regular A; AB for regular A and B. *)
Inductive regular : string -> Prop :=
  | regular_empty : regular ""
  | regular_wrap  : forall opening closing inner,
      matching opening closing -> regular inner ->
      regular (String opening (inner ++ String closing ""))
  | regular_cat   : forall prefix suffix,
      regular prefix -> regular suffix -> regular (prefix ++ suffix).

(* candidate is sequence with each '?' replaced by some character: same
   length, and at every position sequence has '?' or the character of
   candidate. *)
Definition completion (sequence candidate : string) : Prop :=
  String.length candidate = String.length sequence /\
  forall k, (k < String.length sequence)%nat ->
    String.get k sequence = Some "?"%char \/
    String.get k candidate = String.get k sequence.

(* The characters that can appear in the input string. *)
Definition input_char (character : ascii) : Prop :=
  In character ["("; ")"; "["; "]"; "{"; "}"; "?"]%char.

Record valid_input (sequence : string) : Prop := {
  (* an even integer N (2 <= N <= 200), the length of the string *)
  vi_len  : 2 <= slen sequence <= 200;
  vi_even : N.even (slen sequence) = true;
  (* the string is a bracket-sequence some of whose characters are
     illegible, represented by the '?' character *)
  vi_chars : forall k character,
    String.get k sequence = Some character -> input_char character;
}.

(* The answer: completions lists, without repetition, exactly the regular
   completions of sequence; the output is their number modulo 100000 and
   whether that number is at least 100000, so that its last 5 digits are
   the residue written with 5 digits (leading zeros included) when the flag
   is set, and the residue itself (the whole number) otherwise.  The
   residue alone would print 05292 as 5292. *)
Definition zapis_spec (sequence : string) (output : N * bool) : Prop :=
  exists completions : list string,
    NoDup completions /\
    (forall candidate, In candidate completions <->
       completion sequence candidate /\ regular candidate) /\
    match output with
    | (residue, wrapped) =>
        residue = N.of_nat (List.length completions) mod 100000 /\
        wrapped = (100000 <=? N.of_nat (List.length completions))
    end.

Program zapis : PrimString.string -> uint * bool.

Specification zapis_correct :
  forall (sequence : string) (sequence_str : PrimString.string),
  valid_input sequence -> repr sequence_str sequence ->
  exists output : N * bool,
    repr (zapis sequence_str) output /\ zapis_spec sequence output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
