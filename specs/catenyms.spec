(* @function        catenyms
   @signature       array PrimString.string -> option (array PrimString.string)
   @math_signature  list String.string -> option (list String.string)
   @summary         Given a dictionary of distinct lower-case words,
                    [catenyms words] returns the words arranged as the
                    lexicographically smallest compound catenym that
                    contains each dictionary word exactly once (three or
                    more words, the last letter of each the first letter of
                    the next), or None (the "***" line) when there is none.
                    Lexicographic order is that of the printed line, the
                    words joined by periods.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii Permutation.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A word is a String.string ; a character is its byte code. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of letters of w. *)
Definition slen (w : string) : N := N.of_nat (String.length w).

(* Every character of w is one of a ... z. *)
Definition lowercase (w : string) : Prop :=
  forall k c, String.get k w = Some c ->
    97 <= Ascii.N_of_ascii c <= 122.

(* a.b is a catenym : the last letter of a is the first letter of b. *)
Definition forms_catenym (a b : string) : Prop :=
  String.get (String.length a - 1) a = String.get 0 b.

(* A compound catenym : three or more words, each adjacent pair a catenym. *)
Definition compound_catenym (c : list string) : Prop :=
  3 <= len c /\
  forall j, (S j < List.length c)%nat ->
    forms_catenym (nth j c ""%string) (nth (S j) c ""%string).

(* c is a compound catenym that contains each dictionary word exactly once
   (and nothing else) : a rearrangement of the dictionary. *)
Definition is_answer (words c : list string) : Prop :=
  compound_catenym c /\ Permutation c words.

(* The printed line : the words of c joined by periods. *)
Definition text (c : list string) : string := String.concat "." c.

(* The statement's guarantees, for one test case. *)
Record valid_input (words : list string) : Prop := {
  (* 3 <= n <= 1000, the number of words in the dictionary *)
  vi_n : 3 <= len words <= 1000;
  (* each word is a string of between 1 and 20 lowercase letters *)
  vi_word_length : Forall (fun w => 1 <= slen w <= 20) words;
  vi_word_lower : Forall lowercase words;
  (* n distinct dictionary words *)
  vi_distinct : NoDup words;
}.

(* "***" (None) exactly when no compound catenym uses each word once ;
   otherwise the lexicographically smallest one, by its printed line. *)
Definition catenyms_spec (words : list string) (o : option (list string)) : Prop :=
  match o with
  | None => ~ exists c, is_answer words c
  | Some c =>
      is_answer words c /\
      forall c', is_answer words c' -> String.compare (text c) (text c') <> Gt
  end.

Program catenyms : array PrimString.string -> option (array PrimString.string).

Specification catenyms_correct :
  forall (words : list string) (x : array PrimString.string),
  valid_input words -> repr x words ->
  exists o : option (list string), repr (catenyms x) o /\ catenyms_spec words o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
