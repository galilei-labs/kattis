(** * Catenyms *)

(** ** Description *)

(** Arrange all given words exactly once so each word's last letter matches
    the next word's first letter. Return the lexicographically smallest
    period-separated arrangement, or report that none exists.

    [@kattis catenyms]
    - Difficulty: 6.5

    **Kattis Bounds**
    - 3 to 1,000 distinct words, each containing 1 to 20 lowercase letters. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
2
6
aloha
arachnid
dog
gopher
rat
tiger
3
oak
maple
elm
Output:
aloha.arachnid.dog.gopher.rat.tiger
***
*)

(** ** [@hide] Environment *)

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

(* Math side.  A word is a String.string ; a character is
  its byte code. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of letters of word. *)
Definition slen (word : string) : N :=
  N.of_nat (String.length word).

(** Every character of word is one of a ... z. *)
Definition lowercase (word : string) : Prop :=
  forall position character, String.get position word = Some
    character ->
    97 <= Ascii.N_of_ascii character <= 122.

(** left.right is a catenym : the last letter of left is
    the first letter of right. *)
Definition forms_catenym (left right : string) : Prop :=
  String.get
    (String.length left - 1) left = String.get 0 right.

(** A compound catenym : three or more words, each
    adjacent pair a catenym. *)
Definition compound_catenym (chain : list string) : Prop :=
  3 <= len chain /\
  forall j, (S j < List.length chain)%nat ->
    forms_catenym (nth j chain ""%string) (nth
      (S j) chain ""%string).

(** chain is a compound catenym that contains each
    dictionary word exactly once (and nothing else) : a
    rearrangement of the dictionary. *)
Definition is_answer (words chain : list string) : Prop :=
  compound_catenym chain /\ Permutation chain words.

(** The printed line : the words of chain joined by
    periods. *)
Definition text (chain : list string) : string :=
  String.concat "." chain.

(** [@inside catenyms_correct] The statement's
    guarantees, for one test case. *)
Record valid_input (words : list string) : Prop := {
  (* 3 <= n <= 1000, the number of words in the dictionary
    *)
  vi_n : 3 <= len words <= 1000;
  (* each word is a string of between 1 and 20 lowercase
    letters *)
  vi_word_length : Forall
    (fun word => 1 <= slen word <= 20) words;
  vi_word_lower : Forall lowercase words;
  (* n distinct dictionary words *)
  vi_distinct : NoDup words;
}.

(** ** Correctness *)

(** [@requirement] [@short must return the first
    compound catenym, if one exists.] "***" (None)
    exactly when no compound catenym uses each word once
    ; otherwise the lexicographically smallest one, by
    its printed line. *)
Definition catenyms_spec (words : list string)
  (output : option (list string))
  : Prop :=
  match output with
  | None => ~ exists chain, is_answer words chain
  | Some chain =>
      is_answer words chain /\
      forall chain', is_answer words chain' ->
        String.compare (text chain) (text chain') <> Gt
  end.

(** ** Interface *)

(** The machine-level interface.
    - Input [words]:
    - Output [output]: *)
Program catenyms : array PrimString.string -> option
  (array PrimString.string).

(** ** Bridge *)

(** [@requirement catenyms_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [catenyms_spec]. *)
Specification catenyms_correct :
  forall (words : list string)
    (words_arr : array PrimString.string),
  valid_input words -> repr words_arr words ->
  exists output : option (list string),
    repr (catenyms words_arr) output
      /\ catenyms_spec words output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
