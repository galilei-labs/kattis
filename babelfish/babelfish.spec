(** * Babelfish *)

(** ** Description *)

(** Translate each query word using a dictionary of word pairs, reporting
    words that have no translation.

    [@kattis babelfish]
    - Difficulty: 2.0
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - At most $100{,}000$ dictionary entries and $100{,}000$ query words.
    - Words contain $1\text{ to }10$ lowercase letters; dictionary keys are unique. *)

(** ** Examples *)

(** - Input convention: Translation pairs, a blank line, then one query word per line.
    - Output convention: One translation per line, or eh for a word absent from the dictionary. *)
(* Input:
dog ogday
cat atcay
pig igpay
froot ootfray
loops oopslay

atcay
ittenkay
oopslay
Output:
cat
eh
loops
*)

(** ** [@hide] Environment *)

(* @function        babelfish
   @signature       array PrimString.string -> array PrimString.string ->
                    array PrimString.string -> array (option PrimString.string)
   @math_signature  list string -> list string -> list string ->
                    list (option string)
   @summary         [babelfish english_words foreign_words message_words]
                    translates the message word by word with the dictionary
                    whose i-th entry pairs the English word english_words[i]
                    with the foreign word foreign_words[i]: the k-th answer
                    is Some english_word when message_words[k] is a foreign
                    word of the dictionary and english_word its English
                    word, and None (printed "eh") when message_words[k] is
                    not in the dictionary.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require PrimString.
From Stdlib Require Import String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The dictionary lines "english foreign" are
  two parallel lists,
   one per column: english_words and foreign_words. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The i-th element of l, if any. *)
Definition at_ {A} (l : list A) (i : N) : option A :=
  nth_error l (N.to_nat i).

(** A word of the input: a non-empty sequence of at most
    10 lowercase letters (character codes 97 'a' to 122
    'z'). *)
Definition word (text : string) : Prop :=
  1 <= N.of_nat (String.length text) <= 10 /\
  forall k character, String.get k text = Some character ->
    97 <= N_of_ascii character <= 122.

(** Some dictionary entry pairs the foreign word
    foreign_word with the English word english_word. *)
Definition translates
  (english_words foreign_words : list string)
    (foreign_word english_word : string) : Prop :=
  exists i, at_ foreign_words i = Some foreign_word /\
            at_ english_words i = Some english_word.

(** [@inside babelfish_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (english_words foreign_words message_words : list string)
    : Prop := {
  (* each dictionary entry is a line containing an English
    word, followed by
     a space and a foreign language word *)
  vi_entries : len english_words = len foreign_words;
  (* up to 100 000 dictionary entries *)
  vi_dict_length : len foreign_words <= 100000;
  (* a message of up to 100 000 words *)
  vi_message_length : len message_words <= 100000;
  (* each word in the input is a non-empty sequence of at
    most 10 lowercase
     letters *)
  vi_english_words : Forall word english_words;
  vi_foreign_words : Forall word foreign_words;
  vi_message_words : Forall word message_words;
  (* no foreign word appears more than once in the
    dictionary *)
  vi_distinct : NoDup foreign_words;
}.

(** Some translation when the dictionary contains the query word; None otherwise. *)
Definition answer
  (english_words foreign_words : list string)
    (foreign_word : string)
      (translation : option string) : Prop :=
  forall english_word, translation = Some english_word <->
    translates english_words foreign_words foreign_word
      english_word.

(** ** Correctness *)

(** [@requirement]
    Each output entry is the dictionary translation of the corresponding query, or None
    if the word is absent. *)
Definition babelfish_spec
    (english_words foreign_words message_words : list
      string)
    (output : list (option string)) : Prop :=
  Forall2 (answer english_words foreign_words) message_words
    output.

(** ** Interface *)

(** Translate each query word using a dictionary of word pairs, reporting words that have no
    translation.
    - Input [english_words]: Translations in dictionary order.
    - Input [foreign_words]: Foreign words paired with those translations.
    - Input [message_words]: Words to translate, in query order.
    - Output [output]: Each output entry is the dictionary translation of the corresponding query, or None if the word is absent. *)
Program babelfish :
  array PrimString.string -> array PrimString.string ->
  array PrimString.string -> array
    (option PrimString.string).

(** ** Bridge *)

(** [@requirement babelfish_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [babelfish_spec]. *)
Specification babelfish_correct :
  forall (english_words foreign_words message_words : list
    string)
         (english_words_arr foreign_words_arr
           message_words_arr
            : array PrimString.string),
  valid_input english_words foreign_words message_words ->
  repr english_words_arr english_words ->
  repr foreign_words_arr foreign_words ->
  repr message_words_arr message_words ->
  exists output : list (option string),
    repr (babelfish english_words_arr foreign_words_arr
      message_words_arr)
      output /\
    babelfish_spec english_words foreign_words message_words
      output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
