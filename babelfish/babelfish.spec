(** * Babelfish *)

(** ** Description *)

(** [babelfish english_words foreign_words
    message_words] translates the message word by word
    with the dictionary whose i-th entry pairs the
    English word english_words[i] with the foreign word
    foreign_words[i]: the k-th answer is Some
    english_word when message_words[k] is a foreign word
    of the dictionary and english_word its English word,
    and None (printed "eh") when message_words[k] is not
    in the dictionary.
    [@kattis babelfish]
    - Difficulty: 2.0 *)

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

(** [@inside babelfish_correct] The statement's
    guarantees, for the one test case. *)
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

(** The answer for the foreign word foreign_word: Some
    english_word exactly when the dictionary translates
    foreign_word as english_word, so None exactly when
    foreign_word is not in the dictionary. *)
Definition answer
  (english_words foreign_words : list string)
    (foreign_word : string)
      (translation : option string) : Prop :=
  forall english_word, translation = Some english_word <->
    translates english_words foreign_words foreign_word
      english_word.

(** ** Correctness *)

(** [@requirement] [@short must translate each query
    word using the dictionary.] One answer per message
    word, in order. *)
Definition babelfish_spec
    (english_words foreign_words message_words : list
      string)
    (output : list (option string)) : Prop :=
  Forall2 (answer english_words foreign_words) message_words
    output.

(** ** Interface *)

(** The machine-level interface.
    - Input [english_words]:
    - Input [foreign_words]:
    - Input [message_words]:
    - Output [output]: *)
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
