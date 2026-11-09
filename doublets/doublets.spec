(** * Doublets *)

(** ** Description *)

(** For each pair of words, find a shortest chain of dictionary words
    changing exactly one letter at each step, or report that no chain
    exists. Both endpoints must belong to the dictionary.

    [@kattis doublets]
    - Difficulty: 7.8
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - At most $25{,}143$ dictionary words, each with $1\text{ to }16$ lowercase letters.
    - At most $10$ query pairs. *)

(** ** Examples *)

(** - Input convention: Dictionary words, a blank line, then source-destination word pairs.
    - Output convention: One shortest chain with a word per line, or No solution.; blank lines separate cases. *)
(* Input:
booster
rooster
roaster
coasted
roasted
coastal
postal

booster roasted
coastal postal
Output:
booster
rooster
roaster
roasted

No solution.
*)

(** ** [@hide] Environment *)
(* @function        doublets
   @signature       array PrimString.string -> array PrimString.string ->
                    array PrimString.string ->
                    array (option (array PrimString.string))
   @math_signature  list string -> list string -> list string ->
                    list (option (list string))
   @summary         [doublets dictionary start_words end_words] answers every
                    query k of one input: entry k is a shortest chain of
                    dictionary words from start_words_k to end_words_k in
                    which consecutive words differ in exactly one letter, or
                    None when no such chain exists.  Every word of a chain,
                    endpoints included, is in dictionary; when
                    start_words_k = end_words_k is in dictionary the chain is
                    that one word.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Ascii.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. A word is a String.string; a letter is compared by its
    code. The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of letters of word. *)
Definition slen (word : string) : N :=
  N.of_nat (String.length word).

(** Every letter of word is a lower case letter, 'a' to 'z'. *)
Definition lower (word : string) : Prop :=
  forall k letter, String.get k word = Some letter ->
    97 <= N_of_ascii letter <= 122.

(** word and word' are a doublet: they have the same length and differ
    at exactly one position. *)
Definition doublet (word word' : string) : Prop :=
  String.length word = String.length word' /\
  exists k, (k < String.length word)%nat /\
    String.get k word <> String.get k word' /\
    forall j, (j < String.length word)%nat -> j <> k ->
      String.get j word = String.get j word'.

(** chain is a sequence of dictionary words that begins with start_word,
    ends with end_word, and in which each pair of adjacent words is
    a doublet. *)
Definition is_chain (dictionary : list string)
  (start_word end_word : string)
    (chain : list string) : Prop :=
  nth_error chain 0 = Some start_word /\
  nth_error chain (List.length chain - 1) = Some end_word /\
  Forall (fun word => In word dictionary) chain /\
  forall k word word', nth_error chain k = Some word ->
    nth_error chain (S k) = Some word' ->
      doublet word word'.

(** Some shortest word chain between the endpoints, or None exactly when no chain exists. *)
Definition answer (dictionary : list string)
  (start_word end_word : string)
    (chain_option : option (list string)) : Prop :=
  match chain_option with
  | Some chain => is_chain dictionary start_word end_word
    chain /\
      forall chain', is_chain dictionary start_word end_word
        chain' ->
        len chain <= len chain'
  | None => forall chain, ~ is_chain dictionary start_word
    end_word chain
  end.

(** [@inside doublets_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (dictionary start_words end_words : list string)
    : Prop := {
  (* a dictionary of up to 25 143 words *)
  vi_dict_len : len dictionary <= 25143;
  (* words not exceeding 16 letters each; one per line,
     the dictionary being terminated by an empty line, so
     no word is empty *)
  vi_word_len : Forall (fun word => 1 <= slen word <= 16)
    dictionary;
  (* lower case words *)
  vi_lower : Forall lower dictionary;
  (* a number of word pairs (at most 10) *)
  vi_queries : len start_words <= 10;
  (* the pairs: query k is (start_words_k, end_words_k) *)
  vi_pairs : len start_words = len end_words;
  (* "You are then given a number of pairs of words.":
     the statement gives no bound on the query words (its
     "not exceeding 16 letters" is said of the
     dictionary's words), so the bound is the
     representability limit of PrimString.string,
     PrimString.max_length = 16777211. Human : we may
     also assume they are not more than 16 letters long
     as that seems reasonnable *)
  vi_src_len : Forall (fun word => slen word <= 16777211)
    start_words;
  vi_tgt_len : Forall (fun word => slen word <= 16777211)
    end_words;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry is a shortest dictionary-word chain between the corresponding
    endpoints, changing one letter at each step, or None if no chain exists. *)
Definition doublets_spec
  (dictionary start_words end_words : list string)
    (output : list (option (list string))) : Prop :=
  Forall2 (fun query chain_option =>
             answer dictionary (fst query) (snd query)
               chain_option)
    (combine start_words end_words) output.

(** ** Interface *)

(** For each pair of words, find a shortest chain of dictionary words changing exactly one
    letter at each step, or report that no chain exists. Both endpoints must belong to
    the dictionary.
    - Input [dictionary]: Words permitted in transformation chains.
    - Input [start_words]: Starting word of each query.
    - Input [end_words]: Destination word of each query.
    - Output [output]: Each output entry is a shortest dictionary-word chain between the corresponding endpoints, changing one letter at each step, or None if no chain exists. *)
Program doublets :
  array PrimString.string -> array PrimString.string ->
  array PrimString.string ->
    array (option (array PrimString.string)).

(** ** Bridge *)

(** [@requirement doublets_spec] [@fold full correctness statement] On
    valid represented inputs, [doublets] returns a represented
    output satisfying [doublets_spec]. *)
Specification doublets_correct :
  forall (dictionary start_words end_words : list string)
         (dictionary_arr start_words_arr end_words_arr
            : array PrimString.string),
  valid_input dictionary start_words end_words ->
  repr dictionary_arr dictionary ->
    repr start_words_arr start_words ->
  repr end_words_arr end_words ->
  exists output : list (option (list string)),
    repr (doublets dictionary_arr start_words_arr
      end_words_arr)
      output /\
    doublets_spec dictionary start_words end_words output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
