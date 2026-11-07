(** * Baza *)

(** ** Description *)

(** For each query word, scan an ordered dictionary until a match is found
    or the dictionary ends. Return the number of words examined plus the sum
    of their common-prefix lengths with the query.

    [@kattis baza]
    - Difficulty: 5.5

    **Kattis Bounds**
    - 1 to 30,000 dictionary words and 1 to 30,000 queries.
    - Words contain fewer than 30 lowercase letters; dictionary entries are
      distinct. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
5
hobotnica
robot
hobi
hobit
robi
4
robi
hobi
hobit
rakija
Output:
12
10
16
7
*)

(** ** [@hide] Environment *)

(* @function        baza
   @signature       array PrimString.string -> array PrimString.string -> array uint
   @math_signature  list String.string -> list String.string -> list N
   @summary         [baza database queries] answers every query word of
                    queries, in order: the number of steps the statement's
                    primitive search takes to find it in database, i.e. the
                    number of database words it is compared to (in database
                    order, up to and including the word equal to it, or all
                    of them when it is absent) plus the sum of the lengths
                    of the longest common prefixes of the query and each of
                    those words.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A word is a String.string, a letter its byte
  code. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of letters of word. *)
Definition slen (word : String.string) : N :=
  N.of_nat (String.length word).

(** Every letter of word is a lowercase English letter,
    'a' (97) to 'z' (122). *)
Definition lowercase (word : String.string) : Prop :=
  forall (k : nat)
    (letter : ascii), String.get k word = Some letter ->
    97 <= N_of_ascii letter <= 122.

(** Word word starts with word prefix. *)
Definition starts_with
  (word prefix : String.string) : Prop :=
  exists suffix, word = String.append prefix suffix.

(** prefix_length is the length of the longest common
    prefix of word and word': the longest word that both
    word and word' start with. *)
Definition lcp_length (word word' : String.string)
  (prefix_length : N)
  : Prop :=
  exists prefix,
    starts_with word prefix /\ starts_with word' prefix /\
    slen prefix = prefix_length /\
    forall other, starts_with word other
      -> starts_with word' other ->
      slen other <= prefix_length.

(** The search compares query with the first compared
    database words: up to and including the one equal to
    query (at position k, from 0), or all of them when
    there is none. *)
Definition compared_count (database : list String.string)
  (query : String.string) (compared : N) : Prop :=
  (exists k, nth_error database (N.to_nat k) = Some query /\
     compared = k + 1) \/
  (~ In query database /\ compared = len database).

(** steps is the number of steps of the search for
    query: the number compared of words it is compared
    to, plus the sum of the longest common prefix
    lengths of query with each of them. *)
Definition search_steps (database : list String.string)
  (query : String.string) (steps : N) : Prop :=
  exists compared prefix_lengths,
    compared_count database query compared /\
    Forall2 (lcp_length query) (firstn
      (N.to_nat compared) database)
      prefix_lengths /\
    steps = compared + fold_right N.add 0 prefix_lengths.

(** [@inside baza_correct] The statement's bounds, for
    one test case. *)
Record valid_input
  (database queries : list String.string) : Prop := {
  (* 1 <= N <= 30 000, the number of words in the database
    *)
  vi_n : 1 <= len database <= 30000;
  (* 1 <= Q <= 30 000, the number of words searched for *)
  vi_q : 1 <= len queries <= 30000;
  (* all words in the input will be strings of less than 30
    lowercase
     letters of the English alphabet *)
  vi_db_len : Forall (fun word => slen word < 30) database;
  vi_qs_len : Forall (fun word => slen word < 30) queries;
  vi_db_lower : Forall lowercase database;
  vi_qs_lower : Forall lowercase queries;
  (* all words in the database will be distinct *)
  vi_distinct : NoDup database;
}.

(** ** Correctness *)

(** [@requirement] [@short must count the search steps
    for each query word.] One answer per query, in
    order: the number of steps of its search. *)
Definition baza_spec (database queries : list String.string)
  (output : list N) : Prop :=
  Forall2 (search_steps database) queries output.

(** ** Interface *)

(** The machine-level interface.
    - Input [database]:
    - Input [queries]:
    - Output [output]: *)
Program baza :
  array PrimString.string -> array PrimString.string
    -> array uint.

(** ** Bridge *)

(** [@requirement baza_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying [baza_spec]. *)
Specification baza_correct :
  forall (database queries : list String.string)
         (database_arr queries_arr : array
           PrimString.string),
  valid_input database queries ->
  repr database_arr database -> repr queries_arr queries ->
  exists output : list N,
    repr (baza database_arr queries_arr) output /\
    baza_spec database queries output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
