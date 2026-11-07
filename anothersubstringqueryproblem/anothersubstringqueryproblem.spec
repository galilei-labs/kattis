(** * Another Substring Query Problem *)

(** ** Description *)

(** For each pattern and occurrence rank, find the starting position of that
    occurrence in a text, counting overlaps. Return -1 if it does not exist.

    [@kattis anothersubstringqueryproblem]
    - Difficulty: 7.7

    **Kattis Bounds**
    - Text length and query count from 1 to 200000.
    - Nonempty lowercase patterns, with total length at most 200000.
    - Occurrence ranks from 1 to the text length. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
abacabadabacaba
4
a 7
e 3
bac 2
abada 1
Output:
13
-1
10
5
*)

(** ** [@hide] Environment *)

(* @function        kth_occurrences
   @signature       PrimString.string -> array PrimString.string -> array uint
                    -> array sint
   @math_signature  String.string -> list String.string -> list N -> list Z
   @summary         [kth_occurrences text patterns ranks] answers every query
                    at once: cell q is the 1-based position in text where
                    the ranks_q-th occurrence, from the left, of the pattern
                    patterns_q starts, or -1 when patterns_q occurs fewer
                    than ranks_q times in text.  Occurrences may overlap.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The queries are the parallel columns patterns
  and ranks of
   the q query lines; positions are 0-based inside the math
     side, the
   answer adds 1. *)

(** ** Definitions *)

(** The number of elements of l, and the number of
    characters of word. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).
(** The number of characters in the string. *)
Definition slen (word : string) : N :=
  N.of_nat (String.length word).

(** Every character of word is a lower-case letter, 'a'
    (97) to 'z' (122). *)
Definition lowercase (word : string) : Prop :=
  Forall (fun character => 97 <= N_of_ascii character <=
    122)
    (list_ascii_of_string word).

(** The sum of the lengths of the patterns. *)
Definition total_len (patterns : list string) : N :=
  fold_right
    (fun pattern acc => slen pattern + acc) 0 patterns.

(** pattern occurs in text starting at the 0-based
    position position: the |pattern| characters of text
    from position are those of pattern. *)
Definition starts_at (text pattern : string)
  (position : nat) : bool :=
  ((position + String.length pattern <=? String.length
    text)%nat &&
   String.eqb (substring position
     (String.length pattern) text) pattern)%bool.

(** The 0-based positions where pattern occurs in text,
    in increasing order. *)
Definition occurrences (text pattern : string) : list N :=
  map N.of_nat
    (filter (starts_at text pattern) (seq 0
      (String.length text))).

(** The answer to the query (pattern, rank): 1 + the
    position of the rank-th occurrence, or -1 if pattern
    occurs fewer than rank times. *)
Definition answer (text pattern : string) (rank : N) : Z :=
  match nth_error (occurrences text pattern)
    (N.to_nat rank - 1) with
  | Some position => Z.of_N position + 1
  | None => -1
  end.

(** [@inside kth_occurrences_correct] The statement's
    input bounds and guarantees. *)
Record valid_input (text : string) (patterns : list string)
  (ranks : list N)
    : Prop := {
  (* a single string s (1 <= |s| <= 2*10^5), s the text *)
  vi_s_length : 1 <= slen text <= 2 * 10 ^ 5;
  (* It will consist only of lower-case letters. *)
  vi_s_lower : lowercase text;
  (* q (1 <= q <= 2*10^5), the number of queries that follow
    *)
  vi_q : 1 <= len patterns <= 2 * 10 ^ 5;
  (* Each of the next q lines contains a string t
    (a pattern) and an
     integer k (a rank). *)
  vi_ks_length : len ranks = len patterns;
  (* a string t (1 <= |t|) *)
  vi_t_length : Forall
    (fun pattern => 1 <= slen pattern) patterns;
  (* The string t will consist only of lower-case letters.
    *)
  vi_t_lower : Forall lowercase patterns;
  (* an integer k (1 <= k <= |s|) *)
  vi_k : Forall (fun rank => 1 <= rank <= slen text) ranks;
  (* The sum of all |t|'s will be <= 2*10^5 *)
  vi_t_sum : total_len patterns <= 2 * 10 ^ 5;
}.

(** ** Correctness *)

(** [@requirement] [@short must return the requested
    occurrence of each query string.] One answer per
    query, in the order of the queries. *)
Definition kth_occurrences_spec (text : string)
  (patterns : list string)
    (ranks : list N) (output : list Z) : Prop :=
  len output = len patterns /\
  forall (query : nat) pattern rank,
    nth_error patterns query = Some pattern ->
    nth_error ranks query = Some rank ->
    nth_error output query = Some
      (answer text pattern rank).

(** ** Interface *)

(** The machine-level interface.
    - Input [text]:
    - Input [patterns]:
    - Input [ranks]:
    - Output [output]: *)
Program kth_occurrences :
  PrimString.string -> array PrimString.string
    -> array uint -> array sint.

(** ** Bridge *)

(** [@requirement kth_occurrences_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [kth_occurrences_spec]. *)
Specification kth_occurrences_correct :
  forall (text : string) (patterns : list string)
    (ranks : list N)
         (text_str : PrimString.string)
         (patterns_arr : array PrimString.string)
           (ranks_arr : array uint),
  valid_input text patterns ranks ->
  repr text_str text -> repr patterns_arr patterns
    -> repr ranks_arr ranks ->
  exists output : list Z,
    repr (kth_occurrences text_str patterns_arr ranks_arr)
      output /\
    kth_occurrences_spec text patterns ranks output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
