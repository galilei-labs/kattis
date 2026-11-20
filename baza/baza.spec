(** * Baza *)

(** ** Description *)

(** For each query word, scan an ordered dictionary until a match is found
    or the dictionary ends. Return the number of words examined plus the sum
    of their common-prefix lengths with the query.

    [@kattis baza]
    - Difficulty: 5.5
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Dictionary size: $1 \le n \le 3 \times 10^{4}$ and Query count: $1 \le q \le 3 \times 10^{4}$.
    - Words contain fewer than $30$ lowercase letters; dictionary entries are
      distinct. *)

(** ** Examples *)

(** - Input convention: Dictionary size and ordered words, followed by query count and query words.
    - Output convention: One search-step count per query, in input order. *)
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
                    It runs in at most c1 * (L + N + Q + 1) + c2 steps of the cost
                    model on a valid input, L the total length of the
                    database and query words ([sizes]: one trie node per
                    character inserted, one step per character looked up),
                    for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A word is a String.string, a letter its byte
  code. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters in [word]. *)
Definition slen (word : String.string) : N :=
  N.of_nat (String.length word).

(** Every character of [word] is a lowercase English letter. *)
Definition lowercase (word : String.string) : Prop :=
  forall (k : nat)
    (letter : ascii), String.get k word = Some letter ->
    97 <= N_of_ascii letter <= 122.

(** [prefix] is a prefix of [word]. *)
Definition starts_with
  (word prefix : String.string) : Prop :=
  exists suffix, word = String.append prefix suffix.

(** [prefix_length] is the length of the longest common prefix of [word] and
    [word']. *)
Definition lcp_length (word word' : String.string)
  (prefix_length : N)
  : Prop :=
  exists prefix,
    starts_with word prefix /\ starts_with word' prefix /\
    slen prefix = prefix_length /\
    forall other, starts_with word other
      -> starts_with word' other ->
      slen other <= prefix_length.

(** The search compares [query] with the first [compared] database entries, stopping
    at the first exact match or at the end of [database]. *)
Definition compared_count (database : list String.string)
  (query : String.string) (compared : N) : Prop :=
  (exists k, nth_error database (N.to_nat k) = Some query /\
     compared = k + 1) \/
  (~ In query database /\ compared = len database).

(** The sum of the supplied prefix lengths. *)
Fixpoint sum_lengths (lengths : list N) : N :=
  match lengths with
  | [] => 0
  | length :: rest => length + sum_lengths rest
  end.

(** [steps] counts one step per compared database word, plus the length of its
    longest common prefix with [query]. *)
Definition search_steps (database : list String.string)
  (query : String.string) (steps : N) : Prop :=
  exists compared prefix_lengths,
    compared_count database query compared /\
    Forall2 (lcp_length query) (firstn
      (N.to_nat compared) database)
      prefix_lengths /\
    steps = compared + sum_lengths prefix_lengths.

(** [@inside baza_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (database queries : list String.string) : Prop := {
  (* 1 <= N <= 3 * 10^4, the number of words in the database
    *)
  vi_n : 1 <= len database <= 30000;
  (* 1 <= Q <= 3 * 10^4, the number of words searched for *)
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

(** [@requirement]
    Each output entry counts the words examined plus their common-prefix lengths when
    searching the ordered dictionary for the corresponding query. *)
Definition baza_spec (database queries : list String.string)
  (output : list N) : Prop :=
  Forall2 (search_steps database) queries output.

(** ** Complexity *)

(** [@requirement] Runs in $O(D+Q+n+q+1)$ steps, where $D$ and $Q$ are the total database and query string lengths, and $n$ and $q$ their respective counts. *)
Definition baza_time_spec (c1 c2 total_database total_queries n_database n_queries steps : nat) : Prop :=
  (steps <= c1 * (total_database + total_queries + n_database + n_queries + 1) + c2)%nat.

(** ** Interface *)

(** For each query word, scan an ordered dictionary until a match is found or the dictionary
    ends. Return the number of words examined plus the sum of their common-prefix
    lengths with the query.
    - Input [database]: Dictionary words in search order.
    - Input [queries]: Words whose search costs are requested.
    - Output [output]: Each output entry counts the words examined plus their common-prefix lengths when searching the ordered dictionary for the corresponding query. *)
Program baza :
  array PrimString.string -> array PrimString.string
    -> array uint.

(** [@example baza]
    - Sample: 1
    - Input [database]: ["hobotnica"; "robot"; "hobi"; "hobit"; "robi"]%string
    - Input [queries]: ["robi"; "hobi"; "hobit"; "rakija"]%string
    - Output [output]: [12; 10; 16; 7]
*)

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

(** ** Complexity *)

(** [@hide] [baza_cost] is the cost translation of [baza] (the judge
    recomputes it and compares) ... *)
Complexity baza_cost for baza.

(** [@fold complexity bound] ... and runs in at most c1 * (L + N + Q + 1) + c2 steps of the cost model on a valid input, L the total length of the database and query words ([sizes]), N and Q their numbers (one trie node per character inserted, one step per character looked up, a constant per word), for two constants
    quantified before the inputs, on every valid input. [@requirement baza_time_spec] *)
Specification baza_time : exists c1 c2 : nat,
  forall (database queries : list String.string)
  (database_arr queries_arr : array
  PrimString.string),
  valid_input database queries ->
  repr database_arr database -> repr queries_arr queries ->
  baza_time_spec c1 c2 (sizes database_arr) (sizes queries_arr) (size database_arr) (size queries_arr) (cost2 baza_cost database_arr queries_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
