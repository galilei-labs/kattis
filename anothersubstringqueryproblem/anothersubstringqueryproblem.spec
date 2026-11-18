(** * Another Substring Query Problem *)

(** ** Description *)

(** Each query gives a pattern and a positive occurrence rank. Find the starting
    position of that occurrence in the text, ordering occurrences from left to
    right and counting overlaps. Both occurrence ranks and reported positions
    start at one. Return -1 if the pattern has fewer occurrences than requested.

    [@kattis anothersubstringqueryproblem]
    - Difficulty: 7.7
    - CPU time limit: 6 seconds
    - Memory limit: 2048 MB

    **Kattis Bounds**
    - Text length and query count: $1 \le n, q \le 2 \times 10^{5}$.
    - Nonempty lowercase patterns, with total length at most $2 \times 10^{5}$.
    - Occurrence ranks: $1 \le k \le n$. *)

(** ** Examples *)

(** - Input convention: Text, query count, then one pattern and occurrence rank per query.
    - Output convention: One 1-based starting position per query, or -1 if the occurrence does not exist. *)
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
                    It runs in at most c1 * ((n + 1) * (log2 n + 1)^2 + (P +
                    q + 1) * (log2 n + 1)) + c2 steps of the cost model on a
                    valid input, n the length of the text, q the number of
                    queries and P their total length ([sizes]: the suffix
                    array by prefix doubling with a merge sort per round,
                    the persistent segment tree, then per query two binary
                    searches of |t| log n and one k-th query of log n), for
                    two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Ascii.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* The queries are the parallel columns patterns
  and ranks of
   the q query lines; positions are 0-based inside the math
     side, the
   answer adds 1. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).
(** The number of characters in [word]. *)
Definition slen (word : string) : N :=
  N.of_nat (String.length word).

(** Every character of [word] is a lowercase English letter, from 'a' (ASCII 97)
    through 'z' (ASCII 122). *)
Definition lowercase (word : string) : Prop :=
  Forall (fun character => 97 <= N_of_ascii character <=
    122)
    (list_ascii_of_string word).

(** The sum of the character counts of all strings in [patterns]. *)
Fixpoint total_len (patterns : list string) : N :=
  match patterns with
  | [] => 0
  | pattern :: rest => slen pattern + total_len rest
  end.

(** Test whether [pattern] occurs in [text] starting at the zero-based character
    index [position], with the whole pattern contained in the text. *)
Definition starts_at (text pattern : string)
  (position : nat) : bool :=
  ((position + String.length pattern <=? String.length
    text)%nat &&
   String.eqb (substring position
     (String.length pattern) text) pattern)%bool.

(** All zero-based starting indices of [pattern] in [text], in increasing order,
    including overlapping occurrences. *)
Definition occurrences (text pattern : string) : list N :=
  map N.of_nat
    (filter (starts_at text pattern) (seq 0
      (String.length text))).

(** [answer text pattern rank] is the one-based starting position of occurrence
    number [rank] of [pattern] in [text]. Occurrences are ordered by starting
    position from left to right, including overlaps. Return -1 if there are fewer
    than [rank] occurrences. Valid queries have [rank] at least one; this helper
    treats a zero rank as one. *)
Definition answer (text pattern : string) (rank : N) : Z :=
  match nth_error (occurrences text pattern)
    (N.to_nat rank - 1) with
  | Some position => Z.of_N position + 1
  | None => -1
  end.

(** [@inside kth_occurrences_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (text : string) (patterns : list string)
  (ranks : list N)
    : Prop := {
  (* a single string s (1 <= |s| <= 2 * 10^5), s the text *)
  vi_s_length : 1 <= slen text <= 2 * 10 ^ 5;
  (* It will consist only of lower-case letters. *)
  vi_s_lower : lowercase text;
  (* q (1 <= q <= 2 * 10^5), the number of queries that follow
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
  (* The sum of all |t|'s will be <= 2 * 10^5 *)
  vi_t_sum : total_len patterns <= 2 * 10 ^ 5;
}.

(** ** Correctness *)

(** [@requirement]
    [output] contains one answer per entry of [patterns], in the same order.
    Each pattern is paired with the corresponding entry of [ranks]. Its answer
    is the one-based starting position in [text] of that occurrence, counting
    from left to right and including overlaps, or -1 if it does not exist. *)
Definition kth_occurrences_spec (text : string)
  (patterns : list string)
    (ranks : list N) (output : list Z) : Prop :=
  len output = len patterns /\
  forall (query : nat) pattern rank,
    nth_error patterns query = Some pattern ->
    nth_error ranks query = Some rank ->
    nth_error output query = Some
      (answer text pattern rank).

(** ** Complexity *)

(** [@requirement] Runs in $O((n+1)\log^2(n+2)+(L+q+1)\log(n+2))$ steps, where $n$ is the text length, $q$ the number of patterns, and $L$ their total length. *)
Definition kth_occurrences_time_spec (c1 c2 n_text total_patterns n_patterns steps : nat) : Prop :=
  (steps <= c1 * ((n_text + 1) * (Nat.log2 (n_text) + 1) * (Nat.log2 (n_text) + 1) + (total_patterns + n_patterns + 1) * (Nat.log2 (n_text) + 1)) + c2)%nat.

(** ** Interface *)

(** Answer the queries given by corresponding entries of [patterns] and [ranks].
    Occurrences are ordered from left to right and may overlap.
    - Input [text]: Lowercase text to search.
    - Input [patterns]: Nonempty lowercase pattern for each query, in query order.
    - Input [ranks]: One-based occurrence rank for each entry of [patterns]; this
      array has the same length as [patterns].
    - Output [output]: One answer per query, in the same order: the one-based
      starting position in [text], or -1 if the requested occurrence is absent. *)
Program kth_occurrences :
  PrimString.string -> array PrimString.string
    -> array uint -> array sint.

(** [@example kth_occurrences]
    - Sample: 1
    - Input [text]: "abacabadabacaba"%string
    - Input [patterns]: ["a"; "e"; "bac"; "abada"]%string
    - Input [ranks]: [7; 3; 2; 1]
    - Output [output]: [13; -1; 10; 5]%Z
*)

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

(** ** Complexity *)

(** [@hide] [kth_occurrences_cost] is the cost translation of [kth_occurrences] (the judge
    recomputes it and compares) ... *)
Complexity kth_occurrences_cost for kth_occurrences.

(** [@fold complexity bound] ... and runs in at most c1 * ((n + 1) * (log2 n + 1)^2 + (P + q + 1) * (log2 n + 1)) + c2 steps of the cost model on a valid input, n the length of the text, q the number of queries and P their total length ([sizes]: the suffix array by prefix doubling with a merge sort per round, the persistent segment tree, then per query two binary searches of |t| log n and one k-th query of log n), for two constants
    quantified before the inputs, on every valid input. [@requirement kth_occurrences_time_spec] *)
Specification kth_occurrences_time : exists c1 c2 : nat,
  forall (text : string) (patterns : list string)
  (ranks : list N)
  (text_str : PrimString.string)
  (patterns_arr : array PrimString.string)
  (ranks_arr : array uint),
  valid_input text patterns ranks ->
  repr text_str text -> repr patterns_arr patterns
  -> repr ranks_arr ranks ->
  kth_occurrences_time_spec c1 c2 (size text_str) (sizes patterns_arr) (size patterns_arr) (cost3 kth_occurrences_cost text_str patterns_arr ranks_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
