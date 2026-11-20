(** * Suffix Sorting *)

(** ** Description *)

(** Sort a text's suffixes lexicographically. In the Kattis problem, each case
    supplies a text, a query count, and that many zero-based ranks in the sorted
    suffix ordering. For each requested rank, report the starting position of
    the suffix at that rank, also using zero-based indices.

    The Rocq function [suffix_array] takes only the text and returns the full
    array of starting positions in sorted suffix order. The input/output
    wrapper handles the query count and ranks by selecting entries from this
    array. For example, for the text "popup", the array is [1; 4; 0; 2; 3],
    so a query for rank $2$ reports starting position $0$.

    [@kattis suffixsorting]
    - Difficulty: 4.4
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Text length: $1 \le n \le 10^{5}$. *)

(** ** Examples *)

(** These examples use the Kattis text format, not direct calls to [suffix_array].
    - Input convention: Per case: text, followed by a query count and that many zero-based suffix ranks. Only the text is passed to [suffix_array].
    - Output convention: For each requested rank, the corresponding entry of the full array returned by [suffix_array]. These entries are zero-based starting positions in the text. *)
(* Input:
popup
5 0 1 2 3 4
Popup
5 0 1 2 3 4
Suffixes are jolly fun, eh old chap?
7 35 3 18 33 26 6 2
Output:
1 4 0 2 3
0 1 4 2 3
17 18 19 20 21 22 23
*)

(** ** [@hide] Environment *)

(* @function        suffix_array
   @signature       PrimString.string -> array uint
   @math_signature  string -> list N
   @summary         [suffix_array text] returns the starting positions of
                    the suffixes of text, from the lexicographically smallest
                    suffix to the largest ; the harness answers the query
                    q with entry q
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the length
                    of the text (at most log2 n + 1 doubling rounds of
                    linear counting sorts), for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Permutation.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters in [text]. *)
Definition slen (text : string) : N :=
  N.of_nat (String.length text).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** The suffix of [text] beginning at zero-based index [position]. *)
Definition suffix (text : string) (position : N) : string :=
  substring (N.to_nat position) (String.length text) text.

(** [earlier] precedes [later] in lexicographic character-code order, with a proper
    prefix preceding its extension. *)
Definition lex_lt (earlier later : string) : Prop :=
  String.compare earlier later = Lt.

(** All valid zero-based character positions in [text]. *)
Definition positions (text : string) : list N :=
  map N.of_nat (seq 0 (String.length text)).

(** [@inside suffix_array_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (text : string) : Prop := {
  (* a non-empty string of length at most 10^5 *)
  vi_s : 1 <= slen text <= 10 ^ 5;
}.

(** ** Correctness *)

(** [@requirement]
    The output is a permutation of all starting positions that orders the corresponding
    suffixes lexicographically. *)
Definition suffix_array_spec
  (text : string)
  (output : list N)
  : Prop :=
  Permutation output (positions text) /\
  forall rank, rank + 1 < len output ->
    lex_lt (suffix text (get_list_N output rank))
           (suffix text (get_list_N output (rank + 1))).

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the text length. *)
Definition suffix_array_time_spec (c1 c2 n_text steps : nat) : Prop :=
  (steps <= c1 * ((n_text + 1) * (Nat.log2 (n_text) + 1)) + c2)%nat.

(** ** Interface *)

(** Compute the full suffix array for [text], independently of any queries.
    Unlike the Kattis text input, this function takes no query count or ranks.
    The input/output wrapper answers each requested zero-based rank by selecting
    the entry at that rank from the returned array.
    - Input [text]: Text whose suffixes are to be sorted.
    - Output [output]: All zero-based suffix starting positions in lexicographic suffix order; the entry at each rank is the start of the suffix having that rank. *)
Program suffix_array : PrimString.string -> array uint.

(** [@example suffix_array]
    - Sample: 1
    - Case: 1
    - Input [text]: "popup"%string
    - Output [output]: [1; 4; 0; 2; 3]
*)

(** [@example suffix_array]
    - Sample: 1
    - Case: 2
    - Input [text]: "Popup"%string
    - Output [output]: [0; 1; 4; 2; 3]
*)

(** [@example suffix_array]
    - Sample: 1
    - Case: 3
    - Input [text]: "Suffixes are jolly fun, eh old chap?"%string
    - Output [output]: [8; 30; 23; 18; 12; 26; 22; 35; 0; 33; 9; 31; 29; 11; 24; 6; 2; 3; 19; 25; 32; 4; 13; 28; 15; 16; 21; 27; 14; 34; 10; 7; 1; 20; 5; 17]
*)

(** ** Bridge *)

(** [@requirement suffix_array_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [suffix_array_spec]. *)
Specification suffix_array_correct :
  forall (text : string) (text_str : PrimString.string),
  valid_input text -> repr text_str text ->
  exists output : list N,
    repr (suffix_array text_str) output /\
    suffix_array_spec text output.

(** ** Complexity *)

(** [@hide] [suffix_array_cost] is the cost translation of [suffix_array] (the judge
    recomputes it and compares) ... *)
Complexity suffix_array_cost for suffix_array.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the length of the text (at most log2 n + 1 doubling rounds of linear counting sorts), for two constants
    quantified before the inputs, on every valid input. [@requirement suffix_array_time_spec] *)
Specification suffix_array_time : exists c1 c2 : nat,
  forall (text : string) (text_str : PrimString.string),
  valid_input text -> repr text_str text ->
  suffix_array_time_spec c1 c2 (size text_str) (cost1 suffix_array_cost text_str).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
