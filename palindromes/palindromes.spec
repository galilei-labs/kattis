(** * Palindromes *)

(** ** Description *)

(** For each queried interval of a string, count the nonempty palindromic
    substrings contained entirely within that interval. Count occurrences by
    their start and end positions: equal strings at different positions
    contribute separately.

    [@kattis palindromes]
    - Difficulty: 7.2
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - String length: $1 \le n \le 10^{5}$ lowercase characters; Query count: $1 \le q \le 10^{5}$.
    - Each query is a nonempty interval within the string. *)

(** ** Examples *)

(** - Input convention: Text, query count, then inclusive 1-based interval endpoints.
    - Output convention: One count of contained palindromic substrings per query. *)
(* Input:
aabacab
5
1 7
1 4
3 7
2 5
5 7
Output:
11
6
7
5
3
*)

(** ** [@hide] Environment *)
(* @function        palindromes
   @signature       PrimString.string -> array uint -> array uint -> array uint
   @math_signature  String.string -> list N -> list N -> list N
   @summary         [palindromes name left_ends right_ends] answers every
                    customer of the company name: customer k remembers the
                    letters left_end .. right_end of name (1-based, left_end
                    = left_ends_k, right_end = right_ends_k), and answer k is
                    the number of pairs (i, j) with left_end <= i <= j <=
                    right_end such that the letters i .. j of name form a
                    palindrome.
                    It runs in at most c1 * (n + m + 1) * (log2 (n + m) + 1)
                    + c2 steps of the cost model on a valid input, n the
                    length of the name and m the number of queries
                    (Manacher's pass is linear, the queries are sorted and
                    answered with Fenwick trees in log n each), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require String Ascii PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters in [name]. *)
Definition slen (name : String.string) : N :=
  N.of_nat (String.length name).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition at_ (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** Every character of [name] is a lowercase English letter. *)
Definition lowercase (name : String.string) : Prop :=
  forall k letter, String.get k name = Some letter ->
    97 <= Ascii.N_of_ascii letter <= 122.

(** The substring from one-based index [i] through [j], inclusive. *)
Definition sub (name : String.string)
  (i j : N) : String.string :=
  String.substring (N.to_nat (i - 1)) (N.to_nat (j - i + 1))
    name.

(** The characters of [text] in reverse order. *)
Definition reverse (text : String.string) : String.string :=
  String.string_of_list_ascii (rev
    (String.list_ascii_of_string text)).

(** [text] equals its reversal. *)
Definition palindrome (text : String.string) : bool :=
  String.eqb text (reverse text).

(** All integers from [low] through [high], inclusive; empty when [high] is smaller
    than [low]. *)
Definition range (low high : N) : list N :=
  map N.of_nat (seq (N.to_nat low) (N.to_nat (high + 1 -
    low))).

(** All index pairs [(i, j)] satisfying [left_end <= i <= j <= right_end]. *)
Definition index_pairs (left_end right_end : N) : list
  (N * N) :=
  flat_map (fun i => map (fun j => (i, j)) (range i
    right_end))
           (range left_end right_end).

(** The number of start-and-end index pairs within the inclusive, one-based
    interval [left_end, right_end] of [name] whose substring is a palindrome.
    Equal strings at different positions are counted separately. *)
Definition palindromic_count (name : String.string)
  (left_end right_end : N)
    : N :=
  len (filter (fun span => palindrome (sub name (fst span)
    (snd span)))
              (index_pairs left_end right_end)).

(** [@inside palindromes_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (name : String.string)
  (left_ends right_ends : list N)
    : Prop := {
  (* a string s consisting of n lowercase letters *)
  vi_lower : lowercase name;
  (* 1 <= n <= 10^5 *)
  vi_n : 1 <= slen name <= 100000;
  (* 1 <= m <= 10^5, the number of customers *)
  vi_m : 1 <= len left_ends <= 100000;
  (* m lines, each a pair l r with 1 <= l <= r <= n (one
     l and one r per line: the two lists have the same
     length) *)
  vi_lr : Forall2 (fun left_end right_end =>
            1 <= left_end <= right_end /\ right_end
            <= slen name)
            left_ends right_ends;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry counts nonempty palindromic substring occurrences
    contained entirely within the corresponding query interval, counting
    different start-and-end index pairs separately. *)
Definition palindromes_spec (name : String.string)
    (left_ends right_ends : list N) (output : list N) : Prop
      :=
  len output = len left_ends /\
  forall k, k < len output ->
    at_ output k = palindromic_count name (at_ left_ends k)
      (at_ right_ends k).

(** ** Complexity *)

(** [@requirement] Runs in $O((n+q+1)\log(n+q+2))$ steps, where $n$ is the name length and $q$ the number of interval queries. *)
Definition palindromes_time_spec (c1 c2 n_name n_left_ends steps : nat) : Prop :=
  (steps <= c1 * ((n_name + n_left_ends + 1) * (Nat.log2 (n_name + n_left_ends) + 1)) + c2)%nat.

(** ** Interface *)

(** Count nonempty palindromic substring occurrences entirely within each query
    interval. Occurrences with different start or end positions count separately.
    - Input [name]: Text containing the queried substrings.
    - Input [left_ends]: Inclusive one-based left endpoint of each query.
    - Input [right_ends]: Inclusive one-based right endpoint of each query.
    - Output [output]: Number of palindromic occurrences within each query interval, in query order, counting equal strings at different positions separately. *)
Program palindromes : PrimString.string -> array uint ->
  array uint -> array uint.

(** [@example palindromes]
    - Sample: 1
    - Input [name]: "aabacab"%string
    - Input [left_ends]: [1; 1; 3; 2; 5]
    - Input [right_ends]: [7; 4; 7; 5; 7]
    - Output [output]: [11; 6; 7; 5; 3]
*)

(** ** Bridge *)

(** [@requirement palindromes_spec] [@fold full correctness statement]
    On valid represented inputs, [palindromes] returns a represented
    output satisfying [palindromes_spec]. *)
Specification palindromes_correct :
  forall (name : String.string) (left_ends right_ends : list
    N)
         (name_str : PrimString.string)
         (left_ends_arr right_ends_arr : array uint),
  valid_input name left_ends right_ends ->
    repr name_str name ->
  repr left_ends_arr left_ends ->
    repr right_ends_arr right_ends ->
  exists output : list N,
    repr (palindromes name_str left_ends_arr right_ends_arr)
      output /\
    palindromes_spec name left_ends right_ends output.

(** ** Complexity *)

(** [@hide] [palindromes_cost] is the cost translation of [palindromes] (the judge
    recomputes it and compares) ... *)
Complexity palindromes_cost for palindromes.

(** [@fold complexity bound] ... and runs in at most c1 * (n + m + 1) * (log2 (n + m) + 1) + c2 steps of the cost model on a valid input, n the length of the name and m the number of queries (Manacher's pass is linear, the queries are sorted and answered with Fenwick trees in log n each), for two constants
    quantified before the inputs, on every valid input. [@requirement palindromes_time_spec] *)
Specification palindromes_time : exists c1 c2 : nat,
  forall (name : String.string) (left_ends right_ends : list
  N)
  (name_str : PrimString.string)
  (left_ends_arr right_ends_arr : array uint),
  valid_input name left_ends right_ends ->
  repr name_str name ->
  repr left_ends_arr left_ends ->
  repr right_ends_arr right_ends ->
  palindromes_time_spec c1 c2 (size name_str) (size left_ends_arr) (cost3 palindromes_cost name_str left_ends_arr right_ends_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
