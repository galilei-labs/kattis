(** * Palindromes *)

(** ** Description *)

(** For each queried interval of a string, count the palindromic substrings
    contained entirely within that interval.

    [@kattis palindromes]
    - Difficulty: 7.2
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1\text{ to }100{,}000$ lowercase characters; Query count: $1 \le q \le 100{,}000$.
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require String Ascii PrimString.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The m lines "l r" of the input are two parallel lists.
    The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of letters of name. *)
Definition slen (name : String.string) : N :=
  N.of_nat (String.length name).

(** Element k of l, 0-based. *)
Definition at_ (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** Every letter of name is a lowercase letter, 'a' (97) .. 'z' (122). *)
Definition lowercase (name : String.string) : Prop :=
  forall k letter, String.get k name = Some letter ->
    97 <= Ascii.N_of_ascii letter <= 122.

(** name_i name_(i+1) .. name_j, 1-based, i <= j. *)
Definition sub (name : String.string)
  (i j : N) : String.string :=
  String.substring (N.to_nat (i - 1)) (N.to_nat (j - i + 1))
    name.

(** text read backwards. *)
Definition reverse (text : String.string) : String.string :=
  String.string_of_list_ascii (rev
    (String.list_ascii_of_string text)).

(** text reads the same forwards and backwards. *)
Definition palindrome (text : String.string) : bool :=
  String.eqb text (reverse text).

(** The integers low, low+1, ..., high (empty when high < low). *)
Definition range (low high : N) : list N :=
  map N.of_nat (seq (N.to_nat low) (N.to_nat (high + 1 -
    low))).

(** The pairs (i, j) with left_end <= i <= j <= right_end. *)
Definition index_pairs (left_end right_end : N) : list
  (N * N) :=
  flat_map (fun i => map (fun j => (i, j)) (range i
    right_end))
           (range left_end right_end).

(** The number of palindromic substrings contained within the inclusive query interval. *)
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
  (* 1 <= n <= 100 000 *)
  vi_n : 1 <= slen name <= 100000;
  (* 1 <= m <= 100 000, the number of customers *)
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
    Each output entry counts palindromic substrings contained entirely within the
    corresponding query interval. *)
Definition palindromes_spec (name : String.string)
    (left_ends right_ends : list N) (output : list N) : Prop
      :=
  len output = len left_ends /\
  forall k, k < len output ->
    at_ output k = palindromic_count name (at_ left_ends k)
      (at_ right_ends k).

(** ** Interface *)

(** For each queried interval of a string, count the palindromic substrings contained
    entirely within that interval.
    - Input [name]: Text containing the queried substrings.
    - Input [left_ends]: Inclusive left endpoint of each query.
    - Input [right_ends]: Inclusive right endpoint of each query.
    - Output [output]: Each output entry counts palindromic substrings contained entirely within the corresponding query interval. *)
Program palindromes : PrimString.string -> array uint ->
  array uint -> array uint.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
