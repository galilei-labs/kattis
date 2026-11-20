(** * Catenyms *)

(** ** Description *)

(** Arrange all given words exactly once so each word's last letter matches
    the next word's first letter. Return the lexicographically smallest
    period-separated arrangement, or report that none exists.

    [@kattis catenyms]
    - Difficulty: 6.5
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Distinct word count: $3 \le n \le 10^{3}$; word length: $1 \le \ell \le 20$ lowercase letters. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives a word count followed by one word per line.
    - Output convention: The smallest valid period-separated word chain, or *** if none exists. *)
(* Input:
2
6
aloha
arachnid
dog
gopher
rat
tiger
3
oak
maple
elm
Output:
aloha.arachnid.dog.gopher.rat.tiger
***
*)

(** ** [@hide] Environment *)

(* @function        catenyms
   @signature       array PrimString.string -> option (array PrimString.string)
   @math_signature  list String.string -> option (list String.string)
   @summary         Given a dictionary of distinct lower-case words,
                    [catenyms words] returns the words arranged as the
                    lexicographically smallest compound catenym that
                    contains each dictionary word exactly once (three or
                    more words, the last letter of each the first letter of
                    the next), or None (the "***" line) when there is none.
                    Lexicographic order is that of the printed line, the
                    words joined by periods.
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of words (the sort, each comparison a primitive; the
                    Euler path is linear), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii Permutation.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A word is a String.string ; a character is
  its byte code. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters in [word]. *)
Definition slen (word : string) : N :=
  N.of_nat (String.length word).

(** Every character of [word] is a lowercase English letter. *)
Definition lowercase (word : string) : Prop :=
  forall position character, String.get position word = Some
    character ->
    97 <= Ascii.N_of_ascii character <= 122.

(** The last letter of [left] equals the first letter of [right]. *)
Definition forms_catenym (left right : string) : Prop :=
  String.get
    (String.length left - 1) left = String.get 0 right.

(** A chain of at least three words in which each adjacent pair satisfies
    [forms_catenym]. *)
Definition compound_catenym (chain : list string) : Prop :=
  3 <= len chain /\
  forall j, (S j < List.length chain)%nat ->
    forms_catenym (nth j chain ""%string) (nth
      (S j) chain ""%string).

(** [chain] is a [compound_catenym] containing every input word exactly once, with
    multiplicities preserved. *)
Definition is_answer (words chain : list string) : Prop :=
  compound_catenym chain /\ Permutation chain words.

(** The words of [chain] joined by periods, as printed in the result. *)
Definition text (chain : list string) : string :=
  String.concat "." chain.

(** [@inside catenyms_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (words : list string) : Prop := {
  (* 3 <= n <= 10^3, the number of words in the dictionary
    *)
  vi_n : 3 <= len words <= 1000;
  (* each word is a string of between 1 and 20 lowercase
    letters *)
  vi_word_length : Forall
    (fun word => 1 <= slen word <= 20) words;
  vi_word_lower : Forall lowercase words;
  (* n distinct dictionary words *)
  vi_distinct : NoDup words;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the lexicographically smallest period-separated chain using every word
    once with matching endpoint letters, or None if no chain exists. *)
Definition catenyms_spec (words : list string)
  (output : option (list string))
  : Prop :=
  match output with
  | None => ~ exists chain, is_answer words chain
  | Some chain =>
      is_answer words chain /\
      forall chain', is_answer words chain' ->
        String.compare (text chain) (text chain') <> Gt
  end.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of words. *)
Definition catenyms_time_spec (c1 c2 n_words steps : nat) : Prop :=
  (steps <= c1 * ((n_words + 1) * (Nat.log2 (n_words) + 1)) + c2)%nat.

(** ** Interface *)

(** Arrange all given words exactly once so each word's last letter matches the next word's
    first letter. Return the lexicographically smallest period-separated arrangement, or
    report that none exists.
    - Input [words]: Words to arrange into a chain, each used exactly once.
    - Output [output]: The output is the lexicographically smallest period-separated chain using every word once with matching endpoint letters, or None if no chain exists. *)
Program catenyms : array PrimString.string -> option
  (array PrimString.string).

(** [@example catenyms]
    - Sample: 1
    - Case: 1
    - Input [words]: ["aloha"; "arachnid"; "dog"; "gopher"; "rat"; "tiger"]%string
    - Output [output]: Some ["aloha"; "arachnid"; "dog"; "gopher"; "rat"; "tiger"]%string
*)

(** [@example catenyms]
    - Sample: 1
    - Case: 2
    - Input [words]: ["oak"; "maple"; "elm"]%string
    - Output [output]: None
*)

(** ** Bridge *)

(** [@requirement catenyms_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [catenyms_spec]. *)
Specification catenyms_correct :
  forall (words : list string)
    (words_arr : array PrimString.string),
  valid_input words -> repr words_arr words ->
  exists output : option (list string),
    repr (catenyms words_arr) output
      /\ catenyms_spec words output.

(** ** Complexity *)

(** [@hide] [catenyms_cost] is the cost translation of [catenyms] (the judge
    recomputes it and compares) ... *)
Complexity catenyms_cost for catenyms.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of words (the sort, each comparison a primitive; the Euler path is linear), for two constants
    quantified before the inputs, on every valid input. [@requirement catenyms_time_spec] *)
Specification catenyms_time : exists c1 c2 : nat,
  forall (words : list string)
  (words_arr : array PrimString.string),
  valid_input words -> repr words_arr words ->
  catenyms_time_spec c1 c2 (size words_arr) (cost1 catenyms_cost words_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
