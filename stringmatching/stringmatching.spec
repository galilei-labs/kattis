(** * String Matching *)

(** ** Description *)

(** Find every occurrence of a pattern in a text, including overlaps, and
    return the starting positions in ascending order.

    [@kattis stringmatching]
    - Difficulty: 3.3
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Nonempty pattern and text; the input file is at most $5$ MB.
    - This specification additionally caps text length at $4{,}194{,}303$ so all
      match positions fit the output array. *)

(** ** Examples *)

(** - Input convention: Repeated pairs of lines: pattern first, then text; input ends at EOF.
    - Output convention: All 0-based match positions in ascending order, on one line per case. *)
(* Input:
p
Popup
helo
Hello there!
peek a boo
you speek a bootiful language
anas
bananananaspaj
Output:
2 4

5
7
*)

(** ** [@hide] Environment *)

(* @function        find_all
   @signature       PrimString.string -> PrimString.string -> array uint
   @math_signature  string -> string -> list N
   @summary         [find_all pattern text] returns, in ascending order,
                    every position of text at which pattern occurs,
                    overlapping occurrences included
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  String.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters of [text]. *)
Definition slen (text : string) : N :=
  N.of_nat (String.length text).

(** The k-th position listed in positions, for k < [len]
    positions (0 outside, never relied on). *)
Definition get_list_N (positions : list N) (k : N) : N :=
  nth (N.to_nat k) positions 0.

(** [pattern] occurs in [text] at position : [text] is
    [pattern] preceded by position characters and
    followed by any. *)
Definition occurs_at (pattern text : string) (position : N)
  : Prop :=
  exists before after,
    text = (before ++ pattern ++ after)%string /\ slen
      before = position.

(** The positions are listed in strictly [ascending]
    order. *)
Definition ascending (positions : list N) : Prop :=
  forall j k, j < k < len positions ->
    get_list_N positions j < get_list_N positions k.

(** [@inside find_all_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. The additional array-size constraint is specific to the implementation. *)
Record valid_input (pattern text : string) : Prop := {
  (* a non-empty pattern, a non-empty text *)
  vi_pat : 1 <= slen pattern;
  vi_txt : 1 <= slen text;
  (* the input file is not larger than 5 Mb *)
  vi_file : slen pattern + slen text <= 5 * 10 ^ 6;
  (* NOT THE KATTIS BOUND (2026-10-17). Kattis allows a
     text of 5 Mb, but the output is an [array uint] and
     a PArray has at most PArray.max_length = 4194303
     cells, while a text of n characters can hold up to n
     occurrences (pattern "a" , text "aaa..." ): on such
     an input the contract would demand an output no
     array can represent and find_all_correct would be
     false. So the text is capped at what a PArray can
     hold; every answer then fits (at most slen text -
     slen pattern + 1 <= 4194303 positions). Kattis
     inputs with a longer text are outside this contract. *)
  vi_txt_parray : slen text <= 4194303;
}.

(** ** Correctness *)

(** [@requirement]
    The output lists every starting position of a pattern occurrence, including
    overlaps, exactly once in ascending order. *)
Definition find_all_spec
  (pattern text : string)
  (output : list N)
  : Prop :=
  ascending output /\
  forall position, In position output <-> occurs_at pattern
    text position.

(** ** Interface *)

(** Find every occurrence of a pattern in a text, including overlaps, and return the
    starting positions in ascending order.
    - Input [pattern]: Pattern whose occurrences are sought.
    - Input [text]: Text in which to search, including overlapping occurrences.
    - Output [output]: The output lists every starting position of a pattern occurrence, including overlaps, exactly once in ascending order. *)
Program find_all : PrimString.string -> PrimString.string ->
  array uint.

(** ** Bridge *)

(** [@requirement find_all_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [find_all_spec]. *)
Specification find_all_correct :
  forall (pattern text : string)
    (pattern_str text_str : PrimString.string),
  valid_input pattern text -> repr pattern_str pattern ->
  repr text_str text ->
  exists output : list N,
    repr (find_all pattern_str text_str) output /\
    find_all_spec pattern text output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
