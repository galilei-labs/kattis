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
    - Match positions are returned in two consecutive arrays so results can
      exceed the capacity of a single Rocq primitive array. *)

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
   @signature       PrimString.string -> PrimString.string -> array uint * array uint
   @math_signature  string -> string -> list N
   @summary         [find_all pattern text] returns, in ascending order,
                    every position of text at which pattern occurs,
                    overlapping occurrences included
                    It runs in at most c1 * (|pat| + |txt| + 1) + c2 steps
                    of the cost model, for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  String.
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

(** The entry at zero-based index [k] in [positions], or zero beyond the end. *)
Definition get_list_N (positions : list N) (k : N) : N :=
  nth (N.to_nat k) positions 0.

(** [pattern] occurs in [text] at zero-based index [position]. *)
Definition occurs_at (pattern text : string) (position : N)
  : Prop :=
  exists before after,
    text = (before ++ pattern ++ after)%string /\ slen
      before = position.

(** The entries of [positions] are strictly increasing. *)
Definition ascending (positions : list N) : Prop :=
  forall j k, j < k < len positions ->
    get_list_N positions j < get_list_N positions k.

(** [@inside find_all_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (pattern text : string) : Prop := {
  (* a non-empty pattern, a non-empty text *)
  vi_pat : 1 <= slen pattern;
  vi_txt : 1 <= slen text;
  (* the input file is not larger than 5 Mb *)
  vi_file : slen pattern + slen text <= 5 * 10 ^ 6;
}.

(** The runtime result represents one mathematical list: the positions in
    the first array followed by those in the second array. *)
Definition positions_repr (result : array uint * array uint)
  (positions : list N) : Prop :=
  exists first second : list N,
    repr result (first, second) /\ positions = first ++ second.

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

(** ** Complexity *)

(** [@requirement] Runs in $O(m+n+1)$ steps, where $m$ is the pattern length and $n$ the text length. *)
Definition find_all_time_spec (c1 c2 n_pattern n_text steps : nat) : Prop :=
  (steps <= c1 * (n_pattern + n_text + 1) + c2)%nat.

(** ** Interface *)

(** Find every occurrence of a pattern in a text, including overlaps, and return the
    starting positions in ascending order.
    - Input [pattern]: Pattern whose occurrences are sought.
    - Input [text]: Text in which to search, including overlapping occurrences.
    - Output [output]: The output lists every starting position of a pattern occurrence, including overlaps, exactly once in ascending order. At runtime, concatenate the first returned array with the second to obtain this list. *)
Program find_all : PrimString.string -> PrimString.string ->
  array uint * array uint.

(** [@example find_all]
    - Sample: 1
    - Case: 1
    - Input [pattern]: "p"%string
    - Input [text]: "Popup"%string
    - Output [output]: [2; 4]
*)

(** [@example find_all]
    - Sample: 1
    - Case: 2
    - Input [pattern]: "helo"%string
    - Input [text]: "Hello there!"%string
    - Output [output]: []
*)

(** [@example find_all]
    - Sample: 1
    - Case: 3
    - Input [pattern]: "peek a boo"%string
    - Input [text]: "you speek a bootiful language"%string
    - Output [output]: [5]
*)

(** [@example find_all]
    - Sample: 1
    - Case: 4
    - Input [pattern]: "anas"%string
    - Input [text]: "bananananaspaj"%string
    - Output [output]: [7]
*)

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
    positions_repr (find_all pattern_str text_str) output /\
    find_all_spec pattern text output.

(** ** Complexity *)

(** [@hide] [find_all_cost] is the cost translation of [find_all] (the judge
    recomputes it and compares) ... *)
Complexity find_all_cost for find_all.

(** [@fold complexity bound] ... and runs in at most c1 * (|pat| + |txt| + 1) + c2 steps of the cost model, for two constants
    quantified before the inputs. [@requirement find_all_time_spec] *)
Specification find_all_time : exists c1 c2 : nat, forall pattern_str text_str : PrimString.string,
  find_all_time_spec c1 c2 (size pattern_str) (size text_str) (cost2 find_all_cost pattern_str text_str).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
