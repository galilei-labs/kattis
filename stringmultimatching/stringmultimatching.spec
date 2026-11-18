(** * String Multimatching *)

(** ** Description *)

(** Find every occurrence of each pattern in a text, including overlaps, and
    return ascending starting positions for each pattern.

    [@kattis stringmultimatching]
    - Difficulty: 4.1
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Nonempty patterns with total length at most $10^{5}$.
    - Nonempty text of length at most $2 \times 10^{5}$. *)

(** ** Examples *)

(** - Input convention: Per case: pattern count, one pattern per line, then the text; input ends at EOF.
    - Output convention: One line of ascending 0-based match positions per pattern. *)
(* Input:
2
p
pup
Popup
2
You
peek a boo
you speek a bootiful language
4
anas
ana
an
a
bananananaspaj
Output:
2 4
2

5
7
1 3 5 7
1 3 5 7
1 3 5 7 9 12
*)

(** ** [@hide] Environment *)

(* @function        multimatch
   @signature       array PrimString.string -> PrimString.string
                    -> array (array uint)
   @math_signature  list string -> string -> list (list N)
   @summary         [multimatch patterns text] returns, for every pattern
                    patterns[i] and in ascending order, every position of
                    text at which patterns[i] occurs, overlapping
                    occurrences included
                    It runs in at most c1 * (P + T + k + 1) + c2 steps of
                    the cost model on a valid input, P the total length of
                    the patterns, T the length of the text and k the total
                    number of positions reported ([sizes] of the input and
                    of the output: the automaton, one pass over the text,
                    the output), for two constants c1, c2.
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

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N ) (k : N) : N := nth
  (N.to_nat k) l 0.
(** The row at zero-based index [i] in [rows], or an empty list beyond the end. *)
Definition get_row (rows : list (list N)) (i : N) : list N
  :=
  nth (N.to_nat i) rows [].
(** The pattern at zero-based index [i] in [patterns], or the empty string beyond
    the end. *)
Definition get_pattern (patterns : list string ) (i : N) :
  string :=
  nth (N.to_nat i) patterns ""%string.

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

(** The total length of the [patterns]. *)
Definition total_length (patterns : list string) : N :=
  N.of_nat (list_sum (map String.length patterns)).

(** [@inside multimatch_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (patterns : list string) (text : string)
  : Prop := {
  (* every pattern is non-empty *)
  vi_patterns : Forall (fun pattern => 1 <= slen pattern)
    patterns;
  (* the total length of all patterns is no more than
     10^5 *)
  vi_total : total_length patterns <= 10 ^ 5;
  (* a non-empty text of length at most 2 * 10^5 *)
  vi_txt : 1 <= slen text <= 2 * 10 ^ 5;
}.

(** ** Correctness *)

(** [@requirement]
    For each pattern, the output lists every occurrence position, including overlaps,
    exactly once in ascending order. *)
Definition multimatch_spec
  (patterns : list string)
  (text : string)
  (output : list (list N))
  : Prop :=
  len output = len patterns /\
  forall i, i < len patterns ->
    ascending (get_row output i) /\
    forall position, In position (get_row output i) <->
      occurs_at (get_pattern patterns i) text position.

(** ** Complexity *)

(** [@requirement] Runs in $O(L+n+z+1)$ steps, where $L$ is the total pattern length, $n$ the text length, and $z$ the total number of reported occurrences. *)
Definition multimatch_time_spec (c1 c2 total_patterns n_text total_output steps : nat) : Prop :=
  (steps <= c1 * (total_patterns + n_text + total_output + 1) + c2)%nat.

(** ** Interface *)

(** Find every occurrence of each pattern in a text, including overlaps, and return
    ascending starting positions for each pattern.
    - Input [patterns]: Patterns whose occurrences are sought.
    - Input [text]: Text searched for every pattern.
    - Output [output]: For each pattern, the output lists every occurrence position, including overlaps, exactly once in ascending order. *)
Program multimatch : array PrimString.string ->
  PrimString.string ->
                       array (array uint).

(** [@example multimatch]
    - Sample: 1
    - Case: 1
    - Input [patterns]: ["p"; "pup"]%string
    - Input [text]: "Popup"%string
    - Output [output]: [[2; 4]; [2]]
*)

(** [@example multimatch]
    - Sample: 1
    - Case: 2
    - Input [patterns]: ["You"; "peek a boo"]%string
    - Input [text]: "you speek a bootiful language"%string
    - Output [output]: [[]; [5]]
*)

(** [@example multimatch]
    - Sample: 1
    - Case: 3
    - Input [patterns]: ["anas"; "ana"; "an"; "a"]%string
    - Input [text]: "bananananaspaj"%string
    - Output [output]: [[7]; [1; 3; 5; 7]; [1; 3; 5; 7]; [1; 3; 5; 7; 9; 12]]
*)

(** ** Bridge *)

(** [@requirement multimatch_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [multimatch_spec]. *)
Specification multimatch_correct :
  forall (patterns : list string) (text : string)
         (patterns_arr : array PrimString.string)
         (text_str : PrimString.string),
  valid_input patterns text -> repr patterns_arr patterns ->
  repr text_str text ->
  exists output : list (list N),
    repr (multimatch patterns_arr text_str) output /\
    multimatch_spec patterns text output.

(** ** Complexity *)

(** [@hide] [multimatch_cost] is the cost translation of [multimatch] (the judge
    recomputes it and compares) ... *)
Complexity multimatch_cost for multimatch.

(** [@fold complexity bound] ... and runs in at most c1 * (P + T + k + 1) + c2 steps of the cost model on a valid input, P the total length of the patterns, T the length of the text and k the total number of positions reported ([sizes] of the input and of the output: the automaton, one pass over the text, the output), for two constants
    quantified before the inputs, on every valid input. [@requirement multimatch_time_spec] *)
Specification multimatch_time : exists c1 c2 : nat,
  forall (patterns : list string) (text : string)
  (patterns_arr : array PrimString.string)
  (text_str : PrimString.string),
  valid_input patterns text -> repr patterns_arr patterns ->
  repr text_str text ->
  multimatch_time_spec c1 c2 (sizes patterns_arr) (size text_str) (sizes (multimatch patterns_arr text_str)) (cost2 multimatch_cost patterns_arr text_str).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
