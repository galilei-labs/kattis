(** * Suffix Sorting *)

(** ** Description *)

(** List the starting [positions] of a [text]'s suffixes
    in lexicographic order.

    [@kattis suffixsorting]
    - Difficulty: 4.3
    - CPU time limit: 1 second
    - Memory limit: 1024 MB *)

(** ** [@hide] Environment *)

(* @function        suffix_array
   @signature       PrimString.string -> array uint
   @math_signature  string -> list N
   @summary         [suffix_array text] returns the starting positions of
                    the suffixes of text, from the lexicographically smallest
                    suffix to the largest ; the harness answers the query
                    q with entry q
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Permutation.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
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

(** The k-th element of l, for k < [len] l (0 outside,
    never relied on). *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** The [suffix] of [text] starting at position. *)
Definition suffix (text : string) (position : N) : string :=
  substring (N.to_nat position) (String.length text) text.

(** earlier comes strictly before later in lexicographic
    order : at the first position where they differ
    earlier has the smaller character code, or earlier is
    a proper prefix of later. *)
Definition lex_lt (earlier later : string) : Prop :=
  String.compare earlier later = Lt.

(** The [positions] 0 .. n - 1 of [text]. *)
Definition positions (text : string) : list N :=
  map N.of_nat (seq 0 (String.length text)).

(** [@inside suffix_array_correct] The statement's
    bounds, for one test case. *)
Record valid_input (text : string) : Prop := {
  (* a non-empty string of length at most 100000 *)
  vi_s : 1 <= slen text <= 10 ^ 5;
}.

(** ** Correctness *)

(** [@requirement] [@short List the starting positions of
    a text's suffixes in lexicographic order.] Every
    position exactly once, each [suffix] before the next. *)
Definition suffix_array_spec
  (text : string)
  (output : list N)
  : Prop :=
  Permutation output (positions text) /\
  forall rank, rank + 1 < len output ->
    lex_lt (suffix text (get_list_N output rank))
           (suffix text (get_list_N output (rank + 1))).

(** ** Interface *)

(** List the starting [positions] of a [text]'s suffixes
    in lexicographic order.
    - Input [text]:
    - Output [output]: *)
Program suffix_array : PrimString.string -> array uint.

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

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
