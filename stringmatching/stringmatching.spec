(* @function        find_all
   @signature       PrimString.string -> PrimString.string -> array uint
   @math_signature  string -> string -> list N
   @summary         [find_all pattern text] returns, in ascending order,
                    every position of text at which pattern occurs,
                    overlapping occurrences included
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of characters of text. *)
Definition slen (text : string) : N := N.of_nat (String.length text).

(* The k-th position listed in positions, for k < len positions (0
   outside, never relied on). *)
Definition get_list_N (positions : list N) (k : N) : N :=
  nth (N.to_nat k) positions 0.

(* pattern occurs in text at position : text is pattern preceded by
   position characters and followed by any. *)
Definition occurs_at (pattern text : string) (position : N) : Prop :=
  exists before after,
    text = (before ++ pattern ++ after)%string /\ slen before = position.

(* The positions are listed in strictly ascending order. *)
Definition ascending (positions : list N) : Prop :=
  forall j k, j < k < len positions ->
    get_list_N positions j < get_list_N positions k.

(* The statement's bounds, for one test case -- plus one bound that is NOT
   Kattis's, vi_txt_parray. *)
Record valid_input (pattern text : string) : Prop := {
  (* a non-empty pattern, a non-empty text *)
  vi_pat : 1 <= slen pattern;
  vi_txt : 1 <= slen text;
  (* the input file is not larger than 5 Mb *)
  vi_file : slen pattern + slen text <= 5 * 10 ^ 6;
  (* NOT THE KATTIS BOUND (2026-10-17). Kattis allows a text of 5 Mb, but
     the output is an [array uint] and a PArray has at most
     PArray.max_length = 4194303 cells, while a text of n characters can
     hold up to n occurrences (pattern "a", text "aaa..."): on such an
     input the contract would demand an output no array can represent and
     find_all_correct would be false. So the text is capped at what a
     PArray can hold; every answer then fits (at most
     slen text - slen pattern + 1 <= 4194303 positions). Kattis inputs with a
     longer text are outside this contract. *)
  vi_txt_parray : slen text <= 4194303;
}.

(* The positions of the occurrences of pattern in text, each once, in
   ascending order. *)
Definition find_all_spec (pattern text : string) (output : list N)
    : Prop :=
  ascending output /\
  forall position, In position output <-> occurs_at pattern text position.

(* machine side : the only thing that gets extracted *)
Program find_all : PrimString.string -> PrimString.string -> array uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification find_all_correct :
  forall (pattern text : string) (pattern_str text_str : PrimString.string),
  valid_input pattern text -> repr pattern_str pattern ->
  repr text_str text ->
  exists output : list N,
    repr (find_all pattern_str text_str) output /\
    find_all_spec pattern text output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
