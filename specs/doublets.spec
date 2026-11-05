(* @function        doublets
   @signature       array PrimString.string -> array PrimString.string ->
                    array PrimString.string ->
                    array (option (array PrimString.string))
   @math_signature  list string -> list string -> list string ->
                    list (option (list string))
   @summary         [doublets dict src tgt] answers every query k of one
                    input: entry k is a shortest chain of dictionary words
                    from src_k to tgt_k in which consecutive words differ in
                    exactly one letter, or None when no such chain exists.
                    Every word of a chain, endpoints included, is in dict;
                    when src_k = tgt_k is in dict the chain is that one word.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A word is a String.string; a letter is compared by its code. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of letters of w. *)
Definition slen (w : string) : N := N.of_nat (String.length w).

(* Every letter of w is a lower case letter, 'a' to 'z'. *)
Definition lower (w : string) : Prop :=
  forall k c, String.get k w = Some c -> 97 <= N_of_ascii c <= 122.

(* a and b are a doublet: they have the same length and differ at exactly
   one position. *)
Definition doublet (a b : string) : Prop :=
  String.length a = String.length b /\
  exists k, (k < String.length a)%nat /\
    String.get k a <> String.get k b /\
    forall j, (j < String.length a)%nat -> j <> k ->
      String.get j a = String.get j b.

(* c is a sequence of dictionary words that begins with s, ends with t, and
   in which each pair of adjacent words is a doublet. *)
Definition is_chain (dict : list string) (s t : string) (c : list string)
    : Prop :=
  nth_error c 0 = Some s /\
  nth_error c (List.length c - 1) = Some t /\
  Forall (fun w => In w dict) c /\
  forall k a b, nth_error c k = Some a -> nth_error c (S k) = Some b ->
    doublet a b.

(* The answer to the pair (s, t): Some c with c a chain no longer than any
   other chain, or None exactly when there is no chain at all. *)
Definition answer (dict : list string) (s t : string)
    (r : option (list string)) : Prop :=
  match r with
  | Some c => is_chain dict s t c /\
              forall c', is_chain dict s t c' -> len c <= len c'
  | None => forall c, ~ is_chain dict s t c
  end.

(* The statement's guarantees, for one input. *)
Record valid_input (dict src tgt : list string) : Prop := {
  (* a dictionary of up to 25 143 words *)
  vi_dict_len : len dict <= 25143;
  (* words not exceeding 16 letters each; one per line, the dictionary
     being terminated by an empty line, so no word is empty *)
  vi_word_len : Forall (fun w => 1 <= slen w <= 16) dict;
  (* lower case words *)
  vi_lower : Forall lower dict;
  (* a number of word pairs (at most 10) *)
  vi_queries : len src <= 10;
  (* the pairs: query k is (src_k, tgt_k) *)
  vi_pairs : len src = len tgt;
  (* "You are then given a number of pairs of words.": the statement gives
     no bound on the query words (its "not exceeding 16 letters" is said of
     the dictionary's words), so the bound is the representability limit
     of PrimString.string, PrimString.max_length = 16777211. 
     Human : we may also assume they are not more than 16 letters long as that seems reasonnable*)
  vi_src_len : Forall (fun w => slen w <= 16777211) src;
  vi_tgt_len : Forall (fun w => slen w <= 16777211) tgt;
}.

(* One answer per pair, in order. *)
Definition doublets_spec (dict src tgt : list string)
    (o : list (option (list string))) : Prop :=
  Forall2 (fun st r => answer dict (fst st) (snd st) r) (combine src tgt) o.

Program doublets :
  array PrimString.string -> array PrimString.string ->
  array PrimString.string -> array (option (array PrimString.string)).

Specification doublets_correct :
  forall (dict src tgt : list string)
         (xd xs xt : array PrimString.string),
  valid_input dict src tgt -> repr xd dict -> repr xs src -> repr xt tgt ->
  exists o : list (option (list string)),
    repr (doublets xd xs xt) o /\ doublets_spec dict src tgt o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
