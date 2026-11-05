(* @function        palindromes
   @signature       PrimString.string -> array uint -> array uint -> array uint
   @math_signature  String.string -> list N -> list N -> list N
   @summary         [palindromes s ls rs] answers every customer of the
                    company name s: customer k remembers s_l .. s_r
                    (1-based, l = ls_k, r = rs_k), and answer k is the number
                    of pairs (i, j) with l <= i <= j <= r such that
                    s_i .. s_j is a palindrome.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require String Ascii PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The m lines "l r" of the input are two parallel lists. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of letters of s. *)
Definition slen (s : String.string) : N := N.of_nat (String.length s).

(* Element k of l, 0-based. *)
Definition at_ (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* Every letter of s is a lowercase letter, 'a' (97) .. 'z' (122). *)
Definition lowercase (s : String.string) : Prop :=
  forall k c, String.get k s = Some c -> 97 <= Ascii.N_of_ascii c <= 122.

(* s_i s_(i+1) .. s_j, 1-based, i <= j. *)
Definition sub (s : String.string) (i j : N) : String.string :=
  String.substring (N.to_nat (i - 1)) (N.to_nat (j - i + 1)) s.

(* w read backwards. *)
Definition reverse (w : String.string) : String.string :=
  String.string_of_list_ascii (rev (String.list_ascii_of_string w)).

(* w reads the same forwards and backwards. *)
Definition palindrome (w : String.string) : bool := String.eqb w (reverse w).

(* The integers a, a+1, ..., b (empty when b < a). *)
Definition range (a b : N) : list N :=
  map N.of_nat (seq (N.to_nat a) (N.to_nat (b + 1 - a))).

(* The pairs (i, j) with l <= i <= j <= r. *)
Definition index_pairs (l r : N) : list (N * N) :=
  flat_map (fun i => map (fun j => (i, j)) (range i r)) (range l r).

(* The statement's answer for the customer remembering s_l .. s_r: the
   number of pairs (i, j), l <= i <= j <= r, with s_i .. s_j a palindrome. *)
Definition palindromic_count (s : String.string) (l r : N) : N :=
  len (filter (fun p => palindrome (sub s (fst p) (snd p))) (index_pairs l r)).

Record valid_input (s : String.string) (ls rs : list N) : Prop := {
  (* a string s consisting of n lowercase letters *)
  vi_lower : lowercase s;
  (* 1 <= n <= 100 000 *)
  vi_n : 1 <= slen s <= 100000;
  (* 1 <= m <= 100 000, the number of customers *)
  vi_m : 1 <= len ls <= 100000;
  (* m lines, each a pair l r with 1 <= l <= r <= n (one l and one r per
     line: the two lists have the same length) *)
  vi_lr : Forall2 (fun l r => 1 <= l <= r /\ r <= slen s) ls rs;
}.

(* One answer per customer, in input order. *)
Definition palindromes_spec (s : String.string) (ls rs o : list N) : Prop :=
  len o = len ls /\
  forall k, k < len o -> at_ o k = palindromic_count s (at_ ls k) (at_ rs k).

Program palindromes : PrimString.string -> array uint -> array uint -> array uint.

Specification palindromes_correct :
  forall (s : String.string) (ls rs : list N)
         (x : PrimString.string) (xl xr : array uint),
  valid_input s ls rs -> repr x s -> repr xl ls -> repr xr rs ->
  exists o : list N, repr (palindromes x xl xr) o /\ palindromes_spec s ls rs o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
