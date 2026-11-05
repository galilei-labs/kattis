(* @function        baza
   @signature       array PrimString.string -> array PrimString.string -> array uint
   @math_signature  list String.string -> list String.string -> list N
   @summary         [baza db qs] answers every query word of qs, in order: the
                    number of steps the statement's primitive search takes to
                    find it in the database db, i.e. the number of database
                    words it is compared to (in database order, up to and
                    including the word equal to it, or all of them when it is
                    absent) plus the sum of the lengths of the longest common
                    prefixes of the query and each of those words.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A word is a String.string, a letter its byte code. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of letters of w. *)
Definition slen (w : String.string) : N := N.of_nat (String.length w).

(* Every letter of w is a lowercase English letter, 'a' (97) to 'z' (122). *)
Definition lowercase (w : String.string) : Prop :=
  forall (k : nat) (c : ascii), String.get k w = Some c ->
    97 <= N_of_ascii c <= 122.

(* Word w starts with word p. *)
Definition starts_with (w p : String.string) : Prop :=
  exists s, w = String.append p s.

(* l is the length of the longest common prefix of a and b: the longest
   word that both a and b start with. *)
Definition lcp_length (a b : String.string) (l : N) : Prop :=
  exists p, starts_with a p /\ starts_with b p /\ slen p = l /\
    forall q, starts_with a q -> starts_with b q -> slen q <= l.

(* The search compares w with the first c database words: up to and
   including the one equal to w (at position k, from 0), or all of them
   when there is none. *)
Definition compared_count (db : list String.string) (w : String.string) (c : N)
  : Prop :=
  (exists k, nth_error db (N.to_nat k) = Some w /\ c = k + 1) \/
  (~ In w db /\ c = len db).

(* s is the number of steps of the search for w: the number c of words it
   is compared to, plus the sum of the longest common prefix lengths of w
   with each of them. *)
Definition search_steps (db : list String.string) (w : String.string) (s : N)
  : Prop :=
  exists c ls,
    compared_count db w c /\
    Forall2 (lcp_length w) (firstn (N.to_nat c) db) ls /\
    s = c + fold_right N.add 0 ls.

(* The statement's bounds, for one test case. *)
Record valid_input (db qs : list String.string) : Prop := {
  (* 1 <= N <= 30 000, the number of words in the database *)
  vi_n : 1 <= len db <= 30000;
  (* 1 <= Q <= 30 000, the number of words searched for *)
  vi_q : 1 <= len qs <= 30000;
  (* all words in the input will be strings of less than 30 lowercase
     letters of the English alphabet *)
  vi_db_len : Forall (fun w => slen w < 30) db;
  vi_qs_len : Forall (fun w => slen w < 30) qs;
  vi_db_lower : Forall lowercase db;
  vi_qs_lower : Forall lowercase qs;
  (* all words in the database will be distinct *)
  vi_distinct : NoDup db;
}.

(* One answer per query, in order: the number of steps of its search. *)
Definition baza_spec (db qs : list String.string) (o : list N) : Prop :=
  Forall2 (search_steps db) qs o.

Program baza :
  array PrimString.string -> array PrimString.string -> array uint.

Specification baza_correct :
  forall (db qs : list String.string) (x y : array PrimString.string),
  valid_input db qs -> repr x db -> repr y qs ->
  exists o : list N, repr (baza x y) o /\ baza_spec db qs o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
