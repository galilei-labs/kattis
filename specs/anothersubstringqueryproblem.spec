(* @function        kth_occurrences
   @signature       PrimString.string -> array PrimString.string -> array uint
                    -> array sint
   @math_signature  String.string -> list String.string -> list N -> list Z
   @summary         [kth_occurrences s ts ks] answers every query at once:
                    cell q is the 1-based position in s where the ks_q-th
                    occurrence, from the left, of the pattern ts_q starts, or
                    -1 when ts_q occurs fewer than ks_q times in s.
                    Occurrences may overlap.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The queries are the parallel columns ts (patterns) and ks
   (ranks) of the q query lines; positions are 0-based inside the math
   side, the answer adds 1. *)

(* The number of elements of l, and the number of characters of s. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).
Definition slen (s : string) : N := N.of_nat (String.length s).

(* Every character of s is a lower-case letter, 'a' (97) to 'z' (122). *)
Definition lowercase (s : string) : Prop :=
  Forall (fun c => 97 <= N_of_ascii c <= 122) (list_ascii_of_string s).

(* The sum of the lengths of the patterns. *)
Definition total_len (ts : list string) : N :=
  fold_right (fun t acc => slen t + acc) 0 ts.

(* t occurs in s starting at the 0-based position p: the |t| characters of
   s from p are those of t. *)
Definition starts_at (s t : string) (p : nat) : bool :=
  ((p + String.length t <=? String.length s)%nat &&
   String.eqb (substring p (String.length t) s) t)%bool.

(* The 0-based positions where t occurs in s, in increasing order. *)
Definition occurrences (s t : string) : list N :=
  map N.of_nat (filter (starts_at s t) (seq 0 (String.length s))).

(* The answer to the query (t, k): 1 + the position of the k-th
   occurrence, or -1 if t occurs fewer than k times. *)
Definition answer (s t : string) (k : N) : Z :=
  match nth_error (occurrences s t) (N.to_nat k - 1) with
  | Some p => Z.of_N p + 1
  | None => -1
  end.

Record valid_input (s : string) (ts : list string) (ks : list N) : Prop := {
  (* a single string s (1 <= |s| <= 2*10^5) *)
  vi_s_length : 1 <= slen s <= 2 * 10 ^ 5;
  (* It will consist only of lower-case letters. *)
  vi_s_lower : lowercase s;
  (* q (1 <= q <= 2*10^5), the number of queries that follow *)
  vi_q : 1 <= len ts <= 2 * 10 ^ 5;
  (* Each of the next q lines contains a string t and an integer k. *)
  vi_ks_length : len ks = len ts;
  (* a string t (1 <= |t|) *)
  vi_t_length : Forall (fun t => 1 <= slen t) ts;
  (* The string t will consist only of lower-case letters. *)
  vi_t_lower : Forall lowercase ts;
  (* an integer k (1 <= k <= |s|) *)
  vi_k : Forall (fun k => 1 <= k <= slen s) ks;
  (* The sum of all |t|'s will be <= 2*10^5 *)
  vi_t_sum : total_len ts <= 2 * 10 ^ 5;
}.

(* One answer per query, in the order of the queries. *)
Definition kth_occurrences_spec (s : string) (ts : list string) (ks : list N)
    (o : list Z) : Prop :=
  len o = len ts /\
  forall (q : nat) t k, nth_error ts q = Some t -> nth_error ks q = Some k ->
    nth_error o q = Some (answer s t k).

(* sint for the answers, for the -1 *)
Program kth_occurrences :
  PrimString.string -> array PrimString.string -> array uint -> array sint.

Specification kth_occurrences_correct :
  forall (s : string) (ts : list string) (ks : list N)
         (x : PrimString.string) (y : array PrimString.string) (z : array uint),
  valid_input s ts ks -> repr x s -> repr y ts -> repr z ks ->
  exists o : list Z, repr (kth_occurrences x y z) o /\
                     kth_occurrences_spec s ts ks o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
