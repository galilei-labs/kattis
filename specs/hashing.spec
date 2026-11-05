(* @function        hashes
   @signature       uint -> PrimString.string -> array uint -> array uint
                    -> array uint
   @math_signature  N -> string -> list N -> list N -> list N
   @summary         [hashes r s ls rs] returns, for every query
                    (ls[i], rs[i]), the hash with key r of the substring
                    s[ls[i]] ... s[rs[i] - 1], for one family of hashes
                    indexed by the key : equal substrings get equal hashes
                    under every key, and two different substrings get
                    equal hashes for at most max of their lengths of the
                    2^61 - 1 keys, so a key drawn at random by the harness
                    separates them with high probability
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of characters of s. *)
Definition slen (s : string) : N := N.of_nat (String.length s).

(* The i-th element of l, for i < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (i : N) : N := nth (N.to_nat i) l 0.

(* The code of a character : a byte, 97 for "a". *)
Definition code (c : ascii) : N := N_of_ascii c.

(* The characters of s, in order. *)
Definition chars (s : string) : list ascii := list_ascii_of_string s.

(* The substring s[l] ... s[r - 1]. *)
Definition window (s : string) (l r : N) : string :=
  substring (N.to_nat l) (N.to_nat (r - l)) s.

(* The keys : 0 .. key_count - 1.  The statement leaves the hash free ;
   key_count is our choice, the number of residues modulo the Mersenne
   prime 2^61 - 1. *)
Definition key_count : N := 2 ^ 61 - 1.
Definition key (r : N) : Prop := r < key_count.

(* At most d keys satisfy bad : they all fit in a list of at most d
   entries.  For a key drawn uniformly, bad then has probability at most
   d / key_count. *)
Definition few_bad_keys (d : N) (bad : N -> Prop) : Prop :=
  exists l : list N, len l <= d /\ forall r, key r -> bad r -> In r l.

(* H is a separating family of hashes : two different strings get equal
   hashes for at most max of their lengths of the keys.  At the
   statement's bounds that is at most 300000 of the 2^61 - 1 keys, a
   probability below 2 * 10^-13 per pair of different substrings.
   (The polynomial hash r^|w| + w_0 r^(|w|-1) + ... + w_(|w|-1) modulo
   2^61 - 1 is one such family : two different strings give two different
   polynomials in r of degree at most max(|w|, |w'|) over the field
   Z/(2^61 - 1)Z, which agree on at most that many keys.) *)
Definition separating (H : N -> string -> N) : Prop :=
  forall w w' : string, w <> w' ->
    few_bad_keys (N.max (slen w) (slen w')) (fun r => H r w = H r w').

(* The statement's bounds, for the one test case, and the range of the
   key. *)
Record valid_input (r : N) (s : string) (ls rs : list N) : Prop := {
  (* the key, our own argument *)
  vi_key : key r;
  (* S consists of letters a-z, at least one, no more than 300000 *)
  vi_s_length : 1 <= slen s <= 3 * 10 ^ 5;
  vi_s_letters : Forall (fun c => code "a" <= code c <= code "z") (chars s);
  (* 0 <= Q <= 300000 queries, one L and one R each *)
  vi_queries : len ls <= 3 * 10 ^ 5;
  vi_rs_length : len rs = len ls;
  (* 0 <= L < R <= N *)
  vi_windows : forall i, i < len ls ->
    get_list_N ls i < get_list_N rs i <= slen s;
}.

(* The answer of one call, for the family H : H is separating, and there
   is one hash per query, the family's hash under the key of the queried
   substring.  That hash depends on the key and the spelled substring
   only, so two queries on equal substrings get equal hashes : the
   statement's first half.  Its second half, different substrings get
   different hashes with high probability, is [separating H]. *)
Definition hashes_spec (H : N -> string -> N) (r : N) (s : string)
                       (ls rs h : list N) : Prop :=
  separating H /\
  len h = len ls /\
  forall i, i < len ls ->
    get_list_N h i = H r (window s (get_list_N ls i) (get_list_N rs i)).

(* machine side : the only thing that gets extracted *)
Program hashes : uint -> PrimString.string -> array uint -> array uint ->
                   array uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential).  The family H is bound in front of the inputs : the
   same family answers every call, under every key. *)
Specification hashes_correct :
  exists H : N -> string -> N,
  forall (r : N) (s : string) (ls rs : list N)
         (xr : uint) (xs : PrimString.string) (xl xr' : array uint),
  valid_input r s ls rs ->
  repr xr r -> repr xs s -> repr xl ls -> repr xr' rs ->
  exists h : list N, repr (hashes xr xs xl xr') h /\ hashes_spec H r s ls rs h.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
