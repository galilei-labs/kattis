(** * String Hashing *)

(** ** Description *)

(** Compute keyed hashes for queried substrings. Equal substrings must
    always hash equally; distinct substrings may collide for at most as many
    keys as their maximum length, among 2^61 - 1 possible keys.

    [@kattis hashing]
    - Difficulty: 4.9
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 300000 lowercase text characters; at most 300000 queries.
    - Each query selects a nonempty substring within the text. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
abba
6
0 1
3 4
1 2
2 3
0 2
2 4
Output:
33
33
34
34
143
124
*)

(** ** [@hide] Environment *)
(* @function        hashes
   @signature       uint -> PrimString.string -> array uint -> array uint
                    -> array uint
   @math_signature  N -> string -> list N -> list N -> list N
   @summary         [hashes hash_key text query_lefts query_rights]
                    returns, for every query (query_lefts[i],
                    query_rights[i]), the hash with key hash_key of the
                    substring text[query_lefts[i]] ...
                    text[query_rights[i] - 1], for one family of hashes
                    indexed by the key : equal substrings get equal hashes
                    under every key, and two different substrings get
                    equal hashes for at most max of their lengths of the
                    2^61 - 1 keys, so a key drawn at random by the harness
                    separates them with high probability
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters of str. *)
Definition slen (str : string) : N :=
  N.of_nat (String.length str).

(** The i-th element of l, for i < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (i : N) : N :=
  nth (N.to_nat i) l 0.

(** The code of a character : a byte, 97 for "a". *)
Definition code (character : ascii) : N :=
  N_of_ascii character.

(** The characters of str, in order. *)
Definition chars (str : string) : list ascii :=
  list_ascii_of_string str.

(** The substring str[start] ... str[stop - 1]. *)
Definition window (str : string)
  (start stop : N) : string :=
  substring (N.to_nat start) (N.to_nat (stop - start)) str.

(** The keys : 0 .. key_count - 1. The statement leaves the hash free ;
    key_count is our choice, the number of residues modulo the
    Mersenne prime 2^61 - 1. *)
Definition key_count : N := 2 ^ 61 - 1.
(** The [key] definition. *)
Definition key (candidate : N) : Prop :=
  candidate < key_count.

(** At most bound keys satisfy bad : they all fit in a list of at most
    bound entries. For a key drawn uniformly, bad then has
    probability at most bound / key_count. *)
Definition few_bad_keys (bound : N)
  (bad : N -> Prop) : Prop :=
  exists bad_keys : list N, len bad_keys <= bound /\
    forall candidate, key candidate -> bad candidate ->
      In candidate bad_keys.

(** hash_family is a separating family of hashes : two different strings
    get equal hashes for at most max of their lengths of the keys.
    At the statement's bounds that is at most 300000 of the 2^61 - 1
    keys, a probability below 2 * 10^-13 per pair of different
    substrings. (The polynomial hash key^|word| + word_0
    key^(|word|-1) + ... + word_(|word|-1) modulo 2^61 - 1 is one
    such family : two different strings give two different
    polynomials in the key of degree at most max(|word|, |word'|)
    over the field Z/(2^61 - 1)Z, which agree on at most that many
    keys.) *)
Definition separating
  (hash_family : N -> string -> N) : Prop :=
  forall word word' : string, word <> word' ->
    few_bad_keys (N.max (slen word) (slen word'))
      (fun candidate => hash_family candidate word =
            hash_family candidate word').

(** [@inside hashes_correct] The statement's bounds, for the one test
    case, and the range of the key. *)
Record valid_input (hash_key : N) (text : string)
    (query_lefts query_rights : list N) : Prop := {
  (* the key, our own argument *)
  vi_key : key hash_key;
  (* S consists of letters a-z, at least one, no more
     than 300000 *)
  vi_s_length : 1 <= slen text <= 3 * 10 ^ 5;
  vi_s_letters : Forall (fun character =>
            code "a" <= code character <=
            code "z")
            (chars text);
  (* 0 <= Q <= 300000 queries, one L and one R each *)
  vi_queries : len query_lefts <= 3 * 10 ^ 5;
  vi_rs_length : len query_rights = len query_lefts;
  (* 0 <= L < R <= N *)
  vi_windows : forall i, i < len query_lefts ->
    get_list_N query_lefts i < get_list_N query_rights i <=
      slen text;
}.

(** ** Correctness *)

(** [@requirement] [@short The answer of one call, for the family
    hash_family : hash_family is    separating, and there is one
    hash per query, the family's hash under    the key of the
    queried substring.  That hash depends on the key and    the
    spelled substring only, so two queries on equal substrings get
    equal hashes : the statement's first half.  Its second half,
    different    substrings get different hashes with high
    probability, is    [separating hash_family].] The answer of one
    call, for the family hash_family : hash_family is separating,
    and there is one hash per query, the family's hash under the key
    of the queried substring. That hash depends on the key and the
    spelled substring only, so two queries on equal substrings get
    equal hashes : the statement's first half. Its second half,
    different substrings get different hashes with high probability,
    is [separating hash_family]. *)
Definition hashes_spec (hash_family : N -> string -> N)
  (hash_key : N)
    (text : string) (query_lefts query_rights : list N)
      (output : list N)
    : Prop :=
  separating hash_family /\
  len output = len query_lefts /\
  forall i, i < len query_lefts ->
    get_list_N output i =
      hash_family hash_key
        (window text (get_list_N query_lefts i) (get_list_N
          query_rights i)).

(** ** Interface *)

(** The [hashes] program on machine values.
    - Input [hash_key]:
    - Input [text]:
    - Input [query_lefts]:
    - Input [query_rights]:
    - Output [output]: *)
Program hashes : uint -> PrimString.string -> array uint ->
  array uint ->
                   array uint.

(** ** Bridge *)

(** [@requirement hashes_spec] [@fold full correctness statement] On
    valid represented inputs, [hashes] returns a represented output
    satisfying [hashes_spec]. *)
Specification hashes_correct :
  exists hash_family : N -> string -> N,
  forall (hash_key : N) (text : string) (query_lefts
    query_rights : list N)
         (hash_key_int : uint) (text_str :
           PrimString.string)
         (query_lefts_arr query_rights_arr : array uint),
  valid_input hash_key text query_lefts query_rights ->
  repr hash_key_int hash_key -> repr text_str text ->
  repr query_lefts_arr query_lefts ->
    repr query_rights_arr query_rights ->
  exists output : list N,
    repr (hashes hash_key_int text_str query_lefts_arr
      query_rights_arr)
      output /\
    hashes_spec hash_family hash_key text query_lefts
      query_rights
      output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
