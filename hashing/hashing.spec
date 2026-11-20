(** * String Hashing *)

(** ** Description *)

(** Compute keyed hashes for queried substrings. Equal substrings must
    always hash equally; distinct substrings may collide for at most as many
    keys as their maximum length, among $2^{61} - 1$ possible keys.

    [@kattis hashing]
    - Difficulty: 4.9
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Text length: $1 \le n \le 3 \times 10^{5}$ lowercase characters; at most $3 \times 10^{5}$ queries.
    - Each query selects a nonempty substring within the text. *)

(** ** Examples *)

(** - Input convention: Text, query count, then 0-based half-open substring intervals L R.
    - Output convention: One integer substring hash per query. *)
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
                    It runs in at most c1 * (n + q + 1) + c2 steps of the
                    cost model on a valid input, n the length of the text
                    and q the number of queries (two linear tables, then
                    O(1) per query), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Ascii.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters in [str]. *)
Definition slen (str : string) : N :=
  N.of_nat (String.length str).

(** The entry at zero-based index [i] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N) (i : N) : N :=
  nth (N.to_nat i) l 0.

(** The code of a character : a byte, 97 for "a". *)
Definition code (character : ascii) : N :=
  N_of_ascii character.

(** The characters of [str], in order. *)
Definition chars (str : string) : list ascii :=
  list_ascii_of_string str.

(** The substring of [str] from zero-based index [start], inclusive, to [stop],
    exclusive. *)
Definition window (str : string)
  (start stop : N) : string :=
  substring (N.to_nat start) (N.to_nat (stop - start)) str.

(** The number of possible keys, $2^{61} - 1$, corresponding to residues modulo this Mersenne prime. *)
Definition key_count : N := 2 ^ 61 - 1.
(** [candidate] is a valid key: a residue from zero through [key_count - 1]. *)
Definition key (candidate : N) : Prop :=
  candidate < key_count.

(** At most [bound] keys satisfy [bad]. A uniformly drawn key therefore satisfies
    [bad] with probability at most [bound / key_count]. *)
Definition few_bad_keys (bound : N)
  (bad : N -> Prop) : Prop :=
  exists bad_keys : list N, len bad_keys <= bound /\
    forall candidate, key candidate -> bad candidate ->
      In candidate bad_keys.

(** A [hash_family] maps a key and a string to a hash. Fixing the key selects one
    deterministic hash function; randomness is in the choice of key, not in
    evaluating the function.

    For any two distinct strings, at most the maximum of their lengths many keys
    give equal hashes. Under the input bounds, at most $3 \times 10^{5}$ of the $2^{61}-1$
    keys collide for a fixed pair: probability below $2 \times 10^{-13}$ for a
    uniformly chosen key. This condition does not prescribe a particular hashing
    formula. *)
Definition separating
  (hash_family : N -> string -> N) : Prop :=
  forall word word' : string, word <> word' ->
    few_bad_keys (N.max (slen word) (slen word'))
      (fun candidate => hash_family candidate word =
            hash_family candidate word').

(** [@inside hashes_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (hash_key : N) (text : string)
    (query_lefts query_rights : list N) : Prop := {
  (* the key, our own argument *)
  vi_key : key hash_key;
  (* S consists of letters a-z, at least one, no more
     than 3 * 10^5 *)
  vi_s_length : 1 <= slen text <= 3 * 10 ^ 5;
  vi_s_letters : Forall (fun character =>
            code "a" <= code character <=
            code "z")
            (chars text);
  (* 0 <= Q <= 3 * 10^5 queries, one L and one R each *)
  vi_queries : len query_lefts <= 3 * 10 ^ 5;
  vi_rs_length : len query_rights = len query_lefts;
  (* 0 <= L < R <= N *)
  vi_windows : forall i, i < len query_lefts ->
    get_list_N query_lefts i < get_list_N query_rights i <=
      slen text;
}.

(** ** Correctness *)

(** [@requirement]
    Each output is [hash_family hash_key] applied to the corresponding substring.
    All queries use the same supplied key and the same fixed family.
    Equal substrings have equal hashes; distinct substrings collide for at most
    their maximum length in keys among $2^{61} - 1$ keys. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O(n+q+1)$ steps, where $n$ is the text length and $q$ the number of substring queries. *)
Definition hashes_time_spec (c1 c2 n_text n_query_lefts steps : nat) : Prop :=
  (steps <= c1 * (n_text + n_query_lefts + 1) + c2)%nat.

(** ** Interface *)

(** Compute keyed hashes for queried substrings. Equal substrings must always hash equally;
    distinct substrings may collide for at most as many keys as their maximum length,
    among $2^{61} - 1$ possible keys.

    A hash family maps a key and a string to a hash. The family is fixed across all
    calls and described mathematically by [hashes_correct]; it is not a runtime
    argument. The key selects one deterministic hash function within that family.
    Choosing a key uniformly at random makes collisions unlikely for any fixed
    pair of distinct substrings.
    - Input [hash_key]: Key from zero through [key_count - 1], supplied by the harness rather than read from Kattis input. The harness chooses it randomly; every substring query in this call uses this same key.
    - Input [text]: Text containing the queried substrings.
    - Input [query_lefts]: Inclusive zero-based left endpoint of each substring query.
    - Input [query_rights]: Exclusive zero-based right endpoint of each substring query.
    - Output [output]: The output hashes each queried substring using the supplied key and a common hash family. Equal substrings have equal hashes; distinct substrings collide for at most their maximum length in keys among $2^{61} - 1$ keys. *)
Program hashes : uint -> PrimString.string -> array uint ->
  array uint ->
                   array uint.

(** [@example hashes]
    - Sample: 1
    - Context [hash_family]: N -> string -> N
    - Input [hash_key]: 42
    - Input [text]: "abba"%string
    - Input [query_lefts]: [0; 3; 1; 2; 0; 2]
    - Input [query_rights]: [1; 4; 2; 3; 2; 4]
    - Output [output]: [hash_family 42 "a"%string; hash_family 42 "a"%string; hash_family 42 "b"%string; hash_family 42 "b"%string; hash_family 42 "ab"%string; hash_family 42 "ba"%string]
*)

(** ** Bridge *)

(** [@requirement hashes_spec] [@fold full correctness statement] On
    valid represented inputs, [hashes] returns a represented output
    satisfying [hashes_spec].

    The existential [hash_family] is a mathematical witness, not a runtime
    argument. It is quantified before all keys and inputs: one fixed separating
    family must explain the outputs for every call, rather than choosing a new
    family for each input or query. The contract does not fix its formula. *)
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

(** ** Complexity *)

(** [@hide] [hashes_cost] is the cost translation of [hashes] (the judge
    recomputes it and compares) ... *)
Complexity hashes_cost for hashes.

(** [@fold complexity bound] ... and runs in at most c1 * (n + q + 1) + c2 steps of the cost model on a valid input, n the length of the text and q the number of queries (two linear tables, then O(1) per query), for two constants
    quantified before the inputs, on every valid input. [@requirement hashes_time_spec] *)
Specification hashes_time : exists c1 c2 : nat,
  forall (hash_key : N) (text : string) (query_lefts
  query_rights : list N)
  (hash_key_int : uint) (text_str :
  PrimString.string)
  (query_lefts_arr query_rights_arr : array uint),
  valid_input hash_key text query_lefts query_rights ->
  repr hash_key_int hash_key -> repr text_str text ->
  repr query_lefts_arr query_lefts ->
  repr query_rights_arr query_rights ->
  hashes_time_spec c1 c2 (size text_str) (size query_lefts_arr) (cost4 hashes_cost hash_key_int text_str query_lefts_arr query_rights_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
