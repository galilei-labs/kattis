(** * Join Strings *)

(** ** Description *)

(** Process operations that append one string to another and empty the
    source. Return the single string remaining after all operations.

    [@kattis joinstrings]
    - Difficulty: 3.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to $10^{5}$ nonempty lowercase strings, totaling at most $10^{6}$
      characters.
    - Exactly N - 1 operations on distinct source and target indices; an
      emptied source is never accessed again. *)

(** ** Examples *)

(** - Input convention: String count and strings, followed by 1-based destination-source pairs for concatenation.
    - Output convention: The single remaining concatenated string. *)
(* Input:
4
cute
cat
kattis
is
3 2
4 1
3 4
Output:
kattiscatiscute
*)

(** ** [@hide] Environment *)
(* @function        joinstrings
   @signature       array PrimString.string -> array uint -> array uint ->
                    PrimString.string
   @math_signature  list String.string -> list N -> list N -> String.string
   @summary         [joinstrings strings targets sources] executes, in
                    order, the N-1 operations of the statement on the N
                    strings S_1..S_N = strings: the i-th operation (1-based
                    indices a_i = targets_i, b_i = sources_i) sets
                    S_(a_i) := S_(a_i) ++ S_(b_i), then S_(b_i) := "". It
                    returns the one string that remains at the end, the
                    S_r whose index r is no b_i.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Types: the N-1 operation lines "a b" are two parallel arrays,
    targets (the a_i) and sources (the b_i), kept 1-based as in the
    statement. Math side. The strings S_1..S_N are a list, S_k at
    position k - 1. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).
(** The [slen] definition. *)
Definition slen (word : string) : N :=
  N.of_nat (String.length word).

(** S_k, 1-based. *)
Definition str (state : list string) (k : N) : string :=
  nth (N.to_nat (k - 1)) state ""%string.

(** state with S_k (1-based) replaced by replacement. *)
Definition set_str (state : list string) (k : N)
  (replacement : string)
    : list string :=
  firstn (N.to_nat (k - 1)) state ++ replacement :: skipn
    (N.to_nat k) state.

(** One operation "target source": S_target := S_target + S_source, then
    S_source := "". *)
Definition join (state : list string)
  (target source : N) : list string :=
  set_str (set_str state target (str state target ++ str
    state source))
    source ""%string.

(** The strings after all the operations, executed in the order given. *)
Definition run (strings : list string)
  (targets sources : list N)
    : list string :=
  fold_left (fun state op => join state (fst op) (snd op))
    (combine targets sources) strings.

(** Every character of word is a lowercase letter 'a'..'z'. *)
Definition lowercase (word : string) : Prop :=
  forall k letter, String.get k word = Some letter ->
    97 <= N_of_ascii letter <= 122.

(** The total number of characters over all the strings. *)
Definition total (strings : list string) : N :=
  fold_right N.add 0 (map slen strings).

(** [@inside joinstrings_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (strings : list string)
  (targets sources : list N)
    : Prop := {
  (* 1 <= N <= 10^5 *)
  vi_n : 1 <= len strings <= 10 ^ 5;
  (* N non-empty strings *)
  vi_nonempty : Forall (fun word => 1 <= slen word) strings;
  (* all the characters are lowercase alphabets from 'a'
     to 'z' *)
  vi_lower : Forall lowercase strings;
  (* the total number of characters over all the strings
     is at most 10^6 *)
  vi_total : total strings <= 10 ^ 6;
  (* N - 1 operations *)
  vi_len_a : len targets = len strings - 1;
  vi_len_b : len sources = len strings - 1;
  (* 1 <= a, b <= N *)
  vi_a : Forall (fun target => 1 <= target <= len strings)
    targets;
  vi_b : Forall (fun source => 1 <= source <= len strings)
    sources;
  (* a <> b *)
  vi_neq : forall i, (i < List.length targets)%nat ->
    nth i targets 0 <> nth i sources 0;
  (* after the i-th operation, no future operation
     accesses S_b *)
  vi_future : forall i j, (i < j)%nat ->
    (j < List.length targets)%nat ->
    nth j targets 0 <> nth i sources 0 /\ nth j sources 0 <>
      nth i sources 0;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the single string remaining after the append-and-clear operations are
    executed in order. *)
Definition joinstrings_spec (strings : list string)
  (targets sources : list N)
    (output : string) : Prop :=
  exists survivor, 1 <= survivor <= len strings /\ ~ In
    survivor sources /\
    output = str (run strings targets sources) survivor.

(** ** Interface *)

(** Process operations that append one string to another and empty the source. Return the
    single string remaining after all operations.
    - Input [strings]:
    - Input [targets]:
    - Input [sources]:
    - Output [output]: *)
Program joinstrings :
  array PrimString.string -> array uint -> array uint ->
    PrimString.string.

(** ** Bridge *)

(** [@requirement joinstrings_spec] [@fold full correctness statement]
    On valid represented inputs, [joinstrings] returns a represented
    output satisfying [joinstrings_spec]. *)
Specification joinstrings_correct :
  forall (strings : list string) (targets sources : list N)
         (strings_arr : array PrimString.string)
         (targets_arr sources_arr : array uint),
  valid_input strings targets sources ->
  repr strings_arr strings -> repr targets_arr targets ->
  repr sources_arr sources ->
  exists output : string,
    repr (joinstrings strings_arr targets_arr sources_arr)
      output /\
    joinstrings_spec strings targets sources output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
