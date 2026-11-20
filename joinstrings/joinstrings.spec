(** * Join Strings *)

(** ** Description *)

(** Process operations that append one string to another and empty the
    source. Return the single string remaining after all operations.

    [@kattis joinstrings]
    - Difficulty: 3.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - String count: $1 \le N \le 10^{5}$; nonempty lowercase strings total at most $10^{6}$
      characters.
    - Exactly $N-1$ operations on distinct source and target indices; an
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
                    It runs in at most c1 * (N + 1) + c2 steps of the cost
                    model on a valid input, N the number of strings (O(1)
                    per splice, one concatenation pass at the end; the
                    primitive string operations count one step each), for
                    two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).
(** The number of characters in [word]. *)
Definition slen (word : string) : N :=
  N.of_nat (String.length word).

(** The string at one-based index [k] in [state]. *)
Definition str (state : list string) (k : N) : string :=
  nth (N.to_nat (k - 1)) state ""%string.

(** Replace the string at one-based index [k] in [state] with [replacement]. *)
Definition set_str (state : list string) (k : N)
  (replacement : string)
    : list string :=
  firstn (N.to_nat (k - 1)) state ++ replacement :: skipn
    (N.to_nat k) state.

(** Append the source string to the target string, then clear the source string. *)
Definition join (state : list string)
  (target source : N) : list string :=
  set_str (set_str state target (str state target ++ str
    state source))
    source ""%string.

(** The strings after all the operations, executed in the order given. *)
Fixpoint run (strings : list string)
  (targets sources : list N)
    : list string :=
  match targets, sources with
  | target :: targets', source :: sources' =>
      run (join strings target source) targets' sources'
  | _, _ => strings
  end.

(** Every character of [word] is a lowercase English letter. *)
Definition lowercase (word : string) : Prop :=
  forall k letter, String.get k word = Some letter ->
    97 <= N_of_ascii letter <= 122.

(** The total number of characters over all the strings. *)
Fixpoint total (strings : list string) : N :=
  match strings with
  | [] => 0
  | word :: rest => slen word + total rest
  end.

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

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the number of input strings. *)
Definition joinstrings_time_spec (c1 c2 n_strings steps : nat) : Prop :=
  (steps <= c1 * (n_strings + 1) + c2)%nat.

(** ** Interface *)

(** Process operations that append one string to another and empty the source. Return the
    single string remaining after all operations.
    - Input [strings]: Initial strings indexed by the operations.
    - Input [targets]: Destination string of each append operation.
    - Input [sources]: Source string appended and then emptied at each operation.
    - Output [output]: The output is the single string remaining after the append-and-clear operations are executed in order. *)
Program joinstrings :
  array PrimString.string -> array uint -> array uint ->
    PrimString.string.

(** [@example joinstrings]
    - Sample: 1
    - Input [strings]: ["cute"; "cat"; "kattis"; "is"]%string
    - Input [targets]: [3; 4; 3]
    - Input [sources]: [2; 1; 4]
    - Output [output]: "kattiscatiscute"%string
*)

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

(** ** Complexity *)

(** [@hide] [joinstrings_cost] is the cost translation of [joinstrings] (the judge
    recomputes it and compares) ... *)
Complexity joinstrings_cost for joinstrings.

(** [@fold complexity bound] ... and runs in at most c1 * (N + 1) + c2 steps of the cost model on a valid input, N the number of strings (O(1) per splice, one concatenation pass at the end; the primitive string operations count one step each), for two constants
    quantified before the inputs, on every valid input. [@requirement joinstrings_time_spec] *)
Specification joinstrings_time : exists c1 c2 : nat,
  forall (strings : list string) (targets sources : list N)
  (strings_arr : array PrimString.string)
  (targets_arr sources_arr : array uint),
  valid_input strings targets sources ->
  repr strings_arr strings -> repr targets_arr targets ->
  repr sources_arr sources ->
  joinstrings_time_spec c1 c2 (size strings_arr) (cost3 joinstrings_cost strings_arr targets_arr sources_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
