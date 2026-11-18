(** * Zapis *)

(** ** Description *)

(** Count substitutions of question marks that produce a balanced sequence
    of round, square and curly brackets. Return the last five digits and
    whether the count reaches $10^{5}$.

    [@kattis zapis]
    - Difficulty: 5.0
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Even string length: $2 \le n \le 200$.
    - Characters are round, square or curly brackets, or question marks. *)

(** ** Examples *)

(** - Input convention: String length, followed by brackets and ? placeholders.
    - Output convention: The completion count; counts of at least $10^{5}$ use their last five digits, including leading zeros. *)
(* Input:
6
()()()
Output:
1
*)

(** ** [@hide] Environment *)

(* @function        zapis
   @signature       PrimString.string -> uint * bool
   @math_signature  String.string -> N * bool
   @summary         [zapis sequence] counts the ways to replace every '?' of
                    sequence by a character so that the result is a regular
                    bracket-sequence over ( ) [ ] { }, every other character
                    of sequence being kept. It returns that count modulo
                    100000 and whether the count is at least 100000: the
                    answer printed is the residue, padded with leading zeros
                    to 5 digits when the flag is set (the last 5 digits).
                    It runs in at most c1 * (n + 1)^3 + c2 steps of the cost
                    model on a valid input, n the length of the sequence
                    (the interval table, a split loop per entry), for two
                    constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray
  PrimString.
From Stdlib Require Import String Ascii.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A string is a String.string, a character an
   ascii. *)

(** ** Definitions *)

(** The number of characters in [text]. *)
Definition slen (text : string) : N :=
  N.of_nat (String.length text).

(** [opening] is the opening bracket that [closing]
    closes. *)
Definition matching (opening closing : ascii) : Prop :=
     (opening = "("%char /\ closing = ")"%char)
  \/ (opening = "["%char /\ closing = "]"%char)
  \/ (opening = "{"%char /\ closing = "}"%char).

(** [regular text] means that [text] is a balanced bracket sequence: empty, a
    balanced sequence enclosed by matching brackets, or a concatenation of
    balanced sequences. *)
Inductive regular : string -> Prop :=
  | regular_empty : regular ""
  | regular_wrap  : forall opening closing inner,
      matching opening closing -> regular inner ->
      regular (String opening (inner ++ String closing ""))
  | regular_cat   : forall prefix suffix,
      regular prefix -> regular suffix -> regular
        (prefix ++ suffix).

(** [candidate] has the same length as [sequence] and agrees at every position that
    is not a question mark. *)
Definition completion (sequence candidate : string) : Prop
  :=
  String.length candidate = String.length sequence /\
  forall k, (k < String.length sequence)%nat ->
    String.get k sequence = Some "?"%char \/
    String.get k candidate = String.get k sequence.

(** The characters that can appear in the input string. *)
Definition input_char (character : ascii) : Prop :=
  In character ["("; ")"; "["; "]"; "{"; "}"; "?"]%char.

(** [@inside zapis_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sequence : string) : Prop := {
  (* an even integer N (2 <= N <= 200), the length of the
     string *)
  vi_len  : 2 <= slen sequence <= 200;
  vi_even : N.even (slen sequence) = true;
  (* the string is a bracket-sequence some of whose
     characters are illegible, represented by the '?'
     character *)
  vi_chars : forall k character,
    String.get k sequence = Some character -> input_char
      character;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the number of balanced-bracket completions modulo $10^{5}$ and a
    flag indicating whether the full count is at least $10^{5}$. *)
Definition zapis_spec
  (sequence : string)
  (output : N * bool)
  : Prop :=
  exists completions : list string,
    NoDup completions /\
    (forall candidate, In candidate completions <->
       completion sequence candidate /\ regular candidate)
         /\
    match output with
    | (residue, wrapped) =>
        residue = N.of_nat (List.length completions) mod
          100000 /\
        wrapped = (100000 <=? N.of_nat (List.length
          completions))
    end.

(** ** Complexity *)

(** [@requirement] Runs in $O(n^3)$ steps, where $n$ is the input string length. *)
Definition zapis_time_spec (c1 c2 n_sequence steps : nat) : Prop :=
  (steps <= c1 * ((n_sequence + 1) * (n_sequence + 1) * (n_sequence + 1)) + c2)%nat.

(** ** Interface *)

(** Count substitutions of question marks that produce a balanced sequence of round, square
    and curly brackets. Return the last five digits and whether the count reaches
    $10^{5}$.
    - Input [sequence]: Bracket sequence containing question marks to replace.
    - Output [output]: The output gives the number of balanced-bracket completions modulo $10^{5}$ and a flag indicating whether the full count is at least $10^{5}$. *)
Program zapis : PrimString.string -> uint * bool.

(** [@example zapis]
    - Sample: 1
    - Input [sequence]: "()()()"%string
    - Output [output]: (1, false)
*)

(** ** Bridge *)

(** [@requirement zapis_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [zapis_spec]. *)
Specification zapis_correct :
  forall (sequence : string) (sequence_str :
    PrimString.string),
  valid_input sequence -> repr sequence_str sequence ->
  exists output : N * bool,
    repr (zapis sequence_str) output /\ zapis_spec sequence
      output.

(** ** Complexity *)

(** [@hide] [zapis_cost] is the cost translation of [zapis] (the judge
    recomputes it and compares) ... *)
Complexity zapis_cost for zapis.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1)^3 + c2 steps of the cost model on a valid input, n the length of the sequence (the interval table, a split loop per entry), for two constants
    quantified before the inputs, on every valid input. [@requirement zapis_time_spec] *)
Specification zapis_time : exists c1 c2 : nat,
  forall (sequence : string) (sequence_str :
  PrimString.string),
  valid_input sequence -> repr sequence_str sequence ->
  zapis_time_spec c1 c2 (size sequence_str) (cost1 zapis_cost sequence_str).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
