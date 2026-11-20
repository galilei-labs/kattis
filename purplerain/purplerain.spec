(** * Purple Rain *)

(** ** Description *)

(** A narrow peninsula is divided into sections numbered from west to east.
    Each section is marked R or B according to whether its rain is primarily
    red or blue. Find a nonempty contiguous stretch where the difference
    between the counts of red and blue sections is largest, regardless of
    which color is more common. Break ties by the westernmost starting
    section, then the westernmost ending section.

    [@kattis purplerain]
    - Difficulty: 3.8
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - String length: $1 \le n \le 10^{5}$; each character is R or B. *)

(** ** Examples *)

(** - Input convention: A single string containing only R and B.
    - Output convention: Inclusive 1-based endpoints of the optimal substring, with earliest endpoints breaking ties. *)
(* Input:
BBRRBRRBRB
Output:
3 7
*)

(** ** [@hide] Environment *)

(* @function        purplerain
   @signature       PrimString.string -> uint * uint
   @math_signature  String.string -> N * N
   @summary         [purplerain colors] takes the colours of sections 1 to
                    n of the peninsula (a string of 'R' and 'B') and
                    returns the first and last section (west, east),
                    1 <= west <= east <= n, of a part maximising
                    |#R - #B| over its sections.  Among all maximising
                    parts it returns the one with the smallest west, and
                    then the smallest east.
                    It runs in at most c1 * n + c2 steps of the cost model,
                    n the number of sections, for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import PrimString String Ascii.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* Section k (1-based, West to East) has the
   colour of character k - 1 of colors. *)

(** ** Definitions *)

(** The number of sections in [colors], one per character. *)
Definition slen (colors : String.string) : N :=
  N.of_nat (String.length colors).

(** The number of occurrences of [letter] in [text]. *)
Fixpoint count (letter : ascii) (text : String.string) : N
  :=
  match text with
  | EmptyString => 0
  | String head rest =>
      (if Ascii.eqb head letter then 1 else 0) + count
        letter rest
  end.

(** [west] and [east] are valid one-based endpoints of a nonempty inclusive interval
    of sections. *)
Definition is_part (colors : String.string) (west east : N)
  : Prop :=
  1 <= west /\ west <= east /\ east <= slen colors.

(** The substring of [colors] from one-based section [west] through [east],
    inclusive. *)
Definition part (colors : String.string) (west east : N) :
  String.string :=
  String.substring (N.to_nat (west - 1))
    (N.to_nat (east - west + 1))
    colors.

(** The absolute difference between the counts of R and B in the inclusive interval
    from [west] through [east]. *)
Definition difference (colors : String.string)
  (west east : N) : Z :=
  Z.abs (Z.of_N (count "R" (part colors west east))
         - Z.of_N (count "B" (part colors west east))).

(** Compare intervals by their western endpoint first, then by their eastern
    endpoint; equality is permitted. *)
Definition west_or_equal (west east west' east' : N) : Prop
  :=
  west < west' \/ (west = west' /\ east <= east').

(** [@inside purplerain_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (colors : String.string) : Prop := {
  (* a string of n characters (1 <= n <= 10^5) *)
  vi_n : 1 <= slen colors <= 10 ^ 5;
  (* the string consists of uppercase ASCII letters 'R'
     and 'B' only *)
  vi_colors : forall k color, String.get k colors = Some
    color ->
    color = "R"%char \/ color = "B"%char;
}.

(** ** Correctness *)

(** [@requirement]
    The output identifies the stretch of peninsula with the largest absolute
    difference between red and blue section counts, breaking ties by the
    westernmost start and then the westernmost end. *)
Definition purplerain_spec
  (colors : String.string)
  (output : N * N)
  : Prop :=
  match output with
  | (west, east) =>
      is_part colors west east /\
      (forall west' east', is_part colors west' east' ->
         (difference colors west' east' <= difference colors
           west east)%Z) /\
      (forall west' east', is_part colors west' east' ->
         difference colors west' east' = difference colors
           west east ->
         west_or_equal west east west' east')
  end.

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the colour sequence length. *)
Definition purplerain_time_spec (c1 c2 n_colors steps : nat) : Prop :=
  (steps <= c1 * n_colors + c2)%nat.

(** ** Interface *)

(** Find the stretch of peninsula with the largest red-blue imbalance,
    breaking ties by its western endpoint first, then its eastern endpoint.
    - Input [colors]: Rain colors R or B for sections in west-to-east order.
    - Output [output]: Inclusive one-based western and eastern section numbers of the selected stretch. *)
Program purplerain : PrimString.string -> uint * uint.

(** [@example purplerain]
    - Sample: 1
    - Input [colors]: "BBRRBRRBRB"%string
    - Output [output]: (3, 7)
*)

(** ** Bridge *)

(** [@requirement purplerain_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [purplerain_spec]. *)
Specification purplerain_correct :
  forall (colors : String.string) (colors_str :
    PrimString.string),
  valid_input colors -> repr colors_str colors ->
  exists output : N * N,
    repr (purplerain colors_str) output /\
    purplerain_spec colors output.

(** ** Complexity *)

(** [@hide] [purplerain_cost] is the cost translation of [purplerain] (the judge
    recomputes it and compares) ... *)
Complexity purplerain_cost for purplerain.

(** [@fold complexity bound] ... and runs in at most c1 * n + c2 steps of the cost model, n the number of sections, for two constants
    quantified before the input. [@requirement purplerain_time_spec] *)
Specification purplerain_time : exists c1 c2 : nat, forall colors_str : PrimString.string,
  purplerain_time_spec c1 c2 (size colors_str) (cost1 purplerain_cost colors_str).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
