(** * Sumsets *)

(** ** Description *)

(** Find the largest member of an integer set equal to the sum of three
    other distinct members, or report that none exists.

    [@kattis sumsets]
    - Difficulty: 6.7
    - CPU time limit: 11 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Distinct integer count: $1 \le n \le 4 \times 10^{3}$.
    - Values: $-2^{29} \le a_i \le 2^{29} - 1$. *)

(** ** Examples *)

(** - Input convention: Set size, followed by distinct integer elements, one per line.
    - Output convention: The largest valid target value, or no solution. *)
(* Input:
5
2
3
5
7
12
Output:
12
*)

(** ** [@hide] Environment *)

(* @function        sumsets
   @signature       array sint -> option sint
   @math_signature  list Z -> option Z
   @summary         [sumsets elements] takes the set S of distinct integers
                    and returns [Some target] for the largest target such
                    that first + second + third = target where first,
                    second, third and target are distinct elements of S,
                    and [None] ("no solution") when no such target exists.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope Z_scope.

(* S is the list elements of its elements, in
   input order. The elements are signed (the statement
   allows negatives) : sint / Z. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** [target] and three pairwise distinct summands all belong to [elements], and
    their sum is [target]. The summands are also distinct from [target]. *)
Definition sum_of_three (elements : list Z) (target : Z) :
  Prop :=
  exists first second third,
    In first elements /\ In second elements /\ In third
      elements /\
    In target elements /\
    first <> second /\ first <> third /\ first <> target /\
    second <> third /\ second <> target /\ third <> target
      /\
    first + second + third = target.

(** [@inside sumsets_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (elements : list Z) : Prop := {
  (* 1 <= N <= 4 * 10^3, the number of elements in S *)
  vi_n : (1 <= len elements <= 4000)%N;
  (* each element of S is a distinct integer *)
  vi_distinct : NoDup elements;
  (* each element x satisfies -2^29 <= x <= 2^29 - 1 *)
  vi_range : Forall
    (fun element => -536870912 <= element <= 536870911)
               elements;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the greatest input value expressible as the sum of three other
    distinct input elements, or None if no such value exists. *)
Definition sumsets_spec
  (elements : list Z )
  (output : option Z )
  : Prop :=
  match output with
  | Some target =>
      sum_of_three elements target /\
      forall target', sum_of_three elements target' ->
        target' <= target
  | None => forall target, ~ sum_of_three elements target
  end.

(** ** Interface *)

(** Find the largest member of an integer set equal to the sum of three other distinct
    members, or report that none exists.
    - Input [elements]: Distinct integers available for the sum relation.
    - Output [output]: The output is the greatest input value expressible as the sum of three other distinct input elements, or None if no such value exists. *)
Program sumsets : array sint -> option sint.

(** [@example sumsets]
    - Sample: 1
    - Input [elements]: [2; 3; 5; 7; 12]%Z
    - Output [output]: Some 12%Z
*)

(** ** Bridge *)

(** [@requirement sumsets_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [sumsets_spec]. *)
Specification sumsets_correct :
  forall (elements : list Z) (elements_arr : array sint),
  valid_input elements -> repr elements_arr elements ->
  exists output : option Z,
    repr (sumsets elements_arr) output /\
    sumsets_spec elements output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
