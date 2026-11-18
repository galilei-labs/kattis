(** * Cold-puter Science *)

(** ** Description *)

(** Given daily temperatures in degrees Celsius, count the days on which
    the temperature was below freezing: strictly less than zero.

    [@kattis cold]
    - Difficulty: 1.2
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1 \le n \le 100$.
    - $-10^{6} \le t_i \le 10^{6}$ for every value $t_i$. *)

(** ** Examples *)

(** - Input convention: A function call with an integer list; semicolons separate list elements.
    - Output convention: The number of list elements strictly below zero. *)
(* count_negatives [5; -10; 15] = 1 *)
(* count_negatives [-14; -5; -39; -5; -7] = 5 *)

(** ** [@hide] Environment *)
(* @function        count_negatives
   @signature       array sint -> uint
   @math_signature  list Z -> N
   @summary         [count_negatives temperatures] returns the number of
                    elements of temperatures that are strictly below zero
                    It runs in at most c1 * n + c2 steps of the cost model,
                    n the length of the array, for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** [temperature] is strictly below zero. *)
Definition is_negative (temperature : Z) : bool :=
  temperature <? 0.

(** [@inside count_negatives_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (temperatures : list Z) : Prop := {
  (* 1 <= n <= 100 *)
  vi_length : (1 <= len temperatures <= 100)%N;
  (* -10^6 <= t <= 10^6 *)
  vi_values :
    Forall
      (fun temperature => - 10 ^ 6 <= temperature <= 10 ^ 6)
      temperatures;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the number of days with a temperature strictly below zero
    degrees Celsius. *)
Definition count_negatives_spec
  (temperatures : list Z) (output : N) : Prop :=
  output = len (filter is_negative temperatures).

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the number of temperatures. *)
Definition count_negatives_time_spec (c1 c2 n_temperatures steps : nat) : Prop :=
  (steps <= c1 * n_temperatures + c2)%nat.

(** ** Interface *)

(** Count the days with a temperature strictly below zero degrees Celsius.
    - Input [temperatures]: Daily integer temperatures in degrees Celsius.
    - Output [output]: Number of days below freezing. *)
Program count_negatives : array sint -> uint.

(** [@example count_negatives]
    - Sample: 1
    - Input [temperatures]: [5; -10; 15]%Z
    - Output [output]: 1
*)

(** [@example count_negatives]
    - Sample: 2
    - Input [temperatures]: [-14; -5; -39; -5; -7]%Z
    - Output [output]: 5
*)

(** ** Bridge *)

(** [@requirement count_negatives_spec] [@fold full correctness statement]
    On a valid represented input, [count_negatives] returns a represented output
    satisfying [count_negatives_spec]. *)
Specification count_negatives_correct :
  forall (temperatures : list Z)
         (temperatures_arr : array sint),
  valid_input temperatures ->
  repr temperatures_arr temperatures ->
  exists output : N,
    repr (count_negatives temperatures_arr) output /\
    count_negatives_spec temperatures output.

(** ** Complexity *)

(** [@hide] [count_negatives_cost] is the cost translation of [count_negatives] (the judge
    recomputes it and compares) ... *)
Complexity count_negatives_cost for count_negatives.

(** [@fold complexity bound] ... and runs in at most c1 * n + c2 steps of the cost model, n the length of the array, for two constants
    quantified before the input. [@requirement count_negatives_time_spec] *)
Specification count_negatives_time : exists c1 c2 : nat, forall temperatures_arr : array sint,
  count_negatives_time_spec c1 c2 (size temperatures_arr) (cost1 count_negatives_cost temperatures_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
