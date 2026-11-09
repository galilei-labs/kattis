(** * Cold-puter Science *)

(** ** Description *)

(** Given [n] integers [t_1, ..., t_n], count how many are strictly below zero.

    [@kattis cold]
    - Difficulty: 1.2
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - [1 <= n <= 100]
    - [-1000000 <= t_i <= 1000000] for every [i] *)

(** ** Examples *)
(* count_negatives [5; -10; 15] = 1 *)
(* count_negatives [-14; -5; -39; -5; -7] = 5 *)

(** ** [@hide] Environment *)
(* @function        count_negatives
   @signature       array sint -> uint
   @math_signature  list Z -> N
   @summary         [count_negatives temperatures] returns the number of
                    elements of temperatures that are strictly below zero
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** [temperature] is strictly below zero. *)
Definition is_negative (temperature : Z) : bool :=
  temperature <? 0.

(** [@inside count_negatives_correct] The statement's bounds. *)
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

(** [@requirement] [@short must output the number of negative entries of [temperatures].]
    The result [output] is the number of negative entries of [temperatures]. *)
Definition count_negatives_spec
  (temperatures : list Z) (output : N) : Prop :=
  output = len (filter is_negative temperatures).

(** ** Interface *)

(** Count the integers strictly below zero, on machine types.
    - Input [temperatures]:
    - Output [output]: *)
Program count_negatives : array sint -> uint.

(** ** Bridge *)

(** [@requirement count_negatives_spec] [@fold full correctness statement]
    Every valid input is machine-representable and, on its machine
    representation, the program returns a machine-representable output
    satisfying the specification. *)
Specification count_negatives_correct :
  forall (temperatures : list Z)
         (temperatures_arr : array sint),
  valid_input temperatures ->
  repr temperatures_arr temperatures ->
  exists output : N,
    repr (count_negatives temperatures_arr) output /\
    count_negatives_spec temperatures output.

(** [@hide] The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
