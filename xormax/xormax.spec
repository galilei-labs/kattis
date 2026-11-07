(** * Xor Maximization *)

(** ** Description *)

(** Find the largest XOR obtainable from a subset of the
    input entries.

    [@kattis xormax]
    - Difficulty: 5.9
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB *)

(** ** [@hide] Environment *)

(* @function        xormax
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [xormax numbers] is the largest xor-sum of a subset of
                    the list numbers: some subset of the entries xors to it,
                    and no subset xors to more.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. The list numbers is a_1, ..., a_n in input
   order. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The xor-sum of values: the bitwise xor of its
    elements, 0 for the empty list. *)
Fixpoint xor_sum (values : list N) : N :=
  match values with
  | [] => 0
  | value :: rest => N.lxor value (xor_sum rest)
  end.

(** The entries of values selected by mask: the i-th
    entry is kept when the i-th boolean of mask is true. *)
Fixpoint pick (mask : list bool) (values : list N) : list N
  :=
  match mask, values with
  | keep :: mask_rest, value :: rest =>
      if keep then value :: pick mask_rest rest else pick
        mask_rest rest
  | _, _ => []
  end.

(** xor_value is the xor-sum of some subset of the
    entries of [numbers] (one mask bit per entry; the
    empty subset, of xor-sum 0, is a subset too). *)
Definition subset_xor (numbers : list N) (xor_value : N) :
  Prop :=
  exists mask : list bool,
    len mask = len numbers /\ xor_sum (pick mask numbers) =
      xor_value.

(** [@inside xormax_correct] The statement's bounds. *)
Record valid_input (numbers : list N) : Prop := {
  (* an integer n (1 <= n <= 100 000): the length of the
     list *)
  vi_n : 1 <= len numbers <= 100000;
  (* n integers a_1, ..., a_n (1 <= a_i <= 10^18) *)
  vi_a : Forall (fun number => 1 <= number <= 10 ^ 18)
    numbers;
}.

(** ** Correctness *)

(** [@requirement] [@short Find the largest XOR
    obtainable from a subset of the input entries.] The
    answer: the maximal xor-sum of a subset, attained and
    not exceeded. *)
Definition xormax_spec
  (numbers : list N )
  (output : N)
  : Prop :=
  subset_xor numbers output /\
  forall candidate, subset_xor numbers candidate ->
    candidate <= output.

(** ** Interface *)

(** Find the largest XOR obtainable from a subset of the
    input entries.
    - Input [numbers]:
    - Output [output]: *)
Program xormax : array uint -> uint.

(** ** Bridge *)

(** [@requirement xormax_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [xormax_spec]. *)
Specification xormax_correct :
  forall (numbers : list N) (numbers_arr : array uint),
  valid_input numbers -> repr numbers_arr numbers ->
  exists output : N,
    repr (xormax numbers_arr) output /\ xormax_spec numbers
      output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
