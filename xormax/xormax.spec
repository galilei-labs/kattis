(** * Xor Maximization *)

(** ** Description *)

(** Find the largest bitwise XOR obtainable from any subset of the input
    integers.

    [@kattis xormax]
    - Difficulty: 5.9
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Sequence length: $1 \le n \le 10^{5}$; each value: $1 \le a_i \le 10^{18}$. *)

(** ** Examples *)

(** - Input convention: Sequence length, followed by space-separated positive integers.
    - Output convention: A single integer giving the maximum subset XOR. *)
(* Input:
3
1 3 5
Output:
7
*)

(** ** [@hide] Environment *)

(* @function        xormax
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [xormax numbers] is the largest xor-sum of a subset of
                    the list numbers: some subset of the entries xors to it,
                    and no subset xors to more.
                    It runs in at most c1 * (n + 1) + c2 steps of the cost
                    model, n the number of entries (one insertion into the
                    63-cell basis per entry), for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* The list numbers is a_1, ..., a_n in input
   order. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The bitwise XOR of [values], with value zero for the empty list. *)
Fixpoint xor_sum (values : list N) : N :=
  match values with
  | [] => 0
  | value :: rest => N.lxor value (xor_sum rest)
  end.

(** Select entries of [values] whose corresponding Boolean in [mask] is true. *)
Fixpoint pick (mask : list bool) (values : list N) : list N
  :=
  match mask, values with
  | keep :: mask_rest, value :: rest =>
      if keep then value :: pick mask_rest rest else pick
        mask_rest rest
  | _, _ => []
  end.

(** [xor_value] is the bitwise XOR of some subset of the entries of [numbers].
    The empty subset is permitted and has XOR zero. *)
Definition subset_xor (numbers : list N) (xor_value : N) :
  Prop :=
  exists mask : list bool,
    len mask = len numbers /\ xor_sum (pick mask numbers) =
      xor_value.

(** [@inside xormax_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (numbers : list N) : Prop := {
  (* an integer n (1 <= n <= 10^5): the length of the
     list *)
  vi_n : 1 <= len numbers <= 100000;
  (* n integers a_1, ..., a_n (1 <= a_i <= 10^18) *)
  vi_a : Forall (fun number => 1 <= number <= 10 ^ 18)
    numbers;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the maximum XOR of any subset of the input values. *)
Definition xormax_spec
  (numbers : list N )
  (output : N)
  : Prop :=
  subset_xor numbers output /\
  forall candidate, subset_xor numbers candidate ->
    candidate <= output.

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the number of input numbers. *)
Definition xormax_time_spec (c1 c2 n_numbers steps : nat) : Prop :=
  (steps <= c1 * (n_numbers + 1) + c2)%nat.

(** ** Interface *)

(** Find the largest bitwise XOR obtainable from any subset of the input integers.
    - Input [numbers]: Integers available for subset selection.
    - Output [output]: The output is the maximum XOR of any subset of the input values. *)
Program xormax : array uint -> uint.

(** [@example xormax]
    - Sample: 1
    - Input [numbers]: [1; 3; 5]
    - Output [output]: 7
*)

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

(** ** Complexity *)

(** [@hide] [xormax_cost] is the cost translation of [xormax] (the judge
    recomputes it and compares) ... *)
Complexity xormax_cost for xormax.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) + c2 steps of the cost model, n the number of entries (one insertion into the 63-cell basis per entry), for two constants
    quantified before the input. [@requirement xormax_time_spec] *)
Specification xormax_time : exists c1 c2 : nat, forall numbers_arr : array uint,
  xormax_time_spec c1 c2 (size numbers_arr) (cost1 xormax_cost numbers_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
