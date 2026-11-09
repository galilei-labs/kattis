(** * The Calculus of Ada *)

(** ** Description *)

(** Given polynomial values at equally spaced inputs, find the smallest
    possible degree and predict the next value.

    [@kattis ada]
    - Difficulty: 2.2
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Value count: $2 \le n \le 10$; each between -$2{,}000{,}000$ and $2{,}000{,}000$.
    - At least two values differ. *)

(** ** Examples *)

(** - Input convention: Number of observations, followed by polynomial values at equally spaced inputs.
    - Output convention: Minimum polynomial degree and predicted next value, separated by a space. *)
(* Input:
5 3 6 9 12 15
Output:
1 18
*)

(** ** [@hide] Environment *)

(* @function        ada
   @signature       array sint -> uint * sint
   @math_signature  list Z -> N * Z
   @summary         [ada values] reads values as the values of a polynomial
                    at n = length values regularly spaced inputs and returns
                    (degree, next_value): degree is the degree of a
                    minimal-degree polynomial producing these values, and
                    next_value is the value of that polynomial at the next
                    regularly spaced input.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  A polynomial is the list of its real
  coefficients, the
   constant one first; degree + 1 coefficients make a
     polynomial of degree
   at most degree. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** c_0 + c_1 input + c_2 input^2 + ..., the c_i being
    the coefficients. *)
Definition poly_eval (coefficients : list R)
  (input : R) : R :=
  fold_right (fun coefficient acc =>
    (coefficient + input * acc)%R) 0%R
    coefficients.

(** Evaluated at the regularly spaced inputs start,
    start + spacing, start + 2 spacing, ..., the
    polynomial coefficients takes the values v_1, v_2,
    ..., v_n of values in order. *)
Definition produces (coefficients : list R)
  (start spacing : R)
    (values : list Z) : Prop :=
  forall j : nat, (j < List.length values)%nat ->
    poly_eval coefficients
      (start + INR j * spacing)%R = IZR (nth j values 0).

(** Some polynomial of degree at most degree produces
    values at start, start + spacing, ... *)
Definition fits_degree (start spacing : R)
  (values : list Z) (degree : N)
    : Prop :=
  exists coefficients : list R,
    len coefficients = (degree + 1)%N /\
    produces coefficients start spacing values.

(** degree is the least degree of a polynomial producing
    values at start, start + spacing, ... *)
Definition minimal_degree (start spacing : R)
  (values : list Z) (degree : N)
    : Prop :=
  fits_degree start spacing values degree /\
  forall degree', fits_degree start spacing values degree'
    ->
    (degree <= degree')%N.

(** [@inside ada_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (values : list Z) : Prop := {
  (* a value n, the number of polynomial evaluations, with 2
    <= n <= 10 *)
  vi_n : (2 <= len values <= 10)%N;
  (* each v_j satisfies -2 000 000 <= v_j <= 2 000 000 *)
  vi_values : Forall
    (fun value => -2000000 <= value <= 2000000) values;
  (* at least two of those values differ from each other *)
  vi_differ : exists value value',
    In value values /\ In value' values /\ value <> value';
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the minimum degree of a polynomial fitting the equally spaced
    observations and its value at the next input. *)
Definition ada_spec (values : list Z)
  (output : N * Z) : Prop :=
  match output with
  | (degree, next_value) =>
    forall start spacing : R, (0 < spacing)%R ->
      minimal_degree start spacing values degree /\
      forall coefficients : list R,
        len coefficients = (degree + 1)%N ->
        produces coefficients start spacing values ->
        poly_eval coefficients
          (start + INR (List.length values) * spacing)%R
          = IZR next_value
  end.

(** ** Interface *)

(** Given polynomial values at equally spaced inputs, find the smallest possible degree and
    predict the next value.
    - Input [values]: Polynomial values at equally spaced inputs.
    - Output [output]: The output gives the minimum degree of a polynomial fitting the equally spaced observations and its value at the next input. *)
Program ada : array sint -> uint * sint.

(** ** Bridge *)

(** [@requirement ada_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying [ada_spec]. *)
Specification ada_correct : forall (values : list Z)
  (values_arr : array sint),
  valid_input values -> repr values_arr values ->
  exists output : N * Z, repr (ada values_arr) output
    /\ ada_spec values output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals
    rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
