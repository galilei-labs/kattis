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

From Stdlib Require Import ZArith NArith List Uint63 PArray Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  A polynomial is the list of its real coefficients, the
   constant one first; degree + 1 coefficients make a polynomial of degree
   at most degree. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* c_0 + c_1 input + c_2 input^2 + ..., the c_i being the coefficients. *)
Definition poly_eval (coefficients : list R) (input : R) : R :=
  fold_right (fun coefficient acc => (coefficient + input * acc)%R) 0%R
    coefficients.

(* Evaluated at the regularly spaced inputs start, start + spacing,
   start + 2 spacing, ..., the polynomial coefficients takes the values
   v_1, v_2, ..., v_n of values in order. *)
Definition produces (coefficients : list R) (start spacing : R)
    (values : list Z) : Prop :=
  forall j : nat, (j < List.length values)%nat ->
    poly_eval coefficients (start + INR j * spacing)%R = IZR (nth j values 0).

(* Some polynomial of degree at most degree produces values at start,
   start + spacing, ... *)
Definition fits_degree (start spacing : R) (values : list Z) (degree : N)
    : Prop :=
  exists coefficients : list R,
    len coefficients = (degree + 1)%N /\
    produces coefficients start spacing values.

(* degree is the least degree of a polynomial producing values at start,
   start + spacing, ... *)
Definition minimal_degree (start spacing : R) (values : list Z) (degree : N)
    : Prop :=
  fits_degree start spacing values degree /\
  forall degree', fits_degree start spacing values degree' ->
    (degree <= degree')%N.

(* The statement's bounds. *)
Record valid_input (values : list Z) : Prop := {
  (* a value n, the number of polynomial evaluations, with 2 <= n <= 10 *)
  vi_n : (2 <= len values <= 10)%N;
  (* each v_j satisfies -2 000 000 <= v_j <= 2 000 000 *)
  vi_values : Forall (fun value => -2000000 <= value <= 2000000) values;
  (* at least two of those values differ from each other *)
  vi_differ : exists value value',
    In value values /\ In value' values /\ value <> value';
}.

(* Whatever the start and the spacing > 0 of the inputs: degree is the
   minimal degree, and every polynomial of degree at most degree producing
   values takes the value next_value at the next input
   start + n spacing. *)
Definition ada_spec (values : list Z) (output : N * Z) : Prop :=
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

Program ada : array sint -> uint * sint.

Specification ada_correct : forall (values : list Z) (values_arr : array sint),
  valid_input values -> repr values_arr values ->
  exists output : N * Z, repr (ada values_arr) output /\ ada_spec values output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
