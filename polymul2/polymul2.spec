(** * Polynomial Multiplication 2 *)

(** ** Description *)

(** Multiply two integer polynomials given by their coefficients in
    increasing degree order, returning the product in the same order.

    [@kattis polymul2]
    - Difficulty: 4.5
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Each polynomial has degree from 1 to 131,071.
    - Input and output coefficients are signed 32-bit integers. *)

(** ** Examples *)

(* Kattis sample : first_coeffs = [1; 0; 5] (1 + 5 x^2)
   and second_coeffs = [0; -2] (-2 x). The product has 3
   + 2 - 1 = 4 coefficients, output = [0; -2; 0; -10] (-2
   x - 10 x^3) : at point 2, eval output 2 = -84 = eval
   first_coeffs 2 * eval second_coeffs 2 = 21 * (-4), and
   likewise at every point. *)

(** ** [@hide] Environment *)

(* @function        polymul
   @signature       array sint -> array sint -> array sint
   @math_signature  list Z -> list Z -> list Z
   @summary         [polymul first_coeffs second_coeffs] returns the
                    coefficients, lowest degree first, of the product of
                    the two polynomials whose coefficients are first_coeffs
                    and second_coeffs : the list of
                    |first_coeffs| + |second_coeffs| - 1 coefficients whose
                    polynomial takes the value
                    first(point) * second(point) at every integer point.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side. A polynomial is the list of its
   coefficients, a_0 first. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Evaluate the polynomial with coefficients [coeffs]
    at [point], using Horner's form. *)
Fixpoint eval (coeffs : list Z) (point : Z) : Z :=
  match coeffs with
  | [] => 0
  | coeff :: higher => coeff + point * eval higher point
  end.

(** [product_coeffs] contains the coefficients of the
    product, from lowest to highest degree. Its length
    is the sum of the input lengths minus one, and its
    value at every integer [point] equals the product
    of the input polynomials' values. *)
Definition is_product
  (first_coeffs second_coeffs product_coeffs : list Z)
  : Prop :=
  len product_coeffs =
    (len first_coeffs + len second_coeffs - 1)%N /\
  forall point : Z,
    eval product_coeffs point =
    eval first_coeffs point * eval second_coeffs point.

(** [@inside polymul_correct] The statement's bounds, for
    the one test case. *)
Record valid_input
  (first_coeffs second_coeffs : list Z) : Prop := {
  (* 1 <= n <= 131071 = 2^17 - 1 : a polynomial of degree
     n has n + 1 coefficients *)
  vi_a_length : (2 <= len first_coeffs <= 2 ^ 17)%N;
  vi_b_length : (2 <= len second_coeffs <= 2 ^ 17)%N;
  (* all coefficients fit in a signed 32-bit integer *)
  vi_a_coeffs :
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31)
      first_coeffs;
  vi_b_coeffs :
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31)
      second_coeffs;
  (* all coefficients in the result fit in a signed
     32-bit integer : a guarantee of the statement on the
     output, hence a condition on the inputs *)
  vi_product : forall product_coeffs,
    is_product first_coeffs second_coeffs product_coeffs ->
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31)
      product_coeffs;
}.

(** ** Correctness *)

(** [@requirement] [@short Multiply two polynomials whose
    integer coefficients are listed from lowest to
    highest degree.] The result is the product. *)
Definition polymul_spec
  (first_coeffs second_coeffs : list Z)
  (output : list Z)
  : Prop :=
  is_product first_coeffs second_coeffs output.

(** ** Interface *)

(** Multiply two polynomials whose integer coefficients
    are listed from lowest to highest degree.
    - Input [first_coeffs]:
    - Input [second_coeffs]:
    - Output [output]: *)
Program polymul : array sint -> array sint -> array sint.

(** ** Bridge *)

(** [@requirement polymul_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [polymul_spec]. *)
Specification polymul_correct :
  forall (first_coeffs second_coeffs : list Z)
         (first_coeffs_arr second_coeffs_arr : array sint),
  valid_input first_coeffs second_coeffs ->
  repr first_coeffs_arr first_coeffs ->
  repr second_coeffs_arr second_coeffs ->
  exists output : list Z,
    repr
      (polymul first_coeffs_arr second_coeffs_arr) output /\
    polymul_spec first_coeffs second_coeffs output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
