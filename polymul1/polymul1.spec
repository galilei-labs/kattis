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

(* Math side.  A polynomial is the list of its coefficients, a_0 first. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The value at point of the polynomial with coefficients coeffs :
   coeffs_0 + coeffs_1 * point + coeffs_2 * point^2 + ... (Horner's
   form). *)
Fixpoint eval (coeffs : list Z) (point : Z) : Z :=
  match coeffs with
  | [] => 0
  | coeff :: higher => coeff + point * eval higher point
  end.

(* product_coeffs is the product of first_coeffs and second_coeffs : it
   has |first_coeffs| + |second_coeffs| - 1 coefficients and its
   polynomial takes the value first(point) * second(point) at every
   integer point.  Two polynomials of the same length that agree at every
   integer have the same coefficients (a nonzero polynomial has finitely
   many roots), so this pins product_coeffs down. *)
Definition is_product (first_coeffs second_coeffs product_coeffs : list Z)
    : Prop :=
  len product_coeffs = (len first_coeffs + len second_coeffs - 1)%N /\
  forall point : Z,
    eval product_coeffs point =
    eval first_coeffs point * eval second_coeffs point.

(* The statement's bounds, for one test case. *)
Record valid_input (first_coeffs second_coeffs : list Z) : Prop := {
  (* 1 <= n <= 255 : a polynomial of degree n has n + 1 coefficients *)
  vi_a_length : (2 <= len first_coeffs <= 256)%N;
  vi_b_length : (2 <= len second_coeffs <= 256)%N;
  (* all coefficients fit in a signed 32-bit integer *)
  vi_a_coeffs :
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31) first_coeffs;
  vi_b_coeffs :
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31) second_coeffs;
  (* all coefficients in the result fit in a signed 32-bit integer : a
     guarantee of the statement on the output, hence a condition on the
     inputs *)
  vi_product : forall product_coeffs,
    is_product first_coeffs second_coeffs product_coeffs ->
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31) product_coeffs;
}.

(* The result is the product. *)
Definition polymul_spec (first_coeffs second_coeffs : list Z)
    (output : list Z) : Prop :=
  is_product first_coeffs second_coeffs output.

(* Kattis sample, first test case : first_coeffs = [1; 0; 5] (1 + 5 x^2)
   and second_coeffs = [0; -2] (-2 x).  The product has 3 + 2 - 1 = 4
   coefficients, output = [0; -2; 0; -10] (-2 x - 10 x^3) : at
   point 2, eval output 2 = -84 =
   eval first_coeffs 2 * eval second_coeffs 2 = 21 * (-4), and likewise at
   every point. *)

(* machine side : the only thing that gets extracted *)
Program polymul : array sint -> array sint -> array sint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification polymul_correct :
  forall (first_coeffs second_coeffs : list Z)
         (first_coeffs_arr second_coeffs_arr : array sint),
  valid_input first_coeffs second_coeffs ->
  repr first_coeffs_arr first_coeffs ->
  repr second_coeffs_arr second_coeffs ->
  exists output : list Z,
    repr (polymul first_coeffs_arr second_coeffs_arr) output /\
    polymul_spec first_coeffs second_coeffs output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
