(** * Polynomial Multiplication 1 *)

(** ** Description *)

(** Multiply two integer polynomials given by their coefficients in
    increasing degree order, returning the product in the same order.

    [@kattis polymul1]
    - Difficulty: 1.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Polynomial degrees: $1 \le n,m \le 255$.
    - Input and output coefficients: $-2^{31} \le c_i < 2^{31}$, with $c_i \in \mathbb{Z}$. *)

(** ** Examples *)

(** - Input convention: Two integer polynomials $A(x)=\sum_{i=0}^{n} a_i x^i$ and $B(x)=\sum_{j=0}^{m} b_j x^j$.
    - Output convention: The coefficients $c_0,\ldots,c_{n+m}$ of $A(x)B(x)$.

    Take $A(x)=1+5x^2$ and $B(x)=-2x$. Then $A(x)B(x)=-2x-10x^3$. *)
(* polymul [1; 0; 5] [0; -2] = [0; -2; 0; -10] *)

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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope Z_scope.

Notation "'ℕ'" := N.
Delimit Scope N_scope with ℕ.
Notation "'ℤ'" := Z.

(* Math side. A polynomial is the list of its
   coefficients, a_0 first. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : ℕ :=
  N.of_nat (List.length l).

(** Evaluate the polynomial with coefficients [coeffs]
    at [point], using Horner's form. *)
Fixpoint eval (coeffs : list ℤ) (point : ℤ) : ℤ :=
  match coeffs with
  | [] => 0
  | coeff :: higher => coeff + point * eval higher point
  end.

(** ** Correctness *)

(** [@requirement]
    The output contains the coefficients of the product polynomial in increasing degree
    order. *)
Definition polymul_spec
  (first_coeffs second_coeffs : list ℤ)
  (output : list ℤ)
  : Prop :=
  len output =
    (len first_coeffs + len second_coeffs - 1)%ℕ /\
  forall point : ℤ,
    eval output point =
    eval first_coeffs point * eval second_coeffs point.

(** [@inside polymul_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (first_coeffs second_coeffs : list ℤ) : Prop := {
  (* 1 <= n <= 255 : a polynomial of degree n has n + 1
     coefficients *)
  vi_a_length : (2 <= len first_coeffs <= 256)%ℕ;
  vi_b_length : (2 <= len second_coeffs <= 256)%ℕ;
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
    polymul_spec first_coeffs second_coeffs product_coeffs ->
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31)
      product_coeffs;
}.

(** ** Interface *)

(** Multiply two integer polynomials given by their coefficients in increasing degree order,
    returning the product in the same order.
    - Input [first_coeffs]: Coefficients $a_0,\ldots,a_n$ of the first polynomial $A(x)$.
    - Input [second_coeffs]: Coefficients $b_0,\ldots,b_m$ of the second polynomial $B(x)$.
    - Output [output]: Coefficients $c_0,\ldots,c_{n+m}$ of the product $A(x)B(x)$, in increasing degree order. *)
Program polymul : array sint -> array sint -> array sint.

(** ** Bridge *)

(** [@requirement polymul_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [polymul_spec]. *)
Specification polymul_correct :
  forall (first_coeffs second_coeffs : list ℤ)
         (first_coeffs_arr second_coeffs_arr : array sint),
  valid_input first_coeffs second_coeffs ->
  repr first_coeffs_arr first_coeffs ->
  repr second_coeffs_arr second_coeffs ->
  exists output : list ℤ,
    repr
      (polymul first_coeffs_arr second_coeffs_arr) output /\
    polymul_spec first_coeffs second_coeffs output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
