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
   @summary         [polymul A_coeffs B_coeffs] returns the
                    coefficients, lowest degree first, of the product of
                    the two polynomials whose coefficients are A_coeffs
                    and B_coeffs : the list of
                    |A_coeffs| + |B_coeffs| - 1 coefficients whose
                    polynomial takes the value
                    first(point) * second(point) at every integer point.
                    It runs in at most c1 * (p + 1) * (q + 1) + c2 steps of
                    the cost model on a valid input, p and q the lengths of
                    the two inputs (the schoolbook double loop), for two
                    constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

Notation "'ℕ'" := N.
Delimit Scope N_scope with ℕ.
Notation "'ℤ'" := Z.

(* A polynomial is the list of its
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
For input polynomials $A$ and $B$ of degrees $n$ and $m$, the output polynomial $C$:
- has degree $n + m$;
- satisfies $C(x) = A(x)B(x)$ at every integer point $x \in ℤ$. *)
Definition polymul_spec
  (A_coeffs B_coeffs : list ℤ)
  (output : list ℤ)
  : Prop :=
  len output =
    (len A_coeffs + len B_coeffs - 1)%ℕ /\
  forall point : ℤ,
    eval output point =
    eval A_coeffs point * eval B_coeffs point.

(** [@inside polymul_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (A_coeffs B_coeffs : list ℤ) : Prop := {
  (* 1 <= n <= 255 : a polynomial of degree n has n + 1
     coefficients *)
  vi_a_length : (2 <= len A_coeffs <= 256)%ℕ;
  vi_b_length : (2 <= len B_coeffs <= 256)%ℕ;
  (* all coefficients fit in a signed 32-bit integer *)
  vi_a_coeffs :
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31)
      A_coeffs;
  vi_b_coeffs :
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31)
      B_coeffs;
  (* all coefficients in the result fit in a signed
     32-bit integer : a guarantee of the statement on the
     output, hence a condition on the inputs *)
  vi_product : forall product_coeffs,
    polymul_spec A_coeffs B_coeffs product_coeffs ->
    Forall (fun coeff => - 2 ^ 31 <= coeff < 2 ^ 31)
      product_coeffs;
}.

(** ** Complexity *)

(** [@requirement] Runs in $O((n+1)(m+1))$ steps, where $n$ and $m$ are the numbers of coefficients in the two input polynomials. *)
Definition polymul_time_spec (c1 c2 n_A_coeffs n_B_coeffs steps : nat) : Prop :=
  (steps <= c1 * ((n_A_coeffs + 1) * (n_B_coeffs + 1)) + c2)%nat.

(** ** Interface *)

(** Multiply two integer polynomials given by their coefficients in increasing degree order,
    returning the product in the same order.
    - Input [A_coeffs]: Coefficients $a_0,\ldots,a_n$ of the first polynomial $A(x)$.
    - Input [B_coeffs]: Coefficients $b_0,\ldots,b_m$ of the second polynomial $B(x)$.
    - Output [output]: Coefficients $c_0,\ldots,c_{n+m}$ of the product $A(x)B(x)$, in increasing degree order. *)
Program polymul : array sint -> array sint -> array sint.

(** [@example polymul]
    - Sample: 1
    - Input [A_coeffs]: [1; 0; 5]%Z
    - Input [B_coeffs]: [0; -2]%Z
    - Output [output]: [0; -2; 0; -10]%Z
*)

(** ** Bridge *)

(** [@requirement polymul_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [polymul_spec]. *)
Specification polymul_correct :
  forall (A_coeffs B_coeffs : list ℤ)
         (A_coeffs_arr B_coeffs_arr : array sint),
  valid_input A_coeffs B_coeffs ->
  repr A_coeffs_arr A_coeffs ->
  repr B_coeffs_arr B_coeffs ->
  exists output : list ℤ,
    repr
      (polymul A_coeffs_arr B_coeffs_arr) output /\
    polymul_spec A_coeffs B_coeffs output.

(** ** Complexity *)

(** [@hide] [polymul_cost] is the cost translation of [polymul] (the judge
    recomputes it and compares) ... *)
Complexity polymul_cost for polymul.

(** [@fold complexity bound] ... and runs in at most c1 * (p + 1) * (q + 1) + c2 steps of the cost model on a valid input, p and q the lengths of the two inputs (the schoolbook double loop), for two constants
    quantified before the inputs, on every valid input. [@requirement polymul_time_spec] *)
Specification polymul_time : exists c1 c2 : nat,
  forall (A_coeffs B_coeffs : list ℤ)
  (A_coeffs_arr B_coeffs_arr : array sint),
  valid_input A_coeffs B_coeffs ->
  repr A_coeffs_arr A_coeffs ->
  repr B_coeffs_arr B_coeffs ->
  polymul_time_spec c1 c2 (size A_coeffs_arr) (size B_coeffs_arr) (cost2 polymul_cost A_coeffs_arr B_coeffs_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
