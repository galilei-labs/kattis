(* @function        polymul
   @signature       array sint -> array sint -> array sint
   @math_signature  list Z -> list Z -> list Z
   @summary         [polymul a b] returns the coefficients, lowest degree
                    first, of the product of the two polynomials whose
                    coefficients are a and b : the list of |a| + |b| - 1
                    coefficients whose polynomial takes the value
                    a(x) * b(x) at every integer x.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  A polynomial is the list of its coefficients, a_0 first. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The value at x of the polynomial with coefficients a :
   a_0 + a_1 * x + a_2 * x^2 + ... (Horner's form). *)
Fixpoint eval (a : list Z) (x : Z) : Z :=
  match a with
  | [] => 0
  | c :: a' => c + x * eval a' x
  end.

(* p is the product of a and b : it has |a| + |b| - 1 coefficients and its
   polynomial takes the value a(x) * b(x) at every integer x.  Two
   polynomials of the same length that agree at every integer have the
   same coefficients (a nonzero polynomial has finitely many roots), so
   this pins p down. *)
Definition is_product (a b p : list Z) : Prop :=
  len p = (len a + len b - 1)%N /\
  forall x : Z, eval p x = eval a x * eval b x.

(* The statement's bounds, for one test case. *)
Record valid_input (a b : list Z) : Prop := {
  (* 1 <= n <= 255 : a polynomial of degree n has n + 1 coefficients *)
  vi_a_length : (2 <= len a <= 256)%N;
  vi_b_length : (2 <= len b <= 256)%N;
  (* all coefficients fit in a signed 32-bit integer *)
  vi_a_coeffs : Forall (fun c => - 2 ^ 31 <= c < 2 ^ 31) a;
  vi_b_coeffs : Forall (fun c => - 2 ^ 31 <= c < 2 ^ 31) b;
  (* all coefficients in the result fit in a signed 32-bit integer : a
     guarantee of the statement on the output, hence a condition on the
     inputs *)
  vi_product : forall p, is_product a b p ->
    Forall (fun c => - 2 ^ 31 <= c < 2 ^ 31) p;
}.

(* The result is the product. *)
Definition polymul_spec (a b p : list Z) : Prop := is_product a b p.

(* Kattis sample, first test case : a = [1; 0; 5] (1 + 5 x^2) and
   b = [0; -2] (-2 x).  The product has 3 + 2 - 1 = 4 coefficients,
   p = [0; -2; 0; -10] (-2 x - 10 x^3) : at x = 2, eval p 2 = -84 =
   eval a 2 * eval b 2 = 21 * (-4), and likewise at every x. *)

(* machine side : the only thing that gets extracted *)
Program polymul : array sint -> array sint -> array sint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification polymul_correct : forall (a b : list Z) (x y : array sint),
  valid_input a b -> repr x a -> repr y b ->
  exists p : list Z, repr (polymul x y) p /\ polymul_spec a b p.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
