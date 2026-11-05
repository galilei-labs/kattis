(* @function        primepower
   @signature       uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N
   @summary         [primepower e l r] returns the product of p^e over all
                    primes p with l <= p <= r, reduced modulo 10^9 + 7.  The
                    three arguments are the three integers of the input, in
                    the order E, L, R; the result is the integer printed.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Znumtheory.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The modulus of the output, 10^9 + 7. *)
Definition modulus : N := 1000000007.

(* The product of p^e over the primes p of [lo, lo + k - 1] (1 when there
   are none). *)
Fixpoint prime_power_product_from (e lo : N) (k : nat) : N :=
  match k with
  | O => 1
  | S k' =>
      (if prime_dec (Z.of_N lo) then lo ^ e else 1)
      * prime_power_product_from e (lo + 1) k'
  end.

(* The product of p^e over the primes p with l <= p <= r. *)
Definition prime_power_product (e l r : N) : N :=
  prime_power_product_from e l (N.to_nat (r + 1 - l)).

(* The statement's bounds. *)
Record valid_input (e l r : N) : Prop := {
  (* E (1 <= E <= 1,000,000) *)
  vi_e : 1 <= e <= 10 ^ 6;
  (* L and R (1 <= L <= R <= 1,000,000) *)
  vi_l : 1 <= l;
  vi_lr : l <= r;
  vi_r : r <= 10 ^ 6;
}.

(* The answer: the product modulo 10^9 + 7. *)
Definition primepower_spec (e l r o : N) : Prop :=
  o = prime_power_product e l r mod modulus.

Program primepower : uint -> uint -> uint -> uint.

Specification primepower_correct :
  forall (e l r : N) (x y z : uint),
  valid_input e l r -> repr x e -> repr y l -> repr z r ->
  exists o : N, repr (primepower x y z) o /\ primepower_spec e l r o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
