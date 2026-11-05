(* @function        ada
   @signature       array sint -> uint * sint
   @math_signature  list Z -> N * Z
   @summary         [ada v] reads v as the values of a polynomial at
                    n = length v regularly spaced inputs and returns (d, w):
                    d is the degree of a minimal-degree polynomial producing
                    these values, and w is the value of that polynomial at
                    the next regularly spaced input.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  A polynomial is the list of its real coefficients, the
   constant one first; d + 1 coefficients make a polynomial of degree at
   most d. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* c_0 + c_1 x + c_2 x^2 + ... *)
Definition poly_eval (c : list R) (x : R) : R :=
  fold_right (fun a acc => (a + x * acc)%R) 0%R c.

(* Evaluated at the regularly spaced inputs x0, x0 + h, x0 + 2h, ..., the
   polynomial c takes the values v_1, v_2, ..., v_n in order. *)
Definition produces (c : list R) (x0 h : R) (v : list Z) : Prop :=
  forall j : nat, (j < List.length v)%nat ->
    poly_eval c (x0 + INR j * h)%R = IZR (nth j v 0).

(* Some polynomial of degree at most d produces v at x0, x0 + h, ... *)
Definition fits_degree (x0 h : R) (v : list Z) (d : N) : Prop :=
  exists c : list R, len c = (d + 1)%N /\ produces c x0 h v.

(* d is the least degree of a polynomial producing v at x0, x0 + h, ... *)
Definition minimal_degree (x0 h : R) (v : list Z) (d : N) : Prop :=
  fits_degree x0 h v d /\ forall d', fits_degree x0 h v d' -> (d <= d')%N.

(* The statement's bounds. *)
Record valid_input (v : list Z) : Prop := {
  (* a value n, the number of polynomial evaluations, with 2 <= n <= 10 *)
  vi_n : (2 <= len v <= 10)%N;
  (* each v_j satisfies -2 000 000 <= v_j <= 2 000 000 *)
  vi_values : Forall (fun x => -2000000 <= x <= 2000000) v;
  (* at least two of those values differ from each other *)
  vi_differ : exists a b, In a v /\ In b v /\ a <> b;
}.

(* Whatever the start x0 and the spacing h > 0 of the inputs: d is the
   minimal degree, and every polynomial of degree at most d producing v
   takes the value w at the next input x0 + n h. *)
Definition ada_spec (v : list Z) (o : N * Z) : Prop :=
  let (d, w) := o in
  forall x0 h : R, (0 < h)%R ->
    minimal_degree x0 h v d /\
    forall c : list R, len c = (d + 1)%N -> produces c x0 h v ->
      poly_eval c (x0 + INR (List.length v) * h)%R = IZR w.

Program ada : array sint -> uint * sint.

Specification ada_correct : forall (v : list Z) (x : array sint),
  valid_input v -> repr x v ->
  exists o : N * Z, repr (ada x) o /\ ada_spec v o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
