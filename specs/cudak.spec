(* @function        cudak
   @signature       uint -> uint -> uint -> uint * uint
   @math_signature  N -> N -> N -> N * N
   @summary         [cudak a b s] answers Bozo's two questions on the
                    interval [a, b]: how many integers x with a <= x <= b
                    have decimal digit sum s, and which is the smallest of
                    them.  The answer is the pair (count, smallest); the
                    input guarantees that at least one such integer exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* [digit_sum n t]: the decimal digits of n add up to t (the last digit
   is n mod 10, the others are those of n / 10; 0 has digit sum 0). *)
Inductive digit_sum : N -> N -> Prop :=
| digit_sum_zero : digit_sum 0 0
| digit_sum_step : forall n t,
    0 < n -> digit_sum (n / 10) t -> digit_sum n (n mod 10 + t).

(* x is one of the integers Bozo asks about: in [a, b], digit sum s. *)
Definition qualifies (a b s x : N) : Prop :=
  a <= x <= b /\ digit_sum x s.

(* Exactly c integers satisfy P: they form a duplicate-free list of
   length c. *)
Definition count_is (P : N -> Prop) (c : N) : Prop :=
  exists l : list N, NoDup l /\ (forall x, In x l <-> P x) /\ len l = c.

(* The statement's bounds. *)
Record valid_input (a b s : N) : Prop := {
  (* 1 <= A <= B < 10^15 *)
  vi_a : 1 <= a <= b;
  vi_b : b < 10 ^ 15;
  (* 1 <= S <= 135 *)
  vi_s : 1 <= s <= 135;
  (* the input data will guarantee that the first number (the count) is
     at least 1 *)
  vi_exists : exists x, qualifies a b s x;
}.

(* The answer (c, m): c is the number of integers of [a, b] with digit
   sum s, and m is the least of them. *)
Definition cudak_spec (a b s : N) (o : N * N) : Prop :=
  let (c, m) := o in
  count_is (qualifies a b s) c /\
  qualifies a b s m /\
  (forall x, qualifies a b s x -> m <= x).

Program cudak : uint -> uint -> uint -> uint * uint.

Specification cudak_correct :
  forall (a b s : N) (x y z : uint),
  valid_input a b s -> repr x a -> repr y b -> repr z s ->
  exists o : N * N, repr (cudak x y z) o /\ cudak_spec a b s o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
