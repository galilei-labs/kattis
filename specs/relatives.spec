(* @function        relatives
   @signature       uint -> uint
   @math_signature  N -> N
   @summary         [relatives n] is the number of positive integers k less
                    than n that are relatively prime to n, in the
                    statement's sense: no integer x >= 2 divides both. One
                    test case per call; n = 1 gives 0.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The statement's definition: a and b are relatively prime when there are
   no integers x >= 2, y >= 1, z >= 1 such that a = x*y and b = x*z (all
   three are positive, so they range over N). *)
Definition relatively_prime (a b : N) : Prop :=
  ~ exists x y z, 2 <= x /\ 1 <= y /\ 1 <= z /\ a = x * y /\ b = x * z.

(* k is counted for n: a positive integer less than n, relatively prime
   to n. *)
Definition relative (n k : N) : Prop :=
  1 <= k < n /\ relatively_prime k n.

(* c is the number of naturals satisfying P: P holds of exactly the
   members of a duplicate-free list of length c. *)
Definition count_of (P : N -> Prop) (c : N) : Prop :=
  exists l : list N, NoDup l /\ (forall k, In k l <-> P k) /\ len l = c.

(* The statement's bounds, for one test case. *)
Record valid_input (n : N) : Prop := {
  (* a line with 1 <= n <= 1 000 000 000 *)
  vi_n : 1 <= n <= 10^9;
}.

(* The answer: how many positive integers less than n are relatively prime
   to n. *)
Definition relatives_spec (n c : N) : Prop :=
  count_of (relative n) c.

Program relatives : uint -> uint.

Specification relatives_correct : forall (n : N) (x : uint),
  valid_input n -> repr x n ->
  exists c : N, repr (relatives x) c /\ relatives_spec n c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
