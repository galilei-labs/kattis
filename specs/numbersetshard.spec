(* @function        numbersets
   @signature       uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N
   @summary         [numbersets a b p] is the number of sets left when every
                    integer of [a, b] starts in a set of its own and the sets
                    of any two integers of [a, b] sharing a prime factor at
                    least p are merged.  One call per test case.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Znumtheory Relations.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

Definition in_interval (a b x : N) : Prop := a <= x <= b.

(* Some prime q >= p divides both x and y. *)
Definition share_prime_at_least (p x y : N) : Prop :=
  exists q : N, prime (Z.of_N q) /\ p <= q /\ N.divide q x /\ N.divide q y.

(* One merge of the statement: two integers of the interval sharing such a
   prime factor. *)
Definition merge (a b p x y : N) : Prop :=
  in_interval a b x /\ in_interval a b y /\ share_prime_at_least p x y.

(* x and y end in the same set: they are linked by a chain of merges. *)
Definition same_set (a b p : N) : N -> N -> Prop :=
  clos_refl_sym_trans N (merge a b p).

(* There are n sets at the end: n integers of the interval, no two in the
   same set, such that every integer of the interval is in the set of one
   of them. *)
Definition set_count (a b p n : N) : Prop :=
  exists reps : list N,
    len reps = n /\
    Forall (in_interval a b) reps /\
    ForallOrdPairs (fun r s => ~ same_set a b p r s) reps /\
    (forall x, in_interval a b x -> exists r, In r reps /\ same_set a b p x r).

(* The statement's bounds, for one test case. *)
Record valid_input (a b p : N) : Prop := {
  (* 1 <= A <= B <= 10^12 *)
  vi_a : 1 <= a;
  vi_ab : a <= b;
  vi_b : b <= 10 ^ 12;
  (* B <= A + 1 000 000 *)
  vi_width : b <= a + 1000000;
  (* 2 <= P <= B *)
  vi_p : 2 <= p <= b;
}.

(* The answer: the number of sets at the end. *)
Definition numbersets_spec (a b p n : N) : Prop := set_count a b p n.

Program numbersets : uint -> uint -> uint -> uint.

Specification numbersets_correct : forall (a b p : N) (x y z : uint),
  valid_input a b p -> repr x a -> repr y b -> repr z p ->
  exists n : N, repr (numbersets x y z) n /\ numbersets_spec a b p n.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
