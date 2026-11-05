(* @function        xormax
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [xormax a] is the largest xor-sum of a subset of the
                    numbers of the list a: some subset of the entries xors
                    to it, and no subset xors to more.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The list is a_1, ..., a_n in input order. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The xor-sum of l: the bitwise xor of its elements, 0 for the empty list. *)
Fixpoint xor_sum (l : list N) : N :=
  match l with
  | [] => 0
  | x :: r => N.lxor x (xor_sum r)
  end.

(* The entries of a selected by the mask m: a_i is kept when the i-th
   boolean of m is true. *)
Fixpoint pick (m : list bool) (a : list N) : list N :=
  match m, a with
  | b :: m', x :: a' => if b then x :: pick m' a' else pick m' a'
  | _, _ => []
  end.

(* v is the xor-sum of some subset of the entries of a (one mask bit per
   entry; the empty subset, of xor-sum 0, is a subset too). *)
Definition subset_xor (a : list N) (v : N) : Prop :=
  exists m : list bool, len m = len a /\ xor_sum (pick m a) = v.

(* The statement's bounds. *)
Record valid_input (a : list N) : Prop := {
  (* an integer n (1 <= n <= 100 000): the length of the list *)
  vi_n : 1 <= len a <= 100000;
  (* n integers a_1, ..., a_n (1 <= a_i <= 10^18) *)
  vi_a : Forall (fun x => 1 <= x <= 10 ^ 18) a;
}.

(* The answer: the maximal xor-sum of a subset, attained and not exceeded. *)
Definition xormax_spec (a : list N) (o : N) : Prop :=
  subset_xor a o /\ forall v, subset_xor a v -> v <= o.

Program xormax : array uint -> uint.

Specification xormax_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists o : N, repr (xormax x) o /\ xormax_spec a o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
