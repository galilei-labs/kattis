(* @function        canonical
   @signature       array uint -> bool
   @math_signature  list N -> bool
   @summary         [canonical c] takes a coin system given as its
                    denominations in increasing order, the first being 1,
                    and returns true exactly when the system is canonical:
                    no positive amount has a minimum number of coins
                    strictly smaller than the number of coins the greedy
                    algorithm uses for it.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A coin system is the list of its denominations, c_1 first. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The denomination c_(k+1) (index k, from 0). *)
Definition coin (c : list N) (k : N) : N := nth (N.to_nat k) c 0.

(* The amount x is the sum of exactly m coins of c, each denomination
   usable any number of times. *)
Inductive sums_to (c : list N) : N -> N -> Prop :=
| sums_nil : sums_to c 0 0
| sums_cons : forall d x m,
    In d c -> sums_to c x m -> sums_to c (x + d) (m + 1).

(* m is the smallest number of coins required to dispense exactly x. *)
Definition min_coins (c : list N) (x m : N) : Prop :=
  sums_to c x m /\ forall m', sums_to c x m' -> m <= m'.

(* d is a coin of the largest denomination that is at most x. *)
Definition largest_le (c : list N) (x d : N) : Prop :=
  In d c /\ d <= x /\ forall e, In e c -> e <= x -> e <= d.

(* The greedy algorithm, repeatedly choosing a coin of the largest
   denomination at most the amount still owed until it reaches zero,
   dispenses x with g coins. *)
Inductive greedy_uses (c : list N) : N -> N -> Prop :=
| greedy_nil : greedy_uses c 0 0
| greedy_step : forall x d g,
    0 < x -> largest_le c x d ->
    greedy_uses c (x - d) g -> greedy_uses c x (g + 1).

(* A counterexample: a positive integer x such that the minimum number of
   coins required to dispense exactly x is less than the number of coins
   used by the greedy algorithm. *)
Definition counterexample (c : list N) (x : N) : Prop :=
  0 < x /\ exists m g, min_coins c x m /\ greedy_uses c x g /\ m < g.

(* The statement's input guarantees. *)
Record valid_input (c : list N) : Prop := {
  (* 2 <= n <= 100, the number of denominations *)
  vi_n : 2 <= len c <= 100;
  (* c_1 = 1 *)
  vi_first : coin c 0 = 1;
  (* c_1 < c_2 < ... < c_n *)
  vi_increasing : forall k, k + 1 < len c -> coin c k < coin c (k + 1);
  (* c_n <= 10^6 (each denomination, the largest being c_n) *)
  vi_max : Forall (fun d => d <= 10 ^ 6) c;
}.

(* "canonical" (true) exactly when S has no counterexample, i.e. the greedy
   algorithm is always optimal; "non-canonical" (false) otherwise. *)
Definition canonical_spec (c : list N) (b : bool) : Prop :=
  b = true <-> forall x, ~ counterexample c x.

Program canonical : array uint -> bool.

Specification canonical_correct : forall (c : list N) (x : array uint),
  valid_input c -> repr x c ->
  exists b : bool, repr (canonical x) b /\ canonical_spec c b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
