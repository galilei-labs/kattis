(* @function        yatp
   @signature       array uint -> array uint -> array uint -> array uint -> uint
   @math_signature  list N -> list N -> list N -> list N -> N
   @summary         [yatp p eu ev ew] takes a tree on the nodes 1..n (n the
                    length of p, node v of penalty the v-th entry of p) whose
                    k-th edge joins eu_k and ev_k with weight ew_k.  The cost
                    of a simple path is the sum of its edge weights plus the
                    product of the penalties of its two endpoints (the square
                    of the penalty for the path of 0 edges); the result is
                    the sum, over every node u, of the smallest cost of a
                    simple path starting at u.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The edge list of the input, n - 1 lines "i j w", is given as
   three parallel lists, one per column; nodes are numbered 1..n as in the
   statement. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, counting from 0. *)
Definition get (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* The penalty of node v (1 <= v <= n). *)
Definition penalty (p : list N) (v : N) : N := get p (v - 1).

(* Edge k exists and joins a and b, in either orientation. *)
Definition joins (eu ev : list N) (k a b : N) : Prop :=
  k < len eu /\
  ((get eu k = a /\ get ev k = b) \/ (get eu k = b /\ get ev k = a)).

(* [walk eu ev vs ks]: the nodes vs, in order, are linked one to the next
   by the edges ks. *)
Inductive walk (eu ev : list N) : list N -> list N -> Prop :=
| walk_one : forall a, walk eu ev [a] []
| walk_step : forall a b k vs ks,
    joins eu ev k a b -> walk eu ev (b :: vs) ks ->
    walk eu ev (a :: b :: vs) (k :: ks).

(* A simple path from u to v: a walk from u to v with no repeated node. *)
Definition simple_path (eu ev : list N) (u v : N) (vs ks : list N) : Prop :=
  walk eu ev vs ks /\ hd_error vs = Some u /\ last vs u = v /\ NoDup vs.

(* The cost of the path from u to v along the edges ks. *)
Definition cost (p ew : list N) (u v : N) (ks : list N) : N :=
  fold_right (fun k acc => get ew k + acc) 0 ks
  + penalty p u * penalty p v.

(* c is the smallest cost of a simple path starting at u. *)
Definition min_cost (p eu ev ew : list N) (u c : N) : Prop :=
  (exists v vs ks, simple_path eu ev u v vs ks /\ cost p ew u v ks = c) /\
  (forall v vs ks, simple_path eu ev u v vs ks -> c <= cost p ew u v ks).

(* f 1 + f 2 + ... + f n. *)
Fixpoint sum_nodes (f : N -> N) (n : nat) : N :=
  match n with
  | O => 0
  | S m => sum_nodes f m + f (N.of_nat n)
  end.

Record valid_input (p eu ev ew : list N) : Prop := {
  (* 1 <= n <= 200 000, the number of nodes; n penalties *)
  vi_n : 1 <= len p <= 200000;
  (* 1 <= p <= 1 000 000, the penalty of each node *)
  vi_p : Forall (fun x => 1 <= x <= 1000000) p;
  (* n - 1 lines, each "i j w" *)
  vi_m : len eu = len p - 1;
  vi_ev : len ev = len eu;
  vi_ew : len ew = len eu;
  (* 1 <= i <= n, 1 <= j <= n *)
  vi_i : Forall (fun i => 1 <= i <= len p) eu;
  vi_j : Forall (fun j => 1 <= j <= len p) ev;
  (* i <> j *)
  vi_ij : forall k, k < len eu -> get eu k <> get ev k;
  (* 1 <= w <= 1 000 000 *)
  vi_w : Forall (fun w => 1 <= w <= 1000000) ew;
  (* "You are given a tree": n - 1 edges joining every two nodes *)
  vi_tree : forall a b, 1 <= a <= len p -> 1 <= b <= len p ->
    exists vs ks, walk eu ev vs ks /\ hd_error vs = Some a /\ last vs a = b;
}.

(* The answer: the sum over the nodes u of the smallest cost of a simple
   path starting at u. *)
Definition yatp_spec (p eu ev ew : list N) (s : N) : Prop :=
  exists f : N -> N,
    (forall u, 1 <= u <= len p -> min_cost p eu ev ew u (f u)) /\
    s = sum_nodes f (List.length p).

Program yatp : array uint -> array uint -> array uint -> array uint -> uint.

Specification yatp_correct :
  forall (p eu ev ew : list N) (xp xu xv xw : array uint),
  valid_input p eu ev ew ->
  repr xp p -> repr xu eu -> repr xv ev -> repr xw ew ->
  exists s : N, repr (yatp xp xu xv xw) s /\ yatp_spec p eu ev ew s.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
