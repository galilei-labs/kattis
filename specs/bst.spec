(* @function        bst
   @signature       array uint -> array uint
   @math_signature  list N -> list N
   @summary         The numbers of a, a permutation of 1..N, are inserted in
                    order into an initially empty (unbalanced) binary search
                    tree, the first one becoming the root, at depth 0.
                    [bst a] has length N and its cell k is the counter C after
                    the (k+1)-th insertion: the sum of the depths at which
                    a_0, ..., a_k were placed.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The j-th element of l (0-based); 0 beyond the end. *)
Definition get (l : list N) (j : N) : N := nth (N.to_nat j) l 0.

(* A binary tree with a number written inside each node. *)
Inductive tree : Type :=
| Leaf : tree
| Node : tree -> N -> tree -> tree.

(* Inserting y: traverse the tree as if searching for y, and put y as a new
   leaf, left of Z if y < Z, right of Z if Z < y, where the search cannot
   continue. *)
Fixpoint insert (y : N) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf y Leaf
  | Node l z r =>
      if y <? z then Node (insert y l) z r
      else if z <? y then Node l z (insert y r)
      else t
  end.

(* The depth of the node holding y: the number of edges from the root down
   to it along the search path of y. *)
Fixpoint depth (y : N) (t : tree) : N :=
  match t with
  | Leaf => 0
  | Node l z r =>
      if y <? z then N.succ (depth y l)
      else if z <? y then N.succ (depth y r)
      else 0
  end.

(* The tree built from the sequence l: the first number at the root, every
   other number inserted in order. *)
Definition tree_of (l : list N) : tree :=
  fold_left (fun t y => insert y t) l Leaf.

(* The depth of a_j in the tree right after its insertion. *)
Definition placed_depth (a : list N) (j : N) : N :=
  depth (get a j) (tree_of (firstn (N.to_nat j + 1) a)).

(* The counter C after the first k insertions: the sum of the depths of
   a_0, ..., a_(k-1); C is 0 before any insertion. *)
Fixpoint counter (a : list N) (k : nat) : N :=
  match k with
  | O => 0
  | S j => counter a j + placed_depth a (N.of_nat j)
  end.

(* The statement's bounds. *)
Record valid_input (a : list N) : Prop := {
  (* 1 <= N <= 300 000, N the length of the sequence *)
  vi_n : 1 <= len a <= 300000;
  (* the numbers of the sequence are integers in the interval [1, N] *)
  vi_range : Forall (fun x => 1 <= x <= len a) a;
  (* the numbers will be distinct *)
  vi_distinct : NoDup a;
}.

(* One counter per insertion: cell k is C after a_k has been inserted. *)
Definition bst_spec (a c : list N) : Prop :=
  len c = len a /\
  forall k, k < len c -> get c k = counter a (N.to_nat k + 1).

(* machine side : the only thing that gets extracted *)
Program bst : array uint -> array uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification bst_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists c : list N, repr (bst x) c /\ bst_spec a c.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
