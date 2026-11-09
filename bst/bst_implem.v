(* Executable implementation and its required termination dependencies.
   Correctness proofs are in bst_proofs.v. *)
(* Implementation of bst (bst.spec): the depth counter of an unbalanced
   binary search tree, computed online with a red-black tree.

   Code.  The keys inserted so far are held in a red-black tree (an
   inductive tree, insertion in the Okasaki style, [lbal]/[rbal] on the
   side of the descent).  For the new key y, one descent [around] finds its
   predecessor p and successor s in the set, with the sentinels 0 (no
   predecessor) and N+1 (no successor).  The flat table [d], indexed by
   key (size N+2), holds depth+1 of every inserted key and 0 elsewhere
   (the sentinels included), so the new key's depth+1 is
   1 + max d.[p] d.[s]: in the statement's tree the new key hangs below
   whichever of p and s is deeper (theorem [key_depth]).  The counter is a
   uint; the answers go into one array threaded linearly.

   Termination: the red-black functions recurse structurally on the tree;
   the main loop on an erased [Acc (Zwf 0) (gap n j)] proof, the
   template's device.  No nat, no Z in the code. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Inductive color : Type := Red | Black.

Inductive rbt : Type :=
| RE : rbt
| RN : color -> rbt -> int -> rbt -> rbt.

(* Okasaki's balance, the red-red violation being on the left. *)
Definition lbal (l : rbt) (k : int) (r : rbt) : rbt :=
  match l with
  | RN Red (RN Red a x b) y c => RN Red (RN Black a x b) y (RN Black c k r)
  | RN Red a x (RN Red b y c) => RN Red (RN Black a x b) y (RN Black c k r)
  | _ => RN Black l k r
  end.

(* The same, the violation being on the right. *)
Definition rbal (l : rbt) (k : int) (r : rbt) : rbt :=
  match r with
  | RN Red (RN Red b y c) z d => RN Red (RN Black l k b) y (RN Black c z d)
  | RN Red b y (RN Red c z d) => RN Red (RN Black l k b) y (RN Black c z d)
  | _ => RN Black l k r
  end.

Fixpoint rb_ins (y : int) (t : rbt) : rbt :=
  match t with
  | RE => RN Red RE y RE
  | RN c l k r =>
      if y <? k then
        match c with
        | Red => RN Red (rb_ins y l) k r
        | Black => lbal (rb_ins y l) k r
        end
      else if k <? y then
        match c with
        | Red => RN Red l k (rb_ins y r)
        | Black => rbal l k (rb_ins y r)
        end
      else t
  end.

Definition make_black (t : rbt) : rbt :=
  match t with
  | RE => RE
  | RN _ l k r => RN Black l k r
  end.

Definition rb_insert (y : int) (t : rbt) : rbt := make_black (rb_ins y t).

(* The predecessor and the successor of y among the keys of t, p and s
   being returned when t has none below / above y on the search path. *)
Fixpoint around (y : int) (t : rbt) (p s : int) : int * int :=
  match t with
  | RE => (p, s)
  | RN _ l k r => if y <? k then around y l p k else around y r k s
  end.

Definition imax (u v : int) : int := if u <? v then v else u.

(* Insertions j, j+1, ..., n-1. *)
Fixpoint loop (x : array uint) (n j : int) (t : rbt) (d : array int)
    (c : int) (o : array int) (H : Acc (Zwf 0) (gap n j)) {struct H}
    : array int :=
  match bdec (j <? n) with
  | left Hj =>
      let y := x.[j] in
      let ps := around y t 0 (n + 1) in
      let e := 1 + imax d.[fst ps] d.[snd ps] in
      let c' := c + e - 1 in
      loop x n (j + 1) (rb_insert y t) d.[y <- e] c' o.[j <- c']
        (Acc_inv H (dec_step n j Hj))
  | right _ => o
  end.

Definition bst_impl (x : array uint) : array uint :=
  let n := PArray.length x in
  loop x n 0 RE (PArray.make (n + 2) 0) 0 (PArray.make n 0)
    (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: the statement's tree                                     *)
(* ------------------------------------------------------------------ *)

Local Open Scope N_scope.

Local Close Scope N_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bst : array uint -> array uint := bst_impl.
