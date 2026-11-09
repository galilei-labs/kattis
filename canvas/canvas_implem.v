(* Executable implementation and its required termination dependencies.
   Correctness proofs are in canvas_proofs.v. *)
(* Implementation of canvas (canvas.spec): Huffman's greedy algorithm on
   a binary min-heap kept in one flat array (heapify, then pop the lightest
   group a, replace the next lightest b by a + b, add a + b to the total).
   Part A: trees and Huffman's exchange lemma; Part B: runs of the painting
   machine <-> trees over the canvasses; Part C: the program and its heap
   proofs.  Termination by erased Acc on Z measures; no nat, no Z in the
   extracted code. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  Permutation Bool.
Import ListNotations.

Unset Lia Cache.

(* ================================================================== *)
(* Part A.  Binary trees over leaf labels, their cost, Huffman's      *)
(* exchange lemma.                                                     *)
(* ================================================================== *)

Open Scope N_scope.

Close Scope N_scope.

(* ================================================================== *)
(* Part C.  The program: Huffman's greedy algorithm on a binary        *)
(* min-heap kept in one flat array.                                    *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition meas (i : int) : Z := (wB - (φ i))%Z.

Lemma dec_meas : forall b i m, (b && (i <? m)) = true -> Zwf 0 (meas m) (meas i).
Proof.
  intros b i m H. apply andb_prop in H. destruct H as [_ H].
  rewrite ltb_spec in H. pose proof (to_Z_bounded m). pose proof (to_Z_bounded i).
  unfold Zwf, meas. lia.
Qed.

Lemma dec_pred : forall j k, (j <? k) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros j k H. rewrite ltb_spec in H. pose proof (to_Z_bounded j).
  assert ((φ (k - 1)) = (φ k) - 1)%Z by sia. unfold Zwf. lia.
Qed.

(* Sift the value at i down the heap h.[0 .. sz-1]. *)
Fixpoint sift (h : array int) (sz i : int) (H : Acc (Zwf 0) (meas i)) {struct H}
    : array int :=
  let x := h.[i] in
  let l := 2 * i + 1 in
  if l <? sz then
    let yl := h.[l] in
    let r := l + 1 in
    if (r <? sz) && (h.[r] <? yl) then
      let yr := h.[r] in
      match bdec ((yr <? x) && (i <? r)) with
      | left Hd => sift (h.[i <- yr].[r <- x]) sz r (Acc_inv H (dec_meas _ i r Hd))
      | right _ => h
      end
    else
      match bdec ((yl <? x) && (i <? l)) with
      | left Hd => sift (h.[i <- yl].[l <- x]) sz l (Acc_inv H (dec_meas _ i l Hd))
      | right _ => h
      end
  else h.

(* Heapify: sift k-1, k-2, ..., 0. *)
Fixpoint build (h : array int) (sz k : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : array int :=
  match bdec (0 <? k) with
  | left Hk => build (sift h sz (k - 1) (Zwf_well_founded 0 (meas (k - 1)))) sz (k - 1)
                 (Acc_inv H (dec_pred 0 k Hk))
  | right _ => h
  end.

(* The greedy loop: pop the lightest group a, replace the next lightest b
   by a + b, add a + b to the total. *)
Fixpoint huff (h : array int) (sz acc : int) (H : Acc (Zwf 0) (φ sz)) {struct H} : int :=
  match bdec (1 <? sz) with
  | left Hs =>
      let a := h.[0] in
      let sz1 := sz - 1 in
      let h1 := sift (h.[0 <- h.[sz1]]) sz1 0 (Zwf_well_founded 0 (meas 0)) in
      let b := h1.[0] in
      let h2 := sift (h1.[0 <- a + b]) sz1 0 (Zwf_well_founded 0 (meas 0)) in
      huff h2 sz1 (acc + (a + b)) (Acc_inv H (dec_pred 1 sz Hs))
  | right _ => acc
  end.

Definition canvas_impl (x : array uint) : uint :=
  let sz := PArray.length x in
  let h := build (PArray.copy x) sz (sz / 2) (Zwf_well_founded 0 (φ (sz / 2))) in
  huff h sz 0 (Zwf_well_founded 0 (φ sz)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition canvas : array uint -> uint := canvas_impl.
