(* Executable implementation and its required termination dependencies.
   Correctness proofs are in knapsack_proofs.v. *)
(* Implementation of knapsack (knapsack.spec): the textbook 0/1 knapsack
   dynamic program with a rolling value row and one flat decision table.

   Code.  [knapsack C values weights] (n items, C1 = C + 1):
   - [row] : array int of C1 cells, initially 0 ; [dec] : array bool of
     n * C1 cells, initially false ;
   - for i = 0 .. n-1 ([items_loop]), for c = C down to w_i ([item_loop],
     driven by k = c + 1 while w_i < k): if row[c - w_i] + v_i > row[c]
     then row[c] := row[c - w_i] + v_i and dec[i * C1 + c] := true.  The
     descending scan keeps row[c - w_i] at its value for the first i items;
   - the answer value is row[C] ;
   - [walk] goes back from (i, c) = (n, C): for i = n-1 down to 0, when
     dec[i * C1 + c] holds, i is written at the next free cell of an
     [array int] of n cells and c -= w_i ; the k cells written are then
     copied into an array of exactly k cells ([copy_loop]).
   All arrays are threaded linearly; everything is Uint63 [int].

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof (the shape of template/polymul1).

   Proof.  The math side ([Math] section) defines the DP [best i c] (best
   value with the first i items and capacity c), the decision [take i c]
   and the reconstruction [recon i c]; [recon] is a selection that fits,
   its value is [best], and [best] is optimal ([best_opt], by removing the
   last item from any selection).  The machine side ([Proofs] section)
   proves one invariant lemma per loop. *)

From Knapsack.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
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

Lemma down_step : forall w k : int,
  (w <? k) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros w k H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded w).
  assert (H1 : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Item (v, w), row base [base] of the decision table: capacities
   c = k-1, k-2, ..., w (descending). *)
Fixpoint item_loop (v w base k : int) (row : array int) (dec : array bool)
    (H : Acc (Zwf 0) (φ k)) {struct H} : array int * array bool :=
  match bdec (w <? k) with
  | left Hk =>
      let c := k - 1 in
      let cand := row.[c - w] + v in
      if row.[c] <? cand
      then item_loop v w base c row.[c <- cand] dec.[base + c <- true]
             (Acc_inv H (down_step w k Hk))
      else item_loop v w base c row dec (Acc_inv H (down_step w k Hk))
  | right _ => (row, dec)
  end.

(* Items i, i+1, ..., n-1. *)
Fixpoint items_loop (xv xw : array int) (n C1 i : int) (row : array int)
    (dec : array bool) (H : Acc (Zwf 0) (gap n i)) {struct H}
    : array int * array bool :=
  match bdec (i <? n) with
  | left Hi =>
      let rd := item_loop xv.[i] xw.[i] (i * C1) C1 row dec
                  (Zwf_well_founded 0 (φ C1)) in
      items_loop xv xw n C1 (i + 1) (fst rd) (snd rd)
        (Acc_inv H (dec_step n i Hi))
  | right _ => (row, dec)
  end.

(* The walk back: items i-1, ..., 0 at remaining capacity c; k cells of
   out are written. *)
Fixpoint walk (xw : array int) (dec : array bool) (C1 i c k : int)
    (out : array int) (H : Acc (Zwf 0) (φ i)) {struct H} : int * array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let j := i - 1 in
      if dec.[j * C1 + c]
      then walk xw dec C1 j (c - xw.[j]) (k + 1) out.[k <- j]
             (Acc_inv H (down_step 0 i Hi))
      else walk xw dec C1 j c k out (Acc_inv H (down_step 0 i Hi))
  | right _ => (k, out)
  end.

(* dst[j .. m-1] := src[j .. m-1]. *)
Fixpoint copy_loop (src dst : array int) (m j : int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int :=
  match bdec (j <? m) with
  | left Hj => copy_loop src dst.[j <- src.[j]] m (j + 1)
                 (Acc_inv H (dec_step m j Hj))
  | right _ => dst
  end.

Definition knapsack_impl (Cw : int) (xv xw : array int) : int * array int :=
  let n := PArray.length xv in
  let C1 := Cw + 1 in
  let rd := items_loop xv xw n C1 0 (PArray.make C1 0)
              (PArray.make (n * C1) false) (Zwf_well_founded 0 (gap n 0)) in
  let bestv := (fst rd).[Cw] in
  let ko := walk xw (snd rd) C1 n Cw 0 (PArray.make n 0)
              (Zwf_well_founded 0 (φ n)) in
  let k := fst ko in
  (bestv, copy_loop (snd ko) (PArray.make k 0) k 0
            (Zwf_well_founded 0 (gap k 0))).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition knapsack : uint -> array uint -> array uint -> uint * array uint
  := knapsack_impl.
