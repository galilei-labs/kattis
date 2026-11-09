(* Executable implementation and its required termination dependencies.
   Correctness proofs are in longincsubseq_proofs.v. *)
(* Implementation of longincsubseq (longincsubseq.spec): patience sorting
   with a binary search, O(n log n).

   Code.  [lis x] makes one left-to-right pass over x maintaining
   - [tails], a flat array of n positions whose first L cells hold, for each
     length m = 1 .. L, the position of the smallest last value of an
     increasing subsequence of length m of the prefix read so far (their
     values strictly increase);
   - [pred], a flat array of n positions: pred.[i] is the position preceding
     i in the subsequence built when i was read.
   For x.[i] a lower-bound binary search (signed comparisons, [Sint63.ltb])
   finds the least k <= L with x.[tails.[k]] >= x.[i]; then
   pred.[i] := tails.[k-1] (k > 0), tails.[k] := i, and L grows when k = L.
   The answer is rebuilt in O(L) by following [pred] from tails.[L-1],
   filling the result array from its last cell down to cell 0.  All three
   arrays are threaded linearly; x is only read.  No Z, no nat, no list.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap _ _)] proof, as in template/polymul1.

   Proof.  The pass invariant [Inv] says: the tails are below i and their
   values strictly increase; a ghost height function h (existentially
   quantified) gives each read position j a height h j with, when h j > 0,
   pred.[j] < j, h pred.[j] = h j - 1, x.[pred.[j]] < x.[j], and the
   height of tails.[k] is k; and every increasing subsequence of the prefix
   (the inductive [reach a j m]: one of length m ending at position j) has
   m <= L and x.[tails.[m-1]] <= x.[j].  The last clause gives optimality,
   the height clause makes the pred chain from tails.[L-1] an increasing
   subsequence of length L. *)

From Longincsubseq.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
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

Lemma mid_spec : forall lo hi mid : int,
  mid = lo + (hi - lo) / 2 -> (lo <? hi) = true ->
  ((φ lo) <= (φ mid) < (φ hi))%Z.
Proof. intros lo hi mid -> H. rewrite ltb_spec in H. sia. Qed.

Lemma dec_lo : forall lo hi mid : int,
  mid = lo + (hi - lo) / 2 -> (lo <? hi) = true ->
  Zwf 0 (gap hi (mid + 1)) (gap hi lo).
Proof.
  intros lo hi mid Hm H. pose proof (mid_spec lo hi mid Hm H) as M.
  assert (H1 : (φ (mid + 1)) = ((φ mid) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_hi : forall lo hi mid : int,
  mid = lo + (hi - lo) / 2 -> (lo <? hi) = true ->
  Zwf 0 (gap mid lo) (gap hi lo).
Proof.
  intros lo hi mid Hm H. pose proof (mid_spec lo hi mid Hm H) as M.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall c : int,
  (0 <? c) = true -> Zwf 0 (gap (c - 1) 0) (gap c 0).
Proof.
  intros c H. rewrite ltb_spec in H.
  assert (H1 : (φ (c - 1)) = ((φ c) - 1)%Z) by sia.
  unfold Zwf, gap. change (φ 0) with 0%Z in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The least k in [lo, hi] with x.[tails.[k]] >= v (signed), assuming the
   values x.[tails.[_]] increase. *)
Fixpoint bsearch (x : array sint) (tails : array int) (v lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : int :=
  match bdec (lo <? hi) with
  | left Hlt =>
      let mid := lo + (hi - lo) / 2 in
      match bdec (Sint63.ltb x.[tails.[mid]] v) with
      | left _ =>
          bsearch x tails v (mid + 1) hi
            (Acc_inv H (dec_lo lo hi mid eq_refl Hlt))
      | right _ =>
          bsearch x tails v lo mid
            (Acc_inv H (dec_hi lo hi mid eq_refl Hlt))
      end
  | right _ => lo
  end.

(* The pass over positions i, i+1, ..., n-1; returns (L, (tails, pred)). *)
Fixpoint main_loop (x : array sint) (n i L : int) (tails pred : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int * (array int * array int) :=
  match bdec (i <? n) with
  | left Hi =>
      let v := x.[i] in
      let k := bsearch x tails v 0 L (Zwf_well_founded 0 (gap L 0)) in
      let p := if k =? 0 then 0 else tails.[k - 1] in
      let pred' := pred.[i <- p] in
      let tails' := tails.[k <- i] in
      main_loop x n (i + 1) (if k =? L then L + 1 else L) tails' pred'
        (Acc_inv H (dec_step n i Hi))
  | right _ => (L, (tails, pred))
  end.

(* Cells c-1, c-2, ..., 0 of res receive j, pred.[j], pred.[pred.[j]], ... *)
Fixpoint build (pred : array int) (c j : int) (res : array int)
    (H : Acc (Zwf 0) (gap c 0)) {struct H} : array int :=
  match bdec (0 <? c) with
  | left Hc =>
      build pred (c - 1) pred.[j] res.[c - 1 <- j]
        (Acc_inv H (dec_down c Hc))
  | right _ => res
  end.

Definition lis_impl (x : array sint) : array uint :=
  let n := PArray.length x in
  match main_loop x n 0 0 (PArray.make n 0) (PArray.make n 0)
          (Zwf_well_founded 0 (gap n 0)) with
  | (L, (tails, pred)) =>
      build pred L tails.[L - 1] (PArray.make L 0)
        (Zwf_well_founded 0 (gap L 0))
  end.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition lis : array sint -> array uint := lis_impl.
