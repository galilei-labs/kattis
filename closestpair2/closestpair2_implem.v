(* Executable implementation and its required termination dependencies.
   Correctness proofs are in closestpair2_proofs.v. *)
(* Implementation of closestpair2 (closestpair2.spec): the divide and
   conquer closest pair (CLRS 33.4) on exact integer hundredths.

   Code.  [msort] sorts the indices 0 .. n-1 by x (top-down merge sort,
   two ping-pong arrays).  [solve lo hi tgt oth] returns the closest pair
   of the points P[lo, hi) and leaves them sorted by y in tgt[lo, hi): it
   solves both halves into oth, merges them by y into tgt, keeps the
   better half result as best, filters the points within best of the
   dividing line (squared x gap) into oth[lo, hi) in y order, and scans
   each strip point against its successors while their squared y gap is
   below the current best.  A leaf is one point, with the sentinel INF.
   All arithmetic is exact on 63-bit ints: coordinates are at most 10^7
   hundredths, so every squared distance is below 2^50.

   Termination: erased [Acc (Zwf 0)] on a Z gap, as in polymul1.

   Proof: see README.md, "Implementation". *)

From Closestpair2.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith QArith Qabs List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation.
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

(* the split test and the middle of [lo, hi) *)
Definition splits (lo hi : int) : bool := (lo <? hi) && (1 <? hi - lo).
Definition midp (lo hi : int) : int := lo + (hi - lo) / 2.

Lemma splits_spec : forall lo hi, splits lo hi = true ->
  ((φ lo) < (φ hi) /\ 2 <= (φ hi) - (φ lo)
   /\ (φ (midp lo hi)) = (φ lo) + ((φ hi) - (φ lo)) / 2)%Z.
Proof.
  intros lo hi H. unfold splits in H. apply andb_prop in H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold midp.
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. split; [lia|]. split; [change (φ 1) with 1%Z in H2; lia|].
  pose proof (to_Z_bounded hi).
  rewrite add_spec, div_spec, E. change (φ 2) with 2%Z.
  apply Z.mod_small. split; [pose proof (to_Z_bounded lo); apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]|].
  pose proof (Z.div_le_upper_bound ((φ hi) - (φ lo)) 2 ((φ hi) - (φ lo)) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma dec_left : forall lo hi, splits lo hi = true ->
  Zwf 0 (gap (midp lo hi) lo) (gap hi lo).
Proof.
  intros lo hi H. destruct (splits_spec lo hi H) as (A & B & C).
  unfold Zwf, gap. rewrite C.
  pose proof (Z.div_pos ((φ hi) - (φ lo)) 2 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt ((φ hi) - (φ lo)) 2 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma dec_right : forall lo hi, splits lo hi = true ->
  Zwf 0 (gap hi (midp lo hi)) (gap hi lo).
Proof.
  intros lo hi H. destruct (splits_spec lo hi H) as (A & B & C).
  unfold Zwf, gap. rewrite C.
  pose proof (Z.div_le_lower_bound ((φ hi) - (φ lo)) 2 1 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt ((φ hi) - (φ lo)) 2 ltac:(lia) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Merge of src[lo, mid) and src[mid, hi), both sorted by key, into
   dst[lo, hi); i, j, k are the read and write positions. *)
Fixpoint merge_loop (key : array sint) (src : array int) (mid hi i j k : int)
    (dst : array int) (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if i <? mid then
        if hi <=? j then
          merge_loop key src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
            (Acc_inv H (dec_step hi k Hk))
        else if Sint63.leb key.[src.[i]] key.[src.[j]] then
          merge_loop key src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
            (Acc_inv H (dec_step hi k Hk))
        else
          merge_loop key src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
            (Acc_inv H (dec_step hi k Hk))
      else
        merge_loop key src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
          (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

Definition merge (key : array sint) (src : array int) (lo mid hi : int)
    (dst : array int) : array int :=
  merge_loop key src mid hi lo mid lo dst (Zwf_well_founded 0 (gap hi lo)).

(* Merge sort of the indices lo .. hi-1 by xs into tgt[lo, hi), with oth
   as the ping-pong buffer: the halves are sorted into oth, then merged
   into tgt.  Returns (tgt, oth). *)
Fixpoint msort (xs : array sint) (lo hi : int) (tgt oth : array int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int * array int :=
  match bdec (splits lo hi) with
  | left Hs =>
      let mid := midp lo hi in
      let '(o1, t1) := msort xs lo mid oth tgt (Acc_inv H (dec_left lo hi Hs)) in
      let '(o2, t2) := msort xs mid hi o1 t1 (Acc_inv H (dec_right lo hi Hs)) in
      (merge xs o2 lo mid hi t2, o2)
  | right _ => (tgt.[lo <- lo], oth)
  end.

(* A result: two point indices and their squared distance. *)
Definition res : Type := (int * int) * int.
Definition bd (r : res) : int := snd r.

(* no squared distance reaches it *)
Definition INF : int := 4611686018427387904.

(* the squared distance of points a and b, in hundredths squared *)
Definition d2 (xs ys : array sint) (a b : int) : int :=
  let dx := xs.[a] - xs.[b] in
  let dy := ys.[a] - ys.[b] in
  dx * dx + dy * dy.

(* the strip test: point v is within the best distance of the line *)
Definition near (xs : array sint) (xm b v : int) : bool :=
  let dx := xs.[v] - xm in dx * dx <? b.

(* Copy the points of t[k, hi) that pass [near] to o[c, ...), in order. *)
Fixpoint strip_loop (xs : array sint) (xm b : int) (t : array int) (hi k c : int)
    (o : array int) (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int * int :=
  match bdec (k <? hi) with
  | left Hk =>
      let v := t.[k] in
      if near xs xm b v then
        strip_loop xs xm b t hi (k + 1) (c + 1) o.[c <- v] (Acc_inv H (dec_step hi k Hk))
      else
        strip_loop xs xm b t hi (k + 1) c o (Acc_inv H (dec_step hi k Hk))
  | right _ => (o, c)
  end.

(* Compare strip point s with its successors t, s < t < e, while their
   y gap is below the best distance. *)
Fixpoint inner_loop (xs ys : array sint) (T : array int) (e s t : int) (r : res)
    (H : Acc (Zwf 0) (gap e t)) {struct H} : res :=
  match bdec (t <? e) with
  | left Ht =>
      let a := T.[s] in
      let b := T.[t] in
      let dy := ys.[b] - ys.[a] in
      if dy * dy <? bd r then
        let d := d2 xs ys a b in
        inner_loop xs ys T e s (t + 1) (if d <? bd r then ((a, b), d) else r)
          (Acc_inv H (dec_step e t Ht))
      else r
  | right _ => r
  end.

Fixpoint outer_loop (xs ys : array sint) (T : array int) (e s : int) (r : res)
    (H : Acc (Zwf 0) (gap e s)) {struct H} : res :=
  match bdec (s <? e) with
  | left Hs =>
      outer_loop xs ys T e (s + 1)
        (inner_loop xs ys T e s (s + 1) r (Zwf_well_founded 0 (gap e (s + 1))))
        (Acc_inv H (dec_step e s Hs))
  | right _ => r
  end.

(* The closest pair among the points P[lo, hi) (P sorted by x), which
   also leaves them sorted by y in tgt[lo, hi); oth is the ping-pong
   buffer, and its segment [lo, hi) holds the strip after the merge.
   Returns ((tgt, oth), best). *)
Fixpoint solve (xs ys : array sint) (P : array int) (lo hi : int)
    (tgt oth : array int) (H : Acc (Zwf 0) (gap hi lo)) {struct H}
    : (array int * array int) * res :=
  match bdec (splits lo hi) with
  | left Hs =>
      let mid := midp lo hi in
      let '((o1, t1), r1) := solve xs ys P lo mid oth tgt (Acc_inv H (dec_left lo hi Hs)) in
      let '((o2, t2), r2) := solve xs ys P mid hi o1 t1 (Acc_inv H (dec_right lo hi Hs)) in
      let t3 := merge ys o2 lo mid hi t2 in
      let r0 := if bd r2 <? bd r1 then r2 else r1 in
      let '(o3, e) := strip_loop xs xs.[P.[mid]] (bd r0) t3 hi lo lo o2
                        (Zwf_well_founded 0 (gap hi lo)) in
      ((t3, o3), outer_loop xs ys o3 e lo r0 (Zwf_well_founded 0 (gap e lo)))
  | right _ => ((tgt.[lo <- P.[lo]], oth), ((0, 0), INF))
  end.

Definition closestpair_impl (xs ys : array sint) : uint * uint :=
  let n := PArray.length xs in
  let '(P, A) := msort xs 0 n (PArray.make n 0) (PArray.make n 0)
                   (Zwf_well_founded 0 (gap n 0)) in
  let '(_, r) := solve xs ys P 0 n A (PArray.make n 0)
                   (Zwf_well_founded 0 (gap n 0)) in
  fst r.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition closestpair : array sint -> array sint -> uint * uint := closestpair_impl.
