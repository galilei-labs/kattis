(* Correctness proofs for closestpair2_implem.v. *)
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

From Closestpair2 Require Export closestpair2_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma of_Z_to_Z : forall k : Z, (0 <= k < wB)%Z -> (φ (of_Z k)) = k.
Proof. intros k Hk. rewrite of_Z_spec. apply Z.mod_small. exact Hk. Qed.

Lemma succ_to_Z : forall i m : int, ((φ i) < (φ m))%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof. intros i m H. pose proof (to_Z_bounded m). sia. Qed.

(* ------------------------------------------------------------------ *)
(* Segments of an array (or of any function on positions) as lists     *)
(* ------------------------------------------------------------------ *)

Fixpoint seg (f : int -> int) (lo : Z) (n : nat) : list int :=
  match n with
  | O => []
  | S n' => f (of_Z lo) :: seg f (lo + 1) n'
  end.

Definition segZ (f : int -> int) (lo hi : Z) : list int := seg f lo (Z.to_nat (hi - lo)).

Lemma seg_length : forall f n lo, List.length (seg f lo n) = n.
Proof. intros f n. induction n as [|n IH]; intros lo; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma seg_app : forall f n m lo,
  seg f lo (n + m) = seg f lo n ++ seg f (lo + Z.of_nat n) m.
Proof.
  intros f n. induction n as [|n IH]; intros m lo; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. do 2 f_equal. f_equal. rewrite Zpos_P_of_succ_nat. lia.
Qed.

Lemma segZ_app : forall f lo mid hi, (lo <= mid <= hi)%Z ->
  segZ f lo hi = segZ f lo mid ++ segZ f mid hi.
Proof.
  intros f lo mid hi H. unfold segZ.
  replace (Z.to_nat (hi - lo)) with (Z.to_nat (mid - lo) + Z.to_nat (hi - mid))%nat by lia.
  rewrite seg_app. do 2 f_equal. lia.
Qed.

Lemma segZ_nil : forall f lo hi, (hi <= lo)%Z -> segZ f lo hi = [].
Proof. intros f lo hi H. unfold segZ. replace (Z.to_nat (hi - lo)) with O by lia. reflexivity. Qed.

Lemma segZ_snoc : forall f lo hi, (lo <= hi)%Z ->
  segZ f lo (hi + 1) = segZ f lo hi ++ [f (of_Z hi)].
Proof.
  intros f lo hi H. rewrite (segZ_app f lo hi (hi + 1)) by lia. f_equal.
  unfold segZ. replace (Z.to_nat (hi + 1 - hi)) with 1%nat by lia. reflexivity.
Qed.

Lemma seg_ext : forall f g n lo,
  (forall k, (lo <= k < lo + Z.of_nat n)%Z -> f (of_Z k) = g (of_Z k)) ->
  seg f lo n = seg g lo n.
Proof.
  intros f g n. induction n as [|n IH]; intros lo H; simpl; [reflexivity|].
  rewrite H by lia. f_equal. apply IH. intros k Hk. apply H. lia.
Qed.

Lemma segZ_ext : forall f g lo hi,
  (forall k, (lo <= k < hi)%Z -> f (of_Z k) = g (of_Z k)) ->
  segZ f lo hi = segZ g lo hi.
Proof. intros f g lo hi H. unfold segZ. apply seg_ext. intros k Hk. apply H. lia. Qed.

Lemma seg_In : forall f n lo v,
  In v (seg f lo n) <-> exists k, (lo <= k < lo + Z.of_nat n)%Z /\ f (of_Z k) = v.
Proof.
  intros f n. induction n as [|n IH]; intros lo v; simpl.
  - split; [intros []| intros (k & Hk & _); lia].
  - rewrite IH. split.
    + intros [E | (k & Hk & E)]; [exists lo; split; [lia|exact E]|].
      exists k. split; [lia|exact E].
    + intros (k & Hk & E). destruct (Z.eq_dec k lo) as [->|D]; [left; exact E|].
      right. exists k. split; [lia|exact E].
Qed.

Lemma segZ_In : forall f lo hi v,
  In v (segZ f lo hi) <-> exists k, (lo <= k < hi)%Z /\ f (of_Z k) = v.
Proof.
  intros f lo hi v. unfold segZ. rewrite seg_In. split; intros (k & Hk & E); exists k;
    (split; [lia|exact E]).
Qed.

Lemma seg_nth : forall f n lo c, (c < n)%nat ->
  nth_error (seg f lo n) c = Some (f (of_Z (lo + Z.of_nat c))).
Proof.
  intros f n. induction n as [|n IH]; intros lo c Hc; [lia|].
  destruct c as [|c]; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. do 3 f_equal. lia.
Qed.

(* distinct positions of a duplicate-free segment hold distinct values *)
Lemma segZ_NoDup_inj : forall f lo hi, NoDup (segZ f lo hi) ->
  forall k1 k2, (lo <= k1 < hi)%Z -> (lo <= k2 < hi)%Z ->
  f (of_Z k1) = f (of_Z k2) -> k1 = k2.
Proof.
  intros f lo hi H k1 k2 H1 H2 E. unfold segZ in H.
  rewrite NoDup_nth_error in H. rewrite seg_length in H.
  assert (A : Z.to_nat (k1 - lo) = Z.to_nat (k2 - lo)).
  { apply H; [lia|]. rewrite !seg_nth by lia.
    replace (lo + Z.of_nat (Z.to_nat (k1 - lo)))%Z with k1 by lia.
    replace (lo + Z.of_nat (Z.to_nat (k2 - lo)))%Z with k2 by lia.
    rewrite E. reflexivity. }
  lia.
Qed.

(* the segment of positions [lo, hi) of an array; positions are below wB *)
Lemma get_of_Z : forall (a : array int) (p : int), PArray.get a (of_Z (φ p)) = a.[p].
Proof. intros a p. rewrite of_to_Z. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Sortedness of a segment of indices by a coordinate array            *)
(* ------------------------------------------------------------------ *)

Definition KZ (key : array sint) (v : int) : Z := Sint63.to_Z key.[v].

Definition sorted_seg (key : array sint) (a : array int) (lo hi : Z) : Prop :=
  forall p q : int, (lo <= (φ p))%Z -> ((φ p) <= (φ q))%Z -> ((φ q) < hi)%Z ->
  (KZ key a.[p] <= KZ key a.[q])%Z.

Definition below (key : array sint) (a : array int) (lo hi : Z) (v : Z) : Prop :=
  forall p : int, (lo <= (φ p) < hi)%Z -> (KZ key a.[p] <= v)%Z.

Lemma set_other_Z : forall (a : array int) (k x p : int),
  (φ p) <> (φ k) -> a.[k <- x].[p] = a.[p].
Proof. intros a k x p H. apply aget_set_other. intro E. apply H. rewrite E. reflexivity. Qed.

Lemma set_same_Z : forall (a : array int) (k x p : int),
  (φ p) = (φ k) -> ((φ k) < (φ (PArray.length a)))%Z -> a.[k <- x].[p] = x.
Proof.
  intros a k x p H L. replace p with k by (apply to_Z_inj; lia).
  apply aget_set_same. rewrite ltb_spec. exact L.
Qed.

Lemma snoc_set : forall (a : array int) (k x : int) (lo : Z),
  (0 <= lo <= (φ k))%Z -> ((φ k) < (φ (PArray.length a)))%Z ->
  segZ (PArray.get a.[k <- x]) lo ((φ k) + 1) = segZ (PArray.get a) lo (φ k) ++ [x].
Proof.
  intros a k x lo H L. rewrite segZ_snoc by lia. f_equal.
  - apply segZ_ext. intros j Hj. apply set_other_Z.
    rewrite of_Z_to_Z by (pose proof (to_Z_bounded k); lia). lia.
  - rewrite of_to_Z. f_equal. apply aget_set_same. rewrite ltb_spec. exact L.
Qed.

Lemma sorted_snoc : forall key (a : array int) (k x : int) (lo : Z),
  ((φ k) < (φ (PArray.length a)))%Z ->
  sorted_seg key a lo (φ k) -> below key a lo (φ k) (KZ key x) ->
  sorted_seg key a.[k <- x] lo ((φ k) + 1).
Proof.
  intros key a k x lo L S B p q H1 H2 H3.
  destruct (Z.eq_dec (φ q) (φ k)) as [Eq | Nq].
  - rewrite (set_same_Z a k x q Eq L).
    destruct (Z.eq_dec (φ p) (φ k)) as [Ep | Np].
    + rewrite (set_same_Z a k x p Ep L). lia.
    + rewrite set_other_Z by exact Np. apply B. lia.
  - rewrite (set_other_Z a k x q Nq), (set_other_Z a k x p) by lia. apply S; lia.
Qed.

Lemma below_snoc : forall key (a : array int) (k x : int) (lo v : Z),
  ((φ k) < (φ (PArray.length a)))%Z ->
  below key a lo (φ k) v -> (KZ key x <= v)%Z ->
  below key a.[k <- x] lo ((φ k) + 1) v.
Proof.
  intros key a k x lo v L B Hx p Hp.
  destruct (Z.eq_dec (φ p) (φ k)) as [Ep | Np].
  - rewrite (set_same_Z a k x p Ep L). exact Hx.
  - rewrite set_other_Z by exact Np. apply B. lia.
Qed.

Lemma below_mono : forall key a lo hi v w, below key a lo hi v -> (v <= w)%Z -> below key a lo hi w.
Proof. intros key a lo hi v w B H p Hp. specialize (B p Hp). lia. Qed.

(* ------------------------------------------------------------------ *)
(* Merge                                                               *)
(* ------------------------------------------------------------------ *)

Lemma merge_loop_eq : forall key src mid hi i j k dst H,
  merge_loop key src mid hi i j k dst H =
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
Proof. intros. destruct H. reflexivity. Qed.

Definition merge_post (key : array sint) (src : array int) (lo : Z) (mid hi : int)
    (k : Z) (dst d' : array int) : Prop :=
  PArray.length d' = PArray.length dst /\
  (forall p : int, ((φ p) < k \/ (φ hi) <= (φ p))%Z -> d'.[p] = dst.[p]) /\
  Permutation (segZ (PArray.get d') lo (φ hi))
    (segZ (PArray.get src) lo (φ mid) ++ segZ (PArray.get src) (φ mid) (φ hi)) /\
  sorted_seg key d' lo (φ hi).

Lemma merge_loop_spec : forall key (src : array int) (mid hi : int) (lo : Z),
  (0 <= lo)%Z ->
  sorted_seg key src lo (φ mid) -> sorted_seg key src (φ mid) (φ hi) ->
  forall z i j k dst H, gap hi k = z ->
  (lo <= (φ i) <= (φ mid))%Z -> ((φ mid) <= (φ j) <= (φ hi))%Z ->
  ((φ k) - lo = ((φ i) - lo) + ((φ j) - (φ mid)))%Z ->
  ((φ hi) <= (φ (PArray.length dst)))%Z ->
  Permutation (segZ (PArray.get dst) lo (φ k))
    (segZ (PArray.get src) lo (φ i) ++ segZ (PArray.get src) (φ mid) (φ j)) ->
  sorted_seg key dst lo (φ k) ->
  (((φ i) < (φ mid))%Z -> below key dst lo (φ k) (KZ key src.[i])) ->
  (((φ j) < (φ hi))%Z -> below key dst lo (φ k) (KZ key src.[j])) ->
  merge_post key src lo mid hi (φ k) dst (merge_loop key src mid hi i j k dst H).
Proof.
  intros key src mid hi lo Hlo SL SR z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j k dst H Hz Hi Hj Hk Hlen Hp Hs Hbi Hbj.
  rewrite merge_loop_eq.
  destruct (bdec (k <? hi)) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    assert (K1 : (φ (k + 1)) = ((φ k) + 1)%Z) by (apply (succ_to_Z k hi); lia).
    assert (Lk : ((φ k) < (φ (PArray.length dst)))%Z) by lia.
    (* taking src[i] *)
    assert (Ti : ((φ i) < (φ mid))%Z ->
                 (((φ j) < (φ hi))%Z -> (KZ key src.[i] <= KZ key src.[j])%Z) ->
                 forall H',
                 merge_post key src lo mid hi (φ k) dst
                   (merge_loop key src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]] H')).
    { intros Him Hij H'.
      assert (I1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply (succ_to_Z i mid); lia).
      edestruct (IH (gap hi (k + 1))) with (i := i + 1) (j := j) (k := k + 1)
        (dst := dst.[k <- src.[i]]) (H := H') as (L & F & Pm & S);
        [ rewrite <- Hz; apply dec_step; exact Hkh | reflexivity | lia | lia | lia
        | rewrite alength_set; lia | | | | | ].
      - rewrite K1, snoc_set by lia. rewrite I1, segZ_snoc by lia. rewrite of_to_Z.
        rewrite <- app_assoc.
        apply Permutation_trans with
          ((segZ (PArray.get src) lo (φ i) ++ segZ (PArray.get src) (φ mid) (φ j)) ++ [src.[i]]);
          [apply Permutation_app_tail; exact Hp|].
        rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
      - rewrite K1. apply sorted_snoc; [exact Lk | exact Hs | apply Hbi; exact Him].
      - intros Hi1. rewrite K1, I1 in *.
        assert (Ord : (KZ key src.[i] <= KZ key src.[i + 1])%Z) by (apply SL; lia).
        apply below_snoc; [exact Lk | | exact Ord].
        apply below_mono with (KZ key src.[i]); [apply Hbi; exact Him | exact Ord].
      - intros Hj1. rewrite K1. apply below_snoc; [exact Lk | apply Hbj; exact Hj1 | apply Hij; exact Hj1].
      - split; [rewrite L; apply alength_set|]. split; [|split; assumption].
        intros p Hpp. rewrite F by lia. apply set_other_Z. lia. }
    (* taking src[j] *)
    assert (Tj : ((φ j) < (φ hi))%Z ->
                 (((φ i) < (φ mid))%Z -> (KZ key src.[j] <= KZ key src.[i])%Z) ->
                 forall H',
                 merge_post key src lo mid hi (φ k) dst
                   (merge_loop key src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]] H')).
    { intros Hjh Hji H'.
      assert (J1 : (φ (j + 1)) = ((φ j) + 1)%Z) by (apply (succ_to_Z j hi); lia).
      edestruct (IH (gap hi (k + 1))) with (i := i) (j := j + 1) (k := k + 1)
        (dst := dst.[k <- src.[j]]) (H := H') as (L & F & Pm & S);
        [ rewrite <- Hz; apply dec_step; exact Hkh | reflexivity | lia | lia | lia
        | rewrite alength_set; lia | | | | | ].
      - rewrite K1, snoc_set by lia. rewrite J1, segZ_snoc by lia. rewrite of_to_Z.
        rewrite app_assoc. apply Permutation_app_tail. exact Hp.
      - rewrite K1. apply sorted_snoc; [exact Lk | exact Hs | apply Hbj; exact Hjh].
      - intros Hi1. rewrite K1. apply below_snoc; [exact Lk | apply Hbi; exact Hi1 | apply Hji; exact Hi1].
      - intros Hj1. rewrite K1, J1 in *.
        assert (Ord : (KZ key src.[j] <= KZ key src.[j + 1])%Z) by (apply SR; lia).
        apply below_snoc; [exact Lk | | exact Ord].
        apply below_mono with (KZ key src.[j]); [apply Hbj; exact Hjh | exact Ord].
      - split; [rewrite L; apply alength_set|]. split; [|split; assumption].
        intros p Hpp. rewrite F by lia. apply set_other_Z. lia. }
    destruct (i <? mid) eqn:Eim.
    + rewrite ltb_spec in Eim.
      destruct (hi <=? j) eqn:Ehj.
      * rewrite leb_spec in Ehj. apply Ti; [exact Eim | intro; lia].
      * rewrite <- Bool.not_true_iff_false, leb_spec in Ehj.
        destruct (Sint63.leb key.[src.[i]] key.[src.[j]]) eqn:El.
        -- apply Ti; [exact Eim|]. intros _. unfold KZ.
           destruct (Sint63.lebP key.[src.[i]] key.[src.[j]]); [assumption | discriminate].
        -- apply Tj; [lia|]. intros _. unfold KZ.
           destruct (Sint63.lebP key.[src.[i]] key.[src.[j]]); [discriminate | lia].
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Eim.
      apply Tj; [lia | intro; lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkh.
    assert (Ei : (φ i) = (φ mid)) by lia. assert (Ej : (φ j) = (φ hi)) by lia.
    assert (Ek : (φ k) = (φ hi)) by lia.
    split; [reflexivity|]. split; [reflexivity|].
    rewrite Ek, Ei, Ej in Hp. rewrite Ek in Hs. split; assumption.
Qed.

Lemma merge_spec : forall key (src : array int) (lo mid hi : int) (dst : array int),
  ((φ lo) <= (φ mid) <= (φ hi))%Z -> ((φ hi) <= (φ (PArray.length dst)))%Z ->
  sorted_seg key src (φ lo) (φ mid) -> sorted_seg key src (φ mid) (φ hi) ->
  merge_post key src (φ lo) mid hi (φ lo) dst (merge key src lo mid hi dst).
Proof.
  intros key src lo mid hi dst H L SL SR. unfold merge.
  pose proof (to_Z_bounded lo).
  apply merge_loop_spec with (z := gap hi lo); try assumption; try lia; try reflexivity.
  - rewrite !segZ_nil by lia. constructor.
  - intros p q; lia.
  - intros _ p; lia.
  - intros _ p; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Frames                                                              *)
(* ------------------------------------------------------------------ *)

Lemma segZ_frame : forall (a b : array int) (lo hi : Z),
  (0 <= lo)%Z -> (hi <= 4194303)%Z ->
  (forall p : int, (lo <= (φ p) < hi)%Z -> a.[p] = b.[p]) ->
  segZ (PArray.get a) lo hi = segZ (PArray.get b) lo hi.
Proof.
  intros a b lo hi H1 H2 H. apply segZ_ext. intros k Hk. apply H.
  rewrite of_Z_to_Z by (rewrite wB_val; lia). exact Hk.
Qed.

Lemma sorted_frame : forall key (a b : array int) (lo hi : Z),
  (forall p : int, (lo <= (φ p) < hi)%Z -> a.[p] = b.[p]) ->
  sorted_seg key a lo hi -> sorted_seg key b lo hi.
Proof.
  intros key a b lo hi F S p q H1 H2 H3. rewrite <- !F by lia. apply S; lia.
Qed.

Lemma splits_false : forall lo hi, ((φ lo) < (φ hi))%Z -> splits lo hi = false ->
  (φ hi) = ((φ lo) + 1)%Z.
Proof.
  intros lo hi H E. unfold splits in E.
  replace (lo <? hi) with true in E by (symmetry; rewrite ltb_spec; exact H).
  simpl in E. rewrite <- Bool.not_true_iff_false, ltb_spec in E.
  assert ((φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia. change (φ 1) with 1%Z in E. lia.
Qed.

Lemma single_sorted : forall key (a : array int) (lo : Z), sorted_seg key a lo (lo + 1).
Proof.
  intros key a lo p q H1 H2 H3. replace q with p by (apply to_Z_inj; lia). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The merge sort by x                                                 *)
(* ------------------------------------------------------------------ *)

Lemma msort_eq : forall xs lo hi tgt oth H,
  msort xs lo hi tgt oth H =
  match bdec (splits lo hi) with
  | left Hs =>
      let mid := midp lo hi in
      let '(o1, t1) := msort xs lo mid oth tgt (Acc_inv H (dec_left lo hi Hs)) in
      let '(o2, t2) := msort xs mid hi o1 t1 (Acc_inv H (dec_right lo hi Hs)) in
      (merge xs o2 lo mid hi t2, o2)
  | right _ => (tgt.[lo <- lo], oth)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition frame2 (lo hi : int) (t o t' o' : array int) : Prop :=
  PArray.length t' = PArray.length t /\ PArray.length o' = PArray.length o /\
  (forall p : int, ((φ p) < (φ lo) \/ (φ hi) <= (φ p))%Z -> t'.[p] = t.[p] /\ o'.[p] = o.[p]).

Definition msort_post (xs : array sint) (lo hi : int) (tgt oth : array int)
    (r : array int * array int) : Prop :=
  frame2 lo hi tgt oth (fst r) (snd r) /\
  Permutation (segZ (PArray.get (fst r)) (φ lo) (φ hi)) (segZ (fun v => v) (φ lo) (φ hi)) /\
  sorted_seg xs (fst r) (φ lo) (φ hi).

Lemma msort_spec : forall xs z lo hi tgt oth H, gap hi lo = z ->
  ((φ lo) < (φ hi))%Z -> ((φ hi) <= (φ (PArray.length tgt)))%Z -> ((φ hi) <= (φ (PArray.length oth)))%Z ->
  msort_post xs lo hi tgt oth (msort xs lo hi tgt oth H).
Proof.
  intros xs z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi tgt oth H Hz Hlh Lt Lo.
  pose proof (alength_bound tgt) as Bt. pose proof (to_Z_bounded lo) as Blo.
  rewrite msort_eq. destruct (bdec (splits lo hi)) as [Hs | Hs].
  - destruct (splits_spec lo hi Hs) as (_ & H2 & Hm).
    cbv beta zeta.
    assert (Bm : ((φ lo) < (φ (midp lo hi)) < (φ hi))%Z).
    { rewrite Hm. pose proof (Z.div_le_lower_bound ((φ hi) - (φ lo)) 2 1 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt ((φ hi) - (φ lo)) 2 ltac:(lia) ltac:(lia)). lia. }
    pose proof (IH (gap (midp lo hi) lo) ltac:(rewrite <- Hz; apply dec_left; exact Hs)
                  lo (midp lo hi) oth tgt (Acc_inv H (dec_left lo hi Hs)) eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia)) as R1.
    destruct (msort xs lo (midp lo hi) oth tgt (Acc_inv H (dec_left lo hi Hs))) as [o1 t1].
    destruct R1 as ((L1o & L1t & F1) & P1 & S1). cbn [fst snd] in L1o, L1t, F1, P1, S1.
    pose proof (IH (gap hi (midp lo hi)) ltac:(rewrite <- Hz; apply dec_right; exact Hs)
                  (midp lo hi) hi o1 t1 (Acc_inv H (dec_right lo hi Hs)) eq_refl
                  ltac:(lia) ltac:(rewrite L1o; lia) ltac:(rewrite L1t; lia)) as R2.
    destruct (msort xs (midp lo hi) hi o1 t1 (Acc_inv H (dec_right lo hi Hs))) as [o2 t2].
    set (mid := midp lo hi) in *.
    destruct R2 as ((L2o & L2t & F2) & P2 & S2). cbn [fst snd] in L2o, L2t, F2, P2, S2.
    assert (E21 : forall p : int, ((φ lo) <= (φ p) < (φ mid))%Z -> o2.[p] = o1.[p])
      by (intros p Hp; apply (F2 p); lia).
    destruct (merge_spec xs o2 lo mid hi t2 ltac:(lia) ltac:(rewrite L2t, L1t; lia)
                (sorted_frame xs o1 o2 _ _ (fun p Hp => eq_sym (E21 p Hp)) S1) S2)
      as (L3 & F3 & P3 & S3).
    split; [|split]; cbn [fst snd].
    + split; [|split].
      * rewrite L3, L2t, L1t. reflexivity.
      * rewrite L2o, L1o. reflexivity.
      * intros p Hp. split.
        -- rewrite F3 by lia. rewrite (proj2 (F2 p ltac:(lia))). apply (F1 p). lia.
        -- rewrite (proj1 (F2 p ltac:(lia))). apply (F1 p). lia.
    + eapply Permutation_trans; [exact P3|].
      rewrite (segZ_app (fun v => v) (φ lo) (φ mid) (φ hi)) by lia.
      apply Permutation_app; [|exact P2].
      rewrite (segZ_frame o2 o1) by (try lia; exact E21). exact P1.
    + exact S3.
  - pose proof (splits_false lo hi Hlh Hs) as E.
    assert (Llo : ((φ lo) < (φ (PArray.length tgt)))%Z) by lia.
    split; [|split]; cbn [fst snd].
    + split; [apply alength_set|]. split; [reflexivity|].
      intros p Hp. split; [|reflexivity]. apply set_other_Z. lia.
    + rewrite E, snoc_set by lia. rewrite segZ_nil by lia.
      rewrite segZ_snoc, segZ_nil by lia. rewrite of_to_Z. apply Permutation_refl.
    + rewrite E. apply single_sorted.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact arithmetic on the hundredths                                  *)
(* ------------------------------------------------------------------ *)

Lemma sint_mod : forall v : int, (Sint63.to_Z v mod wB)%Z = (φ v).
Proof. intros v. apply Sint63.to_Z_mod_Uint63to_Z. Qed.

Lemma sq_bound : forall u M : Z, (Z.abs u <= M)%Z -> (0 <= u * u <= M * M)%Z.
Proof.
  intros u M H. rewrite <- Z.abs_square. split; [apply Z.square_nonneg|].
  apply Z.mul_le_mono_nonneg; lia.
Qed.

(* the square of a difference of two coordinates, both at most 10^7 in
   absolute value, is computed exactly *)
Lemma sq_diff : forall a b : int,
  (Z.abs (Sint63.to_Z a) <= 10000000)%Z -> (Z.abs (Sint63.to_Z b) <= 10000000)%Z ->
  (φ ((a - b) * (a - b))) =
  ((Sint63.to_Z a - Sint63.to_Z b) * (Sint63.to_Z a - Sint63.to_Z b))%Z.
Proof.
  intros a b Ha Hb. rewrite mul_spec, sub_spec, <- (sint_mod a), <- (sint_mod b).
  rewrite <- Zminus_mod, <- Zmult_mod. apply Z.mod_small. rewrite wB_val.
  pose proof (sq_bound (Sint63.to_Z a - Sint63.to_Z b) 20000000 ltac:(lia)). lia.
Qed.

Section Geometry.

Variables xs ys : array sint.

Definition X (v : int) : Z := Sint63.to_Z xs.[v].
Definition Y (v : int) : Z := Sint63.to_Z ys.[v].

(* the squared distance of points a and b, exactly, in hundredths squared *)
Definition Dz (a b : int) : Z :=
  ((X a - X b) * (X a - X b) + (Y a - Y b) * (Y a - Y b))%Z.

Lemma Dz_sym : forall a b, Dz a b = Dz b a.
Proof. intros a b. unfold Dz. ring. Qed.

(* the coordinates of a point are at most 10^7 in absolute value *)
Definition bnd (v : int) : Prop :=
  (Z.abs (X v) <= 10000000)%Z /\ (Z.abs (Y v) <= 10000000)%Z.

Definition INFZ : Z := 4611686018427387904%Z.

Lemma INF_val : (φ INF) = INFZ.
Proof. reflexivity. Qed.

Lemma Dz_bound : forall a b, bnd a -> bnd b -> (0 <= Dz a b < INFZ)%Z.
Proof.
  intros a b [Ha Ha'] [Hb Hb']. unfold Dz, INFZ.
  pose proof (sq_bound (X a - X b) 20000000 ltac:(lia)).
  pose proof (sq_bound (Y a - Y b) 20000000 ltac:(lia)). lia.
Qed.

Lemma d2_spec : forall a b, bnd a -> bnd b -> (φ (d2 xs ys a b)) = Dz a b.
Proof.
  intros a b [Ha Ha'] [Hb Hb']. unfold d2, Dz, X, Y in *.
  rewrite add_spec, !sq_diff by assumption. apply Z.mod_small. rewrite wB_val.
  pose proof (sq_bound (Sint63.to_Z xs.[a] - Sint63.to_Z xs.[b]) 20000000 ltac:(lia)).
  pose proof (sq_bound (Sint63.to_Z ys.[a] - Sint63.to_Z ys.[b]) 20000000 ltac:(lia)). lia.
Qed.

Lemma near_spec : forall xm b v, bnd v -> (Z.abs (Sint63.to_Z xm) <= 10000000)%Z ->
  near xs xm b v = true <-> ((X v - Sint63.to_Z xm) * (X v - Sint63.to_Z xm) < (φ b))%Z.
Proof.
  intros xm b v [Hv _] Hm. unfold near, X in *. rewrite ltb_spec, sq_diff by assumption.
  reflexivity.
Qed.

Lemma dy_spec : forall a b, bnd a -> bnd b ->
  (φ ((ys.[b] - ys.[a]) * (ys.[b] - ys.[a]))) = ((Y b - Y a) * (Y b - Y a))%Z.
Proof. intros a b [_ Ha] [_ Hb]. unfold Y in *. rewrite sq_diff by assumption. reflexivity. Qed.

(* a result is INF, or the distance of two distinct points of L *)
Definition Valid (L : list int) (r : res) : Prop :=
  ((φ (bd r)) <= INFZ)%Z /\
  (((φ (bd r)) < INFZ)%Z ->
   In (fst (fst r)) L /\ In (snd (fst r)) L /\ fst (fst r) <> snd (fst r) /\
   (φ (bd r)) = Dz (fst (fst r)) (snd (fst r))).

(* ------------------------------------------------------------------ *)
(* The strip scan                                                      *)
(* ------------------------------------------------------------------ *)

Section Scan.

Variable L : list int.
Variable T : array int.
Variable lo : Z.
Variable e : int.
Hypothesis HT : forall p : int, (lo <= (φ p) < (φ e))%Z -> In T.[p] L /\ bnd T.[p].
Hypothesis Hinj : forall p q : int, (lo <= (φ p) < (φ e))%Z -> (lo <= (φ q) < (φ e))%Z ->
  T.[p] = T.[q] -> (φ p) = (φ q).
Hypothesis Hsort : sorted_seg ys T lo (φ e).

Lemma inner_loop_eq : forall s t r H,
  inner_loop xs ys T e s t r H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma inner_loop_spec : forall s z t r H, gap e t = z ->
  (lo <= (φ s))%Z -> ((φ s) < (φ t) <= (φ e))%Z ->
  Valid L r ->
  (forall q : int, ((φ s) < (φ q) < (φ t))%Z -> ((φ (bd r)) <= Dz T.[s] T.[q])%Z) ->
  let r' := inner_loop xs ys T e s t r H in
  Valid L r' /\ ((φ (bd r')) <= (φ (bd r)))%Z /\
  (forall q : int, ((φ s) < (φ q) < (φ e))%Z -> ((φ (bd r')) <= Dz T.[s] T.[q])%Z).
Proof.
  intros s z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t r H Hz Hs Ht Hv Hinv. rewrite inner_loop_eq.
  destruct (bdec (t <? e)) as [Hte | Hte].
  - pose proof Hte as Hte'. rewrite ltb_spec in Hte'.
    destruct (HT s ltac:(lia)) as [Ls Bs]. destruct (HT t ltac:(lia)) as [Lt Bt].
    cbv zeta.
    destruct ((ys.[T.[t]] - ys.[T.[s]]) * (ys.[T.[t]] - ys.[T.[s]]) <? bd r) eqn:Edy.
    + rewrite ltb_spec, (dy_spec _ _ Bs Bt) in Edy.
      assert (T1 : (φ (t + 1)) = ((φ t) + 1)%Z) by (apply (succ_to_Z t e); lia).
      set (r1 := if d2 xs ys T.[s] T.[t] <? bd r then ((T.[s], T.[t]), d2 xs ys T.[s] T.[t]) else r).
      assert (V1 : Valid L r1 /\ ((φ (bd r1)) <= (φ (bd r)))%Z /\
                   ((φ (bd r1)) <= Dz T.[s] T.[t])%Z).
      { unfold r1. destruct (d2 xs ys T.[s] T.[t] <? bd r) eqn:Ed.
        - apply ltb_spec in Ed. rewrite (d2_spec _ _ Bs Bt) in Ed.
          destruct Hv as [Hv1 _].
          unfold Valid, bd; cbn [fst snd]. rewrite (d2_spec _ _ Bs Bt).
          unfold bd in Ed, Hv1.
          split; [split; [lia|]|lia].
          intros _. split; [exact Ls|]. split; [exact Lt|]. split; [|reflexivity].
          intro E. apply Hinj in E; lia.
        - rewrite <- Bool.not_true_iff_false in Ed. rewrite ltb_spec in Ed.
          rewrite (d2_spec _ _ Bs Bt) in Ed.
          split; [exact Hv|]. lia. }
      destruct V1 as (V1 & M1 & D1).
      destruct (IH (gap e (t + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hte)
                  (t + 1) r1 (Acc_inv H (dec_step e t Hte)) eq_refl Hs ltac:(lia) V1)
        as (V2 & M2 & D2).
      { intros q Hq. destruct (Z.eq_dec (φ q) (φ t)) as [Eq | Nq].
        - replace q with t by (apply to_Z_inj; lia). exact D1.
        - specialize (Hinv q ltac:(lia)). lia. }
      split; [exact V2|]. split; [exact (Z.le_trans _ _ _ M2 M1) | exact D2].
    + rewrite <- Bool.not_true_iff_false, ltb_spec, (dy_spec _ _ Bs Bt) in Edy.
      split; [exact Hv|]. split; [lia|].
      intros q Hq. destruct (Z_lt_le_dec (φ q) (φ t)) as [Lq | Gq]; [apply Hinv; lia|].
      destruct (HT q ltac:(lia)) as [_ Bq].
      assert (O1 : (Y T.[s] <= Y T.[t])%Z) by (apply Hsort; lia).
      assert (O2 : (Y T.[t] <= Y T.[q])%Z) by (apply Hsort; lia).
      assert (Q1 : ((Y T.[t] - Y T.[s]) * (Y T.[t] - Y T.[s])
                    <= (Y T.[q] - Y T.[s]) * (Y T.[q] - Y T.[s]))%Z)
        by (apply Z.mul_le_mono_nonneg; lia).
      assert (Q2 : (0 <= (X T.[s] - X T.[q]) * (X T.[s] - X T.[q]))%Z)
        by apply Z.square_nonneg.
      assert (Q3 : ((Y T.[s] - Y T.[q]) * (Y T.[s] - Y T.[q])
                    = (Y T.[q] - Y T.[s]) * (Y T.[q] - Y T.[s]))%Z) by ring.
      unfold Dz. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hte.
    split; [exact Hv|]. split; [lia|]. intros q Hq. apply Hinv. lia.
Qed.

Lemma outer_loop_eq : forall s r H,
  outer_loop xs ys T e s r H =
  match bdec (s <? e) with
  | left Hs =>
      outer_loop xs ys T e (s + 1)
        (inner_loop xs ys T e s (s + 1) r (Zwf_well_founded 0 (gap e (s + 1))))
        (Acc_inv H (dec_step e s Hs))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma outer_loop_spec : forall z s r H, gap e s = z ->
  (lo <= (φ s) <= (φ e))%Z ->
  Valid L r ->
  (forall p q : int, (lo <= (φ p) < (φ s))%Z -> ((φ p) < (φ q) < (φ e))%Z ->
     ((φ (bd r)) <= Dz T.[p] T.[q])%Z) ->
  let r' := outer_loop xs ys T e s r H in
  Valid L r' /\ ((φ (bd r')) <= (φ (bd r)))%Z /\
  (forall p q : int, (lo <= (φ p))%Z -> ((φ p) < (φ q) < (φ e))%Z ->
     ((φ (bd r')) <= Dz T.[p] T.[q])%Z).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros s r H Hz Hs Hv Hinv. rewrite outer_loop_eq.
  destruct (bdec (s <? e)) as [Hse | Hse].
  - pose proof Hse as Hse'. rewrite ltb_spec in Hse'.
    assert (S1 : (φ (s + 1)) = ((φ s) + 1)%Z) by (apply (succ_to_Z s e); lia).
    destruct (inner_loop_spec s (gap e (s + 1)) (s + 1) r
                (Zwf_well_founded 0 (gap e (s + 1))) eq_refl ltac:(lia) ltac:(lia) Hv)
      as (V1 & M1 & D1).
    { intros q Hq. lia. }
    destruct (IH (gap e (s + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hse)
                (s + 1) _ (Acc_inv H (dec_step e s Hse)) eq_refl ltac:(lia) V1)
      as (V2 & M2 & D2).
    { intros p q Hp Hq. destruct (Z.eq_dec (φ p) (φ s)) as [Ep | Np].
      - replace p with s by (apply to_Z_inj; lia). apply D1. lia.
      - specialize (Hinv p q ltac:(lia) Hq). lia. }
    split; [exact V2|]. split; [lia | exact D2].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hse.
    split; [exact Hv|]. split; [lia|]. intros p q Hp Hq. apply Hinv; lia.
Qed.

End Scan.

End Geometry.

(* ------------------------------------------------------------------ *)
(* The strip                                                           *)
(* ------------------------------------------------------------------ *)

Lemma strip_loop_eq : forall xs xm b t hi k c o H,
  strip_loop xs xm b t hi k c o H =
  match bdec (k <? hi) with
  | left Hk =>
      let v := t.[k] in
      if near xs xm b v then
        strip_loop xs xm b t hi (k + 1) (c + 1) o.[c <- v] (Acc_inv H (dec_step hi k Hk))
      else
        strip_loop xs xm b t hi (k + 1) c o (Acc_inv H (dec_step hi k Hk))
  | right _ => (o, c)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sorted_sub : forall key a lo hi lo' hi', sorted_seg key a lo hi ->
  (lo <= lo')%Z -> (hi' <= hi)%Z -> sorted_seg key a lo' hi'.
Proof. intros key a lo hi lo' hi' S H1 H2 p q A B C. apply S; lia. Qed.

Lemma strip_loop_spec : forall (xs ys : array sint) (xm b : int) (t : array int) (hi : int) (lo : Z),
  (0 <= lo)%Z -> sorted_seg ys t lo (φ hi) -> ((φ hi) <= 4194303)%Z ->
  forall z k c o H, gap hi k = z ->
  (lo <= (φ c) <= (φ k))%Z -> ((φ k) <= (φ hi))%Z -> ((φ hi) <= (φ (PArray.length o)))%Z ->
  segZ (PArray.get o) lo (φ c) = filter (near xs xm b) (segZ (PArray.get t) lo (φ k)) ->
  sorted_seg ys o lo (φ c) ->
  (forall q : int, ((φ k) <= (φ q) < (φ hi))%Z -> below ys o lo (φ c) (KZ ys t.[q])) ->
  let R := strip_loop xs xm b t hi k c o H in
  PArray.length (fst R) = PArray.length o /\
  (forall p : int, ((φ p) < (φ c) \/ (φ hi) <= (φ p))%Z -> (fst R).[p] = o.[p]) /\
  ((φ c) <= (φ (snd R)) <= (φ hi))%Z /\
  segZ (PArray.get (fst R)) lo (φ (snd R)) = filter (near xs xm b) (segZ (PArray.get t) lo (φ hi)) /\
  sorted_seg ys (fst R) lo (φ (snd R)).
Proof.
  intros xs ys xm b t hi lo Hlo St Hh z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k c o H Hz Hc Hk Ho Hf Hs Hb. rewrite strip_loop_eq.
  destruct (bdec (k <? hi)) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    assert (K1 : (φ (k + 1)) = ((φ k) + 1)%Z) by (apply (succ_to_Z k hi); lia).
    assert (Ft : filter (near xs xm b) (segZ (PArray.get t) lo (φ (k + 1)))
                 = filter (near xs xm b) (segZ (PArray.get t) lo (φ k)) ++
                   (if near xs xm b t.[k] then [t.[k]] else [])).
    { rewrite K1, segZ_snoc by lia. rewrite filter_app, of_to_Z. reflexivity. }
    cbv zeta. destruct (near xs xm b t.[k]) eqn:En.
    + assert (C1 : (φ (c + 1)) = ((φ c) + 1)%Z) by (apply (succ_to_Z c hi); lia).
      assert (Lc : ((φ c) < (φ (PArray.length o)))%Z) by lia.
      destruct (IH (gap hi (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hkh)
                 (k + 1) (c + 1) o.[c <- t.[k]] (Acc_inv H (dec_step hi k Hkh)) eq_refl
                 ltac:(lia) ltac:(lia) ltac:(rewrite alength_set; lia))
        as (L & F & B & E & S).
      * rewrite Ft, C1, snoc_set by lia. rewrite Hf. reflexivity.
      * rewrite C1. apply sorted_snoc; [exact Lc | exact Hs | apply Hb; lia].
      * intros q Hq. rewrite C1. apply below_snoc; [exact Lc | apply Hb; lia |].
        apply St; lia.
      * split; [rewrite L; apply alength_set|]. split; [|split; [lia | split; assumption]].
        intros p Hp. rewrite F by lia. apply set_other_Z. lia.
    + destruct (IH (gap hi (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hkh)
                 (k + 1) c o (Acc_inv H (dec_step hi k Hkh)) eq_refl
                 ltac:(lia) ltac:(lia) Ho)
        as (L & F & B & E & S).
      * rewrite Ft, app_nil_r. exact Hf.
      * exact Hs.
      * intros q Hq. apply Hb. lia.
      * split; [exact L|]. split; [|split; [lia | split; assumption]].
        intros p Hp. apply F. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkh.
    cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|].
    split; [lia|]. replace (φ hi) with (φ k) by lia. split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The divide and conquer                                              *)
(* ------------------------------------------------------------------ *)

Lemma solve_eq : forall xs ys P lo hi tgt oth H,
  solve xs ys P lo hi tgt oth H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma Valid_incl : forall xs ys L1 L2 r, incl L1 L2 -> Valid xs ys L1 r -> Valid xs ys L2 r.
Proof.
  intros xs ys L1 L2 r I [V1 V2]. split; [exact V1|]. intros Hl.
  destruct (V2 Hl) as (A & B & C & D). split; [apply I; exact A|]. split; [apply I; exact B|].
  split; assumption.
Qed.

Definition solve_post (xs ys : array sint) (P : array int) (lo hi : int) (tgt oth : array int)
    (R : (array int * array int) * res) : Prop :=
  let S := segZ (PArray.get P) (φ lo) (φ hi) in
  frame2 lo hi tgt oth (fst (fst R)) (snd (fst R)) /\
  Permutation (segZ (PArray.get (fst (fst R))) (φ lo) (φ hi)) S /\
  sorted_seg ys (fst (fst R)) (φ lo) (φ hi) /\
  Valid xs ys S (snd R) /\
  (forall p q, In p S -> In q S -> p <> q -> ((φ (bd (snd R))) <= Dz xs ys p q)%Z).

Lemma solve_spec : forall xs ys P z lo hi tgt oth H, gap hi lo = z ->
  ((φ lo) < (φ hi))%Z -> ((φ hi) <= (φ (PArray.length tgt)))%Z ->
  ((φ hi) <= (φ (PArray.length oth)))%Z -> ((φ hi) <= (φ (PArray.length P)))%Z ->
  NoDup (segZ (PArray.get P) (φ lo) (φ hi)) ->
  (forall v, In v (segZ (PArray.get P) (φ lo) (φ hi)) -> bnd xs ys v) ->
  sorted_seg xs P (φ lo) (φ hi) ->
  solve_post xs ys P lo hi tgt oth (solve xs ys P lo hi tgt oth H).
Proof.
  intros xs ys P z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi tgt oth H Hz Hlh Lt Lo LP ND Bd SP.
  pose proof (alength_bound tgt) as Bt. pose proof (to_Z_bounded lo) as Blo.
  rewrite solve_eq. destruct (bdec (splits lo hi)) as [Hs | Hs].
  - destruct (splits_spec lo hi Hs) as (_ & H2 & Hm).
    cbv beta zeta.
    assert (Bm : ((φ lo) < (φ (midp lo hi)) < (φ hi))%Z).
    { rewrite Hm. pose proof (Z.div_le_lower_bound ((φ hi) - (φ lo)) 2 1 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_lt ((φ hi) - (φ lo)) 2 ltac:(lia) ltac:(lia)). lia. }
    assert (ES : segZ (PArray.get P) (φ lo) (φ hi) =
                 segZ (PArray.get P) (φ lo) (φ (midp lo hi)) ++
                 segZ (PArray.get P) (φ (midp lo hi)) (φ hi)) by (apply segZ_app; lia).
    rewrite ES in ND.
    pose proof (IH (gap (midp lo hi) lo) ltac:(rewrite <- Hz; apply dec_left; exact Hs)
                  lo (midp lo hi) oth tgt (Acc_inv H (dec_left lo hi Hs)) eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  (NoDup_app_remove_r _ _ ND)
                  ltac:(intros v Hv; apply Bd; rewrite ES; apply in_or_app; left; exact Hv)
                  ltac:(apply (sorted_sub _ _ _ _ _ _ SP); lia)) as R1.
    destruct (solve xs ys P lo (midp lo hi) oth tgt (Acc_inv H (dec_left lo hi Hs)))
      as [[o1 t1] r1].
    destruct R1 as ((L1o & L1t & F1) & P1 & S1 & V1 & M1).
    cbn [fst snd] in L1o, L1t, F1, P1, S1, V1, M1.
    pose proof (IH (gap hi (midp lo hi)) ltac:(rewrite <- Hz; apply dec_right; exact Hs)
                  (midp lo hi) hi o1 t1 (Acc_inv H (dec_right lo hi Hs)) eq_refl
                  ltac:(lia) ltac:(rewrite L1o; lia) ltac:(rewrite L1t; lia) ltac:(lia)
                  (NoDup_app_remove_l _ _ ND)
                  ltac:(intros v Hv; apply Bd; rewrite ES; apply in_or_app; right; exact Hv)
                  ltac:(apply (sorted_sub _ _ _ _ _ _ SP); lia)) as R2.
    destruct (solve xs ys P (midp lo hi) hi o1 t1 (Acc_inv H (dec_right lo hi Hs)))
      as [[o2 t2] r2].
    destruct R2 as ((L2o & L2t & F2) & P2 & S2 & V2 & M2).
    cbn [fst snd] in L2o, L2t, F2, P2, S2, V2, M2.
    set (mid := midp lo hi) in *.
    set (S := segZ (PArray.get P) (φ lo) (φ hi)) in *.
    set (SL := segZ (PArray.get P) (φ lo) (φ mid)) in *.
    set (SR := segZ (PArray.get P) (φ mid) (φ hi)) in *.
    assert (InL : forall v, In v SL -> In v S) by (intros v Hv; rewrite ES; apply in_or_app; left; exact Hv).
    assert (InR : forall v, In v SR -> In v S) by (intros v Hv; rewrite ES; apply in_or_app; right; exact Hv).
    assert (NDS : NoDup S) by (rewrite ES; exact ND).
    (* the merge *)
    assert (E21 : forall p : int, ((φ lo) <= (φ p) < (φ mid))%Z -> o2.[p] = o1.[p])
      by (intros p Hp; apply (F2 p); lia).
    destruct (merge_spec ys o2 lo mid hi t2 ltac:(lia) ltac:(rewrite L2t, L1t; lia)
                (sorted_frame ys o1 o2 _ _ (fun p Hp => eq_sym (E21 p Hp)) S1) S2)
      as (L3 & F3 & P3 & S3).
    set (t3 := merge ys o2 lo mid hi t2) in *.
    assert (Perm3 : Permutation (segZ (PArray.get t3) (φ lo) (φ hi)) S).
    { eapply Permutation_trans; [exact P3|]. rewrite ES.
      apply Permutation_app; [|exact P2].
      rewrite (segZ_frame o2 o1) by (try lia; exact E21). exact P1. }
    (* the best of the halves *)
    assert (R0 : Valid xs ys S (if (bd r2 <? bd r1)%uint63 then r2 else r1) /\
                 ((φ (bd (if (bd r2 <? bd r1)%uint63 then r2 else r1))) <= (φ (bd r1)))%Z /\
                 ((φ (bd (if (bd r2 <? bd r1)%uint63 then r2 else r1))) <= (φ (bd r2)))%Z).
    { destruct (bd r2 <? bd r1) eqn:E.
      - rewrite ltb_spec in E. split; [|lia]. apply (Valid_incl _ _ SR); [exact InR | exact V2].
      - rewrite <- Bool.not_true_iff_false, ltb_spec in E. split; [|lia].
        apply (Valid_incl _ _ SL); [exact InL | exact V1]. }
    set (r0 := if (bd r2 <? bd r1)%uint63 then r2 else r1) in *.
    destruct R0 as (V0 & M01 & M02).
    (* the dividing line *)
    assert (BPm : bnd xs ys P.[mid]).
    { apply Bd. apply segZ_In. exists (φ mid). split; [lia|]. apply get_of_Z. }
    (* the strip *)
    pose proof (strip_loop_spec xs ys xs.[P.[mid]] (bd r0) t3 hi (φ lo) ltac:(lia) S3
                  ltac:(lia) (gap hi lo) lo lo o2 (Zwf_well_founded 0 (gap hi lo)) eq_refl
                  ltac:(lia) ltac:(lia) ltac:(rewrite L2o, L1o; lia)
                  ltac:(rewrite !segZ_nil by lia; reflexivity)
                  ltac:(intros p q; lia) ltac:(intros q _ p; lia)) as R4.
    destruct (strip_loop xs xs.[P.[mid]] (bd r0) t3 hi lo lo o2 (Zwf_well_founded 0 (gap hi lo)))
      as [o3 e].
    destruct R4 as (L4 & F4 & Be & Fe & S4). cbn [fst snd] in L4, F4, Be, Fe, S4.
    assert (NDT : NoDup (segZ (PArray.get o3) (φ lo) (φ e))).
    { rewrite Fe. apply NoDup_filter. apply (Permutation_NoDup (Permutation_sym Perm3)). exact NDS. }
    assert (InT : forall v, In v (segZ (PArray.get o3) (φ lo) (φ e)) -> In v S).
    { intros v Hv. rewrite Fe, filter_In in Hv. apply (Permutation_in _ Perm3). apply Hv. }
    assert (HT : forall p : int, ((φ lo) <= (φ p) < (φ e))%Z -> In o3.[p] S /\ bnd xs ys o3.[p]).
    { intros p Hp. assert (I : In o3.[p] S).
      { apply InT. apply segZ_In. exists (φ p). split; [lia|]. apply get_of_Z. }
      split; [exact I | apply Bd; exact I]. }
    assert (Hinj : forall p q : int, ((φ lo) <= (φ p) < (φ e))%Z -> ((φ lo) <= (φ q) < (φ e))%Z ->
                     o3.[p] = o3.[q] -> (φ p) = (φ q)).
    { intros p q Hp Hq E. apply (segZ_NoDup_inj _ _ _ NDT); [lia | lia |].
      rewrite !get_of_Z. exact E. }
    destruct (outer_loop_spec xs ys S o3 (φ lo) e HT Hinj S4
                (gap e lo) lo r0 (Zwf_well_founded 0 (gap e lo)) eq_refl ltac:(lia) V0
                ltac:(intros p q Hp Hq; lia))
      as (V5 & M5 & D5).
    set (r := outer_loop xs ys o3 e lo r0 (Zwf_well_founded 0 (gap e lo))) in *.
    (* a pair across the dividing line *)
    assert (Cross : forall p q, In p SL -> In q SR -> p <> q ->
                      ((φ (bd r)) <= Dz xs ys p q)%Z).
    { intros p q Hp Hq Hpq.
      destruct (Z_le_gt_dec (φ (bd r0)) (Dz xs ys p q)) as [Le | Gt]; [lia|].
      pose proof Hp as Hp'. pose proof Hq as Hq'.
      apply segZ_In in Hp' as (a & Ha & Ea). apply segZ_In in Hq' as (b & Hb & Eb).
      assert (Xp : (X xs p <= X xs P.[mid])%Z).
      { rewrite <- Ea. apply (SP (of_Z a) mid); rewrite ?of_Z_to_Z by (rewrite wB_val; lia); lia. }
      assert (Xq : (X xs P.[mid] <= X xs q)%Z).
      { rewrite <- Eb. apply (SP mid (of_Z b)); rewrite ?of_Z_to_Z by (rewrite wB_val; lia); lia. }
      assert (Bp : bnd xs ys p) by (apply Bd; apply InL; exact Hp).
      assert (Bq : bnd xs ys q) by (apply Bd; apply InR; exact Hq).
      assert (Dq : ((X xs q - X xs p) * (X xs q - X xs p) <= Dz xs ys p q)%Z).
      { unfold Dz. pose proof (Z.square_nonneg (Y ys p - Y ys q)).
        replace ((X xs p - X xs q) * (X xs p - X xs q))%Z
          with ((X xs q - X xs p) * (X xs q - X xs p))%Z by ring. lia. }
      assert (Np : near xs xs.[P.[mid]] (bd r0) p = true).
      { apply (proj2 (near_spec xs ys xs.[P.[mid]] (bd r0) p Bp (proj1 BPm))).
        change (Sint63.to_Z xs.[P.[mid]]) with (X xs P.[mid]).
        assert (((X xs p - X xs P.[mid]) * (X xs p - X xs P.[mid])
                 <= (X xs q - X xs p) * (X xs q - X xs p))%Z).
        { replace ((X xs p - X xs P.[mid]) * (X xs p - X xs P.[mid]))%Z
            with ((X xs P.[mid] - X xs p) * (X xs P.[mid] - X xs p))%Z by ring.
          apply Z.mul_le_mono_nonneg; lia. }
        lia. }
      assert (Nq : near xs xs.[P.[mid]] (bd r0) q = true).
      { apply (proj2 (near_spec xs ys xs.[P.[mid]] (bd r0) q Bq (proj1 BPm))).
        change (Sint63.to_Z xs.[P.[mid]]) with (X xs P.[mid]).
        assert (((X xs q - X xs P.[mid]) * (X xs q - X xs P.[mid])
                 <= (X xs q - X xs p) * (X xs q - X xs p))%Z)
          by (apply Z.mul_le_mono_nonneg; lia).
        lia. }
      assert (Tp : In p (segZ (PArray.get o3) (φ lo) (φ e))).
      { rewrite Fe, filter_In. split; [|exact Np].
        apply (Permutation_in _ (Permutation_sym Perm3)). apply InL. exact Hp. }
      assert (Tq : In q (segZ (PArray.get o3) (φ lo) (φ e))).
      { rewrite Fe, filter_In. split; [|exact Nq].
        apply (Permutation_in _ (Permutation_sym Perm3)). apply InR. exact Hq. }
      apply segZ_In in Tp as (k1 & Hk1 & E1). apply segZ_In in Tq as (k2 & Hk2 & E2).
      assert (B1 : (φ (of_Z k1)) = k1) by (apply of_Z_to_Z; rewrite wB_val; lia).
      assert (B2 : (φ (of_Z k2)) = k2) by (apply of_Z_to_Z; rewrite wB_val; lia).
      destruct (Z.lt_trichotomy k1 k2) as [Lt12 | [Eq12 | Gt12]].
      - rewrite <- E1, <- E2. apply D5; lia.
      - exfalso. apply Hpq. rewrite <- E1, <- E2, Eq12. reflexivity.
      - rewrite Dz_sym, <- E1, <- E2. apply D5; lia. }
    split; [|split; [exact Perm3 | split; [exact S3 | split; [exact V5 |]]]]; cbn [fst snd].
    + split; [|split].
      * rewrite L3, L2t, L1t. reflexivity.
      * rewrite L4, L2o, L1o. reflexivity.
      * intros p Hp. split.
        -- rewrite F3 by lia. rewrite (proj2 (F2 p ltac:(lia))). apply (F1 p). lia.
        -- rewrite F4 by lia. rewrite (proj1 (F2 p ltac:(lia))). apply (F1 p). lia.
    + intros p q Hp Hq Hpq. change (In p S) in Hp. change (In q S) in Hq.
      rewrite ES in Hp, Hq. apply in_app_or in Hp, Hq.
      destruct Hp as [Hp | Hp], Hq as [Hq | Hq].
      * specialize (M1 p q Hp Hq Hpq). lia.
      * apply Cross; assumption.
      * rewrite Dz_sym. apply Cross; [assumption | assumption | intro E; apply Hpq; symmetry; exact E].
      * specialize (M2 p q Hp Hq Hpq). lia.
  - pose proof (splits_false lo hi Hlh Hs) as E.
    assert (Llo : ((φ lo) < (φ (PArray.length tgt)))%Z) by lia.
    assert (ES : segZ (PArray.get P) (φ lo) (φ hi) = [P.[lo]]).
    { rewrite E, segZ_snoc, segZ_nil by lia. rewrite of_to_Z. reflexivity. }
    unfold solve_post. rewrite ES. cbn [fst snd].
    split; [|split; [|split; [|split]]].
    + split; [apply alength_set|]. split; [reflexivity|].
      intros p Hp. split; [|reflexivity]. apply set_other_Z. lia.
    + rewrite E, snoc_set by lia. rewrite segZ_nil by lia. apply Permutation_refl.
    + rewrite E. apply single_sorted.
    + unfold Valid, bd. cbn [snd]. rewrite INF_val. split; [lia | intro; lia].
    + intros p q [<- | []] [<- | []] Hpq. exfalso. apply Hpq. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The identity segment                                                *)
(* ------------------------------------------------------------------ *)

Lemma segZ_id_In : forall (m : Z) (v : int), (0 <= m <= 4194303)%Z ->
  In v (segZ (fun v => v) 0 m) <-> ((φ v) < m)%Z.
Proof.
  intros m v Hm. rewrite segZ_In. split.
  - intros (k & Hk & E). rewrite <- E, of_Z_to_Z by (rewrite wB_val; lia). lia.
  - intros H. exists (φ v). pose proof (to_Z_bounded v). split; [lia|]. apply of_to_Z.
Qed.

Lemma seg_id_NoDup : forall n lo, (0 <= lo)%Z -> (lo + Z.of_nat n <= 4194303)%Z ->
  NoDup (seg (fun v => v) lo n).
Proof.
  intros n. induction n as [|n IH]; intros lo H1 H2; simpl; [constructor|].
  constructor; [|apply IH; lia].
  rewrite seg_In. intros (k & Hk & E).
  assert ((φ (of_Z k)) = (φ (of_Z lo))) by (rewrite E; reflexivity).
  rewrite !of_Z_to_Z in H by (rewrite wB_val; lia). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* From the machine to the math side                                   *)
(* ------------------------------------------------------------------ *)

Lemma repr_cell : forall (x : array sint) (l : list Q), repr x l ->
  forall k : nat, (k < List.length l)%nat ->
  (nth k l 0 == (Sint63.to_Z x.[of_Z (Z.of_nat k)] # 100))%Q.
Proof.
  intros x l [_ Hc] k Hk. destruct (Hc k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth l k 0%Q Hm). exact Hr.
Qed.

Lemma repr_len : forall (x : array sint) (l : list Q), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros x l [Hl _]. symmetry. exact Hl. Qed.

Lemma coord_bound : forall (c : Q) (z : Z), (c == z # 100)%Q -> (Qabs c <= 100000)%Q ->
  (Z.abs z <= 10000000)%Z.
Proof.
  intros c z E H. rewrite (Qabs_wd _ _ E) in H. simpl in H.
  unfold Qle in H. simpl in H. lia.
Qed.

Lemma Q_d2 : forall a b c d : Z,
  (((a # 100) - (b # 100)) * ((a # 100) - (b # 100)) +
   ((c # 100) - (d # 100)) * ((c # 100) - (d # 100))
   == ((a - b) * (a - b) + (c - d) * (c - d))%Z # 10000)%Q.
Proof. intros a b c d. unfold Qeq, Qplus, Qminus, Qmult, Qopp. simpl. ring. Qed.

Lemma Qle_hund : forall a b : Z, (a <= b)%Z -> (a # 10000 <= b # 10000)%Q.
Proof. intros a b H. unfold Qle. simpl. lia. Qed.

Lemma dist2_eq : forall (x y : array sint) (xq yq : list Q),
  repr x xq -> repr y yq -> List.length yq = List.length xq ->
  forall i j : N, (i < len xq)%N -> (j < len xq)%N ->
  (dist2 xq yq i j == Dz x y (of_Z (Z.of_N i)) (of_Z (Z.of_N j)) # 10000)%Q.
Proof.
  intros x y xq yq Hx Hy Hl i j Hi Hj. unfold len in Hi, Hj.
  unfold dist2, get_list_Q. cbv zeta.
  rewrite (repr_cell x xq Hx (N.to_nat i)) by lia.
  rewrite (repr_cell x xq Hx (N.to_nat j)) by lia.
  rewrite (repr_cell y yq Hy (N.to_nat i)) by lia.
  rewrite (repr_cell y yq Hy (N.to_nat j)) by lia.
  rewrite !N_nat_Z. unfold Dz, X, Y. apply Q_d2.
Qed.

Lemma make_length : forall n : int, ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n (0 : int)) = n.
Proof.
  intros n H. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma closestpair_impl_correct : forall (xq yq : list Q) (x y : array sint),
  valid_input xq yq -> repr x xq -> repr y yq ->
  exists r : N * N, repr (closestpair_impl x y) r /\ closestpair_spec xq yq r.
Proof.
  intros xq yq x y Hv Hx Hy.
  destruct Hv as [Hn Hlen _ _ Hxb Hyb]. unfold len in Hn, Hlen.
  pose proof (repr_len x xq Hx) as Lx.
  assert (Bnd : forall v : int, ((φ v) < Z.of_nat (List.length xq))%Z -> bnd x y v).
  { intros v Hv. pose proof (to_Z_bounded v) as Bv.
    assert (Ev : of_Z (Z.of_nat (Z.to_nat (φ v))) = v)
      by (rewrite Z2Nat.id by lia; apply of_to_Z).
    split.
    - pose proof (repr_cell x xq Hx (Z.to_nat (φ v)) ltac:(lia)) as C.
      rewrite Ev in C. unfold X.
      apply (coord_bound _ _ C). apply (proj1 (Forall_nth _ _) Hxb). lia.
    - pose proof (repr_cell y yq Hy (Z.to_nat (φ v)) ltac:(lia)) as C.
      rewrite Ev in C. unfold Y.
      apply (coord_bound _ _ C). apply (proj1 (Forall_nth _ _) Hyb). lia. }
  unfold closestpair_impl. cbv zeta.
  set (n := PArray.length x) in *.
  assert (Ln : PArray.length (PArray.make n (0 : int)) = n) by (apply make_length; lia).
  pose proof (msort_spec x (gap n 0) 0 n (PArray.make n 0) (PArray.make n 0)
                (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) ltac:(rewrite Ln; lia) ltac:(rewrite Ln; lia))
    as M.
  destruct (msort x 0 n (PArray.make n 0) (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)))
    as [P A].
  destruct M as ((LP & LA & _) & PP & SPs). cbn [fst snd] in LP, LA, PP, SPs.
  change (φ 0) with 0%Z in PP, SPs.
  set (S := segZ (PArray.get P) 0 (φ n)) in *.
  assert (InS : forall v, In v S <-> ((φ v) < Z.of_nat (List.length xq))%Z).
  { intros v. rewrite <- Lx, <- (segZ_id_In (φ n) v) by lia. split; intros I.
    - apply (Permutation_in _ PP). exact I.
    - apply (Permutation_in _ (Permutation_sym PP)). exact I. }
  assert (NDS : NoDup S).
  { apply (Permutation_NoDup (Permutation_sym PP)). unfold segZ.
    apply seg_id_NoDup; lia. }
  pose proof (solve_spec x y P (gap n 0) 0 n A (PArray.make n 0)
                (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) ltac:(rewrite LA, Ln; lia)
                ltac:(rewrite Ln; lia) ltac:(rewrite LP, Ln; lia)
                NDS ltac:(intros v Iv; apply Bnd; apply InS; exact Iv) SPs) as R.
  destruct (solve x y P 0 n A (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)))
    as [[t o] r].
  destruct R as (_ & _ & _ & V & Mn). cbn [fst snd] in V, Mn.
  change (segZ (PArray.get P) (φ 0) (φ n)) with S in V, Mn.
  (* points 0 and 1 exist, so the result is a true pair *)
  assert (B01 : ((φ (bd r)) < INFZ)%Z).
  { assert (E0 : (φ (of_Z 0)) = 0%Z) by reflexivity.
    assert (E1 : (φ (of_Z 1)) = 1%Z) by reflexivity.
    pose proof (Mn (of_Z 0) (of_Z 1) ltac:(apply InS; lia) ltac:(apply InS; lia)
                  ltac:(intro E; rewrite E in E0; lia)).
    pose proof (Dz_bound x y (of_Z 0) (of_Z 1) ltac:(apply Bnd; lia) ltac:(apply Bnd; lia)).
    lia. }
  destruct V as [_ V]. destruct (V B01) as (Ii & Ij & Nij & Ed).
  destruct r as [[bi bj] d]. cbn [fst snd] in *. unfold bd in Ed, Mn. cbn [snd] in Ed, Mn.
  apply InS in Ii. apply InS in Ij.
  pose proof (to_Z_bounded bi) as Bi. pose proof (to_Z_bounded bj) as Bj.
  exists (Z.to_N (φ bi), Z.to_N (φ bj)). split.
  - split; reflexivity.
  - assert (Ri : of_Z (Z.of_N (Z.to_N (φ bi))) = bi) by (rewrite Z2N.id by lia; apply of_to_Z).
    assert (Rj : of_Z (Z.of_N (Z.to_N (φ bj))) = bj) by (rewrite Z2N.id by lia; apply of_to_Z).
    split.
    + unfold point_pair, len. cbn [fst snd]. split; [lia|]. split; [lia|].
      intro E. apply Nij. apply to_Z_inj. lia.
    + intros p q (Hp & Hq & Hpq). unfold len in Hp, Hq. cbn [fst snd].
      rewrite !(dist2_eq x y xq yq Hx Hy ltac:(lia)) by (unfold len; lia).
      rewrite Ri, Rj. apply Qle_hund. rewrite <- Ed.
      assert (Ep : (φ (of_Z (Z.of_N p))) = Z.of_N p) by (apply of_Z_to_Z; rewrite wB_val; lia).
      assert (Eq : (φ (of_Z (Z.of_N q))) = Z.of_N q) by (apply of_Z_to_Z; rewrite wB_val; lia).
      apply Mn; [apply InS; lia | apply InS; lia |].
      intro E. apply Hpq. assert ((φ (of_Z (Z.of_N p))) = (φ (of_Z (Z.of_N q)))) by (rewrite E; reflexivity).
      lia.
Qed.

Definition closestpair_correct : forall (xs ys : list Q) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists r : N * N, repr (closestpair x y) r /\ closestpair_spec xs ys r
  := closestpair_impl_correct.
