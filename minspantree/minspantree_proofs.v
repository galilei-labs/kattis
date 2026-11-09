(* Correctness proofs for minspantree_implem.v. *)
(* Implementation of minspantree (minspantree.spec): Kruskal. *)

From Minspantree.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import FinFun.
From Stdlib Require Import Permutation.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Minspantree Require Export minspantree_implem.
Open Scope uint63_scope.
Open Scope array_scope.


Lemma step_end_le : forall m w x, ((φ x) <= (φ m))%Z ->
  ((φ x) <= (φ (step_end m w x)) <= (φ m))%Z.
Proof.
  intros m w x H. unfold step_end.
  destruct (w <? m - x) eqn:E; [rewrite ltb_spec in E | lia].
  assert ((φ (m - x)) = (φ m) - (φ x))%Z by sia. sia.
Qed.

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

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make_small : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma aget_set : forall (t : array int) (i j : int) (b : int),
  (i <? PArray.length t) = true ->
  t.[i <- b].[j] = if i =? j then b else t.[j].
Proof.
  intros t i j b H. destruct (i =? j) eqn:E.
  - rewrite eqb_spec in E. subst. apply aget_set_same. exact H.
  - apply aget_set_other. intro F. subst. rewrite eqb_refl in E. discriminate.
Qed.

Lemma int_eq_Z : forall x y : int, (φ x) = (φ y) -> x = y.
Proof. intros x y H. apply to_Z_inj. exact H. Qed.

Lemma of_Z_phi : forall x : int, of_Z (φ x) = x.
Proof. intros x. apply of_to_Z. Qed.

Lemma phi_of_Z : forall z : Z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z H. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

Lemma sleb_iff : forall x y : int,
  Sint63.leb x y = true <-> (Sint63.to_Z x <= Sint63.to_Z y)%Z.
Proof.
  intros x y. change (Sint63.leb x y) with (lesb x y). rewrite Sint63.leb_spec.
  rewrite Z.compare_le_iff. reflexivity.
Qed.

Lemma sleb_false : forall x y : int,
  Sint63.leb x y = false -> (Sint63.to_Z y < Sint63.to_Z x)%Z.
Proof.
  intros x y H. destruct (Z_lt_le_dec (Sint63.to_Z y) (Sint63.to_Z x)); [exact l|].
  apply sleb_iff in l. congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* Segments of arrays, as lists                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint seg (a : array int) (lo : Z) (len : nat) : list int :=
  match len with
  | O => []
  | S l => seg a lo l ++ [a.[of_Z (lo + Z.of_nat l)]]
  end.

Lemma seg_length : forall a lo len, List.length (seg a lo len) = len.
Proof.
  intros a lo len. induction len as [|l IH]; simpl; [reflexivity|].
  rewrite length_app, IH. simpl. lia.
Qed.

Lemma seg_app : forall a lo l1 l2,
  seg a lo (l1 + l2) = seg a lo l1 ++ seg a (lo + Z.of_nat l1) l2.
Proof.
  intros a lo l1 l2. induction l2 as [|l IH]; simpl.
  - rewrite Nat.add_0_r, app_nil_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl. rewrite IH, <- app_assoc.
    rewrite Nat2Z.inj_add, Z.add_assoc. reflexivity.
Qed.

Lemma seg_ext : forall a b lo len,
  (forall p : Z, (lo <= p < lo + Z.of_nat len)%Z -> a.[of_Z p] = b.[of_Z p]) ->
  seg a lo len = seg b lo len.
Proof.
  intros a b lo len. induction len as [|l IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros p Hp; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma nth_seg : forall a lo len i d, (i < len)%nat ->
  nth i (seg a lo len) d = a.[of_Z (lo + Z.of_nat i)].
Proof.
  intros a lo len. induction len as [|l IH]; intros i d Hi; [lia|].
  simpl. destruct (Nat.eq_dec i l) as [E|E].
  - subst. rewrite app_nth2 by (rewrite seg_length; lia).
    rewrite seg_length, Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by (rewrite seg_length; lia). apply IH. lia.
Qed.

Lemma firstn_seg : forall a lo len p, (p <= len)%nat ->
  firstn p (seg a lo len) = seg a lo p.
Proof.
  intros a lo len p Hp.
  replace len with (p + (len - p))%nat by lia.
  rewrite seg_app, firstn_app, seg_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite <- (seg_length a lo p) at 1. apply firstn_all.
Qed.

(* phi of an index made from a small Z *)
Ltac phiZ := rewrite ?phi_of_Z by (rewrite wB_val; lia).

(* ------------------------------------------------------------------ *)
(* iota                                                                *)
(* ------------------------------------------------------------------ *)

Lemma iota_loop_eq : forall m i a H,
  iota_loop m i a H =
  match bdec (i <? m) with
  | left Hi => iota_loop m (i + 1) a.[i <- i] (Acc_inv H (dec_step m i Hi))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma iota_loop_spec : forall m z i a H,
  gap m i = z -> ((φ i) <= (φ m))%Z -> PArray.length a = m ->
  (forall k : int, ((φ k) < (φ i))%Z -> a.[k] = k) ->
  PArray.length (iota_loop m i a H) = m /\
  forall k : int, ((φ k) < (φ m))%Z -> (iota_loop m i a H).[k] = k.
Proof.
  intros m z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i a H Hz Him Hl Ha. rewrite iota_loop_eq.
  destruct (bdec (i <? m)) as [Hi|Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hi | reflexivity | lia
               | rewrite alength_set; exact Hl | ].
    intros k Hk. rewrite aget_set by (rewrite Hl; exact Hi).
    destruct (i =? k) eqn:E; [rewrite eqb_spec in E; congruence|].
    apply Ha. assert (k <> i) by (intro F; subst; rewrite eqb_refl in E; discriminate).
    assert ((φ k) <> (φ i)) by (intro F; apply H0, int_eq_Z, F). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    split; [exact Hl|]. intros k Hk. apply Ha. lia.
Qed.

Lemma iota_spec : forall m : int, ((φ m) <= 4194303)%Z ->
  PArray.length (iota m) = m /\
  forall k : int, ((φ k) < (φ m))%Z -> (iota m).[k] = k.
Proof.
  intros m Hm. unfold iota. eapply iota_loop_spec; [reflexivity | | | ].
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded m). lia.
  - apply alength_make_small. exact Hm.
  - intros k Hk. change (φ 0) with 0%Z in Hk. pose proof (to_Z_bounded k). lia.
Qed.

Lemma seg_snoc_int : forall a lo (i : int), (0 <= lo <= (φ i))%Z ->
  seg a lo (Z.to_nat ((φ i) + 1 - lo)) = seg a lo (Z.to_nat ((φ i) - lo)) ++ [a.[i]].
Proof.
  intros a lo i H.
  replace (Z.to_nat ((φ i) + 1 - lo)) with (S (Z.to_nat ((φ i) - lo))) by lia.
  simpl. do 3 f_equal. rewrite Z2Nat.id by lia.
  replace (lo + ((φ i) - lo))%Z with (φ i) by lia. apply of_Z_phi.
Qed.

Lemma seg_set_step : forall a lo (k : int) x, (0 <= lo <= (φ k))%Z ->
  ((φ k) < (φ (PArray.length a)))%Z ->
  seg a.[k <- x] lo (Z.to_nat ((φ k) + 1 - lo)) = seg a lo (Z.to_nat ((φ k) - lo)) ++ [x].
Proof.
  intros a lo k x H Hk. rewrite seg_snoc_int by lia.
  rewrite aget_set_same by (rewrite ltb_spec; exact Hk).
  f_equal. apply seg_ext. intros p Hp. apply aget_set_other.
  intro F. rewrite F in Hp.
  pose proof (to_Z_bounded k).
  rewrite phi_of_Z in Hp by (pose proof (to_Z_bounded k); lia). lia.
Qed.

Lemma succ_phi : forall i m : int, ((φ i) < (φ m))%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof. intros i m H. pose proof (to_Z_bounded m). sia. Qed.

(* ------------------------------------------------------------------ *)
(* Merge                                                               *)
(* ------------------------------------------------------------------ *)

Definition keyf (ws : array int) (x : int) : Z := Sint63.to_Z ws.[x].

(* adjacent cells of a in [lo, hi) are ordered by weight *)
Definition sorted_seg (ws a : array int) (lo hi : Z) : Prop :=
  forall p : Z, (lo <= p)%Z -> (p + 1 < hi)%Z ->
    (keyf ws a.[of_Z p] <= keyf ws a.[of_Z (p + 1)])%Z.

Lemma merge_loop_eq : forall ws src iend jend kend i j k dst H,
  merge_loop ws src iend jend kend i j k dst H =
  match bdec (k <? kend) with
  | left Hk =>
      if (if i <? iend then
            (if j <? jend then Sint63.leb ws.[src.[i]] ws.[src.[j]] else true)
          else false)
      then merge_loop ws src iend jend kend (i + 1) j (k + 1) dst.[k <- src.[i]]
             (Acc_inv H (dec_step kend k Hk))
      else merge_loop ws src iend jend kend i (j + 1) (k + 1) dst.[k <- src.[j]]
             (Acc_inv H (dec_step kend k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma merge_loop_spec : forall ws src iend jend kend istart jstart kstart dst0,
  ((φ kend) <= (φ (PArray.length dst0)))%Z ->
  sorted_seg ws src (φ istart) (φ iend) -> sorted_seg ws src (φ jstart) (φ jend) ->
  forall z i j k dst H, gap kend k = z ->
  ((φ istart) <= (φ i) <= (φ iend))%Z -> ((φ jstart) <= (φ j) <= (φ jend))%Z ->
  ((φ kstart) <= (φ k) <= (φ kend))%Z ->
  ((φ kend) - (φ k) = ((φ iend) - (φ i)) + ((φ jend) - (φ j)))%Z ->
  PArray.length dst = PArray.length dst0 ->
  (forall p : int, ((φ p) < (φ kstart) \/ (φ k) <= (φ p))%Z -> dst.[p] = dst0.[p]) ->
  Permutation (seg dst (φ kstart) (Z.to_nat ((φ k) - (φ kstart))))
    (seg src (φ istart) (Z.to_nat ((φ i) - (φ istart)))
     ++ seg src (φ jstart) (Z.to_nat ((φ j) - (φ jstart)))) ->
  sorted_seg ws dst (φ kstart) (φ k) ->
  (((φ kstart) < (φ k))%Z ->
     (((φ i) < (φ iend))%Z -> keyf ws dst.[k - 1] <= keyf ws src.[i])%Z /\
     (((φ j) < (φ jend))%Z -> keyf ws dst.[k - 1] <= keyf ws src.[j])%Z) ->
  PArray.length (merge_loop ws src iend jend kend i j k dst H) = PArray.length dst0 /\
  (forall p : int, ((φ p) < (φ kstart) \/ (φ kend) <= (φ p))%Z ->
     (merge_loop ws src iend jend kend i j k dst H).[p] = dst0.[p]) /\
  Permutation (seg (merge_loop ws src iend jend kend i j k dst H)
                   (φ kstart) (Z.to_nat ((φ kend) - (φ kstart))))
    (seg src (φ istart) (Z.to_nat ((φ iend) - (φ istart)))
     ++ seg src (φ jstart) (Z.to_nat ((φ jend) - (φ jstart)))) /\
  sorted_seg ws (merge_loop ws src iend jend kend i j k dst H) (φ kstart) (φ kend).
Proof.
  intros ws src iend jend kend istart jstart kstart dst0 Hkd Hsi Hsj z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j k dst H Hz Hi Hj Hk Hrem Hl Hfr Hperm Hsort Hlast.
  rewrite merge_loop_eq.
  destruct (bdec (k <? kend)) as [Hkk|Hkk].
  - pose proof Hkk as Hkk'. rewrite ltb_spec in Hkk'.
    pose proof (to_Z_bounded kstart) as Bks.
    pose proof (to_Z_bounded istart) as Bis.
    pose proof (to_Z_bounded jstart) as Bjs.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by (eapply succ_phi; exact Hkk').
    assert (Hkl : ((φ k) < (φ (PArray.length dst)))%Z) by (rewrite Hl; lia).
    assert (Hkm1 : (φ (k + 1 - 1)) = (φ k)) by sia.
    assert (Ekm1 : k + 1 - 1 = k) by (apply int_eq_Z; exact Hkm1).
    destruct (if i <? iend then
                (if j <? jend then Sint63.leb ws.[src.[i]] ws.[src.[j]] else true)
              else false) eqn:Etake.
    + (* take src.[i] *)
      assert (Hii : ((φ i) < (φ iend))%Z).
      { destruct (i <? iend) eqn:E; [rewrite ltb_spec in E; exact E | discriminate]. }
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (eapply succ_phi; exact Hii).
      assert (Hjle : ((φ j) < (φ jend))%Z -> (keyf ws src.[i] <= keyf ws src.[j])%Z).
      { intros Hjj. assert (E1 : (i <? iend) = true) by (rewrite ltb_spec; exact Hii).
        assert (E2 : (j <? jend) = true) by (rewrite ltb_spec; exact Hjj).
        rewrite E1, E2 in Etake. apply sleb_iff in Etake. exact Etake. }
      eapply IH; [ rewrite <- Hz; apply dec_step; exact Hkk | reflexivity
                 | lia | lia | lia | lia | rewrite alength_set; exact Hl | | | | ].
      * intros p Hp. rewrite aget_set_other.
        -- apply Hfr. lia.
        -- intro F. subst p. lia.
      * rewrite Hk1, Hi1. rewrite seg_set_step by lia.
        rewrite seg_snoc_int by lia.
        rewrite <- app_assoc.
        eapply Permutation_trans; [apply Permutation_app_tail; exact Hperm|].
        rewrite <- !app_assoc. apply Permutation_app_head.
        apply Permutation_app_comm.
      * intros p Hp1 Hp2. rewrite Hk1 in Hp2.
        destruct (Z.eq_dec (p + 1) (φ k)) as [E|E].
        -- rewrite E, of_Z_phi, aget_set_same by (rewrite ltb_spec; exact Hkl).
           assert (Ep : of_Z p = k - 1).
           { apply int_eq_Z. rewrite phi_of_Z by (pose proof (to_Z_bounded k); lia).
             sia. }
           rewrite Ep, aget_set_other by (intro F; apply int_eq_Z in Hkm1;
             assert ((φ (k - 1)) = (φ k) - 1)%Z by sia; rewrite <- F in H0; lia).
           apply (proj1 (Hlast ltac:(lia))). exact Hii.
        -- rewrite !aget_set_other.
           ++ apply Hsort; lia.
           ++ intro F. assert ((φ (of_Z (p + 1))) = p + 1)%Z
                by (apply phi_of_Z; pose proof (to_Z_bounded k); lia).
              rewrite <- F in H0. lia.
           ++ intro F. assert ((φ (of_Z p)) = p)%Z
                by (apply phi_of_Z; pose proof (to_Z_bounded k); lia).
              rewrite <- F in H0. lia.
      * intros _. rewrite Ekm1, aget_set_same by (rewrite ltb_spec; exact Hkl).
        split.
        -- intros Hi2. rewrite Hi1 in Hi2.
           pose proof (Hsi (φ i) ltac:(lia) ltac:(lia)) as S1.
           rewrite of_Z_phi in S1. rewrite <- Hi1, of_Z_phi in S1. exact S1.
        -- exact Hjle.
    + (* take src.[j] *)
      assert (Hjj : ((φ j) < (φ jend))%Z).
      { destruct (i <? iend) eqn:E1.
        - destruct (j <? jend) eqn:E2; [rewrite ltb_spec in E2; exact E2 | discriminate].
        - rewrite <- Bool.not_true_iff_false, ltb_spec in E1. lia. }
      assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by (eapply succ_phi; exact Hjj).
      assert (Hile : ((φ i) < (φ iend))%Z -> (keyf ws src.[j] <= keyf ws src.[i])%Z).
      { intros Hii. assert (E1 : (i <? iend) = true) by (rewrite ltb_spec; exact Hii).
        assert (E2 : (j <? jend) = true) by (rewrite ltb_spec; exact Hjj).
        rewrite E1, E2 in Etake. apply sleb_false in Etake. unfold keyf. lia. }
      eapply IH; [ rewrite <- Hz; apply dec_step; exact Hkk | reflexivity
                 | lia | lia | lia | lia | rewrite alength_set; exact Hl | | | | ].
      * intros p Hp. rewrite aget_set_other.
        -- apply Hfr. lia.
        -- intro F. subst p. lia.
      * rewrite Hk1, Hj1. rewrite seg_set_step by lia.
        rewrite seg_snoc_int by lia.
        rewrite app_assoc. apply Permutation_app_tail. exact Hperm.
      * intros p Hp1 Hp2. rewrite Hk1 in Hp2.
        destruct (Z.eq_dec (p + 1) (φ k)) as [E|E].
        -- rewrite E, of_Z_phi, aget_set_same by (rewrite ltb_spec; exact Hkl).
           assert (Ep : of_Z p = k - 1).
           { apply int_eq_Z. rewrite phi_of_Z by (pose proof (to_Z_bounded k); lia).
             sia. }
           rewrite Ep, aget_set_other by (intro F; apply int_eq_Z in Hkm1;
             assert ((φ (k - 1)) = (φ k) - 1)%Z by sia; rewrite <- F in H0; lia).
           apply (proj2 (Hlast ltac:(lia))). exact Hjj.
        -- rewrite !aget_set_other.
           ++ apply Hsort; lia.
           ++ intro F. assert ((φ (of_Z (p + 1))) = p + 1)%Z
                by (apply phi_of_Z; pose proof (to_Z_bounded k); lia).
              rewrite <- F in H0. lia.
           ++ intro F. assert ((φ (of_Z p)) = p)%Z
                by (apply phi_of_Z; pose proof (to_Z_bounded k); lia).
              rewrite <- F in H0. lia.
      * intros _. rewrite Ekm1, aget_set_same by (rewrite ltb_spec; exact Hkl).
        split.
        -- exact Hile.
        -- intros Hj2. rewrite Hj1 in Hj2.
           pose proof (Hsj (φ j) ltac:(lia) ltac:(lia)) as S1.
           rewrite of_Z_phi in S1. rewrite <- Hj1, of_Z_phi in S1. exact S1.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkk.
    assert ((φ k) = (φ kend)) by lia.
    assert ((φ i) = (φ iend)) by lia. assert ((φ j) = (φ jend)) by lia.
    split; [exact Hl|]. split; [intros p Hp; apply Hfr; lia|].
    rewrite <- H0, <- H1, <- H2. split; [exact Hperm | exact Hsort].
Qed.

(* ------------------------------------------------------------------ *)
(* Passes and the sort                                                 *)
(* ------------------------------------------------------------------ *)

(* adjacent cells of a below m are ordered, except across a multiple of w *)
Definition runs (ws a : array int) (w m : Z) : Prop :=
  forall p : Z, (0 <= p)%Z -> (p + 1 < m)%Z -> ((p + 1) mod w <> 0)%Z ->
    (keyf ws a.[of_Z p] <= keyf ws a.[of_Z (p + 1)])%Z.

Section ModHelpers.
Local Open Scope Z_scope.

Lemma mod_inner : forall w lo x : Z, (0 < w)%Z -> (lo mod w = 0)%Z ->
  (lo < x < lo + w)%Z -> (x mod w <> 0)%Z.
Proof.
  intros w lo x Hw Hlo Hx.
  assert (E : lo = (lo / w) * w) by (pose proof (Z.div_mod lo w ltac:(lia)); lia).
  replace x with ((x - lo) + (lo / w) * w)%Z by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.

Lemma mod_double : forall w lo : Z, (0 < w)%Z -> (lo mod (2 * w) = 0)%Z ->
  (lo mod w = 0)%Z.
Proof.
  intros w lo Hw H. apply Z.mod_divide; [lia|].
  apply Z.mod_divide in H; [|lia].
  eapply Z.divide_trans; [|exact H]. exists 2%Z. lia.
Qed.

Lemma mod_add_self : forall w lo : Z, (0 < w)%Z -> (lo mod w = 0)%Z ->
  ((lo + w) mod w = 0)%Z.
Proof.
  intros w lo Hw H. apply Z.mod_divide; [lia|].
  apply Z.mod_divide in H; [|lia].
  apply Z.divide_add_r; [exact H | apply Z.divide_refl].
Qed.

End ModHelpers.

Lemma step_end_cases : forall m w x : int, ((φ x) <= (φ m))%Z ->
  (((φ x) + (φ w) < (φ m))%Z /\ (φ (step_end m w x)) = ((φ x) + (φ w))%Z) \/
  (((φ m) <= (φ x) + (φ w))%Z /\ step_end m w x = m).
Proof.
  intros m w x H. unfold step_end.
  assert (Hmx : (φ (m - x)) = ((φ m) - (φ x))%Z) by sia.
  destruct (w <? m - x) eqn:E.
  - left. rewrite ltb_spec, Hmx in E. split; [lia|]. sia.
  - right. rewrite <- Bool.not_true_iff_false, ltb_spec, Hmx in E. split; [lia|reflexivity].
Qed.

Lemma pass_loop_eq : forall ws src m w lo dst H,
  pass_loop ws src m w lo dst H =
  match bdec (lo <? m) with
  | left Hlo =>
      let mid := step_end m w lo in
      let hi := step_end m w mid in
      match bdec (lo <? hi) with
      | left Hlh =>
          pass_loop ws src m w hi
            (merge_loop ws src mid hi hi lo mid lo dst
               (Zwf_well_founded 0 (gap hi lo)))
            (Acc_inv H (dec_lt m lo hi Hlo Hlh))
      | right _ => dst
      end
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma pass_loop_spec : forall ws src m w,
  (1 <= (φ w))%Z -> ((φ m) <= 4194303)%Z -> PArray.length src = m ->
  runs ws src (φ w) (φ m) ->
  forall z lo dst H, gap m lo = z -> ((φ lo) <= (φ m))%Z ->
  (((φ lo) < (φ m))%Z -> (φ lo) mod (2 * (φ w)) = 0)%Z ->
  PArray.length dst = m ->
  Permutation (seg dst 0 (Z.to_nat (φ lo))) (seg src 0 (Z.to_nat (φ lo))) ->
  runs ws dst (2 * (φ w)) (φ lo) ->
  PArray.length (pass_loop ws src m w lo dst H) = m /\
  Permutation (seg (pass_loop ws src m w lo dst H) 0 (Z.to_nat (φ m)))
              (seg src 0 (Z.to_nat (φ m))) /\
  runs ws (pass_loop ws src m w lo dst H) (2 * (φ w)) (φ m).
Proof.
  intros ws src m w Hw Hm Hsl Hruns z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo dst H Hz Hlo Hmod Hdl Hperm Hrd.
  rewrite pass_loop_eq.
  destruct (bdec (lo <? m)) as [Hlm|Hlm].
  - pose proof Hlm as Hlm'. rewrite ltb_spec in Hlm'.
    pose proof (to_Z_bounded lo) as Blo. pose proof (to_Z_bounded w) as Bw.
    cbv zeta.
    set (mid := step_end m w lo).
    set (hi := step_end m w mid).
    assert (Cmid := step_end_cases m w lo ltac:(lia)). fold mid in Cmid.
    assert (Bmid : ((φ lo) < (φ mid) <= (φ m))%Z) by (destruct Cmid as [[? ?]|[? E]]; [|rewrite E]; lia).
    assert (Chi := step_end_cases m w mid ltac:(lia)). fold hi in Chi.
    assert (Bhi : ((φ mid) <= (φ hi) <= (φ m))%Z) by (destruct Chi as [[? ?]|[? E]]; [|rewrite E]; lia).
    assert (Hlow : ((φ lo) mod (φ w) = 0)%Z) by (apply mod_double; [lia | apply Hmod; lia]).
    destruct (bdec (lo <? hi)) as [Hlh|Hlh].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hlh. lia. }
    (* the merge of [lo, mid) and [mid, hi) *)
    destruct (merge_loop_spec ws src mid hi hi lo mid lo dst
                ltac:(rewrite Hdl; lia)
                ltac:(intros p Hp1 Hp2; apply Hruns; [lia | lia |];
                      apply (mod_inner (φ w) (φ lo)); [lia | exact Hlow |];
                      destruct Cmid as [[? E]|[? E]]; [rewrite E in Hp2 | rewrite E in Hp2]; lia)
                ltac:(intros p Hp1 Hp2; apply Hruns; [lia | lia |];
                      destruct Cmid as [[? E]|[? E]];
                      [ apply (mod_inner (φ w) (φ mid)); [lia | rewrite E; apply mod_add_self; [lia|exact Hlow] |];
                        destruct Chi as [[? E2]|[? E2]]; [rewrite E2 in Hp2 | rewrite E2 in Hp2]; lia
                      | rewrite E in Hp1; destruct Chi as [[? E2]|[? E2]];
                        [rewrite E2, E in Hp2 | rewrite E2 in Hp2]; lia ])
                _ lo mid lo dst (Zwf_well_founded 0 (gap hi lo)) eq_refl
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl
                ltac:(intros; reflexivity))
      as (Hl1 & Hf1 & Hp1 & Hs1).
    { rewrite !Z.sub_diag. simpl. apply Permutation_refl. }
    { intros p Hp1 Hp2. lia. }
    { intros F. lia. }
    eapply IH; [ rewrite <- Hz; apply dec_lt; [exact Hlm | exact Hlh] | reflexivity
               | lia | | rewrite Hl1; exact Hdl | | ].
    + intros Hhm. destruct Chi as [[? E2]|[? E2]]; [|rewrite E2 in Hhm; lia].
      destruct Cmid as [[? E]|[? E]]; [|rewrite E in H0; lia].
      rewrite E2, E. replace ((φ lo) + (φ w) + (φ w))%Z with ((φ lo) + 2 * (φ w))%Z by lia.
      apply mod_add_self; [lia | apply Hmod; lia].
    + clear Cmid Chi Hrd Hruns IH.
      replace (Z.to_nat (φ hi)) with (Z.to_nat (φ lo) + Z.to_nat ((φ hi) - (φ lo)))%nat by lia.
      rewrite !seg_app.
      replace (0 + Z.of_nat (Z.to_nat (φ lo)))%Z with (φ lo) by lia.
      rewrite (seg_ext _ dst 0 (Z.to_nat (φ lo)))
        by (intros p Hp; apply Hf1; rewrite phi_of_Z by (rewrite wB_val; lia); lia).
      eapply Permutation_trans; [apply Permutation_app_head; exact Hp1|].
      apply Permutation_app; [exact Hperm|].
      replace (Z.to_nat ((φ hi) - (φ lo))) with
        (Z.to_nat ((φ mid) - (φ lo)) + Z.to_nat ((φ hi) - (φ mid)))%nat by lia.
      rewrite seg_app. rewrite Z2Nat.id by lia.
      replace ((φ lo) + ((φ mid) - (φ lo)))%Z with (φ mid) by lia.
      apply Permutation_refl.
    + clear Cmid Chi IH Hp1 Hperm.
      intros p Hp0 Hph Hpm.
      destruct (Z_lt_le_dec (p + 1) (φ lo)) as [Lt|Ge].
      * rewrite !Hf1 by (rewrite phi_of_Z by (rewrite wB_val; lia); lia).
        apply Hrd; lia.
      * destruct (Z.eq_dec (p + 1) (φ lo)) as [E|E].
        -- exfalso. apply Hpm. rewrite E. apply Hmod. lia.
        -- apply Hs1; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlm.
    assert (E : lo = m) by (apply int_eq_Z; lia). subst lo.
    split; [exact Hdl|]. split; [exact Hperm | exact Hrd].
Qed.

Lemma sort_loop_eq : forall ws m w src dst H,
  sort_loop ws m w src dst H =
  match bdec (w <? m) with
  | left Hw =>
      match bdec (w <? w + w) with
      | left Hww =>
          sort_loop ws m (w + w)
            (pass_loop ws src m w 0 dst (Zwf_well_founded 0 (gap m 0)))
            src (Acc_inv H (dec_lt m w (w + w) Hw Hww))
      | right _ => src
      end
  | right _ => src
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sort_loop_spec : forall ws m (I : list int), ((φ m) <= 4194303)%Z ->
  forall z w src dst H, gap m w = z -> (1 <= (φ w))%Z ->
  PArray.length src = m -> PArray.length dst = m ->
  Permutation (seg src 0 (Z.to_nat (φ m))) I ->
  runs ws src (φ w) (φ m) ->
  PArray.length (sort_loop ws m w src dst H) = m /\
  Permutation (seg (sort_loop ws m w src dst H) 0 (Z.to_nat (φ m))) I /\
  sorted_seg ws (sort_loop ws m w src dst H) 0 (φ m).
Proof.
  intros ws m I Hm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros w src dst H Hz Hw Hsl Hdl Hperm Hruns.
  rewrite sort_loop_eq.
  destruct (bdec (w <? m)) as [Hwm|Hwm].
  - pose proof Hwm as Hwm'. rewrite ltb_spec in Hwm'.
    assert (Hww' : (φ (w + w)) = (2 * (φ w))%Z) by sia.
    destruct (bdec (w <? w + w)) as [Hww|Hww].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hww. lia. }
    destruct (pass_loop_spec ws src m w Hw Hm Hsl Hruns _ 0 dst
                (Zwf_well_founded 0 (gap m 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded m); lia)
                ltac:(intros _; change (φ 0) with 0%Z; apply Z.mod_0_l; lia)
                Hdl ltac:(apply Permutation_refl)
                ltac:(intros p Hp0 Hp1; change (φ 0) with 0%Z in Hp1; lia))
      as (Hl1 & Hp1 & Hr1).
    eapply IH; [ rewrite <- Hz; apply dec_lt; [exact Hwm | exact Hww] | reflexivity
               | lia | exact Hl1 | exact Hsl | | ].
    + eapply Permutation_trans; [exact Hp1 | exact Hperm].
    + rewrite Hww'. exact Hr1.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hwm.
    split; [exact Hsl|]. split; [exact Hperm|].
    intros p Hp0 Hp1. apply Hruns; [lia | exact Hp1 |].
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma sort_edges_spec : forall ws m, ((φ m) <= 4194303)%Z ->
  PArray.length (sort_edges ws m) = m /\
  Permutation (seg (sort_edges ws m) 0 (Z.to_nat (φ m)))
              (seg (iota m) 0 (Z.to_nat (φ m))) /\
  sorted_seg ws (sort_edges ws m) 0 (φ m).
Proof.
  intros ws m Hm. destruct (iota_spec m Hm) as [Hl _].
  unfold sort_edges. eapply sort_loop_spec; [exact Hm | reflexivity | | exact Hl
    | apply alength_make_small; exact Hm | apply Permutation_refl | ].
  - change (φ 1) with 1%Z. lia.
  - intros p _ _ F. change (φ 1) with 1%Z in F. rewrite Z.mod_1_r in F. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: sums over lists of edge indices                          *)
(* ------------------------------------------------------------------ *)

Section Sums.
Local Open Scope Z_scope.

Definition sumZ (f : N -> Z) (l : list N) : Z :=
  fold_right (fun x s => f x + s) 0 l.

Definition ind (x : N) (l : list N) : Z := if in_dec N.eq_dec x l then 1 else 0.

Lemma sumZ_app : forall f l1 l2, sumZ f (l1 ++ l2) = sumZ f l1 + sumZ f l2.
Proof. intros f l1 l2. induction l1 as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sumZ_ext : forall f g l, (forall x, In x l -> f x = g x) -> sumZ f l = sumZ g l.
Proof.
  intros f g l. induction l as [|a l IH]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption).
  reflexivity.
Qed.

Lemma sumZ_add : forall f g l, sumZ (fun x => f x + g x) l = sumZ f l + sumZ g l.
Proof. intros f g l. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sumZ_sub : forall f g l, sumZ (fun x => f x - g x) l = sumZ f l - sumZ g l.
Proof. intros f g l. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sumZ_one : forall l, sumZ (fun _ => 1) l = Z.of_nat (List.length l).
Proof.
  intros l. induction l as [|a l IH]; [reflexivity|].
  change (sumZ (fun _ => 1) (a :: l)) with (1 + sumZ (fun _ => 1) l).
  rewrite IH. change (List.length (a :: l)) with (S (List.length l)). lia.
Qed.

Lemma sumZ_single : forall f a B, NoDup B ->
  sumZ (fun y => (if N.eq_dec y a then 1 else 0) * f y) B = ind a B * f a.
Proof.
  intros f a B HB. induction HB as [|b B Hb HB IH]; simpl.
  - unfold ind. simpl. reflexivity.
  - rewrite IH. unfold ind. destruct (N.eq_dec b a) as [E|E].
    + subst b. destruct (in_dec N.eq_dec a B) as [Ia|Ia]; [contradiction|].
      destruct (in_dec N.eq_dec a (a :: B)) as [_|F]; [lia | exfalso; apply F; left; reflexivity].
    + destruct (in_dec N.eq_dec a B) as [Ia|Ia];
      destruct (in_dec N.eq_dec a (b :: B)) as [Ib|Ib]; try lia.
      * exfalso. apply Ib. right. exact Ia.
      * destruct Ib as [F|F]; [congruence | contradiction].
Qed.

(* double counting: both sides are the sum of f over the elements of A and B *)
Lemma sumZ_double : forall f A B, NoDup A -> NoDup B ->
  sumZ (fun x => ind x B * f x) A = sumZ (fun y => ind y A * f y) B.
Proof.
  intros f A B HA HB. induction HA as [|a A Ha HA IH]; simpl.
  - symmetry. transitivity (sumZ (fun _ => 0) B).
    + apply sumZ_ext. intros. unfold ind. simpl. reflexivity.
    + clear. induction B; simpl; [reflexivity | rewrite IHB; reflexivity].
  - rewrite IH.
    transitivity (sumZ (fun y => (if N.eq_dec y a then 1 else 0) * f y) B
                  + sumZ (fun y => ind y A * f y) B).
    + rewrite sumZ_single by exact HB. reflexivity.
    + rewrite <- sumZ_add. apply sumZ_ext. intros y _. unfold ind.
      destruct (N.eq_dec y a) as [E|E].
      * subst y. destruct (in_dec N.eq_dec a A); [contradiction|].
        destruct (in_dec N.eq_dec a (a :: A)) as [_|F]; [lia | exfalso; apply F; left; reflexivity].
      * destruct (in_dec N.eq_dec y A) as [I1|I1];
        destruct (in_dec N.eq_dec y (a :: A)) as [I2|I2]; try lia.
        -- exfalso. apply I2. right. exact I1.
        -- destruct I2 as [F|F]; [congruence | contradiction].
Qed.

Lemma ind_in : forall x l, In x l -> ind x l = 1.
Proof. intros x l H. unfold ind. destruct (in_dec N.eq_dec x l); [reflexivity | contradiction]. Qed.

Lemma ind_notin : forall x l, ~ In x l -> ind x l = 0.
Proof. intros x l H. unfold ind. destruct (in_dec N.eq_dec x l); [contradiction | reflexivity]. Qed.

Lemma sumZ_incl : forall f A B, NoDup A -> NoDup B -> incl B A ->
  sumZ (fun x => ind x B * f x) A = sumZ f B.
Proof.
  intros f A B HA HB Hi. rewrite sumZ_double by assumption.
  apply sumZ_ext. intros y Hy. rewrite ind_in by (apply Hi; exact Hy). lia.
Qed.

Lemma sumZ_ind : forall A B, NoDup A -> NoDup B ->
  sumZ (fun x => ind x B) A = sumZ (fun y => ind y A) B.
Proof.
  intros A B HA HB.
  transitivity (sumZ (fun x => ind x B * 1) A); [apply sumZ_ext; intros; lia|].
  rewrite sumZ_double by assumption. apply sumZ_ext; intros; lia.
Qed.

Lemma sumZ_ind_incl : forall A B, NoDup A -> NoDup B -> incl B A ->
  sumZ (fun x => ind x B) A = Z.of_nat (List.length B).
Proof.
  intros A B HA HB Hi.
  transitivity (sumZ (fun x => ind x B * 1) A); [apply sumZ_ext; intros; lia|].
  rewrite sumZ_incl by assumption. apply sumZ_one.
Qed.

Lemma total_weight_sumZ : forall ws t, total_weight ws t = sumZ (get_list_Z ws) t.
Proof. intros ws t. induction t as [|a t IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* Abel summation: a sorted sequence of weights, and a difference of
   counts whose prefix sums are never positive *)
Fixpoint chainL (w : N -> Z) (x0 : Z) (l : list N) (L : Z) : Prop :=
  match l with
  | [] => x0 <= L
  | a :: l' => x0 <= w a /\ chainL w (w a) l' L
  end.

Lemma abel : forall (d w : N -> Z) L l c x0,
  (forall p, c + sumZ d (firstn p l) <= 0) -> chainL w x0 l L ->
  (c + sumZ d l) * L <= c * x0 + sumZ (fun x => d x * w x) l.
Proof.
  intros d w L l. induction l as [|a l IH]; intros c x0 Hp Hc; simpl in *.
  - specialize (Hp 0%nat). simpl in Hp. nia.
  - destruct Hc as [H1 H2].
    pose proof (Hp 0%nat) as H0. simpl in H0.
    specialize (IH (c + d a) (w a)).
    assert (IH' : (c + d a + sumZ d l) * L <= (c + d a) * w a + sumZ (fun x => d x * w x) l).
    { apply IH; [|exact H2]. intros p. specialize (Hp (S p)). simpl in Hp. lia. }
    nia.
Qed.

Lemma chain_of_sorted : forall (w : N -> Z) l x0 L,
  (forall i, (S i < List.length l)%nat -> w (nth i l 0%N) <= w (nth (S i) l 0%N)) ->
  (forall x, In x l -> w x <= L) ->
  (match l with [] => True | a :: _ => x0 <= w a end) -> x0 <= L ->
  chainL w x0 l L.
Proof.
  intros w l. induction l as [|a l IH]; intros x0 L Hs Hb Hh HL; simpl; [exact HL|].
  split; [exact Hh|]. apply IH.
  - intros i Hi. apply (Hs (S i)). simpl. lia.
  - intros x Hx. apply Hb. right. exact Hx.
  - destruct l as [|b l]; [exact I|]. apply (Hs 0%nat). simpl. lia.
  - apply Hb. left. reflexivity.
Qed.

End Sums.

(* ------------------------------------------------------------------ *)
(* Math side: partitions given by a root function                      *)
(* ------------------------------------------------------------------ *)

Section Roots.
Local Open Scope Z_scope.

(* R maps every vertex to a representative of its class, a fixpoint *)
Definition validR (n : N) (R : N -> N) : Prop :=
  forall x, (x < n)%N -> (R x < n)%N /\ R (R x) = R x.

(* the classes of a and b merged, b's representative kept *)
Definition mergeR (R : N -> N) (a b : N) : N -> N :=
  fun x => if N.eq_dec (R x) (R a) then R b else R x.

(* the number of representatives below k *)
Fixpoint rootcnt (R : N -> N) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => rootcnt R k' + (if N.eq_dec (R (N.of_nat k')) (N.of_nat k') then 1 else 0)
  end.

Lemma rc_ext : forall R1 R2 k, (forall x, (x < N.of_nat k)%N -> R1 x = R2 x) ->
  rootcnt R1 k = rootcnt R2 k.
Proof.
  intros R1 R2 k. induction k as [|k IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros x Hx; apply H; lia).
  rewrite H by lia. reflexivity.
Qed.

Lemma rc_merge : forall n R a b, validR n R -> (a < n)%N -> (b < n)%N -> R a <> R b ->
  forall k, (k <= N.to_nat n)%nat ->
  rootcnt R k = rootcnt (mergeR R a b) k + (if N.ltb (R a) (N.of_nat k) then 1 else 0).
Proof.
  intros n R a b HV Ha Hb Hab k. induction k as [|k IH]; intros Hk.
  - simpl. destruct (N.ltb_spec (R a) 0); lia.
  - cbn [rootcnt]. rewrite IH by lia.
    set (x := N.of_nat k).
    assert (Hx : (x < n)%N) by (unfold x; lia).
    destruct (HV x Hx) as [Vx1 Vx2]. destruct (HV a Ha) as [Va1 Va2].
    destruct (HV b Hb) as [Vb1 Vb2].
    rewrite Nat2N.inj_succ. fold x. unfold mergeR.
    destruct (N.ltb_spec (R a) x); destruct (N.ltb_spec (R a) (N.succ x));
    destruct (N.eq_dec (R x) x); destruct (N.eq_dec (R x) (R a));
    try destruct (N.eq_dec (R b) x); try destruct (N.eq_dec (R x) x);
    try lia; try congruence;
    (assert (R a = x) by lia; congruence).
Qed.

Lemma rc_merge_le : forall n R a b, validR n R -> (a < n)%N -> (b < n)%N ->
  rootcnt R (N.to_nat n) <= rootcnt (mergeR R a b) (N.to_nat n) + 1.
Proof.
  intros n R a b HV Ha Hb. destruct (N.eq_dec (R a) (R b)) as [E|E].
  - rewrite (rc_ext (mergeR R a b) R); [lia|].
    intros x _. unfold mergeR. destruct (N.eq_dec (R x) (R a)); congruence.
  - rewrite (rc_merge n R a b HV Ha Hb E (N.to_nat n) ltac:(lia)).
    destruct (N.ltb _ _); lia.
Qed.

Lemma rc_merge_eq : forall n R a b, validR n R -> (a < n)%N -> (b < n)%N -> R a <> R b ->
  rootcnt R (N.to_nat n) = rootcnt (mergeR R a b) (N.to_nat n) + 1.
Proof.
  intros n R a b HV Ha Hb E.
  rewrite (rc_merge n R a b HV Ha Hb E (N.to_nat n) ltac:(lia)).
  destruct (HV a Ha) as [Va _].
  destruct (N.ltb_spec (R a) (N.of_nat (N.to_nat n))); lia.
Qed.

Lemma rc_const : forall R c k, (forall x, (x < N.of_nat k)%N -> R x = c) ->
  rootcnt R k = if N.ltb c (N.of_nat k) then 1 else 0.
Proof.
  intros R c k. induction k as [|k IH]; intros H; cbn [rootcnt].
  - destruct (N.ltb_spec c (N.of_nat 0)); lia.
  - rewrite IH by (intros x Hx; apply H; lia).
    rewrite (H (N.of_nat k)) by lia. rewrite Nat2N.inj_succ.
    destruct (N.ltb_spec c (N.of_nat k)); destruct (N.ltb_spec c (N.succ (N.of_nat k)));
    destruct (N.eq_dec c (N.of_nat k)); lia.
Qed.

Lemma rc_le1 : forall R c k, (forall x, (x < N.of_nat k)%N -> R x = c) -> rootcnt R k <= 1.
Proof. intros R c k H. rewrite (rc_const R c k H). destruct (N.ltb _ _); lia. Qed.

Lemma rc_ge : forall R x y k, x <> y -> R x = x -> R y = y ->
  (if N.ltb x (N.of_nat k) then 1 else 0) + (if N.ltb y (N.of_nat k) then 1 else 0)
  <= rootcnt R k.
Proof.
  intros R x y k Hxy Hx Hy. induction k as [|k IH]; cbn [rootcnt].
  - destruct (N.ltb_spec x (N.of_nat 0)); destruct (N.ltb_spec y (N.of_nat 0)); lia.
  - rewrite Nat2N.inj_succ.
    destruct (N.ltb_spec x (N.of_nat k)); destruct (N.ltb_spec x (N.succ (N.of_nat k)));
    destruct (N.ltb_spec y (N.of_nat k)); destruct (N.ltb_spec y (N.succ (N.of_nat k)));
    destruct (N.eq_dec (R (N.of_nat k)) (N.of_nat k)); try lia;
    first [ assert (x = N.of_nat k) by lia; subst x; congruence
          | assert (y = N.of_nat k) by lia; subst y; congruence ].
Qed.

Lemma rc_ge2 : forall R x y k, x <> y -> R x = x -> R y = y ->
  (x < N.of_nat k)%N -> (y < N.of_nat k)%N -> 2 <= rootcnt R k.
Proof.
  intros R x y k Hxy Hx Hy Hxk Hyk. pose proof (rc_ge R x y k Hxy Hx Hy) as H.
  destruct (N.ltb_spec x (N.of_nat k)); destruct (N.ltb_spec y (N.of_nat k)); lia.
Qed.

Lemma rc_ge1 : forall R x k, R x = x -> (x < N.of_nat k)%N -> 1 <= rootcnt R k.
Proof.
  intros R x k Hx Hxk. induction k as [|k IH]; simpl; [lia|].
  destruct (N.eq_dec x (N.of_nat k)) as [E|E].
  - subst x. destruct (N.eq_dec (R (N.of_nat k)) (N.of_nat k)); [|congruence].
    assert (0 <= rootcnt R k) by (clear; induction k; simpl; [lia|];
      destruct (N.eq_dec _ _); lia). lia.
  - assert (1 <= rootcnt R k) by (apply IH; lia).
    destruct (N.eq_dec _ _); lia.
Qed.

Lemma rc_id : forall k, rootcnt (fun x => x) k = Z.of_nat k.
Proof.
  intros k. induction k as [|k IH]; simpl; [reflexivity|]. rewrite IH.
  destruct (N.eq_dec _ _); [lia | congruence].
Qed.

Lemma validR_merge : forall n R a b, validR n R -> (a < n)%N -> (b < n)%N ->
  validR n (mergeR R a b).
Proof.
  intros n R a b HV Ha Hb x Hx. unfold mergeR.
  destruct (HV x Hx) as [Vx1 Vx2]. destruct (HV a Ha) as [Va1 Va2].
  destruct (HV b Hb) as [Vb1 Vb2].
  destruct (N.eq_dec (R x) (R a)).
  - split; [exact Vb1|]. rewrite Vb2. destruct (N.eq_dec (R b) (R a)); congruence.
  - split; [exact Vx1|]. rewrite Vx2. destruct (N.eq_dec (R x) (R a)); congruence.
Qed.

End Roots.

(* ------------------------------------------------------------------ *)
(* Math side: Kruskal's invariant and why it gives a minimum tree       *)
(* ------------------------------------------------------------------ *)

Lemma firstn_app_le : forall {A} p (l1 l2 : list A), (p <= List.length l1)%nat ->
  firstn p (l1 ++ l2) = firstn p l1.
Proof.
  intros A p l1 l2 H. rewrite firstn_app.
  replace (p - List.length l1)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma in_firstn : forall {A} (x : A) p l, In x (firstn p l) -> In x l.
Proof.
  intros A x p l H. rewrite <- (firstn_skipn p l). apply in_or_app. left. exact H.
Qed.

Section Kruskal.
Local Open Scope Z_scope.

Variables (n : N) (us vs : list N) (ws : list Z).
Hypothesis Hend : forall k, edge_index us k ->
  vertex n (get_list_N us k) /\ vertex n (get_list_N vs k).
Hypothesis Hn : (1 <= n)%N.

Local Notation eu k := (get_list_N us k).
Local Notation ev k := (get_list_N vs k).
Local Notation lk := (linked us vs).

Lemma lk_trans : forall sel a b c, lk sel a b -> lk sel b c -> lk sel a c.
Proof.
  intros sel a b c H1 H2. induction H2 as [|b' k c' H IH Hk Hs Hj]; [exact H1|].
  eapply linked_hop; eauto.
Qed.

Lemma lk_edge : forall sel k a b, edge_index us k -> sel k -> joins us vs k a b ->
  lk sel a b.
Proof. intros sel k a b Hk Hs Hj. eapply linked_hop; [apply linked_here | exact Hk | exact Hs | exact Hj]. Qed.

Lemma joins_sym : forall k a b, joins us vs k a b -> joins us vs k b a.
Proof. unfold joins. tauto. Qed.

Lemma lk_sym : forall sel a b, lk sel a b -> lk sel b a.
Proof.
  intros sel a b H. induction H as [|b k c H IH Hk Hs Hj]; [apply linked_here|].
  eapply lk_trans; [|exact IH]. eapply lk_edge; [exact Hk | exact Hs | apply joins_sym; exact Hj].
Qed.

Lemma lk_mono : forall (sel sel' : N -> Prop) a b, (forall k, sel k -> sel' k) ->
  lk sel a b -> lk sel' a b.
Proof.
  intros sel sel' a b Hs H. induction H as [|b k c H IH Hk Hsk Hj]; [apply linked_here|].
  eapply linked_hop; [exact IH | exact Hk | apply Hs; exact Hsk | exact Hj].
Qed.

Lemma lk_const : forall (sel : N -> Prop) (R : N -> N) a b,
  (forall k, edge_index us k -> sel k -> R (eu k) = R (ev k)) ->
  lk sel a b -> R a = R b.
Proof.
  intros sel R a b HR H. induction H as [|b k c H IH Hk Hsk Hj]; [reflexivity|].
  rewrite IH. specialize (HR k Hk Hsk).
  destruct Hj as [[E1 E2]|[E1 E2]]; rewrite <- E1, <- E2; congruence.
Qed.

Lemma mergeR_coarsen : forall R a b x y, R x = R y -> mergeR R a b x = mergeR R a b y.
Proof. intros R a b x y H. unfold mergeR. rewrite H. reflexivity. Qed.

Lemma mergeR_joined : forall R a b, mergeR R a b a = mergeR R a b b.
Proof.
  intros R a b. unfold mergeR.
  destruct (N.eq_dec (R a) (R a)); [|congruence].
  destruct (N.eq_dec (R b) (R a)); congruence.
Qed.

Lemma merge_fold : forall (P : N -> bool) L R, validR n R ->
  (forall k, In k L -> edge_index us k) ->
  (forall k, In k L -> P k = true -> R (eu k) = R (ev k)) ->
  exists R', validR n R' /\
    (forall x y, (x < n)%N -> (y < n)%N -> R x = R y -> R' x = R' y) /\
    rootcnt R (N.to_nat n) <= rootcnt R' (N.to_nat n) + sumZ (fun k => if P k then 0 else 1) L /\
    (forall k, In k L -> R' (eu k) = R' (ev k)).
Proof.
  intros P L. induction L as [|k L IH]; intros R HV HL HP.
  - exists R. split; [exact HV|]. split; [auto|]. split; [simpl; lia|]. intros k [].
  - destruct (IH R HV ltac:(intros j Hj; apply HL; right; exact Hj)
                ltac:(intros j Hj; apply HP; right; exact Hj))
      as (R1 & HV1 & Hc1 & Hn1 & He1).
    destruct (Hend k (HL k (or_introl eq_refl))) as [Hu Hv].
    unfold vertex in Hu, Hv.
    destruct (P k) eqn:Pk.
    + exists R1. split; [exact HV1|]. split; [exact Hc1|].
      split; [simpl; rewrite Pk; lia|].
      intros j [E|Hj]; [subst j | apply He1; exact Hj].
      apply Hc1; [exact Hu | exact Hv | apply HP; [left; reflexivity | exact Pk]].
    + exists (mergeR R1 (eu k) (ev k)).
      split; [apply validR_merge; assumption|].
      split; [intros x y Hx Hy E; apply mergeR_coarsen, Hc1; assumption|].
      split.
      * simpl. rewrite Pk. pose proof (rc_merge_le n R1 (eu k) (ev k) HV1 Hu Hv). lia.
      * intros j [E|Hj]; [subst j; apply mergeR_joined|].
        apply mergeR_coarsen, He1. exact Hj.
Qed.

Lemma count_tree : forall R T Pf, validR n R -> spanning_tree n us vs T ->
  (forall k, In k T -> In k Pf -> R (eu k) = R (ev k)) ->
  sumZ (fun y => ind y Pf) T + rootcnt R (N.to_nat n) <= Z.of_N n.
Proof.
  intros R T Pf HV HT HR.
  destruct HT as [Hte Htd Hts Htsp]. unfold tree_edges in Hte.
  set (P := fun k => if in_dec N.eq_dec k Pf then true else false).
  destruct (merge_fold P T R HV
              ltac:(intros k Hk; rewrite Forall_forall in Hte; apply Hte; exact Hk)
              ltac:(intros k Hk Pk; apply HR; [exact Hk|];
                    unfold P in Pk; destruct (in_dec N.eq_dec k Pf); [assumption|discriminate]))
    as (R' & HV' & _ & Hcnt & He').
  assert (Hconst : forall x, (x < N.of_nat (N.to_nat n))%N -> R' x = R' 0%N).
  { intros x Hx. symmetry. apply (lk_const (fun k => In k T)).
    - intros k Hk HkT. apply He'. exact HkT.
    - apply Htsp; unfold vertex; lia. }
  pose proof (rc_le1 R' (R' 0%N) (N.to_nat n) Hconst) as Hle.
  assert (Hsum : sumZ (fun y => ind y Pf) T + sumZ (fun k => if P k then 0 else 1) T
                 = Z.of_nat (List.length T)).
  { rewrite <- sumZ_add, <- sumZ_one. apply sumZ_ext. intros x _.
    unfold P, ind. destruct (in_dec N.eq_dec x Pf); lia. }
  unfold tree_size, len in Hts. lia.
Qed.

Lemma opt_full : forall R K Pf T, validR n R -> NoDup Pf -> NoDup K -> incl K Pf ->
  (forall e, In e Pf -> R (eu e) = R (ev e)) ->
  rootcnt R (N.to_nat n) + Z.of_nat (List.length K) = Z.of_N n ->
  spanning_tree n us vs T ->
  sumZ (fun x => ind x T - ind x K) Pf <= 0.
Proof.
  intros R K Pf T HV HPf HK Hi Hp Hc HT.
  rewrite sumZ_sub, sumZ_ind by (first [exact HPf | exact (st_distinct _ _ _ _ HT)]).
  rewrite (sumZ_ind_incl Pf K) by assumption.
  pose proof (count_tree R T Pf HV HT ltac:(intros k _ Hk; apply Hp; exact Hk)). lia.
Qed.

Record KI (R : N -> N) (K Pf : list N) : Prop := {
  ki_valid : validR n R;
  ki_count : rootcnt R (N.to_nat n) + Z.of_nat (List.length K) = Z.of_N n;
  ki_pref : forall e, In e Pf -> R (eu e) = R (ev e);
  ki_link : forall x, (x < n)%N -> lk (fun k => In k K) x (R x);
  ki_nodup : NoDup K;
  ki_incl : incl K Pf;
  ki_opt : forall T, spanning_tree n us vs T -> forall p, (p <= List.length Pf)%nat ->
    sumZ (fun x => ind x T - ind x K) (firstn p Pf) <= 0;
}.

Lemma ki_init : KI (fun x => x) [] [].
Proof.
  constructor.
  - intros x Hx. split; [exact Hx | reflexivity].
  - rewrite rc_id. simpl. lia.
  - intros e [].
  - intros x _. apply linked_here.
  - constructor.
  - intros x [].
  - intros T _ p _. rewrite firstn_nil. simpl. lia.
Qed.

Lemma ki_reject : forall R K Pf e, KI R K Pf -> NoDup (Pf ++ [e]) ->
  R (eu e) = R (ev e) -> KI R K (Pf ++ [e]).
Proof.
  intros R K Pf e HK Hnd He.
  assert (Hp' : forall x, In x (Pf ++ [e]) -> R (eu x) = R (ev x)).
  { intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|[Hx|[]]].
    - apply (ki_pref _ _ _ HK). exact Hx.
    - subst x. exact He. }
  constructor.
  - exact (ki_valid _ _ _ HK).
  - exact (ki_count _ _ _ HK).
  - exact Hp'.
  - exact (ki_link _ _ _ HK).
  - exact (ki_nodup _ _ _ HK).
  - apply incl_appl. exact (ki_incl _ _ _ HK).
  - intros T HT p Hp. rewrite length_app in Hp. simpl in Hp.
    destruct (Nat.le_gt_cases p (List.length Pf)) as [Le|Gt].
    + rewrite firstn_app_le by exact Le. apply (ki_opt _ _ _ HK); assumption.
    + rewrite firstn_all2 by (rewrite length_app; simpl; lia).
      eapply opt_full; [exact (ki_valid _ _ _ HK) | exact Hnd | exact (ki_nodup _ _ _ HK)
                       | apply incl_appl; exact (ki_incl _ _ _ HK) | exact Hp'
                       | exact (ki_count _ _ _ HK) | exact HT].
Qed.

Lemma ki_accept : forall R K Pf e a b R', KI R K Pf -> NoDup (Pf ++ [e]) ->
  (forall x, In x Pf -> edge_index us x) ->
  edge_index us e -> joins us vs e a b -> R a <> R b ->
  (forall x, (x < n)%N -> R' x = mergeR R a b x) ->
  KI R' (K ++ [e]) (Pf ++ [e]).
Proof.
  intros R K Pf e a b R' HK Hnd HPe He Hj Hab HR'.
  destruct (Hend e He) as [Hu Hv]. unfold vertex in Hu, Hv.
  assert (Ha : (a < n)%N) by (destruct Hj as [[E1 E2]|[E1 E2]]; subst; assumption).
  assert (Hb : (b < n)%N) by (destruct Hj as [[E1 E2]|[E1 E2]]; subst; assumption).
  pose proof (ki_valid _ _ _ HK) as HV.
  pose proof (validR_merge n R a b HV Ha Hb) as HVM.
  assert (HV' : validR n R').
  { intros x Hx. destruct (HVM x Hx) as [M1 M2].
    rewrite (HR' x Hx). split; [exact M1|]. rewrite HR' by exact M1. exact M2. }
  assert (HeK : ~ In e Pf).
  { intro F. apply (NoDup_remove_2 Pf [] e Hnd). rewrite app_nil_r. exact F. }
  assert (HeK' : ~ In e K) by (intro F; apply HeK; apply (ki_incl _ _ _ HK); exact F).
  assert (Hc' : rootcnt R' (N.to_nat n) + Z.of_nat (List.length (K ++ [e])) = Z.of_N n).
  { rewrite (rc_ext R' (mergeR R a b)) by (intros x Hx; apply HR'; lia).
    pose proof (rc_merge_eq n R a b HV Ha Hb Hab).
    pose proof (ki_count _ _ _ HK). rewrite length_app. simpl. lia. }
  assert (Hp' : forall x, In x (Pf ++ [e]) -> R' (eu x) = R' (ev x)).
  { intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|[Hx|[]]].
    - destruct (Hend x (HPe x Hx)) as [Hxu Hxv]. unfold vertex in Hxu, Hxv.
      rewrite !HR' by assumption. apply mergeR_coarsen.
      apply (ki_pref _ _ _ HK). exact Hx.
    - subst x. rewrite !HR' by assumption.
      destruct Hj as [[E1 E2]|[E1 E2]]; rewrite E1, E2;
        [apply mergeR_joined | symmetry; apply mergeR_joined]. }
  assert (HnK : NoDup (K ++ [e])).
  { apply Permutation_NoDup with (e :: K); [apply Permutation_cons_append|].
    constructor; [exact HeK' | exact (ki_nodup _ _ _ HK)]. }
  assert (HiK : incl (K ++ [e]) (Pf ++ [e])).
  { intros x Hx. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx|Hx]; [left; apply (ki_incl _ _ _ HK); exact Hx | right; exact Hx]. }
  constructor.
  - exact HV'.
  - exact Hc'.
  - exact Hp'.
  - intros x Hx. rewrite (HR' x Hx). unfold mergeR.
    assert (Hm : forall c d, lk (fun k => In k K) c d -> lk (fun k => In k (K ++ [e])) c d)
      by (intros c d; apply lk_mono; intros k Hk; apply in_or_app; left; exact Hk).
    destruct (N.eq_dec (R x) (R a)) as [E|E].
    + eapply lk_trans; [apply Hm; apply (ki_link _ _ _ HK); exact Hx|]. rewrite E.
      eapply lk_trans; [apply lk_sym, Hm; apply (ki_link _ _ _ HK); exact Ha|].
      eapply lk_trans; [eapply lk_edge; [exact He | apply in_or_app; right; left; reflexivity
                                         | exact Hj]|].
      apply Hm. apply (ki_link _ _ _ HK). exact Hb.
    + apply Hm. apply (ki_link _ _ _ HK). exact Hx.
  - exact HnK.
  - exact HiK.
  - intros T HT p Hp. rewrite length_app in Hp. simpl in Hp.
    destruct (Nat.le_gt_cases p (List.length Pf)) as [Le|Gt].
    + rewrite firstn_app_le by exact Le.
      rewrite (sumZ_ext _ (fun x => ind x T - ind x K)).
      * apply (ki_opt _ _ _ HK); assumption.
      * intros x Hx. apply in_firstn in Hx.
        assert (x <> e) by (intro F; subst; contradiction).
        f_equal. unfold ind.
        destruct (in_dec N.eq_dec x (K ++ [e])) as [I1|I1];
        destruct (in_dec N.eq_dec x K) as [I2|I2]; try reflexivity.
        -- apply in_app_iff in I1. destruct I1 as [I1|[I1|[]]]; [contradiction | congruence].
        -- exfalso. apply I1. apply in_or_app. left. exact I2.
    + rewrite firstn_all2 by (rewrite length_app; simpl; lia).
      eapply opt_full; [exact HV' | exact Hnd | exact HnK | exact HiK | exact Hp'
                       | exact Hc' | exact HT].
Qed.

Lemma ki_room : forall R K Pf a b, KI R K Pf -> (a < n)%N -> (b < n)%N -> R a <> R b ->
  Z.of_nat (List.length K) + 1 <= Z.of_N n - 1.
Proof.
  intros R K Pf a b HK Ha Hb Hab.
  pose proof (ki_valid _ _ _ HK) as HV.
  destruct (HV a Ha) as [Va1 Va2]. destruct (HV b Hb) as [Vb1 Vb2].
  pose proof (rc_ge2 R (R a) (R b) (N.to_nat n) Hab Va2 Vb2 ltac:(lia) ltac:(lia)).
  pose proof (ki_count _ _ _ HK). lia.
Qed.

Lemma ki_none : forall R K Pf, KI R K Pf ->
  (forall k, edge_index us k -> In k Pf) ->
  Z.of_nat (List.length K) <> Z.of_N n - 1 ->
  ~ graph_connected n us vs.
Proof.
  intros R K Pf HK Hall HlK Hc.
  pose proof (ki_valid _ _ _ HK) as HV.
  assert (Hconst : forall x, (x < N.of_nat (N.to_nat n))%N -> R x = R 0%N).
  { intros x Hx. symmetry. apply (lk_const every_edge).
    - intros k Hk _. apply (ki_pref _ _ _ HK). apply Hall. exact Hk.
    - apply Hc; unfold vertex; lia. }
  pose proof (rc_le1 R (R 0%N) (N.to_nat n) Hconst).
  destruct (HV 0%N ltac:(lia)) as [V1 V2].
  pose proof (rc_ge1 R (R 0%N) (N.to_nat n) V2 ltac:(lia)).
  pose proof (ki_count _ _ _ HK). lia.
Qed.

Lemma ki_some : forall R K Pf, KI R K Pf -> NoDup Pf ->
  (forall k, edge_index us k <-> In k Pf) ->
  chainL (get_list_Z ws) (-20000) Pf 20000 ->
  Z.of_nat (List.length K) = Z.of_N n - 1 ->
  minimum_spanning_tree n us vs ws (total_weight ws K) K.
Proof.
  intros R K Pf HK HPf Hall Hch HlK.
  pose proof (ki_valid _ _ _ HK) as HV.
  assert (HinK : incl K Pf) by exact (ki_incl _ _ _ HK).
  assert (HST : spanning_tree n us vs K).
  { constructor.
    - unfold tree_edges. rewrite Forall_forall. intros k Hk. apply Hall. apply HinK. exact Hk.
    - exact (ki_nodup _ _ _ HK).
    - unfold tree_size, len. lia.
    - intros u v Hu Hv. unfold vertex in Hu, Hv.
      assert (Hroot : forall x, (x < n)%N -> R x = R 0%N).
      { intros x Hx. destruct (N.eq_dec (R x) (R 0%N)) as [E|E]; [exact E|].
        exfalso. destruct (HV x Hx) as [Vx1 Vx2]. destruct (HV 0%N ltac:(lia)) as [V01 V02].
        pose proof (rc_ge2 R (R x) (R 0%N) (N.to_nat n) E Vx2 V02 ltac:(lia) ltac:(lia)).
        pose proof (ki_count _ _ _ HK). lia. }
      eapply lk_trans; [apply (ki_link _ _ _ HK); exact Hu|].
      rewrite (Hroot u Hu), <- (Hroot v Hv).
      apply lk_sym. apply (ki_link _ _ _ HK). exact Hv. }
  split; [exact HST|]. split; [reflexivity|].
  intros T HT.
  assert (HiT : incl T Pf).
  { intros k Hk. apply Hall. destruct HT as [Hte _ _ _]. unfold tree_edges in Hte.
    rewrite Forall_forall in Hte. apply Hte. exact Hk. }
  set (d := fun x => ind x T - ind x K).
  pose proof (abel d (get_list_Z ws) 20000 Pf 0 (-20000)) as Hab.
  assert (Hpre : forall p, 0 + sumZ d (firstn p Pf) <= 0).
  { intros p. destruct (Nat.le_gt_cases p (List.length Pf)) as [Le|Gt].
    - pose proof (ki_opt _ _ _ HK T HT p Le). unfold d. lia.
    - rewrite firstn_all2 by lia.
      pose proof (ki_opt _ _ _ HK T HT (List.length Pf) ltac:(lia)) as H.
      rewrite firstn_all in H. unfold d. lia. }
  specialize (Hab Hpre Hch).
  assert (Hd0 : sumZ d Pf = 0).
  { unfold d. rewrite sumZ_sub.
    rewrite (sumZ_ind_incl Pf T HPf (st_distinct _ _ _ _ HT) HiT).
    rewrite (sumZ_ind_incl Pf K HPf (ki_nodup _ _ _ HK) HinK).
    pose proof (st_size _ _ _ _ HT) as Hs. unfold tree_size, len in Hs. lia. }
  assert (Hdw : sumZ (fun x => d x * get_list_Z ws x) Pf
                = total_weight ws T - total_weight ws K).
  { rewrite (sumZ_ext _ (fun x => ind x T * get_list_Z ws x - ind x K * get_list_Z ws x))
      by (intros; unfold d; ring).
    rewrite sumZ_sub.
    rewrite (sumZ_incl _ Pf T HPf (st_distinct _ _ _ _ HT) HiT).
    rewrite (sumZ_incl _ Pf K HPf (ki_nodup _ _ _ HK) HinK).
    rewrite !total_weight_sumZ. reflexivity. }
  rewrite Hd0, Hdw in Hab. lia.
Qed.

End Kruskal.

(* ------------------------------------------------------------------ *)
(* Union-find                                                          *)
(* ------------------------------------------------------------------ *)

(* parents are vertices, and a parent link climbs in rank *)
Definition UF (n : Z) (par rk : array int) : Prop :=
  (φ (PArray.length par)) = n /\ (φ (PArray.length rk)) = n /\
  forall v : int, ((φ v) < n)%Z ->
    ((φ (par.[v])) < n)%Z /\ (par.[v] <> v -> ((φ (rk.[v])) < (φ (rk.[par.[v]])))%Z).

Lemma find_eq : forall par rk v H,
  find par rk v H =
  let u := par.[v] in
  if u =? v then v
  else match bdec (rk.[v] <? rk.[u]) with
       | left Hr => find par rk u (Acc_inv H (rdec rk v u Hr))
       | right _ => v
       end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma find_irrel : forall par rk z v (H1 H2 : Acc (Zwf 0) (rgap rk v)),
  rgap rk v = z -> find par rk v H1 = find par rk v H2.
Proof.
  intros par rk z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v H1 H2 Hz. rewrite !find_eq. cbv zeta.
  destruct (par.[v] =? v); [reflexivity|].
  destruct (bdec (rk.[v] <? rk.[par.[v]])) as [Hr|Hr]; [|reflexivity].
  eapply IH; [rewrite <- Hz; apply rdec; exact Hr | reflexivity].
Qed.

Lemma findr_root : forall par rk v, par.[v] = v -> findr par rk v = v.
Proof.
  intros par rk v H. unfold findr. rewrite find_eq. cbv zeta.
  rewrite H, eqb_refl. reflexivity.
Qed.

Lemma findr_step : forall n par rk v, UF n par rk -> ((φ v) < n)%Z -> par.[v] <> v ->
  findr par rk v = findr par rk par.[v].
Proof.
  intros n par rk v [_ [_ HU]] Hv Hp. unfold findr at 1. rewrite find_eq. cbv zeta.
  destruct (par.[v] =? v) eqn:E; [rewrite eqb_spec in E; contradiction|].
  destruct (bdec (rk.[v] <? rk.[par.[v]])) as [Hr|Hr].
  - unfold findr. eapply find_irrel. reflexivity.
  - exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hr.
    apply Hr. apply (proj2 (HU v Hv)). exact Hp.
Qed.

Lemma findr_spec : forall n par rk, UF n par rk -> forall v, ((φ v) < n)%Z ->
  ((φ (findr par rk v)) < n)%Z /\ par.[findr par rk v] = findr par rk v.
Proof.
  intros n par rk HU.
  assert (G : forall z v, rgap rk v = z -> ((φ v) < n)%Z ->
            ((φ (findr par rk v)) < n)%Z /\ par.[findr par rk v] = findr par rk v).
  { intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros v Hz Hv. destruct (eqs par.[v] v) as [E|E].
    - rewrite findr_root by exact E. split; [exact Hv | exact E].
    - rewrite (findr_step n par rk v HU Hv E).
      destruct HU as [_ [_ HU]]. destruct (HU v Hv) as [Hp Hr].
      eapply IH; [| reflexivity | exact Hp].
      rewrite <- Hz. apply rdec. rewrite ltb_spec. apply Hr. exact E. }
  intros v Hv. eapply G; [reflexivity | exact Hv].
Qed.

Lemma union_spec : forall n par rk rk' a b, UF n par rk ->
  ((φ a) < n)%Z -> ((φ b) < n)%Z -> par.[a] = a -> par.[b] = b -> a <> b ->
  (φ (PArray.length rk')) = n ->
  (forall x, x <> b -> rk'.[x] = rk.[x]) ->
  ((φ (rk.[b])) <= (φ (rk'.[b])))%Z -> ((φ (rk'.[a])) < (φ (rk'.[b])))%Z ->
  UF n par.[a <- b] rk' /\
  forall x, ((φ x) < n)%Z ->
    findr par.[a <- b] rk' x = if findr par rk x =? a then b else findr par rk x.
Proof.
  intros n par rk rk' a b HU Ha Hb Hpa Hpb Hab Hl' Hrk Hrb Hrab.
  pose proof HU as [Hlp [Hlr HUc]].
  assert (Hal : (a <? PArray.length par) = true) by (rewrite ltb_spec; lia).
  assert (HU' : UF n par.[a <- b] rk').
  { split; [rewrite alength_set; exact Hlp|]. split; [exact Hl'|].
    intros v Hv. rewrite aget_set by exact Hal.
    destruct (a =? v) eqn:E.
    - rewrite eqb_spec in E. subst v. split; [exact Hb|]. intros _. exact Hrab.
    - assert (Hav : a <> v) by (intro F; subst; rewrite eqb_refl in E; discriminate).
      destruct (HUc v Hv) as [Hp Hr]. split; [exact Hp|]. intros Hpv.
      assert (Hvb : v <> b) by (intro F; subst; contradiction).
      rewrite (Hrk v Hvb). specialize (Hr Hpv).
      destruct (eqs par.[v] b) as [Eb|Eb]; [rewrite Eb in *; lia|].
      rewrite (Hrk _ Eb). exact Hr. }
  split; [exact HU'|].
  assert (G : forall z x, rgap rk x = z -> ((φ x) < n)%Z ->
     findr par.[a <- b] rk' x = if findr par rk x =? a then b else findr par rk x).
  { intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros x Hz Hx.
    destruct (eqs par.[x] x) as [E|E].
    - rewrite (findr_root par rk x E).
      destruct (eqs x a) as [Ea|Ea].
      + subst x. rewrite eqb_refl.
        rewrite (findr_step n _ _ a HU' Ha) by (rewrite aget_set_same by exact Hal; auto).
        rewrite aget_set_same by exact Hal.
        apply findr_root. rewrite aget_set_other by auto. exact Hpb.
      + replace (x =? a) with false by (symmetry; rewrite eqb_false_spec; exact Ea).
        apply findr_root. rewrite aget_set_other by auto. exact E.
    - assert (Ea : a <> x) by (intro F; subst; contradiction).
      assert (E' : par.[a <- b].[x] <> x) by (rewrite aget_set_other by exact Ea; exact E).
      rewrite (findr_step n _ _ x HU' Hx E').
      rewrite (findr_step n _ _ x HU Hx E).
      rewrite aget_set_other by exact Ea.
      destruct (HUc x Hx) as [Hp Hr].
      eapply IH; [| reflexivity | exact Hp].
      rewrite <- Hz. apply rdec. rewrite ltb_spec. apply Hr. exact E. }
  intros x Hx. eapply G; [reflexivity | exact Hx].
Qed.

(* ------------------------------------------------------------------ *)
(* The scan                                                            *)
(* ------------------------------------------------------------------ *)

Definition tN (x : int) : N := Z.to_N (φ x).

Lemma tN_inj : forall x y : int, tN x = tN y -> x = y.
Proof.
  intros x y H. unfold tN in H. apply int_eq_Z.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia.
Qed.

(* the edge indices of the first p cells of the sorted array *)
Definition Pref (ord : array int) (p : nat) : list N := map tN (seg ord 0 p).

Lemma Pref_snoc : forall ord p,
  Pref ord (S p) = Pref ord p ++ [tN ord.[of_Z (Z.of_nat p)]].
Proof. intros ord p. unfold Pref. simpl. rewrite map_app. reflexivity. Qed.

Lemma Pref_split : forall ord p r, Pref ord (p + r) = Pref ord p ++ map tN (seg ord (Z.of_nat p) r).
Proof. intros ord p r. unfold Pref. rewrite seg_app, map_app. reflexivity. Qed.

(* the root function of a union-find state, on the math side *)
Definition Rm (par rk : array int) (x : N) : N := tN (findr par rk (of_Z (Z.of_N x))).

Lemma union_R : forall nZ par rk rk' a0 b0, UF nZ par rk ->
  (Z.of_N a0 < nZ)%Z -> (Z.of_N b0 < nZ)%Z -> (nZ <= 4194303)%Z ->
  let a := findr par rk (of_Z (Z.of_N a0)) in
  let b := findr par rk (of_Z (Z.of_N b0)) in
  a <> b ->
  (φ (PArray.length rk')) = nZ ->
  (forall x, x <> b -> rk'.[x] = rk.[x]) ->
  ((φ (rk.[b])) <= (φ (rk'.[b])))%Z -> ((φ (rk'.[a])) < (φ (rk'.[b])))%Z ->
  UF nZ par.[a <- b] rk' /\
  forall x, (Z.of_N x < nZ)%Z -> Rm par.[a <- b] rk' x = mergeR (Rm par rk) a0 b0 x.
Proof.
  intros nZ par rk rk' a0 b0 HU Ha0 Hb0 HnZ a b Hab Hl Hrk Hrb Hrab.
  assert (Pa : (φ (of_Z (Z.of_N a0))) = Z.of_N a0) by (apply phi_of_Z; rewrite wB_val; lia).
  assert (Pb : (φ (of_Z (Z.of_N b0))) = Z.of_N b0) by (apply phi_of_Z; rewrite wB_val; lia).
  destruct (findr_spec nZ par rk HU (of_Z (Z.of_N a0)) ltac:(lia)) as [Fa1 Fa2].
  destruct (findr_spec nZ par rk HU (of_Z (Z.of_N b0)) ltac:(lia)) as [Fb1 Fb2].
  fold a in Fa1, Fa2. fold b in Fb1, Fb2.
  destruct (union_spec nZ par rk rk' a b HU Fa1 Fb1 Fa2 Fb2 Hab Hl Hrk Hrb Hrab)
    as [HU' Hf].
  split; [exact HU'|].
  intros x Hx. unfold Rm, mergeR.
  rewrite Hf by (rewrite phi_of_Z by (rewrite wB_val; lia); exact Hx).
  fold a b.
  destruct (findr par rk (of_Z (Z.of_N x)) =? a) eqn:E.
  - rewrite eqb_spec in E. rewrite E.
    destruct (N.eq_dec (tN a) (tN a)); [reflexivity | congruence].
  - assert (E' : findr par rk (of_Z (Z.of_N x)) <> a)
      by (intro F; rewrite F, eqb_refl in E; discriminate).
    destruct (N.eq_dec (tN (findr par rk (of_Z (Z.of_N x)))) (tN a)) as [F|F];
      [apply tN_inj in F; contradiction | reflexivity].
Qed.

Lemma w_bound : forall ws, Forall (fun w => (-20000 <= w <= 20000)%Z) ws ->
  forall k, (-20000 <= get_list_Z ws k <= 20000)%Z.
Proof.
  intros ws Hw k. unfold get_list_Z.
  destruct (Nat.lt_ge_cases (N.to_nat k) (List.length ws)) as [L|L].
  - rewrite Forall_forall in Hw. apply Hw. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma tw_bound : forall ws, Forall (fun w => (-20000 <= w <= 20000)%Z) ws ->
  forall K, (Z.abs (total_weight ws K) <= 20000 * Z.of_nat (List.length K))%Z.
Proof.
  intros ws Hw K. induction K as [|k K IH]; simpl; [lia|].
  pose proof (w_bound ws Hw k). lia.
Qed.

Lemma scan_eq : forall n us vs ws ord m q par rk out cnt cost H,
  scan n us vs ws ord m q par rk out cnt cost H =
  match bdec (q <? m) with
  | left Hq =>
      let e := ord.[q] in
      let a := findr par rk us.[e] in
      let b := findr par rk vs.[e] in
      if a =? b then
        scan n us vs ws ord m (q + 1) par rk out cnt cost
          (Acc_inv H (dec_step m q Hq))
      else
        let ra := rk.[a] in
        let rb := rk.[b] in
        if ra <? rb then
          scan n us vs ws ord m (q + 1) par.[a <- b] rk out.[cnt <- e]
            (cnt + 1) (cost + ws.[e]) (Acc_inv H (dec_step m q Hq))
        else if rb <? ra then
          scan n us vs ws ord m (q + 1) par.[b <- a] rk out.[cnt <- e]
            (cnt + 1) (cost + ws.[e]) (Acc_inv H (dec_step m q Hq))
        else
          scan n us vs ws ord m (q + 1) par.[a <- b] rk.[b <- rb + 1]
            out.[cnt <- e] (cnt + 1) (cost + ws.[e])
            (Acc_inv H (dec_step m q Hq))
  | right _ => if cnt =? n - 1 then Some (cost, out) else None
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Scan.

Variables (n : N) (us vs : list N) (ws : list Z) (xn : int) (xu xv xw ord : array int).
Hypothesis Hvi : valid_input n us vs ws.
Hypothesis Hxn : (φ xn) = Z.of_N n.
Local Notation mZ := (Z.of_nat (List.length us)).
Hypothesis Hlu : (φ (PArray.length xu)) = mZ.
Hypothesis Hxu : forall k : int, ((φ k) < mZ)%Z ->
  (φ (xu.[k])) = Z.of_N (get_list_N us (Z.to_N (φ k))).
Hypothesis Hxv : forall k : int, ((φ k) < mZ)%Z ->
  (φ (xv.[k])) = Z.of_N (get_list_N vs (Z.to_N (φ k))).
Hypothesis Hxw : forall k : int, ((φ k) < mZ)%Z ->
  Sint63.to_Z (xw.[k]) = get_list_Z ws (Z.to_N (φ k)).
Hypothesis Hord_range : forall p : Z, (0 <= p < mZ)%Z -> ((φ (ord.[of_Z p])) < mZ)%Z.
Hypothesis Hord_nodup : NoDup (Pref ord (List.length us)).
Hypothesis Hord_all : forall k, edge_index us k <-> In k (Pref ord (List.length us)).
Hypothesis Hchain : chainL (get_list_Z ws) (-20000) (Pref ord (List.length us)) 20000.

Let Hend : forall k, edge_index us k ->
  vertex n (get_list_N us k) /\ vertex n (get_list_N vs k) := vi_endpoints _ _ _ _ Hvi.
Let Hn : (1 <= n)%N := proj1 (vi_n _ _ _ _ Hvi).
Let Hn2 : (n <= 20000)%N := proj2 (vi_n _ _ _ _ Hvi).
Let Hm : (len us <= 30000)%N := vi_m _ _ _ _ Hvi.

Definition SI (q : int) (par rk out : array int) (cnt cost : int) (K : list N) : Prop :=
  UF (Z.of_N n) par rk /\
  (forall v : int, ((φ v) < Z.of_N n)%Z -> ((φ (rk.[v])) <= (φ q))%Z) /\
  KI n us vs (Rm par rk) K (Pref ord (Z.to_nat (φ q))) /\
  (φ cnt) = Z.of_nat (List.length K) /\
  (φ (PArray.length out)) = (Z.of_N n - 1)%Z /\
  (forall j, (j < List.length K)%nat -> tN (out.[of_Z (Z.of_nat j)]) = nth j K 0%N) /\
  Sint63.to_Z cost = total_weight ws K.

Definition scan_post (o : option (int * array int)) : Prop :=
  match o with
  | None => ~ graph_connected n us vs
  | Some (c, out) => exists K,
      Sint63.to_Z c = total_weight ws K /\
      (φ (PArray.length out)) = Z.of_nat (List.length K) /\
      (forall j, (j < List.length K)%nat -> tN (out.[of_Z (Z.of_nat j)]) = nth j K 0%N) /\
      minimum_spanning_tree n us vs ws (total_weight ws K) K
  end.

(* the facts about edge ord.[q] *)
Lemma edge_facts : forall q : int, ((φ q) < mZ)%Z ->
  let e := ord.[q] in
  ((φ e) < mZ)%Z /\ edge_index us (tN e) /\
  Pref ord (Z.to_nat (φ (q + 1))) = Pref ord (Z.to_nat (φ q)) ++ [tN e] /\
  NoDup (Pref ord (Z.to_nat (φ q)) ++ [tN e]) /\
  (forall x, In x (Pref ord (Z.to_nat (φ q))) -> edge_index us x) /\
  xu.[e] = of_Z (Z.of_N (get_list_N us (tN e))) /\
  xv.[e] = of_Z (Z.of_N (get_list_N vs (tN e))) /\
  (get_list_N us (tN e) < n)%N /\ (get_list_N vs (tN e) < n)%N.
Proof.
  intros q Hq e. pose proof (to_Z_bounded q) as Bq.
  assert (He : ((φ e) < mZ)%Z) by (unfold e; rewrite <- (of_Z_phi q); apply Hord_range; lia).
  assert (Hee : edge_index us (tN e)) by (unfold edge_index, len, tN; lia).
  assert (Hq1 : (φ (q + 1)) = ((φ q) + 1)%Z) by (unfold len in Hm; sia).
  assert (Hsn : Pref ord (Z.to_nat (φ (q + 1))) = Pref ord (Z.to_nat (φ q)) ++ [tN e]).
  { rewrite Hq1. replace (Z.to_nat ((φ q) + 1)) with (S (Z.to_nat (φ q))) by lia.
    rewrite Pref_snoc. rewrite Z2Nat.id by lia. rewrite of_Z_phi. reflexivity. }
  assert (Hsplit : Pref ord (List.length us) =
     Pref ord (Z.to_nat (φ (q + 1))) ++
       map tN (seg ord (Z.of_nat (Z.to_nat (φ (q + 1)))) (List.length us - Z.to_nat (φ (q + 1))))).
  { rewrite <- Pref_split. f_equal. lia. }
  rewrite Hsn in Hsplit.
  assert (Hnd : NoDup (Pref ord (Z.to_nat (φ q)) ++ [tN e]))
    by (rewrite Hsplit in Hord_nodup; eapply NoDup_app_remove_r; exact Hord_nodup).
  destruct (Hend (tN e) Hee) as [Hu Hv]. unfold vertex in Hu, Hv.
  split; [exact He|]. split; [exact Hee|]. split; [exact Hsn|]. split; [exact Hnd|].
  split.
  { intros x Hx. apply Hord_all. rewrite Hsplit. apply in_or_app. left. apply in_or_app.
    left. exact Hx. }
  split; [|split; [|split; assumption]].
  - apply int_eq_Z. rewrite Hxu by exact He.
    rewrite phi_of_Z by (unfold len in Hm; rewrite wB_val; lia). reflexivity.
  - apply int_eq_Z. rewrite Hxv by exact He.
    rewrite phi_of_Z by (unfold len in Hm; rewrite wB_val; lia). reflexivity.
Qed.

Lemma accept_step : forall q par rk out cnt cost K par' rk' a0 b0,
  ((φ q) < mZ)%Z -> SI q par rk out cnt cost K ->
  let e := ord.[q] in
  joins us vs (tN e) a0 b0 -> Rm par rk a0 <> Rm par rk b0 ->
  UF (Z.of_N n) par' rk' ->
  (forall v : int, ((φ v) < Z.of_N n)%Z -> ((φ (rk'.[v])) <= (φ q) + 1)%Z) ->
  (forall x, (Z.of_N x < Z.of_N n)%Z -> Rm par' rk' x = mergeR (Rm par rk) a0 b0 x) ->
  SI (q + 1) par' rk' out.[cnt <- e] (cnt + 1) (cost + xw.[e]) (K ++ [tN e]).
Proof.
  intros q par rk out cnt cost K par' rk' a0 b0 Hq HS e Hj Hab HU' Hrk' HR'.
  destruct HS as (HU & Hrk & HK & Hcnt & Hlo & Hcells & Hcost).
  destruct (edge_facts q Hq) as (He & Hee & Hsn & Hnd & HPe & _ & _ & Hu & Hv).
  fold e in He, Hee, Hsn, Hnd, Hu, Hv.
  assert (Ha0 : (a0 < n)%N) by (destruct Hj as [[E1 E2]|[E1 E2]]; subst; assumption).
  assert (Hb0 : (b0 < n)%N) by (destruct Hj as [[E1 E2]|[E1 E2]]; subst; assumption).
  pose proof (ki_room n us vs Hn _ _ _ a0 b0 HK Ha0 Hb0 Hab) as Hroom.
  assert (Hq1 : (φ (q + 1)) = ((φ q) + 1)%Z) by (unfold len in Hm; sia).
  assert (Hc1 : (φ (cnt + 1)) = ((φ cnt) + 1)%Z) by sia.
  assert (Hcl : (cnt <? PArray.length out) = true) by (rewrite ltb_spec; lia).
  split; [exact HU'|].
  split; [intros v Hv'; rewrite Hq1; apply Hrk'; exact Hv'|].
  split.
  { rewrite Hsn. eapply ki_accept; [exact Hend | exact Hn | exact HK | exact Hnd | exact HPe
      | exact Hee | exact Hj | exact Hab | ]. intros x Hx. apply HR'. lia. }
  split; [rewrite Hc1, Hcnt, length_app; simpl; lia|].
  split; [rewrite alength_set; exact Hlo|].
  split.
  { intros j Hj'. rewrite length_app in Hj'. simpl in Hj'.
    destruct (Nat.eq_dec j (List.length K)) as [Ej|Ej].
    - subst j. replace (of_Z (Z.of_nat (List.length K))) with cnt
        by (apply int_eq_Z; rewrite phi_of_Z by (rewrite wB_val; lia); lia).
      rewrite aget_set_same by exact Hcl.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    - rewrite aget_set_other.
      + rewrite app_nth1 by lia. apply Hcells. lia.
      + intro F. assert ((φ cnt) = (φ (of_Z (Z.of_nat j)))) by (rewrite F; reflexivity).
        rewrite phi_of_Z in H by (rewrite wB_val; lia). lia. }
  { rewrite Sint63.add_spec, Hcost, Hxw by exact He.
    rewrite (total_weight_sumZ ws (K ++ [tN e])), sumZ_app. simpl.
    rewrite <- total_weight_sumZ.
    pose proof (tw_bound ws (vi_weights _ _ _ _ Hvi) K).
    pose proof (w_bound ws (vi_weights _ _ _ _ Hvi) (Z.to_N (φ e))).
    unfold tN. rewrite Z.add_0_r. apply Sint63.cmod_small. rewrite wB_val.
    change (9223372036854775808 / 2)%Z with 4611686018427387904%Z. lia. }
Qed.

Lemma scan_spec : forall z q par rk out cnt cost K
    (H : Acc (Zwf 0) (gap (PArray.length xu) q)),
  gap (PArray.length xu) q = z -> ((φ q) <= mZ)%Z -> SI q par rk out cnt cost K ->
  scan_post (scan xn xu xv xw ord (PArray.length xu) q par rk out cnt cost H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q par rk out cnt cost K H Hz Hqm HS.
  rewrite scan_eq.
  destruct (bdec (q <? PArray.length xu)) as [Hq|Hq].
  - pose proof Hq as Hq'. rewrite ltb_spec, Hlu in Hq'.
    destruct (edge_facts q Hq') as (He & Hee & Hsn & Hnd & HPe & Hus & Hvs & Hu & Hv).
    cbv zeta. rewrite Hus, Hvs.
    set (e := ord.[q]) in *.
    set (a0 := get_list_N us (tN e)) in *.
    set (b0 := get_list_N vs (tN e)) in *.
    pose proof HS as HS'.
    destruct HS as (HU & Hrk & HK & Hcnt & Hlo & Hcells & Hcost).
    assert (Hn' : (Z.of_N n <= 4194303)%Z) by lia.
    assert (Hq1 : (φ (q + 1)) = ((φ q) + 1)%Z) by (unfold len in Hm; sia).
    destruct (findr_spec _ _ _ HU (of_Z (Z.of_N a0))
                ltac:(rewrite phi_of_Z by (rewrite wB_val; lia); lia)) as [Fa1 Fa2].
    destruct (findr_spec _ _ _ HU (of_Z (Z.of_N b0))
                ltac:(rewrite phi_of_Z by (rewrite wB_val; lia); lia)) as [Fb1 Fb2].
    set (a := findr par rk (of_Z (Z.of_N a0))) in *.
    set (b := findr par rk (of_Z (Z.of_N b0))) in *.
    pose proof HU as [Hlp [Hlr _]].
    destruct (a =? b) eqn:Eab.
    + rewrite eqb_spec in Eab.
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hq | reflexivity | lia | ].
      split; [exact HU|].
      split; [intros v Hv'; rewrite Hq1; specialize (Hrk v Hv'); lia|].
      split; [|split; [exact Hcnt|split; [exact Hlo|split; [exact Hcells|exact Hcost]]]].
      rewrite Hsn. apply (ki_reject n us vs Hend Hn); [exact HK | exact Hnd |].
      unfold Rm. fold a0 b0 a b. rewrite Eab. reflexivity.
    + assert (Hab : a <> b) by (intro F; rewrite F, eqb_refl in Eab; discriminate).
      assert (HabR : Rm par rk a0 <> Rm par rk b0)
        by (unfold Rm; fold a b; intro F; apply tN_inj in F; contradiction).
      destruct (rk.[a] <? rk.[b]) eqn:E1.
      * rewrite ltb_spec in E1.
        destruct (union_R (Z.of_N n) par rk rk a0 b0 HU ltac:(lia) ltac:(lia) Hn' Hab
                    Hlr (fun _ _ => eq_refl) (Z.le_refl _) E1) as [HU' HR'].
        eapply IH; [rewrite <- Hz; apply dec_step; exact Hq | reflexivity | lia | ].
        apply (accept_step q par rk out cnt cost K _ _ a0 b0 Hq' HS');
          [left; split; reflexivity | exact HabR | exact HU' | | exact HR'].
        intros v Hv'. specialize (Hrk v Hv'). lia.
      * destruct (rk.[b] <? rk.[a]) eqn:E2.
        -- rewrite ltb_spec in E2.
           destruct (union_R (Z.of_N n) par rk rk b0 a0 HU ltac:(lia) ltac:(lia) Hn'
                       (not_eq_sym Hab) Hlr (fun _ _ => eq_refl) (Z.le_refl _) E2)
             as [HU' HR'].
           eapply IH; [rewrite <- Hz; apply dec_step; exact Hq | reflexivity | lia | ].
           apply (accept_step q par rk out cnt cost K _ _ b0 a0 Hq' HS');
             [right; split; reflexivity | exact (not_eq_sym HabR) | exact HU' | | exact HR'].
           intros v Hv'. specialize (Hrk v Hv'). lia.
        -- rewrite <- Bool.not_true_iff_false, ltb_spec in E1, E2.
           assert (Hbl : (b <? PArray.length rk) = true) by (rewrite ltb_spec; lia).
           assert (Hrb : ((φ (rk.[b])) <= (φ q))%Z) by (apply Hrk; exact Fb1).
           assert (Hrb1 : (φ (rk.[b] + 1)) = ((φ (rk.[b])) + 1)%Z) by (unfold len in Hm; sia).
           assert (C1 : (φ (PArray.length rk.[b <- rk.[b] + 1])) = Z.of_N n)
             by (rewrite alength_set; exact Hlr).
           assert (C2 : forall x, x <> b -> rk.[b <- rk.[b] + 1].[x] = rk.[x])
             by (intros x Hx; apply aget_set_other; auto).
           assert (C3 : ((φ (rk.[b])) <= (φ (rk.[b <- (rk.[b] + 1)%uint63].[b])))%Z)
             by (rewrite aget_set_same by exact Hbl; lia).
           assert (C4 : ((φ (rk.[b <- (rk.[b] + 1)%uint63].[a])) < (φ (rk.[b <- (rk.[b] + 1)%uint63].[b])))%Z)
             by (rewrite aget_set_same by exact Hbl;
                 rewrite aget_set_other by (apply not_eq_sym; exact Hab); lia).
           destruct (union_R (Z.of_N n) par rk rk.[b <- rk.[b] + 1] a0 b0 HU
                       ltac:(lia) ltac:(lia) Hn' Hab C1 C2 C3 C4)
             as [HU' HR'].
           eapply IH; [rewrite <- Hz; apply dec_step; exact Hq | reflexivity | lia | ].
           apply (accept_step q par rk out cnt cost K _ _ a0 b0 Hq' HS');
             [left; split; reflexivity | exact HabR | exact HU' | | exact HR'].
           intros v Hv'. rewrite aget_set by exact Hbl.
           destruct (b =? v); [lia|]. specialize (Hrk v Hv'). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hlu in Hq.
    destruct HS as (HU & Hrk & HK & Hcnt & Hlo & Hcells & Hcost).
    replace (Z.to_nat (φ q)) with (List.length us) in HK by lia.
    assert (Hxn1 : (φ (xn - 1)) = (Z.of_N n - 1)%Z) by sia.
    destruct (cnt =? xn - 1) eqn:Ec.
    + rewrite eqb_spec in Ec. simpl. exists K.
      assert (HlK : Z.of_nat (List.length K) = (Z.of_N n - 1)%Z)
        by (rewrite <- Hcnt, Ec; exact Hxn1).
      split; [exact Hcost|]. split; [lia|]. split; [exact Hcells|].
      apply (ki_some n us vs ws Hn _ K _ HK Hord_nodup Hord_all Hchain HlK).
    + simpl. apply (ki_none n us vs Hn _ K _ HK).
      * intros k Hk. apply Hord_all. exact Hk.
      * intro F. rewrite <- Bool.not_true_iff_false, eqb_spec in Ec. apply Ec.
        apply int_eq_Z. lia.
Qed.

End Scan.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

(* Reading an in-bounds cell of an array representing l. *)
Lemma repr_get_uint : forall (x : array uint) (l : list N), repr x l ->
  forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  (φ (x.[i])) = Z.of_N (get_list_N l (Z.to_N (φ i))).
Proof.
  intros x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  unfold get_list_N. rewrite Z_N_nat. erewrite nth_error_nth by exact Hm.
  rewrite <- Hr. pose proof (to_Z_bounded (x.[i])). lia.
Qed.

Lemma repr_get_sint : forall (x : array sint) (l : list Z), repr x l ->
  forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  Sint63.to_Z (x.[i]) = get_list_Z l (Z.to_N (φ i)).
Proof.
  intros x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  unfold get_list_Z. rewrite Z_N_nat. erewrite nth_error_nth by exact Hm.
  exact Hr.
Qed.

Lemma repr_len : forall {M} `{Repr int M} (x : array int) (l : list M), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros M R x l [Hl _]. symmetry. exact Hl. Qed.

Lemma seg_iota : forall (a : array int) (m : int), (forall k : int, ((φ k) < (φ m))%Z -> a.[k] = k) ->
  forall p, (Z.of_nat p <= (φ m))%Z ->
  map tN (seg a 0 p) = map N.of_nat (seq 0 p).
Proof.
  intros a m Ha p. induction p as [|p IH]; intros Hp; [reflexivity|].
  simpl seg. rewrite seq_S, !map_app, IH by lia. f_equal. simpl.
  rewrite Ha by (rewrite phi_of_Z by (pose proof (to_Z_bounded m); lia); lia).
  unfold tN. rewrite phi_of_Z by (pose proof (to_Z_bounded m); lia). f_equal. lia.
Qed.

Lemma ki_start : forall n us vs R, (forall x, (x < n)%N -> R x = x) ->
  KI n us vs R [] [].
Proof.
  intros n us vs R HR. constructor.
  - intros x Hx. rewrite !HR by (try rewrite HR; assumption). split; [exact Hx | reflexivity].
  - rewrite (rc_ext R (fun x => x)) by (intros x Hx; apply HR; lia).
    rewrite rc_id. simpl. lia.
  - intros e [].
  - intros x Hx. rewrite HR by exact Hx. apply linked_here.
  - constructor.
  - intros x [].
  - intros T _ p _. rewrite firstn_nil. simpl. lia.
Qed.

Lemma post_repr : forall n us vs ws (o : option (int * array int)),
  scan_post n us vs ws o ->
  exists r : option (Z * list N),
    repr (o : option (sint * array uint)) r /\ mst_spec n us vs ws r.
Proof.
  intros n us vs ws o Hpost. destruct o as [[c out]|].
  - destruct Hpost as (K & Hc & Hlo & Hcells & Hmst).
    exists (Some (total_weight ws K, K)). split; [|exact Hmst].
    split; [exact Hc|]. split.
    + exact (eq_sym Hlo).
    + intros k Hk. exists (nth k K 0%N). split; [apply nth_error_nth'; exact Hk|].
      exact (Hcells k Hk).
  - exists None. split; [exact I | exact Hpost].
Qed.

Lemma mst_impl_correct :
  forall (n : N) (us vs : list N) (ws : list Z)
         (xn : uint) (xu xv : array uint) (xw : array sint),
  valid_input n us vs ws ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws ->
  exists r : option (Z * list N),
    repr (mst_impl xn xu xv xw : option (sint * array uint)) r /\ mst_spec n us vs ws r.
Proof.
  intros n us vs ws xn xu xv xw Hvi Rn Ru Rv Rw.
  pose proof Hvi as [[Hn1 Hn2] Hm Hlv Hlw Hend Hws].
  unfold len in Hm, Hlv, Hlw.
  assert (Hxn : (φ xn) = Z.of_N n).
  { unfold repr, repr_uint in Rn. pose proof (to_Z_bounded xn). lia. }
  pose proof (repr_len xu us Ru) as Lu.
  pose proof (repr_len xv vs Rv) as Lv.
  pose proof (repr_len xw ws Rw) as Lw.
  assert (Hxu : forall k : int, ((φ k) < Z.of_nat (List.length us))%Z ->
     (φ (xu.[k])) = Z.of_N (get_list_N us (Z.to_N (φ k))))
    by (intros k Hk; apply repr_get_uint; assumption).
  assert (Hxv : forall k : int, ((φ k) < Z.of_nat (List.length us))%Z ->
     (φ (xv.[k])) = Z.of_N (get_list_N vs (Z.to_N (φ k))))
    by (intros k Hk; apply repr_get_uint; [assumption | lia]).
  assert (Hxw : forall k : int, ((φ k) < Z.of_nat (List.length us))%Z ->
     Sint63.to_Z (xw.[k]) = get_list_Z ws (Z.to_N (φ k)))
    by (intros k Hk; apply repr_get_sint; [assumption | lia]).
  set (m := PArray.length xu).
  assert (Lu' : (φ m) = Z.of_nat (List.length us)) by exact Lu.
  assert (Hmb : ((φ m) <= 4194303)%Z) by exact (alength_bound xu).
  destruct (sort_edges_spec xw m Hmb) as (Hol & Hoperm & Hosort).
  set (ord := sort_edges xw m) in *.
  destruct (iota_spec m Hmb) as [_ Hiota].
  set (mn := List.length us).
  assert (Hmn : Z.to_nat (φ m) = mn) by (unfold m, mn; lia).
  rewrite Hmn in Hoperm.
  assert (HP : Permutation (Pref ord mn) (map N.of_nat (seq 0 mn))).
  { unfold Pref. rewrite <- (seg_iota (iota m) m Hiota mn ltac:(unfold m, mn; lia)).
    apply Permutation_map. exact Hoperm. }
  assert (Hord_nodup : NoDup (Pref ord mn)).
  { apply (Permutation_NoDup (Permutation_sym HP)).
    apply Injective_map_NoDup; [intros x y E; lia | apply seq_NoDup]. }
  assert (Hord_all : forall k, edge_index us k <-> In k (Pref ord mn)).
  { intros k. unfold edge_index, len. split; intros Hk.
    - apply (Permutation_in _ (Permutation_sym HP)). apply in_map_iff.
      exists (N.to_nat k). split; [lia|]. apply in_seq. fold mn. lia.
    - apply (Permutation_in _ HP) in Hk. apply in_map_iff in Hk.
      destruct Hk as (j & Ej & Hj). apply in_seq in Hj. fold mn. lia. }
  assert (Hnth : forall i, (i < mn)%nat -> nth i (Pref ord mn) 0%N = tN (ord.[of_Z (Z.of_nat i)])).
  { intros i Hi. unfold Pref. change 0%N with (tN 0). rewrite map_nth.
    rewrite nth_seg by exact Hi. reflexivity. }
  assert (HlP : List.length (Pref ord mn) = mn)
    by (unfold Pref; rewrite length_map, seg_length; reflexivity).
  assert (Hord_range : forall p : Z, (0 <= p < Z.of_nat mn)%Z ->
            ((φ (ord.[of_Z p])) < Z.of_nat mn)%Z).
  { intros p Hp.
    assert (Hin : In (tN (ord.[of_Z p])) (Pref ord mn)).
    { replace p with (Z.of_nat (Z.to_nat p)) by lia. rewrite <- Hnth by lia.
      apply nth_In. rewrite HlP. lia. }
    apply Hord_all in Hin. unfold edge_index, len, tN in Hin. fold mn in Hin.
    pose proof (to_Z_bounded (ord.[of_Z p])). lia. }
  assert (Hchain : chainL (get_list_Z ws) (-20000) (Pref ord mn) 20000).
  { apply chain_of_sorted.
    - intros i Hi. rewrite HlP in Hi. rewrite !Hnth by lia.
      pose proof (Hord_range (Z.of_nat i) ltac:(lia)) as R1.
      pose proof (Hord_range (Z.of_nat (S i)) ltac:(lia)) as R2.
      unfold tN. rewrite <- !Hxw by lia.
      pose proof (Hosort (Z.of_nat i) ltac:(lia) ltac:(unfold m in *; lia)) as S1.
      unfold keyf in S1. replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia. exact S1.
    - intros x _. pose proof (w_bound ws Hws x). lia.
    - destruct (Pref ord mn); [exact I|]. pose proof (w_bound ws Hws n0). lia.
    - lia. }
  (* the initial state *)
  assert (Hnb : ((φ xn) <= 4194303)%Z) by lia.
  destruct (iota_spec xn Hnb) as [Hpl Hpar].
  assert (Hxn1 : (φ (xn - 1)) = (Z.of_N n - 1)%Z) by sia.
  assert (HS : SI n us vs ws ord 0 (iota xn) (PArray.make xn 0) (PArray.make (xn - 1) 0)
                 0 0 []).
  { split.
    { split; [rewrite Hpl; exact Hxn|]. split; [rewrite alength_make_small by lia; exact Hxn|].
      intros v Hv. rewrite Hpar by lia. split; [lia | intros F; contradiction]. }
    split; [intros v _; rewrite aget_make; change (φ 0) with 0%Z; lia|].
    split.
    { apply ki_start. intros x Hx. unfold Rm.
      rewrite findr_root.
      - unfold tN. rewrite phi_of_Z by (rewrite wB_val; lia). lia.
      - apply Hpar. rewrite phi_of_Z by (rewrite wB_val; lia). lia. }
    split; [reflexivity|].
    split; [rewrite alength_make_small by lia; exact Hxn1|].
    split; [intros j Hj; simpl in Hj; lia | reflexivity]. }
  pose proof (scan_spec n us vs ws xn xu xv xw ord Hvi Hxn Lu Hxu Hxv Hxw
                Hord_range Hord_nodup Hord_all Hchain _ 0 _ _ _ 0 0 []
                (Zwf_well_founded 0 (gap m 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) HS) as Hpost.
  unfold mst_impl. exact (post_repr n us vs ws _ Hpost).
Qed.

Definition mst_correct :
  forall (n : N) (us vs : list N) (ws : list Z)
         (xn : uint) (xu xv : array uint) (xw : array sint),
  valid_input n us vs ws ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws ->
  exists r : option (Z * list N),
    repr (mst xn xu xv xw) r /\ mst_spec n us vs ws r
  := mst_impl_correct.
