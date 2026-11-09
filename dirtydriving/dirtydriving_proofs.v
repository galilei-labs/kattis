(* Correctness proofs for dirtydriving_implem.v. *)
(* Implementation of dirtydriving (dirtydriving.spec).

   Code.  [dirtydriving p d] sorts the distances ascending with a top-down
   merge sort on flat arrays (the input array, threaded linearly, and one
   scratch buffer of length n: each merge writes the two sorted halves of
   [lo, hi) into the buffer, then copies [lo, hi) back), then makes one
   linear pass over the sorted array s computing
     max (0, max_k (p * (k + 1) + s.[0] - s.[k])),
   the least D with p * (k + 1) + s.[0] <= D + s.[k] for every k: in the
   sorted order the car s.[k] has exactly k cars between, and s.[0] is the
   car directly in front.  Everything is Uint63 arithmetic (the values stay
   below 20 * 100001 + 10^7).

   Termination: every loop and the sort recurse structurally on an erased
   [Acc (Zwf 0) (gap _ _)] proof, as in template/polymul1. *)

From Dirtydriving.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Dirtydriving Require Export dirtydriving_implem.
Open Scope uint63_scope.
Open Scope array_scope.


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

Lemma of_Z_small : forall z : Z, (0 <= z <= 4194303)%Z -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. Qed.

Lemma neq_of_Z : forall u k : int, (φ u) <> (φ k) -> k <> u.
Proof. intros u k H E. subst. apply H. reflexivity. Qed.

Lemma split_ok_false : forall lo hi, split_ok lo hi = false ->
  ((φ lo) <= (φ hi))%Z -> ((φ hi) <= (φ lo) + 1)%Z.
Proof.
  intros lo hi H Hle. unfold split_ok in H.
  destruct (lo <? hi) eqn:E1; simpl in H.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in H.
    assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
    rewrite E in H. change (φ 1) with 1%Z in H. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E1. lia.
Qed.

Lemma merge_loop_eq : forall a t mid hi i j k H,
  merge_loop a t mid hi i j k H =
  match bdec (k <? hi) with
  | left Hk =>
      if take_left a mid hi i j then
        merge_loop a t.[k <- a.[i]] mid hi (i + 1) j (k + 1)
          (Acc_inv H (dec_step hi k Hk))
      else
        merge_loop a t.[k <- a.[j]] mid hi i (j + 1) (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma copy_loop_eq : forall src dst hi k H,
  copy_loop src dst hi k H =
  match bdec (k <? hi) with
  | left Hk => copy_loop src dst.[k <- src.[k]] hi (k + 1)
                 (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma msort_eq : forall a t lo hi H,
  msort a t lo hi H =
  match bdec (split_ok lo hi) with
  | left Hs =>
      let (a1, t1) := msort a t lo (midp lo hi) (Acc_inv H (dec_l lo hi Hs)) in
      let (a2, t2) := msort a1 t1 (midp lo hi) hi (Acc_inv H (dec_r lo hi Hs)) in
      let t3 := merge_loop a2 t2 (midp lo hi) hi lo (midp lo hi) lo
                  (Zwf_well_founded 0 (gap hi lo)) in
      (copy_loop t3 a2 hi lo (Zwf_well_founded 0 (gap hi lo)), t3)
  | right _ => (a, t)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma max_loop_eq : forall s p s0 n k acc H,
  max_loop s p s0 n k acc H =
  match bdec (k <? n) with
  | left Hk =>
      let v := need p s0 s.[k] k in
      max_loop s p s0 n (k + 1) (if acc <? v then v else acc)
        (Acc_inv H (dec_step n k Hk))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Segments of an array, as lists of Z                                 *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Definition seg (a : array int) (lo hi : Z) : list Z :=
  map (fun k => (φ (a.[of_Z (Z.of_nat k)]))) (seq (Z.to_nat lo) (Z.to_nat (hi - lo))).

Definition sorted (a : array int) (lo hi : Z) : Prop :=
  forall i j : int, lo <= (φ i) -> (φ i) <= (φ j) -> (φ j) < hi -> (φ (a.[i])) <= (φ (a.[j])).

Lemma seg_ext : forall a b lo hi, 0 <= lo -> hi <= 4194303 ->
  (forall k : int, lo <= (φ k) < hi -> a.[k] = b.[k]) -> seg a lo hi = seg b lo hi.
Proof.
  intros a b lo hi H0 H1 H. unfold seg. apply map_ext_in.
  intros k Hk. rewrite in_seq in Hk. f_equal. apply H.
  rewrite of_Z_small by lia. lia.
Qed.

Lemma seg_split : forall a lo mid hi, 0 <= lo <= mid -> mid <= hi ->
  seg a lo hi = seg a lo mid ++ seg a mid hi.
Proof.
  intros a lo mid hi H1 H2. unfold seg. rewrite <- map_app. f_equal.
  replace (Z.to_nat (hi - lo)) with (Z.to_nat (mid - lo) + Z.to_nat (hi - mid))%nat
    by lia.
  rewrite seq_app. f_equal. f_equal. lia.
Qed.

Lemma seg_nil : forall a lo hi, hi <= lo -> seg a lo hi = [].
Proof.
  intros a lo hi H. unfold seg. replace (Z.to_nat (hi - lo)) with 0%nat by lia.
  reflexivity.
Qed.

Lemma seg_snoc : forall a (lo : Z) (k : int), 0 <= lo <= (φ k) ->
  seg a lo ((φ k) + 1) = seg a lo (φ k) ++ [(φ (a.[k]))].
Proof.
  intros a lo k H. rewrite (seg_split a lo (φ k) ((φ k) + 1)) by lia. f_equal.
  unfold seg. replace (Z.to_nat ((φ k) + 1 - (φ k))) with 1%nat by lia. simpl.
  rewrite Z2Nat.id by lia. rewrite of_to_Z. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The copy loop                                                       *)
(* ------------------------------------------------------------------ *)

Lemma copy_loop_spec : forall (src : array int) (hi : int) (z : Z) (k : int)
  (dst : array int) (H : Acc (Zwf 0) (gap hi k)),
  gap hi k = z -> (φ hi) <= (φ (PArray.length dst)) ->
  PArray.length (copy_loop src dst hi k H) = PArray.length dst /\
  forall u : int,
    ((φ k) <= (φ u) < (φ hi) -> (copy_loop src dst hi k H).[u] = src.[u]) /\
    (~ ((φ k) <= (φ u) < (φ hi)) -> (copy_loop src dst hi k H).[u] = dst.[u]).
Proof.
  intros src hi z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k dst H Hz Hl.
  rewrite copy_loop_eq.
  destruct (bdec (k <? hi)%uint63) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hk1 : (φ ((k + 1)%uint63)) = (φ k) + 1) by sia.
    destruct (IH (gap hi ((k + 1)%uint63)) ltac:(rewrite <- Hz; apply dec_step; exact Hk)
                ((k + 1)%uint63) dst.[k <- src.[k]] (Acc_inv H (dec_step hi k Hk))
                eq_refl ltac:(rewrite alength_set; exact Hl)) as [IL IC].
    split; [rewrite IL, alength_set; reflexivity|].
    intros u. rewrite Hk1 in IC. destruct (IC u) as [IC1 IC2]. split.
    + intros Hu. destruct (Z.eq_dec (φ u) (φ k)) as [E | E].
      * assert (u = k) by (apply to_Z_inj; exact E). subst u.
        rewrite IC2 by lia. apply aget_set_same. rewrite ltb_spec. lia.
      * apply IC1. lia.
    + intros Hu. rewrite IC2 by lia. apply aget_set_other.
      apply neq_of_Z. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    split; [reflexivity|]. intros u. split; [lia | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* The merge loop                                                      *)
(* ------------------------------------------------------------------ *)

Lemma take_left_true : forall a mid hi i j, take_left a mid hi i j = true ->
  (φ i) < (φ mid) /\ ((φ j) < (φ hi) -> (φ (a.[i])) <= (φ (a.[j]))).
Proof.
  intros a mid hi i j H. unfold take_left in H.
  destruct (i <? mid)%uint63 eqn:E1; [|discriminate]. rewrite ltb_spec in E1.
  split; [exact E1|]. intros Hj.
  destruct (j <? hi)%uint63 eqn:E2.
  - rewrite leb_spec in H. exact H.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E2. lia.
Qed.

Lemma take_left_false : forall a mid hi i j, take_left a mid hi i j = false ->
  (φ i) < (φ mid) -> (φ j) < (φ hi) /\ (φ (a.[j])) < (φ (a.[i])).
Proof.
  intros a mid hi i j H Hi. unfold take_left in H.
  assert (E1 : (i <? mid)%uint63 = true) by (rewrite ltb_spec; exact Hi).
  rewrite E1 in H.
  destruct (j <? hi)%uint63 eqn:E2; [|discriminate]. rewrite ltb_spec in E2.
  rewrite <- Bool.not_true_iff_false, leb_spec in H. lia.
Qed.

Section Merge.
  Variables (a : array int) (lo mid hi : int).
  Hypothesis Hbounds : 0 <= (φ lo) <= (φ mid) /\ (φ mid) <= (φ hi) <= (φ (PArray.length a)).
  Hypothesis Hsl : sorted a (φ lo) (φ mid).
  Hypothesis Hsr : sorted a (φ mid) (φ hi).

  Lemma merge_loop_spec : forall (z : Z) (i j k : int) (t : array int)
    (H : Acc (Zwf 0) (gap hi k)),
    gap hi k = z ->
    (φ lo) <= (φ i) <= (φ mid) -> (φ mid) <= (φ j) <= (φ hi) -> (φ k) = (φ i) + (φ j) - (φ mid) ->
    PArray.length t = PArray.length a ->
    Permutation (seg t (φ lo) (φ k)) (seg a (φ lo) (φ i) ++ seg a (φ mid) (φ j)) ->
    sorted t (φ lo) (φ k) ->
    (forall u : int, (φ lo) <= (φ u) < (φ k) ->
       ((φ i) < (φ mid) -> (φ (t.[u])) <= (φ (a.[i]))) /\ ((φ j) < (φ hi) -> (φ (t.[u])) <= (φ (a.[j])))) ->
    PArray.length (merge_loop a t mid hi i j k H) = PArray.length a /\
    Permutation (seg (merge_loop a t mid hi i j k H) (φ lo) (φ hi))
                (seg a (φ lo) (φ mid) ++ seg a (φ mid) (φ hi)) /\
    sorted (merge_loop a t mid hi i j k H) (φ lo) (φ hi).
  Proof.
    pose proof (alength_bound a) as Ba.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i j k t H Hz Hi Hj Hk Hlt Hperm Hsort Hbnd.
    rewrite merge_loop_eq.
    destruct (bdec (k <? hi)%uint63) as [Hkh | Hkh].
    - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
      assert (Hk1 : (φ ((k + 1)%uint63)) = (φ k) + 1) by sia.
      assert (Hkl : (k <? PArray.length t)%uint63 = true) by (rewrite ltb_spec; lia).
      assert (Hdec : Zwf 0 (gap hi ((k + 1)%uint63)) z) by (rewrite <- Hz; apply dec_step; exact Hkh).
      destruct (take_left a mid hi i j) eqn:Etl.
      + destruct (take_left_true _ _ _ _ _ Etl) as [Him Hij].
        assert (Hi1 : (φ ((i + 1)%uint63)) = (φ i) + 1) by sia.
        apply (IH _ Hdec); [reflexivity | lia | lia | lia | rewrite alength_set; exact Hlt | | |].
        * rewrite Hk1, Hi1, seg_snoc by lia. rewrite seg_snoc by lia.
          rewrite aget_set_same by exact Hkl.
          rewrite (seg_ext t.[k <- a.[i]] t) by
            (lia || (intros u Hu; apply aget_set_other; apply neq_of_Z; lia)).
          rewrite <- app_assoc. simpl.
          eapply perm_trans; [apply Permutation_app_tail; exact Hperm|].
          rewrite <- app_assoc. apply Permutation_app_head.
          apply Permutation_sym, Permutation_cons_append.
        * intros u v Hu Huv Hv. rewrite Hk1 in Hv.
          destruct (Z.eq_dec (φ v) (φ k)) as [Ev | Ev].
          -- assert (v = k) by (apply to_Z_inj; exact Ev). subst v.
             rewrite (aget_set_same t k) by exact Hkl.
             destruct (Z.eq_dec (φ u) (φ k)) as [Eu | Eu].
             ++ assert (u = k) by (apply to_Z_inj; exact Eu). subst u.
                rewrite (aget_set_same t k) by exact Hkl. lia.
             ++ rewrite aget_set_other by (apply neq_of_Z; lia).
                apply (proj1 (Hbnd u ltac:(lia))). exact Him.
          -- rewrite !aget_set_other by (apply neq_of_Z; lia).
             apply Hsort; lia.
        * intros u Hu. rewrite Hk1 in Hu.
          assert (Hti : (φ (t.[k <- a.[i]].[u])) <= (φ (a.[i]))).
          { destruct (Z.eq_dec (φ u) (φ k)) as [Eu | Eu].
            - assert (u = k) by (apply to_Z_inj; exact Eu). subst u.
              rewrite (aget_set_same t k) by exact Hkl. lia.
            - rewrite aget_set_other by (apply neq_of_Z; lia).
              apply (proj1 (Hbnd u ltac:(lia))). exact Him. }
          split.
          -- intros Hi1m. rewrite Hi1 in Hi1m.
             assert ((φ (a.[i])) <= (φ (a.[(i + 1)%uint63]))) by (apply Hsl; lia). lia.
          -- intros Hjh.
             destruct (Z.eq_dec (φ u) (φ k)) as [Eu | Eu].
             ++ assert (u = k) by (apply to_Z_inj; exact Eu). subst u.
                rewrite (aget_set_same t k) by exact Hkl. apply Hij. exact Hjh.
             ++ rewrite aget_set_other by (apply neq_of_Z; lia).
                apply (proj2 (Hbnd u ltac:(lia))). exact Hjh.
      + assert (Hjh : (φ j) < (φ hi) /\ ((φ i) < (φ mid) -> (φ (a.[j])) < (φ (a.[i])))).
        { destruct (Z.lt_ge_cases (φ i) (φ mid)) as [Him | Him].
          - destruct (take_left_false _ _ _ _ _ Etl Him) as [A B].
            split; [exact A | intros _; exact B].
          - split; [lia | intros; lia]. }
        destruct Hjh as [Hjh Hji].
        assert (Hj1 : (φ ((j + 1)%uint63)) = (φ j) + 1) by sia.
        apply (IH _ Hdec); [reflexivity | lia | lia | lia | rewrite alength_set; exact Hlt | | |].
        * rewrite Hk1, Hj1, seg_snoc by lia. rewrite seg_snoc by lia.
          rewrite aget_set_same by exact Hkl.
          rewrite (seg_ext t.[k <- a.[j]] t) by
            (lia || (intros u Hu; apply aget_set_other; apply neq_of_Z; lia)).
          rewrite app_assoc. apply Permutation_app_tail. exact Hperm.
        * intros u v Hu Huv Hv. rewrite Hk1 in Hv.
          destruct (Z.eq_dec (φ v) (φ k)) as [Ev | Ev].
          -- assert (v = k) by (apply to_Z_inj; exact Ev). subst v.
             rewrite (aget_set_same t k) by exact Hkl.
             destruct (Z.eq_dec (φ u) (φ k)) as [Eu | Eu].
             ++ assert (u = k) by (apply to_Z_inj; exact Eu). subst u.
                rewrite (aget_set_same t k) by exact Hkl. lia.
             ++ rewrite aget_set_other by (apply neq_of_Z; lia).
                apply (proj2 (Hbnd u ltac:(lia))). exact Hjh.
          -- rewrite !aget_set_other by (apply neq_of_Z; lia).
             apply Hsort; lia.
        * intros u Hu. rewrite Hk1 in Hu.
          assert (Htj : (φ (t.[k <- a.[j]].[u])) <= (φ (a.[j]))).
          { destruct (Z.eq_dec (φ u) (φ k)) as [Eu | Eu].
            - assert (u = k) by (apply to_Z_inj; exact Eu). subst u.
              rewrite (aget_set_same t k) by exact Hkl. lia.
            - rewrite aget_set_other by (apply neq_of_Z; lia).
              apply (proj2 (Hbnd u ltac:(lia))). exact Hjh. }
          split.
          -- intros Him. specialize (Hji Him). lia.
          -- intros Hj1h. rewrite Hj1 in Hj1h.
             assert ((φ (a.[j])) <= (φ (a.[(j + 1)%uint63]))) by (apply Hsr; lia). lia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkh.
      assert (Ei : (φ i) = (φ mid)) by lia. assert (Ej : (φ j) = (φ hi)) by lia.
      rewrite Ei, Ej in Hperm. replace (φ k) with (φ hi) in Hperm, Hsort by lia.
      split; [exact Hlt|]. split; [exact Hperm | exact Hsort].
  Qed.
End Merge.

(* ------------------------------------------------------------------ *)
(* The merge sort                                                      *)
(* ------------------------------------------------------------------ *)

Lemma msort_spec : forall (z : Z) (lo hi : int) (a t : array int)
  (H : Acc (Zwf 0) (gap hi lo)) (a' t' : array int),
  gap hi lo = z ->
  0 <= (φ lo) <= (φ hi) -> (φ hi) <= (φ (PArray.length a)) ->
  PArray.length t = PArray.length a ->
  msort a t lo hi H = (a', t') ->
  PArray.length a' = PArray.length a /\ PArray.length t' = PArray.length a /\
  (forall u : int, (φ u) < (φ (PArray.length a)) -> (φ u) < (φ lo) \/ (φ hi) <= (φ u) ->
     a'.[u] = a.[u]) /\
  Permutation (seg a' (φ lo) (φ hi)) (seg a (φ lo) (φ hi)) /\
  sorted a' (φ lo) (φ hi).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi a t H a' t' Hz Hlh Hha Hta Hrun.
  pose proof (alength_bound a) as Ba.
  rewrite msort_eq in Hrun.
  destruct (bdec (split_ok lo hi)) as [Hs | Hs].
  - destruct (split_ok_spec lo hi Hs) as [Hlt Hmid].
    lazymatch type of Hrun with
    | context [msort a t lo _ ?A1] => destruct (msort a t lo _ A1) as [a1 t1] eqn:E1
    end.
    lazymatch type of Hrun with
    | context [msort a1 t1 _ hi ?A2] => destruct (msort a1 t1 _ hi A2) as [a2 t2] eqn:E2
    end.
    set (mid := midp lo hi) in *.
    assert (Hm : (φ lo) < (φ mid) < (φ hi)) by (rewrite Hmid; Z.to_euclidean_division_equations; lia).
    destruct (IH (gap mid lo) ltac:(rewrite <- Hz; apply dec_l; exact Hs)
                lo mid a t _ a1 t1 eq_refl ltac:(lia) ltac:(lia) Hta E1)
      as (L1 & T1 & F1 & P1 & S1).
    destruct (IH (gap hi mid) ltac:(rewrite <- Hz; apply dec_r; exact Hs)
                mid hi a1 t1 _ a2 t2 eq_refl ltac:(lia) ltac:(rewrite L1; lia)
                ltac:(rewrite T1, L1; reflexivity) E2)
      as (L2 & T2 & F2 & P2 & S2).
    rewrite L1 in L2, T2, F2.
    assert (Hs2l : sorted a2 (φ lo) (φ mid)).
    { intros u v Hu Huv Hv. rewrite !F2 by lia. apply S1; lia. }
    destruct (merge_loop_spec a2 lo mid hi ltac:(rewrite L2; lia) Hs2l S2
                _ lo mid lo t2 (Zwf_well_founded 0 (gap hi lo)) eq_refl
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite T2, L2; reflexivity))
      as (L3 & P3 & S3).
    1,2,3: first [ rewrite !seg_nil by lia; apply perm_nil
                 | intros u v Hu Huv Hv; lia
                 | intros u Hu; lia ].
    + cbv beta iota zeta in Hrun.
      injection Hrun as <- <-.
      destruct (copy_loop_spec (merge_loop a2 t2 mid hi lo mid lo
                  (Zwf_well_founded 0 (gap hi lo))) hi _ lo a2
                  (Zwf_well_founded 0 (gap hi lo)) eq_refl ltac:(rewrite L2; lia))
        as [L4 C4].
      set (t3 := merge_loop a2 t2 mid hi lo mid lo (Zwf_well_founded 0 (gap hi lo))) in *.
      set (a3 := copy_loop t3 a2 hi lo (Zwf_well_founded 0 (gap hi lo))) in *.
      assert (E3 : seg a3 (φ lo) (φ hi) = seg t3 (φ lo) (φ hi)).
      { apply seg_ext; [lia | lia |]. intros u Hu. apply (proj1 (C4 u)). exact Hu. }
      split; [rewrite L4, L2; reflexivity|].
      split; [rewrite L3, L2; reflexivity|].
      split; [|split].
      * intros u Hu Hout. rewrite (proj2 (C4 u)) by lia.
        rewrite F2 by lia. apply F1; lia.
      * rewrite E3. eapply perm_trans; [exact P3|].
        rewrite (seg_split a (φ lo) (φ mid) (φ hi)) by lia.
        rewrite (seg_ext a2 a1 (φ lo) (φ mid)) by
          (lia || (intros u Hu; apply F2; lia)).
        rewrite <- (seg_ext a1 a (φ mid) (φ hi)) by
          (lia || (intros u Hu; apply F1; lia)).
        apply Permutation_app; [exact P1 | exact P2].
      * intros u v Hu Huv Hv.
        rewrite !(proj1 (C4 _)) by lia. apply S3; lia.
  - injection Hrun as <- <-.
    pose proof (split_ok_false lo hi Hs ltac:(lia)) as Hw.
    split; [reflexivity|]. split; [exact Hta|]. split; [reflexivity|].
    split; [apply Permutation_refl|].
    intros u v Hu Huv Hv.
    assert (u = v) by (apply to_Z_inj; lia). subst v. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The maximum pass                                                    *)
(* ------------------------------------------------------------------ *)

Section MaxPass.
  Variables (s : array int) (p s0 n : int).
  Hypothesis Hp : (φ p) <= 20.
  Hypothesis Hn : (φ n) <= 100000.
  Hypothesis Hs0 : (φ s0) <= 10 ^ 7.

  Definition M (k : Z) : Z := Z.max 0 ((φ p) * (k + 1) + (φ s0) - (φ (s.[of_Z k]))).

  Lemma need_spec : forall (x k : int), (φ k) < (φ n) ->
    (φ (need p s0 x k)) = Z.max 0 ((φ p) * ((φ k) + 1) + (φ s0) - (φ x)).
  Proof.
    intros x k Hk. pose proof (to_Z_bounded p). pose proof (to_Z_bounded k).
    pose proof (to_Z_bounded s0). pose proof (to_Z_bounded x).
    assert (E : (φ ((p * (k + 1) + s0)%uint63)) = (φ p) * ((φ k) + 1) + (φ s0)).
    { rewrite add_spec, mul_spec, add_spec. change (φ 1) with 1.
      rewrite wB_val.
      rewrite (Z.mod_small ((φ k) + 1)) by lia.
      rewrite (Z.mod_small ((φ p) * ((φ k) + 1))) by nia.
      apply Z.mod_small. nia. }
    unfold need. destruct (x <? p * (k + 1) + s0)%uint63 eqn:Ex.
    - rewrite ltb_spec, E in Ex. rewrite sub_spec, E.
      rewrite Z.mod_small by (rewrite wB_val; nia). lia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec, E in Ex.
      change (φ 0) with 0. lia.
  Qed.

  Lemma max_loop_spec : forall (z : Z) (k acc : int) (H : Acc (Zwf 0) (gap n k)),
    gap n k = z -> 0 <= (φ k) <= (φ n) ->
    (forall k', 0 <= k' < (φ k) -> M k' <= (φ acc)) ->
    ((φ acc) = 0 \/ exists k', 0 <= k' < (φ k) /\ (φ acc) = M k') ->
    (forall k', 0 <= k' < (φ n) -> M k' <= (φ (max_loop s p s0 n k acc H))) /\
    ((φ (max_loop s p s0 n k acc H)) = 0 \/
     exists k', 0 <= k' < (φ n) /\ (φ (max_loop s p s0 n k acc H)) = M k').
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros k acc H Hz Hk Hall Hex.
    rewrite max_loop_eq.
    destruct (bdec (k <? n)%uint63) as [Hkn | Hkn].
    - pose proof Hkn as Hkn'. rewrite ltb_spec in Hkn'.
      assert (Hk1 : (φ ((k + 1)%uint63)) = (φ k) + 1) by sia.
      assert (Ev : (φ (need p s0 s.[k] k)) = M (φ k)).
      { rewrite need_spec by lia. unfold M. rewrite of_to_Z. reflexivity. }
      cbv zeta.
      assert (Ea : (φ (if (acc <? need p s0 s.[k] k)%uint63 then need p s0 s.[k] k else acc))
                   = Z.max (φ acc) (M (φ k))).
      { destruct (acc <? need p s0 s.[k] k)%uint63 eqn:E.
        - rewrite ltb_spec, Ev in E. rewrite Ev. lia.
        - rewrite <- Bool.not_true_iff_false, ltb_spec, Ev in E. lia. }
      apply (IH (gap n ((k + 1)%uint63))); [rewrite <- Hz; apply dec_step; exact Hkn
                                   | reflexivity | lia | | ].
      + intros k' Hk'. rewrite Ea. rewrite Hk1 in Hk'.
        destruct (Z.eq_dec k' (φ k)) as [E | E]; [subst; lia|].
        specialize (Hall k' ltac:(lia)). lia.
      + rewrite Ea, Hk1.
        destruct (Z.le_gt_cases (M (φ k)) (φ acc)) as [C | C].
        * rewrite Z.max_l by exact C.
          destruct Hex as [Hex | (k' & Hk' & Hex)]; [left; exact Hex|].
          right. exists k'. split; [lia | exact Hex].
        * rewrite Z.max_r by lia. right. exists (φ k). split; [lia | reflexivity].
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkn.
      split.
      + intros k' Hk'. apply Hall. lia.
      + destruct Hex as [Hex | (k' & Hk' & Hex)]; [left; exact Hex|].
        right. exists k'. split; [lia | exact Hex].
  Qed.
End MaxPass.

(* ------------------------------------------------------------------ *)
(* Lists                                                               *)
(* ------------------------------------------------------------------ *)

Lemma perm_filter {A} (f : A -> bool) (l l' : list A) :
  Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  induction 1; simpl.
  - constructor.
  - destruct (f x); auto using perm_skip.
  - destruct (f x), (f y); auto using perm_swap, perm_skip, Permutation_refl.
  - eapply perm_trans; eauto.
Qed.

Lemma filter_all {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  induction l as [| x l IHl]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). f_equal. apply IHl. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma filter_none {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  induction l as [| x l IHl]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). apply IHl. intros y Hy. apply H. right. exact Hy.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

(* An array representing d reads, cell by cell, as d. *)
Lemma repr_list : forall (y : array uint) (d : list N), repr y d ->
  d = map Z.to_N (seg y 0 (Z.of_nat (List.length d))).
Proof.
  intros y d Hy.
  assert (Hl : Z.of_nat (List.length d) = (φ (PArray.length y))) by exact (proj1 Hy).
  pose proof (alength_bound y) as By.
  apply nth_error_ext. intros k. unfold seg. rewrite map_map, nth_error_map, nth_error_seq.
  replace (Z.to_nat (Z.of_nat (List.length d) - 0)) with (List.length d) by lia.
  destruct (Nat.ltb_spec k (List.length d)) as [Hk | Hk].
  - destruct (proj2 Hy k Hk) as (m & Hm & Hr).
    assert (Hr' : Z.to_N (φ (y.[of_Z (Z.of_nat k)])) = m) by exact Hr.
    rewrite Hm. simpl. rewrite <- Hr'. reflexivity.
  - apply nth_error_None. exact Hk.
Qed.

Lemma dirtydriving_impl_correct :
  forall (p : N) (d : list N) (x : uint) (y : array uint),
  valid_input p d -> repr x p -> repr y d ->
  exists D : N, repr (dirtydriving_impl x y) D /\ dirtydriving_spec p d D.
Proof.
  intros p d x y Hv Hx Hy.
  destruct Hv as [Hn Hpb Hdb Hnd]. unfold len in Hn.
  pose proof (repr_list y d Hy) as Ed.
  assert (Hl : Z.of_nat (List.length d) = (φ (PArray.length y))) by exact (proj1 Hy).
  assert (Hpz : Z.of_N p = (φ x)).
  { rewrite <- Hx. rewrite Z2N.id by (pose proof (to_Z_bounded x); lia). reflexivity. }
  set (NN := List.length d) in *.
  unfold dirtydriving_impl. cbv zeta.
  set (n := PArray.length y) in *.
  assert (Hmk : PArray.length (PArray.make n (0 : int)) = PArray.length (y : array int)).
  { rewrite alength_make.
    replace (n <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  lazymatch goal with |- context [msort ?A ?B ?C ?D ?E] =>
    destruct (msort A B C D E) as [s t] eqn:Es;
    destruct (msort_spec _ C D A B E s t eq_refl
                ltac:(change (φ 0) with 0; lia) (Z.le_refl _) Hmk Es)
      as (Ls & _ & _ & Ps & Ss)
  end.
  cbn [fst].
  change (φ 0) with 0 in Ps, Ss.
  rewrite <- Hl in Ps, Ss. fold NN in Ps, Ss.
  (* the sorted cells *)
  set (g := fun k : nat => Z.to_N (φ (s.[of_Z (Z.of_nat k)]))).
  set (L := map Z.to_N (seg s 0 (Z.of_nat NN))).
  assert (HL : L = map g (seq 0 NN)).
  { unfold L, seg. rewrite map_map.
    replace (Z.to_nat (Z.of_nat NN - 0)) with NN by lia. reflexivity. }
  assert (HP : Permutation L d).
  { transitivity (map Z.to_N (seg y 0 (Z.of_nat NN)));
      [apply Permutation_map; exact Ps | rewrite <- Ed; apply Permutation_refl]. }
  assert (HND : NoDup L) by exact (Permutation_NoDup (Permutation_sym HP) Hnd).
  assert (HlenL : List.length L = NN) by (rewrite HL, length_map, length_seq; reflexivity).
  assert (Hnth : forall k, (k < NN)%nat -> nth k L 0%N = g k).
  { intros k Hk. rewrite HL.
    rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; lia).
    rewrite map_nth, seq_nth by lia. reflexivity. }
  assert (Hcell : forall k, Z.of_N (g k) = (φ (s.[of_Z (Z.of_nat k)]))).
  { intros k. unfold g. rewrite Z2N.id by (pose proof (to_Z_bounded (s.[of_Z (Z.of_nat k)])); lia).
    reflexivity. }
  assert (Hsortg : forall u v, (u <= v < NN)%nat -> (g u <= g v)%N).
  { intros u v Huv.
    pose proof (Ss (of_Z (Z.of_nat u)) (of_Z (Z.of_nat v))) as S.
    rewrite !of_Z_small in S by lia.
    specialize (S ltac:(lia) ltac:(lia) ltac:(lia)).
    pose proof (Hcell u). pose proof (Hcell v). lia. }
  assert (Hstrict : forall u v, (u < v < NN)%nat -> (g u < g v)%N).
  { intros u v Huv.
    assert (Hle : (g u <= g v)%N) by (apply Hsortg; lia).
    assert (Hne : g u <> g v).
    { intro E. apply (proj1 (NoDup_nth L 0%N)) with (i := u) (j := v) in HND;
        [lia | lia | lia |]. rewrite !Hnth by lia. exact E. }
    lia. }
  assert (Hin : forall z, In z d -> exists k, (k < NN)%nat /\ z = g k).
  { intros z Hz. apply (Permutation_in _ (Permutation_sym HP)) in Hz.
    rewrite HL, in_map_iff in Hz. destruct Hz as (k & Hk & Hk').
    rewrite in_seq in Hk'. exists k. split; [lia | symmetry; exact Hk]. }
  assert (Hing : forall k, (k < NN)%nat -> In (g k) d).
  { intros k Hk. apply (Permutation_in _ HP). rewrite HL. apply in_map.
    rewrite in_seq. lia. }
  assert (Hcars : forall k, (k < NN)%nat -> cars_between d (g k) = N.of_nat k).
  { intros k Hk. unfold cars_between, len.
    rewrite <- (Permutation_length (perm_filter _ _ _ HP)). rewrite HL.
    replace (seq 0 NN) with (seq 0 k ++ seq (0 + k) (NN - k))
      by (rewrite <- seq_app; f_equal; lia).
    rewrite map_app, filter_app, filter_all, filter_none, app_nil_r, length_map, length_seq.
    - reflexivity.
    - intros z Hz. rewrite in_map_iff in Hz. destruct Hz as (u & <- & Hu).
      rewrite in_seq in Hu. apply N.ltb_ge. apply Hsortg. lia.
    - intros z Hz. rewrite in_map_iff in Hz. destruct Hz as (u & <- & Hu).
      rewrite in_seq in Hu. apply N.ltb_lt. apply Hstrict. lia. }
  (* bounds for the maximum pass *)
  assert (Hxb : (φ x) <= 20) by lia.
  assert (Hnb : (φ n) <= 100000) by lia.
  assert (Hs0 : (φ (s.[0])) <= 10 ^ 7).
  { assert (H0 := Hing 0%nat ltac:(lia)).
    rewrite Forall_forall in Hdb. specialize (Hdb _ H0).
    pose proof (Hcell 0%nat) as C. change (of_Z (Z.of_nat 0)) with 0%uint63 in C. lia. }
  lazymatch goal with |- context [max_loop ?A ?B ?C ?D ?E ?F ?G] =>
    destruct (max_loop_spec A B C D Hxb Hnb Hs0 _ E F G eq_refl
                ltac:(change (φ 0) with 0; lia)
                ltac:(change (φ 0) with 0; intros; lia)
                ltac:(left; reflexivity)) as [Hall Hex];
    set (r := max_loop A B C D E F G) in *
  end.
  change (φ 0) with 0 in Hall, Hex. rewrite <- Hl in Hall, Hex. fold NN in Hall, Hex.
  assert (Hrz : Z.of_N (Z.to_N (φ r)) = (φ r))
    by (rewrite Z2N.id by (pose proof (to_Z_bounded r); lia); reflexivity).
  assert (Hc0 : Z.of_N (g 0%nat) = (φ (s.[0])))
    by (rewrite Hcell; reflexivity).
  exists (Z.to_N (φ r)). split; [reflexivity|]. split.
  - intros xx yy Hxx Hyy Hc.
    destruct (Hin xx Hxx) as (kx & Hkx & ->).
    destruct (Hin yy Hyy) as (ky & Hky & ->).
    rewrite Hcars in Hc by exact Hky.
    assert (ky = 0%nat) by lia. subst ky.
    rewrite Hcars by exact Hkx.
    specialize (Hall (Z.of_nat kx) ltac:(lia)). unfold M in Hall.
    pose proof (Hcell kx) as Ck.
    apply N2Z.inj_le. rewrite !N2Z.inj_add, N2Z.inj_mul, N2Z.inj_add, Hpz, Hrz, Ck, Hc0.
    rewrite nat_N_Z. lia.
  - intros D' HD'.
    destruct Hex as [H0 | (k' & Hk' & Heq)].
    + rewrite H0. simpl. lia.
    + specialize (HD' (g (Z.to_nat k')) (g 0%nat) (Hing (Z.to_nat k') ltac:(lia)) (Hing 0%nat ltac:(lia))
                    ltac:(rewrite Hcars by lia; reflexivity)).
      rewrite Hcars in HD' by lia.
      pose proof (Hcell (Z.to_nat k')) as Ck. rewrite Z2Nat.id in Ck by lia.
      unfold M in Heq.
      apply N2Z.inj_le in HD'. rewrite !N2Z.inj_add, N2Z.inj_mul, N2Z.inj_add, Hpz, Ck, Hc0 in HD'.
      rewrite nat_N_Z, Z2Nat.id in HD' by lia.
      apply N2Z.inj_le. rewrite Hrz. lia.
Qed.

Definition dirtydriving_correct :
  forall (p : N) (d : list N) (x : uint) (y : array uint),
  valid_input p d -> repr x p -> repr y d ->
  exists D : N, repr (dirtydriving x y) D /\ dirtydriving_spec p d D
  := dirtydriving_impl_correct.
