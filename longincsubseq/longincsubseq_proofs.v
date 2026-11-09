(* Correctness proofs for longincsubseq_implem.v. *)
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

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export longincsubseq_implem.
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

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma aget_set_cases : forall (t : array int) (i b j : int),
  ((φ i) < (φ (PArray.length t)))%Z ->
  ((φ j) = (φ i) /\ t.[i <- b].[j] = b) \/ ((φ j) <> (φ i) /\ t.[i <- b].[j] = t.[j]).
Proof.
  intros t i b j Hi.
  destruct (Z.eq_dec (φ j) (φ i)) as [E | E].
  - left. split; [exact E|].
    assert (j = i) by (apply to_Z_inj; exact E). subst j.
    apply (get_set_same int t i b). rewrite ltb_spec. exact Hi.
  - right. split; [exact E|].
    apply (get_set_other int t i j b). intro F. apply E. rewrite F. reflexivity.
Qed.

Lemma phi_of_Z : forall z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma bsearch_eq : forall x tails v lo hi H,
  bsearch x tails v lo hi H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma main_loop_eq : forall x n i L tails pred H,
  main_loop x n i L tails pred H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_eq : forall pred c j res H,
  build pred c j res H =
  match bdec (0 <? c) with
  | left Hc =>
      build pred (c - 1) pred.[j] res.[c - 1 <- j]
        (Acc_inv H (dec_down c Hc))
  | right _ => res
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the model                                                *)
(* ------------------------------------------------------------------ *)

(* The value at position z of the sequence. *)
Definition av (a : list Z) (z : Z) : Z := get_list_Z a (Z.to_N z).

(* reach a j m: some increasing subsequence of a of length m ends at j. *)
Inductive reach (a : list Z) : Z -> Z -> Prop :=
| reach1 : forall j, (0 <= j < Z.of_nat (List.length a))%Z -> reach a j 1
| reachS : forall j' j m, reach a j' m ->
    (j' < j < Z.of_nat (List.length a))%Z -> (av a j' < av a j)%Z ->
    reach a j (m + 1).

Lemma reach_pos : forall a j m, reach a j m ->
  (1 <= m /\ 0 <= j < Z.of_nat (List.length a))%Z.
Proof. intros a j m Hr. induction Hr; lia. Qed.

Lemma reach_inv : forall a j m, reach a j m ->
  m = 1%Z \/ exists j' m', m = (m' + 1)%Z /\ reach a j' m' /\
                           (j' < j)%Z /\ (av a j' < av a j)%Z.
Proof.
  intros a j m Hr. destruct Hr as [j Hj | j' j m Hr Hjj Hv].
  - left. reflexivity.
  - right. exists j', m. repeat split; auto; lia.
Qed.

Lemma IS_reach : forall a s, increasing_subseq a s ->
  forall t, (t < List.length s)%nat ->
  reach a (Z.of_N (get_list_N s (N.of_nat t))) (Z.of_nat t + 1).
Proof.
  intros a s (Hiv & Hasc & Hval) t.
  induction t as [| t IH]; intros Ht.
  - apply reach1. pose proof (Hiv (N.of_nat 0) ltac:(unfold len; lia)) as B.
    unfold len in B. lia.
  - replace (Z.of_nat (S t) + 1)%Z with ((Z.of_nat t + 1) + 1)%Z by lia.
    apply reachS with (j' := Z.of_N (get_list_N s (N.of_nat t))).
    + apply IH. lia.
    + pose proof (Hasc (N.of_nat t) (N.of_nat (S t)) ltac:(unfold len; lia)) as B1.
      pose proof (Hiv (N.of_nat (S t)) ltac:(unfold len; lia)) as B2.
      unfold len in B2. lia.
    + unfold av. rewrite !N2Z.id.
      apply Hval. unfold len. lia.
Qed.

(* Reading an in-bounds cell of an array representing a. *)
Lemma repr_get : forall (x : array sint) (a : list Z), repr x a ->
  forall i : int, ((φ i) < Z.of_nat (List.length a))%Z ->
  Sint63.to_Z x.[i] = av a (φ i).
Proof.
  intros x a [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hr.
  unfold av, get_list_Z. rewrite Z_N_nat. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array sint) (a : list Z), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

(* ------------------------------------------------------------------ *)
(* The binary search                                                   *)
(* ------------------------------------------------------------------ *)

Definition bs_ok (a : list Z) (tails : array int) (w : Z) (L r : int) : Prop :=
  ((φ r) <= (φ L))%Z /\
  (forall k, ((φ k) < (φ r))%Z -> (av a (φ (tails.[k])) < w)%Z) /\
  (forall k, ((φ r) <= (φ k) < (φ L))%Z -> (w <= av a (φ (tails.[k])))%Z).

Lemma bsearch_spec : forall (a : list Z) (x : array sint), repr x a ->
  forall (tails : array int) (v L : int),
  (forall k, ((φ k) < (φ L))%Z -> ((φ (tails.[k])) < Z.of_nat (List.length a))%Z) ->
  (forall k k', ((φ k) < (φ k') < (φ L))%Z ->
     (av a (φ (tails.[k])) < av a (φ (tails.[k'])))%Z) ->
  forall z lo hi (H : Acc (Zwf 0) (gap hi lo)), gap hi lo = z ->
  ((φ lo) <= (φ hi) <= (φ L))%Z ->
  (forall k, ((φ k) < (φ lo))%Z -> (av a (φ (tails.[k])) < Sint63.to_Z v)%Z) ->
  (forall k, ((φ hi) <= (φ k) < (φ L))%Z -> (Sint63.to_Z v <= av a (φ (tails.[k])))%Z) ->
  bs_ok a tails (Sint63.to_Z v) L (bsearch x tails v lo hi H).
Proof.
  intros a x Ha tails v L Hb Hs z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi H Hz Hlh Hlo Hhi.
  rewrite bsearch_eq.
  destruct (bdec (lo <? hi)) as [Hlt | Hlt].
  - cbv zeta.
    pose proof (mid_spec lo hi (lo + (hi - lo) / 2) eq_refl Hlt) as Hm.
    pose proof (dec_lo lo hi (lo + (hi - lo) / 2) eq_refl Hlt) as Dlo.
    pose proof (dec_hi lo hi (lo + (hi - lo) / 2) eq_refl Hlt) as Dhi.
    generalize (dec_lo lo hi (lo + (hi - lo) / 2) eq_refl Hlt).
    generalize (dec_hi lo hi (lo + (hi - lo) / 2) eq_refl Hlt).
    set (mid := lo + (hi - lo) / 2) in *. intros D2 D1.
    pose proof (Hb mid ltac:(lia)) as Hbm.
    pose proof (repr_get x a Ha (tails.[mid]) Hbm) as Em.
    destruct (bdec (Sint63.ltb x.[tails.[mid]] v)) as [Hc | Hc].
    + assert (Hc2 : (av a (φ (tails.[mid])) < Sint63.to_Z v)%Z)
        by (rewrite <- Em; exact (proj1 (Sint63.ltb_spec _ _) Hc)).
      clear Hc. rename Hc2 into Hc.
      pose proof (alength_bound tails).
      assert (Hm1 : (φ (mid + 1)) = ((φ mid) + 1)%Z) by sia.
      eapply IH; [ | reflexivity | lia | | exact Hhi].
      * rewrite <- Hz. exact Dlo.
      * intros k Hk. rewrite Hm1 in Hk.
        destruct (Z.eq_dec (φ k) (φ mid)) as [E | E].
        -- assert (k = mid) by (apply to_Z_inj; exact E). subst k. exact Hc.
        -- apply Z.lt_trans with (av a (φ (tails.[mid]))); [apply Hs; lia | exact Hc].
    + assert (Hc2 : ~ (av a (φ (tails.[mid])) < Sint63.to_Z v)%Z).
      { rewrite <- Em. intro F. apply (proj2 (Sint63.ltb_spec _ _)) in F.
        exact (Bool.diff_true_false (eq_trans (eq_sym F) Hc)). }
      clear Hc. rename Hc2 into Hc.
      eapply IH; [ | reflexivity | lia | exact Hlo | ].
      * rewrite <- Hz. exact Dhi.
      * intros k Hk.
        destruct (Z.eq_dec (φ k) (φ mid)) as [E | E].
        -- assert (k = mid) by (apply to_Z_inj; exact E). subst k. lia.
        -- destruct (Z_lt_le_dec (φ k) (φ hi)) as [E2 | E2].
           ++ pose proof (Hs mid k ltac:(lia)). lia.
           ++ apply Hhi. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [lia | split; [exact Hlo | intros k Hk; apply Hhi; lia]].
Qed.

(* ------------------------------------------------------------------ *)
(* The pass invariant                                                  *)
(* ------------------------------------------------------------------ *)

Definition Inv (a : list Z) (i L : int) (tails pred : array int) : Prop :=
  (φ (PArray.length tails)) = Z.of_nat (List.length a) /\
  (φ (PArray.length pred)) = Z.of_nat (List.length a) /\
  ((φ L) <= (φ i) <= Z.of_nat (List.length a))%Z /\
  (forall k, ((φ k) < (φ L))%Z -> ((φ (tails.[k])) < (φ i))%Z) /\
  (forall k k', ((φ k) < (φ k') < (φ L))%Z ->
     (av a (φ (tails.[k])) < av a (φ (tails.[k'])))%Z) /\
  (exists h : Z -> Z,
     (forall j : int, ((φ j) < (φ i))%Z ->
        (0 <= h (φ j))%Z /\
        ((0 < h (φ j))%Z ->
           ((φ (pred.[j])) < (φ j))%Z /\ h (φ (pred.[j])) = (h (φ j) - 1)%Z /\
           (av a (φ (pred.[j])) < av a (φ j))%Z)) /\
     (forall k, ((φ k) < (φ L))%Z -> h (φ (tails.[k])) = (φ k))) /\
  (forall j m, reach a j m -> (j < (φ i))%Z ->
     (m <= (φ L))%Z /\
     forall k, (φ k) = (m - 1)%Z -> (av a (φ (tails.[k])) <= av a j)%Z).

Lemma step_inv : forall a i L tails pred k,
  ((φ i) < Z.of_nat (List.length a))%Z ->
  Inv a i L tails pred ->
  bs_ok a tails (av a (φ i)) L k ->
  Inv a (i + 1) (if k =? L then L + 1 else L) tails.[k <- i]
      pred.[i <- if k =? 0 then 0 else tails.[k - 1]].
Proof.
  intros a i L tails pred k Hin
    (Hlt & Hlp & HLi & Hti & Hsort & (h & Hh & Hht) & Hreach) (HkL & Hlo & Hhi).
  pose proof (alength_bound tails) as Bt.
  assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  assert (Hk_len : ((φ k) < (φ (PArray.length tails)))%Z) by lia.
  assert (Hi_len : ((φ i) < (φ (PArray.length pred)))%Z) by lia.
  assert (HL' : exists L', L' = (if k =? L then L + 1 else L) /\
     ((φ L) <= (φ L') <= (φ L) + 1)%Z /\ ((φ k) < (φ L'))%Z /\
     (forall k', ((φ k') < (φ L'))%Z -> (φ k') <> (φ k) -> ((φ k') < (φ L))%Z)).
  { exists (if k =? L then L + 1 else L). split; [reflexivity|].
    destruct (k =? L) eqn:E.
    - rewrite eqb_spec in E. subst k.
      assert ((φ (L + 1)) = ((φ L) + 1)%Z) by sia.
      split; [lia | split; [lia|]]. intros k' Hk' Hne. lia.
    - rewrite eqb_false_spec in E.
      assert ((φ k) <> (φ L)) by (intro F; apply E; apply to_Z_inj; exact F).
      split; [lia | split; [lia|]]. intros k' Hk' Hne. lia. }
  destruct HL' as (L' & EL' & HL1 & HL2 & HL3). rewrite <- EL'.
  assert (Hp : exists p, p = (if k =? 0 then 0 else tails.[k - 1]) /\
     ((0 < (φ k))%Z -> p = tails.[k - 1] /\ (φ (k - 1)) = ((φ k) - 1)%Z)).
  { exists (if k =? 0 then 0 else tails.[k - 1]). split; [reflexivity|].
    intros Hk0. destruct (k =? 0) eqn:E.
    - rewrite eqb_spec in E. subst k. change (φ 0) with 0%Z in Hk0. lia.
    - split; [reflexivity | sia]. }
  destruct Hp as (p & Ep & Hp). rewrite <- Ep.
  unfold Inv.
  split; [rewrite alength_set; exact Hlt|].
  split; [rewrite alength_set; exact Hlp|].
  split; [lia|].
  split.
  { intros k' Hk'.
    destruct (aget_set_cases tails k i k' Hk_len) as [[E1 E2] | [E1 E2]];
      rewrite E2; [lia|].
    specialize (Hti k' (HL3 k' Hk' E1)). lia. }
  split.
  { intros k1 k2 H12.
    destruct (aget_set_cases tails k i k1 Hk_len) as [[E1 E2] | [E1 E2]];
    destruct (aget_set_cases tails k i k2 Hk_len) as [[F1 F2] | [F1 F2]];
      rewrite E2, F2.
    - lia.
    - pose proof (HL3 k2 ltac:(lia) F1) as B.
      pose proof (Hhi k ltac:(lia)) as B1. pose proof (Hsort k k2 ltac:(lia)) as B2.
      lia.
    - apply Hlo. lia.
    - apply Hsort. pose proof (HL3 k2 ltac:(lia) F1). lia. }
  split.
  { exists (fun z => if Z.eq_dec z (φ i) then (φ k) else h z). split.
    - intros j Hj. rewrite Hi1 in Hj.
      destruct (aget_set_cases pred i p j Hi_len) as [[E1 E2] | [E1 E2]];
        rewrite E2.
      + destruct (Z.eq_dec (φ j) (φ i)) as [_ | C]; [| contradiction].
        split; [pose proof (to_Z_bounded k); lia|].
        intros Hk0. destruct (Hp Hk0) as [Ep' Ek1]. rewrite Ep'.
        pose proof (Hti (k - 1) ltac:(lia)) as B.
        destruct (Z.eq_dec (φ (tails.[k - 1])) (φ i)) as [C | _]; [lia|].
        rewrite (Hht (k - 1) ltac:(lia)).
        split; [lia | split; [lia|]].
        rewrite E1. apply Hlo. lia.
      + destruct (Z.eq_dec (φ j) (φ i)) as [C | _]; [contradiction|].
        destruct (Hh j ltac:(lia)) as [Hh0 Hh1]. split; [exact Hh0|].
        intros Hpos. destruct (Hh1 Hpos) as (Q1 & Q2 & Q3).
        destruct (Z.eq_dec (φ (pred.[j])) (φ i)) as [C | _]; [lia|].
        auto.
    - intros k' Hk'.
      destruct (aget_set_cases tails k i k' Hk_len) as [[E1 E2] | [E1 E2]];
        rewrite E2.
      + destruct (Z.eq_dec (φ i) (φ i)) as [_ | C]; [lia | contradiction].
      + pose proof (HL3 k' Hk' E1) as B. pose proof (Hti k' B) as B1.
        destruct (Z.eq_dec (φ (tails.[k'])) (φ i)) as [C | _]; [lia|].
        apply Hht. exact B. }
  { intros j m Hr Hj. rewrite Hi1 in Hj.
    destruct (Z.eq_dec j (φ i)) as [Ej | Ej].
    - subst j.
      destruct (reach_inv a _ _ Hr) as [Em | (j' & m0 & Em & Hr0 & Hj' & Hv)].
      + subst m. split; [lia|]. intros k' Hk'.
        destruct (aget_set_cases tails k i k' Hk_len) as [[E1 E2] | [E1 E2]];
          rewrite E2; [lia|].
        apply Z.lt_le_incl. apply Hlo. lia.
      + subst m. pose proof (reach_pos a _ _ Hr0) as Pm0.
        destruct (Hreach j' m0 Hr0 ltac:(lia)) as [Hm0L Hm0].
        assert (Hm0k : (m0 <= (φ k))%Z).
        { destruct (Z_le_gt_dec m0 (φ k)) as [G | G]; [exact G|].
          exfalso.
          assert (Bk : (φ (of_Z (m0 - 1))) = (m0 - 1)%Z)
            by (apply phi_of_Z; rewrite wB_val; lia).
          pose proof (Hhi (of_Z (m0 - 1)) ltac:(lia)) as B1.
          pose proof (Hm0 (of_Z (m0 - 1)) Bk) as B2.
          lia. }
        split; [lia|]. intros k' Hk'.
        destruct (aget_set_cases tails k i k' Hk_len) as [[E1 E2] | [E1 E2]];
          rewrite E2; [lia|].
        apply Z.lt_le_incl. apply Hlo. lia.
    - destruct (Hreach j m Hr ltac:(lia)) as [HmL Hm].
      split; [lia|]. intros k' Hk'.
      destruct (aget_set_cases tails k i k' Hk_len) as [[E1 E2] | [E1 E2]];
        rewrite E2.
      + pose proof (Hhi k ltac:(lia)) as B1. pose proof (Hm k ltac:(lia)) as B2.
        lia.
      + apply Hm. exact Hk'. }
Qed.

Lemma main_spec : forall (a : list Z) (x : array sint), repr x a ->
  forall n : int, (φ n) = Z.of_nat (List.length a) ->
  forall z i L tails pred (H : Acc (Zwf 0) (gap n i)), gap n i = z ->
  ((φ i) <= (φ n))%Z ->
  Inv a i L tails pred ->
  Inv a n (fst (main_loop x n i L tails pred H))
          (fst (snd (main_loop x n i L tails pred H)))
          (snd (snd (main_loop x n i L tails pred H))).
Proof.
  intros a x Ha n Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i L tails pred H Hz Hin HI.
  rewrite main_loop_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - cbv zeta. pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    pose proof HI as (Hlt & Hlp & HLi & Hti & Hsort & _ & _).
    pose proof (repr_get x a Ha i ltac:(lia)) as Ev.
    pose proof (bsearch_spec a x Ha tails x.[i] L
                  ltac:(intros k Hk; specialize (Hti k Hk); lia) Hsort
                  _ 0 L (Zwf_well_founded 0 (gap L 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded L); lia)
                  ltac:(intros k Hk; change (φ 0) with 0%Z in Hk;
                        pose proof (to_Z_bounded k); lia)
                  ltac:(intros k Hk; lia)) as Hbs.
    rewrite Ev in Hbs.
    pose proof (alength_bound tails) as Bt.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + apply step_inv; [lia | exact HI | exact Hbs].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    assert (i = n) by (apply to_Z_inj; lia). subst i.
    exact HI.
Qed.

Lemma init_inv : forall (a : list Z) (n : int),
  (φ n) = Z.of_nat (List.length a) -> ((φ n) <= 4194303)%Z ->
  Inv a 0 0 (PArray.make n 0) (PArray.make n 0).
Proof.
  intros a n Hn Hnm.
  assert (Hl : PArray.length (PArray.make n 0) = n).
  { rewrite alength_make.
    pose proof (alength_bound (PArray.make n 0)) as B.
    rewrite alength_make in B.
    destruct (n <=? PArray.max_length) eqn:E; [reflexivity|].
    rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E.
    exfalso. lia. }
  unfold Inv. rewrite Hl. change (φ 0) with 0%Z.
  split; [exact Hn|]. split; [exact Hn|]. split; [lia|].
  split; [intros k Hk; pose proof (to_Z_bounded k); lia|].
  split; [intros k k' Hk; pose proof (to_Z_bounded k); lia|].
  split.
  - exists (fun _ => 0%Z). split; intros j Hj; pose proof (to_Z_bounded j); lia.
  - intros j m Hr Hj. pose proof (reach_pos a j m Hr). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The reconstruction                                                  *)
(* ------------------------------------------------------------------ *)

Definition Out (a : list Z) (Lr : int) (r : array int) : Prop :=
  (φ (PArray.length r)) = (φ Lr) /\
  (forall t, ((φ t) < (φ Lr))%Z -> ((φ (r.[t])) < Z.of_nat (List.length a))%Z) /\
  (forall t t', (φ t') = ((φ t) + 1)%Z -> ((φ t') < (φ Lr))%Z ->
     ((φ (r.[t])) < (φ (r.[t'])))%Z /\ (av a (φ (r.[t])) < av a (φ (r.[t'])))%Z).

Lemma build_spec : forall (a : list Z) (pred : array int) (h : Z -> Z) (Lr : int),
  (forall j : int, ((φ j) < Z.of_nat (List.length a))%Z ->
     (0 <= h (φ j))%Z /\
     ((0 < h (φ j))%Z ->
        ((φ (pred.[j])) < (φ j))%Z /\ h (φ (pred.[j])) = (h (φ j) - 1)%Z /\
        (av a (φ (pred.[j])) < av a (φ j))%Z)) ->
  forall z c j res (H : Acc (Zwf 0) (gap c 0)), gap c 0 = z ->
  (φ (PArray.length res)) = (φ Lr) ->
  ((φ c) <= (φ Lr))%Z ->
  ((1 <= (φ c))%Z -> ((φ j) < Z.of_nat (List.length a))%Z /\ h (φ j) = ((φ c) - 1)%Z) ->
  (((φ c) < (φ Lr))%Z -> (1 <= (φ c))%Z ->
     ((φ j) < (φ (res.[c])))%Z /\ (av a (φ j) < av a (φ (res.[c])))%Z) ->
  (forall t, ((φ c) <= (φ t) < (φ Lr))%Z -> ((φ (res.[t])) < Z.of_nat (List.length a))%Z) ->
  (forall t t', ((φ c) <= (φ t))%Z -> (φ t') = ((φ t) + 1)%Z -> ((φ t') < (φ Lr))%Z ->
     ((φ (res.[t])) < (φ (res.[t'])))%Z /\ (av a (φ (res.[t])) < av a (φ (res.[t'])))%Z) ->
  Out a Lr (build pred c j res H).
Proof.
  intros a pred h Lr Hh z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros c j res H Hz Hlen HcL H4 H5 H6 H7.
  rewrite build_eq.
  destruct (bdec (0 <? c)) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'. change (φ 0) with 0%Z in Hc'.
    assert (Hc1 : (φ (c - 1)) = ((φ c) - 1)%Z) by sia.
    assert (Hcl : ((φ (c - 1)) < (φ (PArray.length res)))%Z) by lia.
    destruct (H4 ltac:(lia)) as [Hjn Hhj].
    destruct (Hh j Hjn) as [_ Hh1].
    eapply IH; [ | reflexivity | rewrite alength_set; exact Hlen | lia | | | | ].
    + rewrite <- Hz. apply dec_down. exact Hc.
    + intros G. destruct (Hh1 ltac:(lia)) as (Q1 & Q2 & Q3). split; lia.
    + intros _ G.
      destruct (aget_set_cases res (c - 1) j (c - 1) Hcl) as [[E1 E2] | [E1 E2]];
        [rewrite E2 | lia].
      destruct (Hh1 ltac:(lia)) as (Q1 & Q2 & Q3). split; lia.
    + intros t Ht.
      destruct (aget_set_cases res (c - 1) j t Hcl) as [[E1 E2] | [E1 E2]];
        rewrite E2; [exact Hjn|].
      apply H6. lia.
    + intros t t' Ht Et' Ht'.
      destruct (aget_set_cases res (c - 1) j t Hcl) as [[E1 E2] | [E1 E2]];
      destruct (aget_set_cases res (c - 1) j t' Hcl) as [[F1 F2] | [F1 F2]];
        rewrite E2, F2.
      * lia.
      * assert (t' = c) by (apply to_Z_inj; lia). subst t'.
        apply H5; lia.
      * lia.
      * apply H7; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc. change (φ 0) with 0%Z in Hc.
    split; [exact Hlen|]. split.
    + intros t Ht. apply H6. pose proof (to_Z_bounded t). lia.
    + intros t t' Et' Ht'. apply H7; [pose proof (to_Z_bounded t); lia | exact Et' | exact Ht'].
Qed.

(* ------------------------------------------------------------------ *)
(* The output                                                          *)
(* ------------------------------------------------------------------ *)

Lemma chain_lt : forall (g : nat -> Z) (L : nat),
  (forall t, (S t < L)%nat -> (g t < g (S t))%Z) ->
  forall t u, (t < u < L)%nat -> (g t < g u)%Z.
Proof.
  intros g L Hg t u. induction u as [| u IH]; intros Htu; [lia|].
  destruct (Nat.eq_dec t u) as [E | E].
  - subst u. apply Hg. lia.
  - apply Z.lt_trans with (g u); [apply IH; lia | apply Hg; lia].
Qed.

Definition out_list (r : array int) (L : int) : list N :=
  map (fun t => Z.to_N (φ (r.[of_nat t]))) (seq 0 (Z.to_nat (φ L))).

Lemma out_correct : forall (a : list Z) (r : array@{Set} int) (L : int),
  Out a L r ->
  (forall j m, reach a j m -> (j < Z.of_nat (List.length a))%Z -> (m <= (φ L))%Z) ->
  @repr (array uint) (list N) _ r (out_list r L) /\ lis_spec a (out_list r L).
Proof.
  intros a r L (Hlen & Hb & Hc) Hopt.
  pose proof (to_Z_bounded L) as BL.
  assert (Hl : List.length (out_list r L) = Z.to_nat (φ L)).
  { unfold out_list. rewrite length_map, length_seq. reflexivity. }
  assert (Hnth : forall t, (t < Z.to_nat (φ L))%nat ->
            nth_error (out_list r L) t = Some (Z.to_N (φ (r.[of_nat t])))).
  { intros t Ht. unfold out_list. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec t (Z.to_nat (φ L))); [reflexivity | lia]. }
  assert (Hget : forall t, (t < Z.to_nat (φ L))%nat ->
            get_list_N (out_list r L) (N.of_nat t) = Z.to_N (φ (r.[of_nat t]))).
  { intros t Ht. unfold get_list_N. rewrite Nat2N.id.
    apply nth_error_nth. apply Hnth. exact Ht. }
  assert (Hphi : forall t, (t < Z.to_nat (φ L))%nat -> (φ (of_nat t)) = Z.of_nat t).
  { intros t Ht. apply phi_of_Z. rewrite wB_val. lia. }
  split.
  - split.
    + rewrite Hl. transitivity (φ L); [lia | exact (eq_sym Hlen)].
    + intros t Ht. rewrite Hl in Ht.
      exists (Z.to_N (φ (r.[of_nat t]))). split; [apply Hnth; exact Ht | reflexivity].
  - assert (HIS : increasing_subseq a (out_list r L)).
    { split; [| split].
      - intros t Ht. unfold len in Ht. rewrite Hl in Ht. replace t with (N.of_nat (N.to_nat t)) by lia.
        rewrite Hget by lia. unfold len.
        pose proof (Hb (of_nat (N.to_nat t)) ltac:(rewrite Hphi by lia; lia)).
        pose proof (to_Z_bounded (r.[of_nat (N.to_nat t)])). lia.
      - intros t u Htu. unfold len in Htu. rewrite Hl in Htu.
        replace t with (N.of_nat (N.to_nat t)) by lia.
        replace u with (N.of_nat (N.to_nat u)) by lia.
        rewrite !Hget by lia.
        assert (G : (Z.of_N (Z.to_N (φ (r.[of_nat (N.to_nat t)])))
                     < Z.of_N (Z.to_N (φ (r.[of_nat (N.to_nat u)]))))%Z).
        { rewrite !Z2N.id by apply to_Z_bounded.
          apply (chain_lt (fun t => (φ (r.[of_nat t]))) (Z.to_nat (φ L))); [|lia].
          intros t0 Ht0.
          apply (Hc (of_nat t0) (of_nat (S t0)));
            rewrite !Hphi by lia; lia. }
        lia.
      - intros t u Htu. unfold len in Htu. rewrite Hl in Htu.
        replace t with (N.of_nat (N.to_nat t)) by lia.
        replace u with (N.of_nat (N.to_nat u)) by lia.
        rewrite !Hget by lia.
        apply (chain_lt (fun t => av a (φ (r.[of_nat t]))) (Z.to_nat (φ L))); [|lia].
        intros t0 Ht0.
        apply (Hc (of_nat t0) (of_nat (S t0)));
          rewrite !Hphi by lia; lia. }
    split; [exact HIS|].
    intros s' Hs'.
    destruct (List.length s') as [| l] eqn:El.
    + unfold len. rewrite El. lia.
    + pose proof (IS_reach a s' Hs' l ltac:(lia)) as R.
      destruct Hs' as (Hiv & _ & _).
      pose proof (Hiv (N.of_nat l) ltac:(unfold len; lia)) as B.
      unfold len in B.
      pose proof (Hopt _ _ R ltac:(lia)) as G.
      unfold len. rewrite El, Hl. lia.
Qed.

Lemma lis_impl_correct : forall (a : list Z) (x : array sint),
  valid_input a -> repr x a ->
  exists s : list N, repr (lis_impl x) s /\ lis_spec a s.
Proof.
  intros a x Hv Ha.
  destruct Hv as [Hva _]. unfold len in Hva.
  pose proof (repr_length x a Ha) as Lx.
  assert (Bx : ((φ (PArray.length x)) <= 4194303)%Z).
  { pose proof (leb_length sint x) as B. rewrite leb_spec, max_length_val in B.
    exact B. }
  pose proof (main_spec a x Ha (PArray.length x) Lx _ 0 0
                (PArray.make (PArray.length x) 0) (PArray.make (PArray.length x) 0)
                (Zwf_well_founded 0 (gap (PArray.length x) 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia)
                (init_inv a (PArray.length x) Lx Bx)) as HI.
  unfold lis_impl.
  destruct (main_loop x (PArray.length x) 0 0 (PArray.make (PArray.length x) 0)
              (PArray.make (PArray.length x) 0)
              (Zwf_well_founded 0 (gap (PArray.length x) 0))) as [L [tl pr]].
  cbv beta iota. simpl fst in HI. simpl snd in HI.
  destruct HI as (Hlt & Hlp & HLi & Hti & Hsort & (h & Hh & Hht) & Hreach).
  assert (HL1 : (1 <= (φ L))%Z).
  { assert (R : reach a 0 1) by (apply reach1; lia).
    destruct (Hreach 0%Z 1%Z R ltac:(lia)). lia. }
  pose proof (alength_bound tl) as Bt.
  assert (Hml : (φ (PArray.length (PArray.make L 0))) = (φ L)).
  { rewrite alength_make.
    destruct (L <=? PArray.max_length) eqn:E; [reflexivity|].
    rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E. lia. }
  assert (HL' : (φ (L - 1)) = ((φ L) - 1)%Z) by sia.
  pose proof (build_spec a pr h L
                ltac:(intros j Hj; apply Hh; lia)
                _ L tl.[L - 1] (PArray.make L 0) (Zwf_well_founded 0 (gap L 0))
                eq_refl Hml ltac:(lia)
                ltac:(intros _; split;
                      [ pose proof (Hti (L - 1) ltac:(lia)); lia
                      | rewrite (Hht (L - 1) ltac:(lia)); exact HL' ])
                ltac:(intros G; lia)
                ltac:(intros t Ht; lia)
                ltac:(intros t t' Ht; lia)) as HO.
  exists (out_list (build pr L tl.[L - 1] (PArray.make L 0)
                      (Zwf_well_founded 0 (gap L 0))) L).
  apply out_correct; [exact HO|].
  intros j m Hr Hj. destruct (Hreach j m Hr ltac:(lia)) as [G _]. exact G.
Qed.

Definition lis_correct : forall (a : list Z) (x : array sint),
  valid_input a -> repr x a ->
  exists s : list N, repr (lis x) s /\ lis_spec a s
  := lis_impl_correct.
