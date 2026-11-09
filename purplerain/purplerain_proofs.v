(* Correctness proofs for purplerain_implem.v. *)
(* Implementation of purplerain (purplerain.spec): maximum subarray in
   its single-scan form, on the prefix sums of R = +1, B = -1.

   Code.  [purplerain x] scans the string West to East once, keeping the
   running prefix sum P(k) = #R - #B of the first k sections (offset by n
   so that it stays a non-negative Uint63 word), the largest prefix sum seen
   so far with the FIRST index where it occurs, and the smallest one with
   the first index where it occurs.  The best |#R - #B| over a part is
   max P - min P, and the Westernmost optimal part is (a + 1, b) where a < b
   are the first indices of the maximum and of the minimum of P (in
   whichever order they come): no smaller start can reach an extreme with
   the other extreme after it, and the first occurrence of the other
   extreme is the smallest end.  One pass, O(1) extra memory, the string
   read in place with [PrimString.get].  No Z, no array.

   Termination: the scan recurses structurally on an erased
   [Acc (Zwf 0) (gap n k)] proof, as in template/polymul1. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf.
From Stdlib Require PrimString String.
From Stdlib Require Import Ascii.

Open Scope uint63_scope.

Unset Lia Cache.

Require Export purplerain_implem.
Open Scope uint63_scope.


Lemma scan_eq : forall x n k p mx imx mn imn H,
  scan x n k p mx imx mn imn H =
  match bdec (k <? n) with
  | left Hk =>
      let p' := if PrimString.get x k =? 82 then p + 1 else p - 1 in
      let k' := k + 1 in
      if mx <? p' then
        scan x n k' p' p' k' mn imn (Acc_inv H (dec_step n k Hk))
      else if p' <? mn then
        scan x n k' p' mx imx p' k' (Acc_inv H (dec_step n k Hk))
      else
        scan x n k' p' mx imx mn imn (Acc_inv H (dec_step n k Hk))
  | right _ => (imx, imn)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: prefix sums on the math string                           *)
(* ------------------------------------------------------------------ *)

(* #R - #B of a string. *)
Definition D (t : String.string) : Z :=
  (Z.of_N (count "R"%char t) - Z.of_N (count "B"%char t))%Z.

(* P(k): #R - #B of the first k sections. *)
Definition Pn (s : String.string) (k : nat) : Z := D (String.substring 0 k s).

Lemma count_app : forall c t1 t2,
  count c (String.append t1 t2) = (count c t1 + count c t2)%N.
Proof.
  intros c t1 t2. induction t1 as [| a t1 IH]; simpl; [reflexivity |].
  rewrite IH. lia.
Qed.

Lemma D_app : forall t1 t2, D (String.append t1 t2) = (D t1 + D t2)%Z.
Proof. intros. unfold D. rewrite !count_app. lia. Qed.

Lemma substring_split : forall a l s,
  String.substring 0 (a + l) s
  = String.append (String.substring 0 a s) (String.substring a l s).
Proof.
  induction a as [| a IH]; intros l s.
  - destruct s; destruct l; reflexivity.
  - destruct s as [| c s]; simpl; [reflexivity |].
    rewrite IH. reflexivity.
Qed.

Lemma substring_one : forall k s c, String.get k s = Some c ->
  String.substring k 1 s = String.String c String.EmptyString.
Proof.
  induction k as [| k IH]; intros s c H; destruct s as [| a s];
    simpl in H |- *; try discriminate.
  - inversion H. destruct s; reflexivity.
  - apply IH. exact H.
Qed.

Lemma Pn_step : forall s k c, String.get k s = Some c ->
  Pn s (S k) = (Pn s k + D (String.String c String.EmptyString))%Z.
Proof.
  intros s k c H. unfold Pn. replace (S k) with (k + 1)%nat by lia.
  rewrite substring_split, D_app, (substring_one _ _ _ H). reflexivity.
Qed.

Lemma Pn_0 : forall s, Pn s 0 = 0%Z.
Proof. intros s. destruct s; reflexivity. Qed.

Lemma difference_Pn : forall s i j, is_part s i j ->
  difference s i j = Z.abs (Pn s (N.to_nat j) - Pn s (N.to_nat (i - 1))).
Proof.
  intros s i j Hp. unfold is_part in Hp.
  unfold difference, part.
  assert (Ej : N.to_nat j = (N.to_nat (i - 1) + N.to_nat (j - i + 1))%nat) by lia.
  assert (E : Pn s (N.to_nat j) = (Pn s (N.to_nat (i - 1))
             + D (String.substring (N.to_nat (i - 1)) (N.to_nat (j - i + 1)) s))%Z).
  { unfold Pn. rewrite Ej, substring_split, D_app. reflexivity. }
  rewrite E. unfold D. f_equal. lia.
Qed.

(* One step of the scan on the math side. *)
Lemma char_step : forall s x, valid_input s -> repr x s ->
  forall k : int, ((φ k) < Z.of_nat (String.length s))%Z ->
  Pn s (S (Z.to_nat (φ k)))
  = (Pn s (Z.to_nat (φ k)) + if (PrimString.get x k =? 82)%uint63 then 1 else -1)%Z.
Proof.
  intros s x Hv [Hl Hc] k Hk.
  pose proof (to_Z_bounded k) as Bk.
  destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as (c & Hg & Hrc).
  rewrite Z2Nat.id in Hrc by lia. rewrite of_to_Z in Hrc.
  unfold repr, repr_uint in Hrc.
  rewrite (Pn_step _ _ _ Hg).
  pose proof (to_Z_bounded (PrimString.get x k)) as Bg.
  destruct (vi_colors _ Hv _ _ Hg) as [-> | ->]; simpl in Hrc |- *.
  - assert (E : (φ (PrimString.get x k)) = 82%Z) by lia.
    replace (PrimString.get x k =? 82) with true; [reflexivity |].
    symmetry. rewrite Uint63.eqb_spec. apply to_Z_inj. rewrite E. reflexivity.
  - assert (E : (φ (PrimString.get x k)) = 66%Z) by lia.
    replace (PrimString.get x k =? 82) with false; [reflexivity |].
    symmetry. rewrite Uint63.eqb_false_spec. intros Heq. rewrite Heq in E.
    discriminate E.
Qed.

(* ------------------------------------------------------------------ *)
(* The loop invariant                                                  *)
(* ------------------------------------------------------------------ *)

Definition inv (s : String.string) (n k p mx imx mn imn : int) : Prop :=
  ((φ k) <= (φ n))%Z /\
  (φ p) = ((φ n) + Pn s (Z.to_nat (φ k)))%Z /\
  (- (φ k) <= Pn s (Z.to_nat (φ k)) <= (φ k))%Z /\
  (φ mx) = ((φ n) + Pn s (Z.to_nat (φ imx)))%Z /\
  (φ mn) = ((φ n) + Pn s (Z.to_nat (φ imn)))%Z /\
  ((φ imx) <= (φ k))%Z /\ ((φ imn) <= (φ k))%Z /\
  (forall t, (t <= Z.to_nat (φ k))%nat -> Pn s t <= Pn s (Z.to_nat (φ imx)))%Z /\
  (forall t, (t < Z.to_nat (φ imx))%nat -> Pn s t < Pn s (Z.to_nat (φ imx)))%Z /\
  (forall t, (t <= Z.to_nat (φ k))%nat -> Pn s (Z.to_nat (φ imn)) <= Pn s t)%Z /\
  (forall t, (t < Z.to_nat (φ imn))%nat -> Pn s (Z.to_nat (φ imn)) < Pn s t)%Z.

Lemma scan_spec : forall s x, valid_input s -> repr x s ->
  forall (z : Z) (k p mx imx mn imn : int)
         (H : Acc (Zwf 0) (gap (PrimString.length x) k)),
  gap (PrimString.length x) k = z ->
  inv s (PrimString.length x) k p mx imx mn imn ->
  exists k' p' mx' mn',
    (φ k') = (φ (PrimString.length x)) /\
    inv s (PrimString.length x) k' p' mx'
        (fst (scan x (PrimString.length x) k p mx imx mn imn H)) mn'
        (snd (scan x (PrimString.length x) k p mx imx mn imn H)).
Proof.
  intros s x Hv Hr z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k p mx imx mn imn H Hz Hinv.
  pose proof Hr as [Hl _].
  set (n := PrimString.length x) in *.
  pose proof (vi_n _ Hv) as Hn. unfold slen in Hn.
  rewrite scan_eq.
  destruct (bdec (k <? n)) as [Hk | Hk].
  - cbv zeta.
    pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    pose proof (to_Z_bounded k) as Bk.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (HK1 : Z.to_nat (φ (k + 1)) = S (Z.to_nat (φ k))) by lia.
    pose proof (char_step s x Hv Hr k ltac:(lia)) as Hstep.
    destruct Hinv as (Hkn & Hp & HPb & Hmx & Hmn & Himx & Himn
                      & Hmax1 & Hmax2 & Hmin1 & Hmin2).
    set (K := Z.to_nat (φ k)) in *.
    set (p' := if PrimString.get x k =? 82 then p + 1 else p - 1).
    assert (Hp' : (φ p') = ((φ n) + Pn s (S K))%Z /\
                  (- (φ (k + 1)) <= Pn s (S K) <= (φ (k + 1)))%Z).
    { subst p'. rewrite Hstep.
      destruct (PrimString.get x k =? 82); split; lia. }
    destruct Hp' as [Hp' HPb'].
    assert (Hz' : Zwf 0 (gap n (k + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hk).
    destruct (mx <? p') eqn:E1.
    + rewrite ltb_spec in E1.
      eapply IH; [exact Hz' | reflexivity |].
      unfold inv. rewrite HK1.
      do 7 (split; [first [assumption | lia] |]).
      split; [| split; [| split]].
      * intros t Ht. destruct (Nat.eq_dec t (S K)) as [-> | Hne]; [lia |].
        specialize (Hmax1 t ltac:(lia)). lia.
      * intros t Ht. specialize (Hmax1 t ltac:(lia)). lia.
      * intros t Ht. destruct (Nat.eq_dec t (S K)) as [-> | Hne].
        -- specialize (Hmin1 K ltac:(lia)). specialize (Hmax1 K ltac:(lia)). lia.
        -- apply Hmin1. lia.
      * exact Hmin2.
    + destruct (p' <? mn) eqn:E2.
      * rewrite ltb_spec in E2.
        eapply IH; [exact Hz' | reflexivity |].
        unfold inv. rewrite HK1.
        do 7 (split; [first [assumption | lia] |]).
        split; [| split; [| split]].
        -- intros t Ht. destruct (Nat.eq_dec t (S K)) as [-> | Hne].
           ++ lia.
           ++ apply Hmax1. lia.
        -- exact Hmax2.
        -- intros t Ht. destruct (Nat.eq_dec t (S K)) as [-> | Hne]; [lia |].
           specialize (Hmin1 t ltac:(lia)). lia.
        -- intros t Ht. specialize (Hmin1 t ltac:(lia)). lia.
      * rewrite <- Bool.not_true_iff_false, ltb_spec in E2.
        rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
        eapply IH; [exact Hz' | reflexivity |].
        unfold inv. rewrite HK1.
        do 7 (split; [first [assumption | lia] |]).
        split; [| split; [| split]].
        -- intros t Ht. destruct (Nat.eq_dec t (S K)) as [-> | Hne]; [lia |].
           apply Hmax1. lia.
        -- exact Hmax2.
        -- intros t Ht. destruct (Nat.eq_dec t (S K)) as [-> | Hne]; [lia |].
           apply Hmin1. lia.
        -- exact Hmin2.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    exists k, p, mx, mn. split; [destruct Hinv; lia | exact Hinv].
Qed.

(* ------------------------------------------------------------------ *)
(* The optimum, on any sequence                                        *)
(* ------------------------------------------------------------------ *)

Lemma opt : forall (f : nat -> Z) (n M m : nat),
  (M <= n)%nat -> (m <= n)%nat ->
  (forall t, (t <= n)%nat -> f t <= f M)%Z ->
  (forall t, (t < M)%nat -> f t < f M)%Z ->
  (forall t, (t <= n)%nat -> f m <= f t)%Z ->
  (forall t, (t < m)%nat -> f m < f t)%Z ->
  forall a b, (a < b <= n)%nat ->
  (Z.abs (f b - f a) <= f M - f m)%Z /\
  (Z.abs (f b - f a) = f M - f m ->
   (Nat.min M m < a)%nat \/ (Nat.min M m = a /\ Nat.max M m <= b)%nat)%Z.
Proof.
  intros f n M m HM Hm Hmax1 Hmax2 Hmin1 Hmin2 a b Hab.
  pose proof (Hmax1 a ltac:(lia)) as A1. pose proof (Hmax1 b ltac:(lia)) as A2.
  pose proof (Hmin1 a ltac:(lia)) as A3. pose proof (Hmin1 b ltac:(lia)) as A4.
  split; [lia |]. intros Heq.
  destruct (Z.le_gt_cases (f a) (f b)) as [Hle | Hgt].
  - (* f a = min, f b = max *)
    assert (Ea : f a = f m) by lia. assert (Eb : f b = f M) by lia.
    assert (Hma : (m <= a)%nat).
    { destruct (Nat.lt_ge_cases a m) as [Hlt | Hge]; [| exact Hge].
      specialize (Hmin2 a Hlt). lia. }
    destruct (Nat.eq_dec m a) as [<- | Hne]; [| left; lia].
    assert (HMb : (M <= b)%nat).
    { destruct (Nat.lt_ge_cases b M) as [Hlt | Hge]; [| exact Hge].
      specialize (Hmax2 b Hlt). lia. }
    destruct (Nat.lt_ge_cases M m); [left; lia | right; lia].
  - assert (Ea : f a = f M) by lia. assert (Eb : f b = f m) by lia.
    assert (HMa : (M <= a)%nat).
    { destruct (Nat.lt_ge_cases a M) as [Hlt | Hge]; [| exact Hge].
      specialize (Hmax2 a Hlt). lia. }
    destruct (Nat.eq_dec M a) as [<- | Hne]; [| left; lia].
    assert (Hmb : (m <= b)%nat).
    { destruct (Nat.lt_ge_cases b m) as [Hlt | Hge]; [| exact Hge].
      specialize (Hmin2 b Hlt). lia. }
    destruct (Nat.lt_ge_cases m M); [left; lia | right; lia].
Qed.

Lemma final_math : forall s (M m : nat),
  let n := String.length s in
  (M <= n)%nat -> (m <= n)%nat ->
  (forall t, (t <= n)%nat -> Pn s t <= Pn s M)%Z ->
  (forall t, (t < M)%nat -> Pn s t < Pn s M)%Z ->
  (forall t, (t <= n)%nat -> Pn s m <= Pn s t)%Z ->
  (forall t, (t < m)%nat -> Pn s m < Pn s t)%Z ->
  (Pn s m < Pn s M)%Z ->
  purplerain_spec s (N.of_nat (Nat.min M m) + 1, N.of_nat (Nat.max M m))%N.
Proof.
  intros s M m n HM Hm Hmax1 Hmax2 Hmin1 Hmin2 Hlt.
  assert (HMm : M <> m) by (intros ->; lia).
  assert (Hpart : is_part s (N.of_nat (Nat.min M m) + 1) (N.of_nat (Nat.max M m))).
  { unfold is_part, slen. fold n. lia. }
  assert (Hd : difference s (N.of_nat (Nat.min M m) + 1) (N.of_nat (Nat.max M m))
               = (Pn s M - Pn s m)%Z).
  { rewrite (difference_Pn _ _ _ Hpart).
    replace (N.to_nat (N.of_nat (Nat.max M m))) with (Nat.max M m) by lia.
    replace (N.to_nat (N.of_nat (Nat.min M m) + 1 - 1)) with (Nat.min M m) by lia.
    destruct (Nat.lt_ge_cases M m).
    - rewrite Nat.max_r, Nat.min_l by lia. lia.
    - rewrite Nat.max_l, Nat.min_r by lia. lia. }
  unfold purplerain_spec.
  split; [exact Hpart |]. rewrite Hd.
  split.
  - intros i' j' Hp'. rewrite (difference_Pn _ _ _ Hp').
    unfold is_part, slen in Hp'. fold n in Hp'.
    apply (opt (Pn s) n M m HM Hm Hmax1 Hmax2 Hmin1 Hmin2). lia.
  - intros i' j' Hp' Heq. rewrite (difference_Pn _ _ _ Hp') in Heq.
    unfold is_part, slen in Hp'. fold n in Hp'.
    destruct (opt (Pn s) n M m HM Hm Hmax1 Hmax2 Hmin1 Hmin2
                (N.to_nat (i' - 1)) (N.to_nat j') ltac:(lia)) as [_ Hw].
    unfold west_or_equal. destruct (Hw Heq) as [H1 | [H1 H2]]; [left | right]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Theorem purplerain_impl_correct : forall (s : String.string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists o : N * N, repr (purplerain_impl x) o /\ purplerain_spec s o.
Proof.
  intros s x Hv Hr.
  pose proof Hr as [Hl _].
  pose proof (vi_n _ Hv) as Hn. unfold slen in Hn.
  set (n := PrimString.length x) in *.
  assert (Hinv0 : inv s n 0 n n 0 n 0).
  { unfold inv. change (Z.to_nat (φ 0)) with 0%nat. rewrite Pn_0.
    change (φ 0) with 0%Z.
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [| split; [| split]]; intros t Ht; try lia;
      replace t with 0%nat by lia; rewrite Pn_0; lia. }
  destruct (scan_spec s x Hv Hr _ 0 n n 0 n 0 (Zwf_well_founded 0 (gap n 0))
              eq_refl Hinv0) as (k & p & mx & mn & Hk & Hinv).
  unfold purplerain_impl. fold n.
  change (PrimString.length x) with n in Hk, Hinv.
  destruct (scan x n 0 n n 0 n 0 (Zwf_well_founded 0 (gap n 0))) as [a b].
  simpl in Hinv.
  destruct Hinv as (Hkn & Hp & HPb & Hmx & Hmn & Hia & Hib
                    & Hmax1 & Hmax2 & Hmin1 & Hmin2).
  assert (HK : Z.to_nat (φ k) = String.length s) by lia.
  rewrite HK in Hmax1, Hmin1.
  (* the maximum is above the minimum: P(1) = P(0) +- 1 *)
  assert (Hlt : (Pn s (Z.to_nat (φ b)) < Pn s (Z.to_nat (φ a)))%Z).
  { pose proof (char_step s x Hv Hr 0 ltac:(change (φ 0) with 0%Z; lia)) as H1.
    change (Z.to_nat (φ 0)) with 0%nat in H1. rewrite Pn_0 in H1.
    pose proof (Hmax1 0%nat ltac:(lia)). pose proof (Hmax1 1%nat ltac:(lia)).
    pose proof (Hmin1 0%nat ltac:(lia)). pose proof (Hmin1 1%nat ltac:(lia)).
    rewrite !Pn_0 in *.
    match type of H1 with context [if ?c then _ else _] => destruct c end; lia. }
  pose proof (final_math s (Z.to_nat (φ a)) (Z.to_nat (φ b)) ltac:(lia) ltac:(lia)
                Hmax1 Hmax2 Hmin1 Hmin2 Hlt) as Hspec.
  pose proof (to_Z_bounded a) as Ba. pose proof (to_Z_bounded b) as Bb.
  eexists. split; [| exact Hspec].
  cbv [repr repr_pair repr_uint fst snd].
  destruct (a <? b) eqn:E.
  - rewrite ltb_spec in E. split; sia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. split; sia.
Qed.

Definition purplerain_correct : forall (s : String.string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists o : N * N, repr (purplerain x) o /\ purplerain_spec s o
  := purplerain_impl_correct.
