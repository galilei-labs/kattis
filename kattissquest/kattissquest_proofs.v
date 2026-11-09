(* Correctness proofs for kattissquest_implem.v. *)
(* Implementation of kattissquest (kattissquest.spec).

   See the README of this try for the design; the code section below is
   self-contained. *)

From Kattissquest.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Kattissquest Require Export kattissquest_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ================================================================== *)
(* Proofs                                                              *)
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
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
Proof. intros t i b H. apply (get_set_same int t i b). rewrite ltb_spec. exact H. Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  (φ i) <> (φ j) -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. apply (get_set_other int t i j b). intro E; apply H; rewrite E; reflexivity. Qed.

Lemma alength_make : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H.
  assert (E : PArray.length (PArray.make n b)
     = if n <=? PArray.max_length then n else PArray.max_length) by exact (length_make int n b).
  etransitivity; [exact E|].
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma aget_make : forall (n : int) (b : int) (i : int), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make int b n i). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_bound_any : forall A (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma add_nov : forall a b : int, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof.
  intros a b H. rewrite add_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a); pose proof (to_Z_bounded b); lia.
Qed.

Lemma sub_nov : forall a b : int, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof.
  intros a b H. rewrite sub_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a); pose proof (to_Z_bounded b); lia.
Qed.

Lemma mul_nov : forall a b : int, ((φ a) * (φ b) < wB)%Z -> (φ (a * b)) = ((φ a) * (φ b))%Z.
Proof.
  intros a b H. rewrite mul_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a); pose proof (to_Z_bounded b); nia.
Qed.

Lemma shl_nov : forall a l : int, ((φ a) * 2 ^ (φ l) < wB)%Z -> (φ (a << l)) = ((φ a) * 2 ^ (φ l))%Z.
Proof.
  intros a l H. rewrite lsl_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a); pose proof (to_Z_bounded l).
  assert (0 < 2 ^ (φ l))%Z by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma shr_spec : forall a l : int, (φ (a >> l)) = ((φ a) / 2 ^ (φ l))%Z.
Proof. intros. apply lsr_spec. Qed.

Lemma ltb_Z : forall a b : int, (a <? b) = ((φ a) <? (φ b))%Z.
Proof.
  intros a b. destruct (a <? b) eqn:E; destruct ((φ a) <? (φ b))%Z eqn:F; auto.
  - rewrite ltb_spec in E. rewrite Z.ltb_ge in F. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. rewrite Z.ltb_lt in F. lia.
Qed.

Lemma leb_Z : forall a b : int, (a <=? b) = ((φ a) <=? (φ b))%Z.
Proof.
  intros a b. destruct (a <=? b) eqn:E; destruct ((φ a) <=? (φ b))%Z eqn:F; auto.
  - rewrite leb_spec in E. rewrite Z.leb_gt in F. lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec in E. rewrite Z.leb_le in F. lia.
Qed.

Lemma eqb_Z : forall a b : int, (a =? b) = ((φ a) =? (φ b))%Z.
Proof.
  intros a b. destruct (a =? b) eqn:E; destruct ((φ a) =? (φ b))%Z eqn:F; auto.
  - rewrite eqb_spec in E. subst. rewrite Z.eqb_neq in F. lia.
  - rewrite eqb_false_spec in E. rewrite Z.eqb_eq in F. exfalso. apply E. apply to_Z_inj. exact F.
Qed.

Ltac neq := let E := fresh in intro E; lia.

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Node sizes                                                          *)
(* ------------------------------------------------------------------ *)

Definition lo (k : Z) : Z := k / 2.
Definition hi (k : Z) : Z := k - k / 2.

Fixpoint szf (n : nat) (k : Z) : Z :=
  match n with
  | O => 2
  | S n => if k <=? 1 then 2 else 2 + szf n (hi k) + 2 ^ hi k * szf n (lo k)
  end.

Definition sz (k : Z) : Z := szf (Z.to_nat k) k.

Lemma hilo : forall k, 2 <= k -> 1 <= lo k /\ 1 <= hi k /\ hi k < k /\ lo k < k /\ hi k + lo k = k
  /\ lo k <= hi k.
Proof. intros k H. unfold lo, hi. Z.to_euclidean_division_equations. lia. Qed.

Lemma szf_stable : forall n k, k <= Z.of_nat n -> szf (S n) k = szf n k.
Proof.
  induction n as [| n IH]; intros k Hk.
  - simpl. destruct (k <=? 1) eqn:E; [reflexivity|]. rewrite Z.leb_gt in E. lia.
  - change (szf (S (S n)) k) with
      (if k <=? 1 then 2 else 2 + szf (S n) (hi k) + 2 ^ hi k * szf (S n) (lo k)).
    change (szf (S n) k) with
      (if k <=? 1 then 2 else 2 + szf n (hi k) + 2 ^ hi k * szf n (lo k)).
    destruct (k <=? 1) eqn:E; [reflexivity|]. rewrite Z.leb_gt in E.
    destruct (hilo k ltac:(lia)) as (? & ? & ? & ? & ? & ?).
    rewrite IH, (IH (lo k)) by lia. reflexivity.
Qed.

Lemma szf_ge : forall d n k, k <= Z.of_nat n -> szf (d + n) k = szf n k.
Proof.
  induction d as [| d IH]; intros n k Hk; [reflexivity|].
  change (S d + n)%nat with (S (d + n)). rewrite szf_stable by lia. apply IH. exact Hk.
Qed.

Lemma sz_node : forall k, 2 <= k -> sz k = 2 + sz (hi k) + 2 ^ hi k * sz (lo k).
Proof.
  intros k Hk. destruct (hilo k Hk) as (? & ? & ? & ? & ? & ?).
  unfold sz. replace (Z.to_nat k) with (S (Z.to_nat k - 1)) by lia.
  change (szf (S (Z.to_nat k - 1)) k) with
    (if k <=? 1 then 2 else 2 + szf (Z.to_nat k - 1) (hi k) + 2 ^ hi k * szf (Z.to_nat k - 1) (lo k)).
  replace (k <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.to_nat k - 1)%nat with ((Z.to_nat k - 1 - Z.to_nat (hi k)) + Z.to_nat (hi k))%nat at 1 by lia.
  rewrite szf_ge by lia.
  replace (Z.to_nat k - 1)%nat with ((Z.to_nat k - 1 - Z.to_nat (lo k)) + Z.to_nat (lo k))%nat at 1 by lia.
  rewrite szf_ge by lia. reflexivity.
Qed.

Lemma sz_leaf : sz 1 = 2.
Proof. reflexivity. Qed.

Lemma szf_ge2 : forall n k, 2 <= szf n k.
Proof.
  induction n as [| n IH]; intros k; [simpl; lia|].
  change (szf (S n) k) with
    (if k <=? 1 then 2 else 2 + szf n (hi k) + 2 ^ hi k * szf n (lo k)).
  destruct (k <=? 1); [lia|].
  pose proof (IH (hi k)); pose proof (IH (lo k)).
  assert (0 <= 2 ^ hi k) by (apply Z.pow_nonneg; lia). nia.
Qed.

Lemma sz_ge2 : forall k, 2 <= sz k.
Proof. intros. apply szf_ge2. Qed.

Lemma sz_bound : forall k, 1 <= k <= 17 -> sz k <= 368024.
Proof.
  intros k Hk.
  assert (k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
          k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17) by lia.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end;
    subst; vm_compute; congruence.
Qed.

Definition nilZ : Z := 9223372036854775807.

Lemma nil_val : (φ nil) = nilZ.
Proof. reflexivity. Qed.

Lemma kl_spec : forall k : int, (φ (kl k)) = lo (φ k).
Proof. intros. unfold kl, lo. apply shr1_spec. Qed.

Lemma kh_spec : forall k : int, (φ (kh k)) = hi (φ k).
Proof.
  intros k. unfold kh, hi. rewrite sub_nov; rewrite shr1_spec; [reflexivity|].
  pose proof (to_Z_bounded k). Z.to_euclidean_division_equations. lia.
Qed.

Lemma pow_split : forall k, 0 <= k -> 2 ^ k = 2 ^ hi k * 2 ^ lo k.
Proof.
  intros k Hk. rewrite <- Z.pow_add_r; [f_equal| |]; unfold hi, lo;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma pow17 : forall k, 0 <= k <= 17 -> 1 <= 2 ^ k <= 131072.
Proof.
  intros k Hk. split.
  - apply (Z.pow_le_mono_r 2 0 k); lia.
  - change 131072 with (2 ^ 17). apply Z.pow_le_mono_r; lia.
Qed.

(* lexicographic order of (high, low) pairs *)
Lemma lex_le : forall P i j i' j', 0 <= j < P -> 0 <= j' < P ->
  (i * P + j <= i' * P + j' <-> i < i' \/ (i = i' /\ j <= j')).
Proof.
  intros P i j i' j' Hj Hj'. split.
  - intros H. destruct (Z.lt_trichotomy i i') as [E | [E | E]]; [left; lia | right; subst; lia |].
    exfalso. assert (i' * P + P <= i * P) by nia. lia.
  - intros [H | [H1 H2]]; [ | subst; lia]. assert (i * P + P <= i' * P) by nia. lia.
Qed.

Lemma mul_step : forall i n s, 0 <= i < n -> 0 <= s -> i * s + s <= n * s.
Proof. intros. nia. Qed.

Lemma decode : forall P i j, 0 <= j < P -> (i * P + j) / P = i /\ (i * P + j) mod P = j.
Proof.
  intros P i j Hj. split.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma encode : forall P y, 0 < P -> y = y / P * P + y mod P /\ 0 <= y mod P < P.
Proof.
  intros P y HP. split; [| apply Z.mod_pos_bound; lia].
  rewrite (Z.div_mod y P) at 1 by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The vEB invariant                                                   *)
(* ------------------------------------------------------------------ *)

Ltac clear_vals :=
  repeat match goal with
  | H : context [Z.div _ _] |- _ => clear H
  | H : context [Z.modulo _ _] |- _ => clear H
  | H : context [Z.max _ _] |- _ => clear H
  | H : context [Z.min _ _] |- _ => clear H
  | H : context [nilZ] |- _ => clear H
  | H : context [Z.pow _ (φ _)] |- _ => clear H
  end.

Ltac clear_pos :=
  repeat match goal with
  | H : context [sz _] |- _ => clear H
  | H : context [PArray.length _] |- _ => clear H
  | H : context [clb _ _ _ _] |- _ => clear H
  end.

Ltac flia := first [ clear_vals; lia | clear_pos; lia | lia ].

Section VEB.

Variable t : array int.
Variable K : Z.
Hypothesis HK : 1 <= K <= 17.
Hypothesis Ht : forall h : int, 1 <= (φ h) <= K -> (φ (t.[h])) = sz (φ h).

Definition leafinv (m M : Z) (S : Z -> Prop) : Prop :=
  (m = nilZ /\ M = nilZ /\ forall y, ~ S y) \/
  (0 <= m <= M /\ M < 2 /\ forall y, S y <-> y = m \/ y = M).

Definition nodeinv (P W m M : Z) (S : Z -> Prop) (C : Z -> Z -> Prop) : Prop :=
  (m = nilZ /\ M = nilZ /\ (forall y, ~ S y) /\ (forall i j, ~ C i j)) \/
  (0 <= m <= M /\ M < W /\
   (forall y, S y <-> y = m \/ (0 <= y /\ C (y / P) (y mod P))) /\
   (forall i j, C i j -> m < i * P + j <= M) /\
   ((m = M /\ forall i j, ~ C i j) \/ (m < M /\ C (M / P) (M mod P)))).

(* [ok v b k S]: the node at cell b of v, of universe 2^k, holds the set S *)
Inductive ok (v : array int) : int -> int -> (Z -> Prop) -> Prop :=
| ok_leaf : forall b k S, (φ k) = 1 -> (φ b) + 2 <= (φ (PArray.length v)) ->
    leafinv (φ (v.[b])) (φ (v.[b + 1])) S -> ok v b k S
| ok_node : forall b k S Ss C, 2 <= (φ k) <= K -> (φ b) + sz (φ k) <= (φ (PArray.length v)) ->
    ok v (b + 2) (kh k) Ss ->
    (forall i : int, (φ i) < 2 ^ hi (φ k) -> ok v (clb t b k i) (kl k) (C (φ i))) ->
    (forall i, Ss i <-> 0 <= i < 2 ^ hi (φ k) /\ exists j, C i j) ->
    (forall i j, C i j -> 0 <= i < 2 ^ hi (φ k)) ->
    nodeinv (2 ^ lo (φ k)) (2 ^ (φ k)) (φ (v.[b])) (φ (v.[b + 1])) S C ->
    ok v b k S.

Definition hide (P : Prop) : Prop := P.

Lemma geom_leaf : forall b : int, (φ b) + 2 <= 4194303 -> (φ (b + 1)) = (φ b) + 1.
Proof. intros b H. rewrite add_nov; change (φ 1) with 1; [lia|]. pose proof (to_Z_bounded b). rewrite wB_val. lia. Qed.

Lemma geom : forall (b k : int), 2 <= (φ k) <= K -> (φ b) + sz (φ k) <= 4194303 ->
  (φ (b + 1)) = (φ b) + 1 /\ (φ (b + 2)) = (φ b) + 2 /\ (φ (b + 2 + 1)) = (φ b) + 3 /\
  sz (φ k) = 2 + sz (hi (φ k)) + 2 ^ hi (φ k) * sz (lo (φ k)) /\
  (φ (kh k)) = hi (φ k) /\ (φ (kl k)) = lo (φ k) /\ 1 <= lo (φ k) /\ 1 <= hi (φ k) /\
  hi (φ k) < (φ k) /\ lo (φ k) < (φ k) /\ hi (φ k) + lo (φ k) = (φ k) /\ lo (φ k) <= hi (φ k) /\
  2 ^ (φ k) = 2 ^ hi (φ k) * 2 ^ lo (φ k) /\ 2 <= 2 ^ lo (φ k) /\ 2 <= 2 ^ hi (φ k) /\
  2 ^ (φ k) <= 131072 /\
  (forall i : int, 0 <= (φ i) < 2 ^ hi (φ k) ->
     (φ (clb t b k i)) = (φ b) + 2 + sz (hi (φ k)) + (φ i) * sz (lo (φ k)) /\
     (φ (clb t b k i + 1)) = (φ b) + 2 + sz (hi (φ k)) + (φ i) * sz (lo (φ k)) + 1 /\
     (φ b) + 2 + sz (hi (φ k)) + (φ i) * sz (lo (φ k)) + sz (lo (φ k)) <= (φ b) + sz (φ k)).
Proof.
  intros b k Hk Hb.
  destruct (hilo (φ k) ltac:(lia)) as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (sz_node (φ k) ltac:(lia)) as Esz.
  pose proof (to_Z_bounded b) as Bb.
  pose proof (sz_ge2 (hi (φ k))) as S1. pose proof (sz_ge2 (lo (φ k))) as S2.
  pose proof (pow17 (lo (φ k)) ltac:(lia)) as P1.
  pose proof (pow17 (hi (φ k)) ltac:(lia)) as P2.
  pose proof (pow17 (φ k) ltac:(lia)) as P3.
  assert (Pl : 2 <= 2 ^ lo (φ k)).
  { change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia. }
  assert (Ph : 2 <= 2 ^ hi (φ k)).
  { change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia. }
  assert (Ekh : (φ (kh k)) = hi (φ k)) by apply kh_spec.
  assert (Ekl : (φ (kl k)) = lo (φ k)) by apply kl_spec.
  assert (Th : (φ (t.[kh k])) = sz (hi (φ k))) by (rewrite Ht; [rewrite Ekh; reflexivity | lia]).
  assert (Tl : (φ (t.[kl k])) = sz (lo (φ k))) by (rewrite Ht; [rewrite Ekl; reflexivity | lia]).
  assert (Q : 2 ^ hi (φ k) * sz (lo (φ k)) <= 4194303) by lia.
  try rewrite wB_val in *.
  assert (E1 : (φ (b + 1)) = (φ b) + 1) by (rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia).
  assert (E2 : (φ (b + 2)) = (φ b) + 2) by (rewrite add_nov; change (φ 2) with 2; rewrite ?wB_val; lia).
  assert (E3 : (φ (b + 2 + 1)) = (φ b) + 3) by (rewrite add_nov, E2; change (φ 1) with 1; rewrite ?wB_val; lia).
  do 16 (split; [first [assumption | lia | apply pow_split; lia] |]).
  intros i Hi.
  unfold clb.
  assert (Mi : (φ i) * sz (lo (φ k)) + sz (lo (φ k)) <= 2 ^ hi (φ k) * sz (lo (φ k)))
    by (apply mul_step; lia).
  assert (Ei : (φ (i * t.[kl k])) = (φ i) * sz (lo (φ k))).
  { rewrite mul_nov, Tl; [reflexivity|]. rewrite Tl, wB_val. lia. }
  assert (Ec : (φ (b + 2 + t.[kh k] + i * t.[kl k])) = (φ b) + 2 + sz (hi (φ k)) + (φ i) * sz (lo (φ k))).
  { rewrite add_nov, Ei, add_nov, E2, Th; rewrite ?E2, ?Th, ?Ei, ?wB_val; lia. }
  split; [exact Ec|]. split; [|lia].
  rewrite add_nov, Ec; change (φ 1) with 1; rewrite ?Ec, ?wB_val; lia.
Qed.

Lemma ok_info : forall v b k S, ok v b k S ->
  1 <= (φ k) <= K /\ (φ b) + sz (φ k) <= (φ (PArray.length v)).
Proof.
  intros v b k S H. destruct H as [b k S Hk Hl _ | b k S Ss C Hk Hl _ _ _ _ _].
  - rewrite Hk, sz_leaf. lia.
  - lia.
Qed.

Lemma ok_minmax : forall v b k S, ok v b k S ->
  ((φ (v.[b])) = nilZ /\ (φ (v.[b + 1])) = nilZ /\ forall y, ~ S y) \/
  (0 <= (φ (v.[b])) <= (φ (v.[b + 1])) /\ (φ (v.[b + 1])) < 2 ^ (φ k) /\ S (φ (v.[b])) /\ S (φ (v.[b + 1])) /\
   forall y, S y -> (φ (v.[b])) <= y <= (φ (v.[b + 1]))).
Proof.
  intros v b k S H. destruct H as [b k S Hk Hl Hinv | b k S Ss C Hk Hl Hs Hc HSs HCi Hinv].
  - destruct Hinv as [Hinv | (Hm & HM & HS)]; [left; exact Hinv|]. right.
    rewrite Hk. change (2 ^ 1) with 2.
    split; [lia|]. split; [lia|]. split; [apply HS; left; reflexivity|].
    split; [apply HS; right; reflexivity|]. intros y Hy. apply HS in Hy. lia.
  - destruct Hinv as [(H1 & H2 & H3 & _) | (Hm & HM & HS & HCb & Hlast)];
      [left; auto|]. right.
    assert (P : 0 < 2 ^ lo (φ k)) by (apply Z.pow_pos_nonneg; unfold lo; Z.to_euclidean_division_equations; lia).
    split; [lia|]. split; [lia|]. split; [apply HS; left; reflexivity|]. split.
    + apply HS. destruct Hlast as [[E _] | [_ Hc']]; [left; lia | right; split; [lia | exact Hc']].
    + intros y Hy. apply HS in Hy. destruct Hy as [Hy | [Hy0 Hy]]; [lia|].
      apply HCb in Hy. destruct (encode (2 ^ lo (φ k)) y P) as [Ey _]. lia.
Qed.

Lemma ok_range : forall v b k S, ok v b k S -> forall y, S y -> 0 <= y < 2 ^ (φ k).
Proof.
  intros v b k S H y Hy. destruct (ok_minmax v b k S H) as [(_ & _ & E) | (A & B & _ & _ & D)].
  - exfalso. exact (E y Hy).
  - specialize (D y Hy). lia.
Qed.

Lemma ok_ext : forall v b k S S', ok v b k S -> (forall y, S y <-> S' y) -> ok v b k S'.
Proof.
  intros v b k S S' H E. destruct H as [b k S Hk Hl Hinv | b k S Ss C Hk Hl Hs Hc HSs HCi Hinv].
  - apply ok_leaf; auto. destruct Hinv as [(A & B & C) | (A & B & C)]; [left | right].
    + split; [exact A|]. split; [exact B|]. intros y Hy. apply (C y). apply E. exact Hy.
    + split; [exact A|]. split; [exact B|]. intros y. rewrite <- E. apply C.
  - apply (ok_node v b k S' Ss C); auto.
    destruct Hinv as [(A & B & D & F) | (A & B & D & F)]; [left | right].
    + split; [exact A|]. split; [exact B|]. split; [|exact F]. intros y Hy. apply (D y). apply E. exact Hy.
    + split; [exact A|]. split; [exact B|]. split; [|exact F]. intros y. rewrite <- E. apply D.
Qed.

Lemma ok_frame : forall v b k S, ok v b k S -> forall v',
  PArray.length v' = PArray.length v ->
  (forall p : int, (φ b) <= (φ p) < (φ b) + sz (φ k) -> v'.[p] = v.[p]) ->
  ok v' b k S.
Proof.
  intros v b k S H. induction H as [b k S Hk Hl Hinv | b k S Ss C Hk Hl Hs IHs Hc IHc HSs HCi Hinv];
    intros v' Hlen Hfr.
  - pose proof (alength_bound v).
    assert (E1 := geom_leaf b ltac:(lia)).
    rewrite Hk, sz_leaf in Hfr.
    apply ok_leaf; [exact Hk | rewrite Hlen; exact Hl |].
    rewrite (Hfr b), (Hfr (b + 1)%uint63) by lia. exact Hinv.
  - pose proof (alength_bound v).
    destruct (geom b k Hk ltac:(lia)) as (E1 & E2 & E3 & Esz & Ekh & Ekl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ecl).
    apply (ok_node v' b k S Ss C); auto.
    + rewrite Hlen; exact Hl.
    + apply IHs; [exact Hlen|]. intros p Hp. apply Hfr. rewrite E2, Ekh in Hp.
      assert (0 <= 2 ^ hi (φ k) * sz (lo (φ k)))
        by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg; lia | pose proof (sz_ge2 (lo (φ k))); lia]).
      lia.
    + intros i Hi. apply IHc; [exact Hi | exact Hlen |]. intros p Hp. apply Hfr.
      pose proof (to_Z_bounded i).
      destruct (Ecl i ltac:(lia)) as (F1 & _ & F3). rewrite F1, Ekl in Hp.
      pose proof (sz_ge2 (hi (φ k))). pose proof (sz_ge2 (lo (φ k))).
      assert (0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; lia). lia.
    + rewrite (Hfr b), (Hfr (b + 1)%uint63) by (pose proof (sz_ge2 (φ k)); lia). exact Hinv.
Qed.

Lemma set2 : forall (v : array int) (b x y : int), (φ b) + 2 <= (φ (PArray.length v)) ->
  let v' := v.[b <- x].[(b + 1)%uint63 <- y] in
  PArray.length v' = PArray.length v /\ v'.[b] = x /\ v'.[(b + 1)%uint63] = y /\
  forall p : int, (φ p) <> (φ b) -> (φ p) <> (φ b) + 1 -> v'.[p] = v.[p].
Proof.
  intros v b x y H v'. pose proof (alength_bound v).
  pose proof (geom_leaf b ltac:(lia)) as E1. unfold v'.
  split; [rewrite !alength_set; reflexivity|].
  split; [rewrite aget_set_other by lia; apply aget_set_same; lia|].
  split; [apply aget_set_same; rewrite alength_set; lia|].
  intros p Hp1 Hp2. rewrite !aget_set_other by lia. reflexivity.
Qed.

Lemma ok_init : forall n (k b : int) (v : array int), (φ k) = n -> 1 <= (φ k) <= K ->
  (φ b) + sz (φ k) <= (φ (PArray.length v)) ->
  (forall p : int, (φ b) <= (φ p) < (φ b) + sz (φ k) -> v.[p] = nil) ->
  ok v b k (fun _ => False).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros k b v En Hk Hl Hnil. pose proof (alength_bound v).
  destruct (Z.eq_dec (φ k) 1) as [E1 | E1].
  - rewrite E1, sz_leaf in Hl, Hnil. apply ok_leaf; [exact E1 | exact Hl |].
    pose proof (geom_leaf b ltac:(lia)) as F.
    left. rewrite (Hnil b), (Hnil (b + 1)%uint63) by lia. auto.
  - destruct (geom b k ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & Esz & Ekh & Ekl & L1 & L2 & L3 & L4 & _ & _ & _ & _ & _ & _ & Ecl).
    assert (0 <= 2 ^ hi (φ k) * sz (lo (φ k)))
      by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg; lia | pose proof (sz_ge2 (lo (φ k))); lia]).
    apply (ok_node v b k _ (fun _ => False) (fun _ _ => False)); [lia | exact Hl | | | | | ].
    + apply (IH (hi (φ k))); [unfold Zwf; lia | exact Ekh | lia | rewrite F2, Ekh; lia |].
      intros p Hp. apply Hnil. rewrite F2, Ekh in Hp.
      lia.
    + intros i Hi. pose proof (to_Z_bounded i).
      destruct (Ecl i ltac:(lia)) as (G1 & _ & G3).
      apply (IH (lo (φ k))); [unfold Zwf; lia | exact Ekl | lia | rewrite G1, Ekl; lia |].
      intros p Hp. apply Hnil. rewrite G1, Ekl in Hp.
      pose proof (sz_ge2 (hi (φ k))).
      assert (0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; [lia | pose proof (sz_ge2 (lo (φ k))); lia]).
      lia.
    + intros i. split; [tauto | intros (_ & j & F); exact F].
    + intros i j F. destruct F.
    + left. rewrite (Hnil b), (Hnil (b + 1)%uint63) by (pose proof (sz_ge2 (φ k)); lia).
      split; [reflexivity|]. split; [reflexivity|]. split; intros; tauto.
Qed.

Lemma ok_single : forall v b k S (x : int), ok v b k S -> (forall y, ~ S y) ->
  (φ x) < 2 ^ (φ k) ->
  ok v.[b <- x].[(b + 1)%uint63 <- x] b k (fun y => y = (φ x)).
Proof.
  intros v b k S x H HS Hx. pose proof (to_Z_bounded x). pose proof (alength_bound v).
  destruct (ok_info v b k S H) as [Hk Hl].
  pose proof (sz_ge2 (φ k)).
  destruct (set2 v b x x ltac:(lia)) as (L & G1 & G2 & G3).
  destruct H as [b k S Hk' Hl' Hinv | b k S Ss C Hk' Hl' Hs Hc HSs HCi Hinv].
  - apply ok_leaf; [exact Hk' | rewrite L; exact Hl' |]. right.
    rewrite G1, G2. rewrite Hk' in Hx. change (2 ^ 1) with 2 in Hx. split; [lia|]. split; [lia|]. tauto.
  - destruct (geom b k Hk' ltac:(lia)) as (F1 & F2 & F3 & Esz & Ekh & Ekl & L1 & L2 & L3 & L4 & _ & _ & _ & _ & _ & _ & Ecl).
    assert (Cn : forall i j, ~ C i j).
    { destruct Hinv as [(_ & _ & _ & D) | (_ & _ & D & _)]; [exact D|].
      exfalso. apply (HS (φ (v.[b]))). apply D. left. reflexivity. }
    apply (ok_node _ b k _ Ss C); [exact Hk' | rewrite L; exact Hl' | | | exact HSs | exact HCi |].
    + apply (ok_frame v); [exact Hs | exact L |]. intros p Hp. apply G3; rewrite F2, Ekh in Hp; lia.
    + intros i Hi. pose proof (to_Z_bounded i). destruct (Ecl i ltac:(lia)) as (E1 & _ & _).
      pose proof (sz_ge2 (hi (φ k))).
      assert (0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; [lia | pose proof (sz_ge2 (lo (φ k))); lia]).
      apply (ok_frame v); [apply Hc; exact Hi | exact L |]. intros p Hp. apply G3; rewrite E1 in Hp; lia.
    + right. rewrite G1, G2. split; [lia|]. split; [lia|]. split; [|split].
      * intros y. split; [intros Hy; left; exact Hy|]. intros [Hy | (_ & Hy)]; [exact Hy | destruct (Cn _ _ Hy)].
      * intros i j Hij. destruct (Cn _ _ Hij).
      * left. split; [reflexivity | exact Cn].
Qed.

Lemma disj : forall B s i j p q : Z, 0 <= i -> 0 <= j -> i <> j -> 2 <= s ->
  B + i * s <= p < B + i * s + s -> B + j * s <= q < B + j * s + s -> p <> q.
Proof.
  intros B s i j p q Hi Hj Hij Hs Hp Hq.
  destruct (Z.lt_ge_cases i j) as [E | E].
  - assert (i * s + s <= j * s) by (apply mul_step; lia). lia.
  - assert (j * s + s <= i * s) by (apply mul_step; lia). lia.
Qed.

Lemma nil_big : forall z, z < 131072 -> z <> nilZ.
Proof. unfold nilZ. lia. Qed.

Lemma mk_nodeinv : forall P W m M (S : Z -> Prop) (C : Z -> Z -> Prop), 0 < P ->
  0 <= m -> M < W ->
  (forall y, S y <-> y = m \/ (0 <= y /\ C (y / P) (y mod P))) ->
  (forall i j, C i j -> m < i * P + j) ->
  (forall i j, C i j -> 0 <= j < P) ->
  S M -> (forall y, S y -> y <= M) ->
  nodeinv P W m M S C.
Proof.
  intros P W m M S C HP Hm HMW HS Hmin Hj HSM Hmax.
  assert (Hin : forall i j, C i j -> S (i * P + j)).
  { intros i j Hc. apply HS. right. split; [pose proof (Hmin i j Hc); lia|].
    destruct (decode P i j (Hj i j Hc)) as [D1 D2]. rewrite D1, D2. exact Hc. }
  assert (HmM : m <= M) by (apply Hmax; apply HS; left; reflexivity).
  right. split; [lia|]. split; [exact HMW|]. split; [exact HS|]. split.
  - intros i j Hc. split; [apply Hmin; exact Hc | apply Hmax; apply Hin; exact Hc].
  - destruct (Z.eq_dec m M) as [E | E].
    + left. split; [exact E|]. intros i j Hc. pose proof (Hmin i j Hc). pose proof (Hmax _ (Hin i j Hc)). lia.
    + right. split; [lia|]. apply HS in HSM. destruct HSM as [HSM | [_ HSM]]; [lia | exact HSM].
Qed.

Lemma ok_crange : forall v b k (C : Z -> Z -> Prop),
  2 <= (φ k) <= K ->
  (forall i : int, (φ i) < 2 ^ hi (φ k) -> ok v (clb t b k i) (kl k) (C (φ i))) ->
  (forall i j, C i j -> 0 <= i < 2 ^ hi (φ k)) ->
  forall i j, C i j -> 0 <= j < 2 ^ lo (φ k).
Proof.
  intros v b k C Hk' Hc HCi i j Hij.
  destruct (HCi i j Hij) as [Hi1 Hi2].
  destruct (hilo (φ k) ltac:(lia)) as (_ & B & A & _).
  pose proof (pow17 (hi (φ k)) ltac:(lia)) as P17.
  assert (Ei : (φ (of_Z i)) = i).
  { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
  assert (Hc' := Hc (of_Z i) ltac:(lia)). rewrite Ei in Hc'.
  pose proof (ok_range _ _ _ _ Hc' j Hij) as R. rewrite kl_spec in R. exact R.
Qed.

Lemma ins_nodeinv : forall P W m M x y (S : Z -> Prop) (C : Z -> Z -> Prop),
  0 < P -> 0 <= m -> M < W -> 0 <= x < W -> x <> m -> ~ S x -> y = Z.max x m ->
  (forall z, S z <-> z = m \/ (0 <= z /\ C (z / P) (z mod P))) ->
  (forall i j, C i j -> m < i * P + j <= M) ->
  (forall i j, C i j -> 0 <= j < P) ->
  S m -> S M -> (forall z, S z -> m <= z <= M) ->
  nodeinv P W (Z.min x m) (Z.max M y) (fun z => S z \/ z = x)
    (fun i j => C i j \/ (i = y / P /\ j = y mod P)).
Proof.
  intros P W m M x y S C HP Hm HMW Hx Hxm HxS Hy HD HCb Crg HSm HSM Hmm.
  destruct (encode P y HP) as [Ey Ry].
  assert (Hyz : forall z, 0 <= z -> ((z / P = y / P /\ z mod P = y mod P) <-> z = y)).
  { intros z Hz. split.
    - intros [E1 E2]. destruct (encode P z HP) as [Ez _]. rewrite Ez, E1, E2. symmetry. exact Ey.
    - intros E. subst z. auto. }
  pose proof (Hmm m HSm) as HmM.
  apply mk_nodeinv; [exact HP | lia | lia | | | | | ].
  - intros z. split.
    + intros [Hz | Hz].
      * apply HD in Hz. destruct Hz as [Hz | [Hz0 Hz]].
        -- destruct (Z.lt_ge_cases x m) as [Lt | Ge]; [right | left; lia].
           split; [lia|]. right. apply Hyz; lia.
        -- right. split; [exact Hz0 | left; exact Hz].
      * destruct (Z.lt_ge_cases x m) as [Lt | Ge]; [left; lia | right].
        split; [lia|]. right. apply Hyz; lia.
    + intros [Hz | (Hz0 & [Hz | Hz])].
      * destruct (Z.lt_ge_cases x m) as [Lt | Ge]; [right; lia | left; apply HD; left; lia].
      * left. apply HD. right. split; [exact Hz0 | exact Hz].
      * apply Hyz in Hz; [|exact Hz0].
        destruct (Z.lt_ge_cases x m) as [Lt | Ge]; [left; apply HD; left; lia | right; lia].
  - intros i j [E | [E1 E2]].
    + apply HCb in E. lia.
    + subst i j. lia.
  - intros i j [E | [E1 E2]]; [apply (Crg _ _ E) | subst j; exact Ry].
  - destruct (Z.le_gt_cases M y) as [Le | Gt].
    + rewrite Z.max_r by exact Le.
      destruct (Z.lt_ge_cases x m) as [Lt | Ge]; [left; replace y with m by lia; exact HSm | right; lia].
    + rewrite Z.max_l by lia. left. exact HSM.
  - intros z [Hz | Hz]; [pose proof (Hmm z Hz); lia | lia].
Qed.

Lemma ins_spec : forall n (k : int), (φ k) = n -> forall (H : Acc (Zwf 0) (φ k)) v b x S,
  ok v b k S -> ~ S (φ x) -> (φ x) < 2 ^ (φ k) ->
  PArray.length (vins t v b k x H) = PArray.length v /\
  (forall p : int, ~ ((φ b) <= (φ p) < (φ b) + sz (φ k)) -> (vins t v b k x H).[p] = v.[p]) /\
  ok (vins t v b k x H) b k (fun y => S y \/ y = (φ x)).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros k En H v b x S Hok HxS Hx.
  pose proof (to_Z_bounded x). pose proof (alength_bound v).
  destruct (ok_info _ _ _ _ Hok) as [Hk Hl]. pose proof (sz_ge2 (φ k)).
  pose proof (pow17 (φ k) ltac:(flia)) as Pk.
  destruct H as [Hacc]. cbn [vins].
  destruct (v.[b] =? nil)%uint63 eqn:Em.
  { (* empty node *)
    rewrite eqb_spec in Em.
    assert (HS : forall y, ~ S y).
    { destruct (ok_minmax _ _ _ _ Hok) as [(_ & _ & E) | (A & B & _)]; [exact E|].
      rewrite Em, nil_val in A. unfold nilZ in A. flia. }
    destruct (set2 v b x x ltac:(flia)) as (L & G1 & G2 & G3).
    split; [exact L|]. split.
    - intros p Hp. apply G3; pose proof (geom_leaf b ltac:(flia)); flia.
    - apply (ok_ext _ _ _ (fun y => y = (φ x))); [apply (ok_single v b k S x Hok HS Hx)|].
      intros y. split; [intros E; right; exact E | intros [E | E]; [destruct (HS y E) | exact E]]. }
  destruct (ok_minmax _ _ _ _ Hok) as [(E0 & _ & _) | (Hm0 & HM & HSm & HSM & Hmm)].
  { rewrite eqb_Z, nil_val, E0, Z.eqb_refl in Em. discriminate. }
  assert (Hxm : (φ x) <> (φ (v.[b]))) by (intro E; apply HxS; rewrite E; exact HSm).
  set (y := (if x <? v.[b] then v.[b] else x)%uint63).
  set (v1 := (if x <? v.[b] then v.[b <- x] else v)%uint63).
  assert (Hy : (φ y) = Z.max (φ x) (φ (v.[b]))).
  { unfold y. rewrite ltb_Z. destruct (Z.ltb_spec (φ x) (φ (v.[b]))); flia. }
  assert (Hv1L : PArray.length v1 = PArray.length v).
  { unfold v1. destruct (x <? v.[b])%uint63; [apply alength_set | reflexivity]. }
  assert (Hv1b : (φ (v1.[b])) = Z.min (φ x) (φ (v.[b]))).
  { unfold v1. rewrite ltb_Z. destruct (Z.ltb_spec (φ x) (φ (v.[b]))).
    - rewrite aget_set_same by flia. flia.
    - flia. }
  assert (Hv1o : forall p : int, (φ p) <> (φ b) -> v1.[p] = v.[p]).
  { intros p Hp. unfold v1. destruct (x <? v.[b])%uint63; [apply aget_set_other; flia | reflexivity]. }
  clearbody y v1.
  destruct Hok as [b k S Hk' Hl' Hinv | b k S Ss C Hk' Hl' Hs Hc HSs HCi Hinv].
  { (* leaf *)
    destruct (bdec (1 <? k)%uint63) as [Hk1 | Hk1].
    { exfalso. rewrite ltb_spec in Hk1. change (φ 1) with 1 in Hk1. flia. }
    pose proof (geom_leaf b ltac:(flia)) as E1.
    assert (Hv1b1 : v1.[(b + 1)%uint63] = v.[(b + 1)%uint63]) by (apply Hv1o; flia).
    rewrite Hk' in Hx, HM. change (2 ^ 1) with 2 in Hx, HM.
    destruct Hinv as [(A & _) | (A & B & HD)]; [exfalso; apply (nil_big (φ (v.[b]))); flia|].
    assert (Emm : (φ (v.[b])) = (φ (v.[(b + 1)%uint63]))).
    { destruct (Z.eq_dec (φ (v.[b])) (φ (v.[(b + 1)%uint63]))) as [E | E]; [exact E|].
      exfalso. apply HxS. apply HD. flia. }
    rewrite Hk', sz_leaf in *.
    destruct (v1.[(b + 1)%uint63] <? y)%uint63 eqn:E2.
    - rewrite ltb_spec, Hv1b1 in E2.
      split; [rewrite alength_set; exact Hv1L|]. split.
      + intros p Hp. rewrite aget_set_other by flia. apply Hv1o. flia.
      + apply ok_leaf; [exact Hk' | rewrite alength_set, Hv1L; exact Hl' |].
        rewrite aget_set_other by flia. rewrite aget_set_same by (rewrite Hv1L; flia).
        right. rewrite Hv1b, Hy. split; [flia|]. split; [flia|].
        intros z. rewrite HD. flia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec, Hv1b1 in E2.
      split; [exact Hv1L|]. split.
      + intros p Hp. apply Hv1o. flia.
      + apply ok_leaf; [exact Hk' | rewrite Hv1L; exact Hl' |].
        rewrite Hv1b1. right. rewrite Hv1b. split; [flia|]. split; [flia|].
        intros z. rewrite HD. flia. }
  (* node *)
  clear Em.
  destruct (geom b k Hk' ltac:(flia)) as (F1 & F2 & F3 & Esz & Ekh & Ekl & L1 & L2 & L3 & L4 & L5 & L6 & Pw & Pl & Ph & _ & Ecl).
  pose proof (ok_crange v b k C Hk' Hc HCi) as Crg.
  set (P := 2 ^ lo (φ k)) in *.
  assert (PB : P <= 131072) by (unfold P; pose proof (pow17 (lo (φ k)) ltac:(flia)); flia).
  destruct Hinv as [(A & _) | (_ & _ & HD & HCb & Hlast)];
    [exfalso; apply (nil_big (φ (v.[b]))); flia|].
  assert (HyK : (φ y) < 2 ^ (φ k)) by flia.
  assert (Hy1 : (φ x) <= (φ y)) by flia. assert (Hy2 : (φ (v.[b])) <= (φ y)) by flia.
  assert (Hb3 : 0 <= (φ (v1.[b]))) by flia.
  change (hide ((φ y) = Z.max (φ x) (φ (v.[b])))) in Hy.
  change (hide ((φ (v1.[b])) = Z.min (φ x) (φ (v.[b])))) in Hv1b.
  change (hide ((φ x) <> (φ (v.[b])))) in Hxm.
  set (hy := (y >> kl k)%uint63).
  set (ly := (y - (hy << kl k))%uint63).
  set (c := clb t b k hy).
  assert (Ehy : (φ hy) = (φ y) / P) by (unfold hy; rewrite shr_spec, Ekl; reflexivity).
  destruct (encode P (φ y) ltac:(flia)) as [Ey Rly].
  assert (Hhy : 0 <= (φ hy) < 2 ^ hi (φ k)).
  { rewrite Ehy. split; [apply Z.div_pos; flia|]. apply Z.div_lt_upper_bound; [flia|].
    rewrite Z.mul_comm, <- Pw. exact HyK. }
  assert (Eshl : (φ (hy << kl k))%uint63 = (φ hy) * P).
  { rewrite shl_nov; rewrite Ekl; fold P; [reflexivity|]. rewrite Ehy, wB_val. flia. }
  assert (Ely : (φ ly) = (φ y) mod P) by (unfold ly; rewrite sub_nov; rewrite Eshl, Ehy; flia).
  clearbody hy ly.
  destruct (Ecl hy Hhy) as (Ec1 & Ec2 & Ec3). fold c in Ec1, Ec2.
  pose proof (sz_ge2 (lo (φ k))) as Slo. pose proof (sz_ge2 (hi (φ k))) as Shi.
  assert (NNhy : 0 <= (φ hy) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
  assert (NNall : 0 <= 2 ^ hi (φ k) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
  assert (Hyc : ~ C (φ hy) (φ ly)).
  { intro Hcy. rewrite Ehy, Ely in Hcy.
    destruct (Z.eq_dec (φ y) (φ (v.[b]))) as [E | E].
    - apply HCb in Hcy. flia.
    - assert (Exy : (φ y) = (φ x)) by (unfold hide in Hy; flia). apply HxS. apply HD. right. split; [flia|]. rewrite <- Exy. exact Hcy. }
  assert (Hyz : forall z, 0 <= z -> ((z / P = (φ hy) /\ z mod P = (φ ly)) <-> z = (φ y))).
  { intros z Hz. rewrite Ehy, Ely. split.
    - intros [E1 E2]. destruct (encode P z ltac:(flia)) as [Ez _]. flia.
    - intros E. subst z. auto. }
  assert (Hc1 : ok v1 c (kl k) (C (φ hy))).
  { apply (ok_frame v); [apply Hc; flia | exact Hv1L |]. intros p Hp. apply Hv1o. rewrite Ec1, Ekl in Hp. flia. }
  set (C' := fun i j => C i j \/ (i = (φ hy) /\ j = (φ ly))).
  set (v2 := match bdec (1 <? k)%uint63 with
             | left Hk0 =>
                 if (v1.[c] =? nil)%uint63
                 then (vins t v1 (b + 2) (kh k) hy (Acc_inv (Acc_intro (φ k) Hacc) (dec_hi k Hk0))).[c <- ly].[(c + 1)%uint63 <- ly]
                 else vins t v1 c (kl k) ly (Acc_inv (Acc_intro (φ k) Hacc) (dec_lo k Hk0))
             | right _ => v1
             end).
  assert (Hv2 : PArray.length v2 = PArray.length v /\
                (forall p : int, ~ ((φ b) + 2 <= (φ p) < (φ b) + sz (φ k)) -> v2.[p] = v1.[p]) /\
                ok v2 (b + 2) (kh k) (fun i => Ss i \/ i = (φ hy)) /\
                (forall i : int, (φ i) < 2 ^ hi (φ k) -> ok v2 (clb t b k i) (kl k) (C' (φ i)))).
  { unfold v2. destruct (bdec (1 <? k)%uint63) as [Hk1 | Hk1].
    2: { exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hk1. change (φ 1) with 1 in Hk1. flia. }
    destruct (v1.[c] =? nil)%uint63 eqn:Ecn.
    - (* the cluster was empty: insert hy into the summary, then fill the cluster *)
      rewrite eqb_spec in Ecn.
      assert (HCe : forall j, ~ C (φ hy) j).
      { destruct (ok_minmax _ _ _ _ Hc1) as [(_ & _ & E) | (A & B & _)]; [exact E|].
        exfalso. rewrite Ecn, nil_val in A. unfold nilZ in A. rewrite Ekl in B. fold P in B. flia. }
      assert (Hns : ~ Ss (φ hy)) by (rewrite HSs; intros (_ & j & Hj); exact (HCe j Hj)).
      assert (Hs1 : ok v1 (b + 2) (kh k) Ss).
      { apply (ok_frame v); [exact Hs | exact Hv1L |]. intros p Hp. apply Hv1o. rewrite F2 in Hp. flia. }
      destruct (IH (hi (φ k)) ltac:(unfold Zwf; flia) (kh k) Ekh
                  (Acc_inv (Acc_intro (φ k) Hacc) (dec_hi k Hk1)) v1 (b + 2)%uint63 hy Ss Hs1 Hns
                  ltac:(rewrite Ekh; flia)) as (L7 & F7 & O7).
      set (v3 := vins t v1 (b + 2) (kh k) hy (Acc_inv (Acc_intro (φ k) Hacc) (dec_hi k Hk1))) in *.
      clearbody v3.
      destruct (set2 v3 c ly ly ltac:(rewrite L7, Hv1L; flia)) as (L8 & G1 & G2 & G3).
      rewrite F2, Ekh in F7.
      split; [rewrite L8, L7; exact Hv1L|]. split; [|split].
      + intros p Hp. rewrite G3 by flia. apply F7. flia.
      + apply (ok_frame v3); [| exact L8 |].
        * apply (ok_ext _ _ _ _ _ O7). intros i. reflexivity.
        * intros p Hp. rewrite F2, Ekh in Hp. apply G3; flia.
      + intros i Hi. pose proof (to_Z_bounded i).
        destruct (Ecl i ltac:(flia)) as (Ei1 & Ei2 & Ei3).
        destruct (Z.eq_dec (φ i) (φ hy)) as [Ei | Ei].
        * assert (i = hy) by (apply to_Z_inj; exact Ei). subst i. fold c.
          apply (ok_ext _ _ _ (fun j => j = (φ ly))).
          -- apply (ok_single v3 c (kl k) (C (φ hy))).
             ++ apply (ok_frame v1); [exact Hc1 | exact L7 |]. intros p Hp. apply F7. rewrite Ec1, Ekl in Hp. flia.
             ++ exact HCe.
             ++ rewrite Ekl. flia.
          -- intros j. unfold C'. split; [intros E; right; auto | intros [E | [_ E]]; [destruct (HCe j E) | exact E]].
        * assert (NNi : 0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
          apply (ok_ext _ _ _ (C (φ i))).
          -- apply (ok_frame v); [apply Hc; exact Hi | rewrite L8, L7; exact Hv1L |].
             intros p Hp. rewrite Ei1, Ekl in Hp.
             assert (D1 : (φ p) <> (φ c)) by (rewrite Ec1; apply (disj ((φ b) + 2 + sz (hi (φ k))) (sz (lo (φ k))) (φ i) (φ hy)); flia).
             assert (D2 : (φ p) <> (φ c) + 1) by (rewrite Ec1; apply (disj ((φ b) + 2 + sz (hi (φ k))) (sz (lo (φ k))) (φ i) (φ hy)); flia).
             rewrite G3 by (rewrite ?Ec2; flia). rewrite F7 by flia. apply Hv1o. flia.
          -- intros j. unfold C'. split; [intros E; left; exact E | intros [E | [E _]]; [exact E | flia]].
    - (* the cluster was not empty: insert ly into it *)
      rewrite eqb_Z, nil_val in Ecn. apply Z.eqb_neq in Ecn.
      assert (Hne : exists j, C (φ hy) j).
      { destruct (ok_minmax _ _ _ _ Hc1) as [(A & _) | (_ & _ & A & _)]; [flia | eexists; exact A]. }
      clear Ecn.
      assert (Hys : Ss (φ hy)) by (apply HSs; split; [flia | exact Hne]).
      destruct (IH (lo (φ k)) ltac:(unfold Zwf; flia) (kl k) Ekl
                  (Acc_inv (Acc_intro (φ k) Hacc) (dec_lo k Hk1)) v1 c ly (C (φ hy)) Hc1 Hyc
                  ltac:(rewrite Ekl; flia)) as (L7 & F7 & O7).
      set (v3 := vins t v1 c (kl k) ly (Acc_inv (Acc_intro (φ k) Hacc) (dec_lo k Hk1))) in *.
      clearbody v3.
      rewrite Ec1, Ekl in F7.
      split; [rewrite L7; exact Hv1L|]. split; [|split].
      + intros p Hp. apply F7. flia.
      + apply (ok_ext _ _ _ Ss).
        * apply (ok_frame v); [exact Hs | rewrite L7; exact Hv1L |].
          intros p Hp. rewrite F2, Ekh in Hp. rewrite F7 by flia. apply Hv1o. flia.
        * intros i. split; [intros E; left; exact E | intros [E | E]; [exact E | rewrite E; exact Hys]].
      + intros i Hi. pose proof (to_Z_bounded i).
        destruct (Ecl i ltac:(flia)) as (Ei1 & Ei2 & Ei3).
        destruct (Z.eq_dec (φ i) (φ hy)) as [Ei | Ei].
        * assert (i = hy) by (apply to_Z_inj; exact Ei). subst i. fold c.
          apply (ok_ext _ _ _ _ _ O7). intros j. unfold C'. split.
          -- intros [E | E]; [left; exact E | right; auto].
          -- intros [E | [_ E]]; [left; exact E | right; exact E].
        * assert (NNi : 0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
          apply (ok_ext _ _ _ (C (φ i))).
          -- apply (ok_frame v); [apply Hc; exact Hi | rewrite L7; exact Hv1L |].
             intros p Hp. rewrite Ei1, Ekl in Hp.
             rewrite F7.
             ++ apply Hv1o. flia.
             ++ intros Hq. apply (disj ((φ b) + 2 + sz (hi (φ k))) (sz (lo (φ k))) (φ i) (φ hy) (φ p) (φ p)); flia.
          -- intros j. unfold C'. split; [intros E; left; exact E | intros [E | [E _]]; [exact E | flia]]. }
  clearbody v2. destruct Hv2 as (Lv2 & Fv2 & Sv2 & Cv2).
  assert (Hv2b1 : v2.[(b + 1)%uint63] = v.[(b + 1)%uint63]) by (rewrite Fv2 by flia; apply Hv1o; flia).
  assert (Hv2b : v2.[b] = v1.[b]) by (apply Fv2; flia).
  assert (FIN : forall r : array int, PArray.length r = PArray.length v ->
            (forall p : int, (φ p) <> (φ b) + 1 -> r.[p] = v2.[p]) ->
            (φ (r.[(b + 1)%uint63])) = Z.max (φ (v.[(b + 1)%uint63])) (φ y) ->
            PArray.length r = PArray.length v /\
            (forall p : int, ~ ((φ b) <= (φ p) < (φ b) + sz (φ k)) -> r.[p] = v.[p]) /\
            ok r b k (fun z => S z \/ z = (φ x))).
  { intros r Lr Fr Er. unfold hide in Hy, Hv1b, Hxm.
    assert (Erb : (φ (r.[b])) = Z.min (φ x) (φ (v.[b]))) by (rewrite Fr by flia; rewrite Hv2b; exact Hv1b).
    split; [exact Lr|]. split.
    - intros p Hp. rewrite Fr by flia. rewrite Fv2 by flia. apply Hv1o. flia.
    - apply (ok_node r b k _ (fun i => Ss i \/ i = (φ hy)) C'); [exact Hk' | rewrite Lr; exact Hl' | | | | | ].
      + apply (ok_frame v2); [exact Sv2 | rewrite Lr; symmetry; exact Lv2 |]. intros p Hp. apply Fr. rewrite F2, Ekh in Hp. flia.
      + intros i Hi. pose proof (to_Z_bounded i). destruct (Ecl i ltac:(flia)) as (Ei1 & _ & _).
        assert (NNi : 0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
        apply (ok_frame v2); [apply Cv2; exact Hi | rewrite Lr; symmetry; exact Lv2 |].
        intros p Hp. apply Fr. rewrite Ei1 in Hp. flia.
      + intros i. unfold C'. split.
        * intros [E | E].
          -- apply HSs in E. destruct E as (E1 & j & E2). split; [exact E1 | exists j; left; exact E2].
          -- split; [flia | exists (φ ly); right; auto].
        * intros (E1 & j & [E2 | [E2 E3]]); [left; apply HSs; split; [exact E1 | exists j; exact E2] | right; exact E2].
      + intros i j E. destruct E as [E | [E _]]; [apply (HCi i j E) | flia].
      + rewrite Erb, Er. unfold C'. rewrite Ehy, Ely.
        apply (ins_nodeinv P (2 ^ (φ k)) (φ (v.[b])) (φ (v.[(b + 1)%uint63])) (φ x) (φ y) S C);
          try assumption; try flia. }
  destruct (v2.[(b + 1)%uint63] <? y)%uint63 eqn:E2.
  - rewrite ltb_spec, Hv2b1 in E2. apply FIN.
    + rewrite alength_set. exact Lv2.
    + intros p Hp. apply aget_set_other. flia.
    + rewrite aget_set_same by (rewrite Lv2; flia). flia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hv2b1 in E2. apply FIN.
    + exact Lv2.
    + intros; reflexivity.
    + rewrite Hv2b1. flia.
Qed.

Lemma ok_clear : forall v b k S, ok v b k S -> (φ (v.[b])) = (φ (v.[(b + 1)%uint63])) ->
  ok v.[b <- nil].[(b + 1)%uint63 <- nil] b k (fun _ => False).
Proof.
  intros v b k S H Emm. pose proof (alength_bound v).
  destruct (ok_info v b k S H) as [Hk Hl]. pose proof (sz_ge2 (φ k)).
  destruct (set2 v b nil nil ltac:(lia)) as (L & G1 & G2 & G3).
  destruct H as [b k S Hk' Hl' Hinv | b k S Ss C Hk' Hl' Hs Hc HSs HCi Hinv].
  - apply ok_leaf; [exact Hk' | rewrite L; exact Hl' |]. left.
    rewrite G1, G2. auto.
  - destruct (geom b k Hk' ltac:(lia)) as (F1 & F2 & F3 & Esz & Ekh & Ekl & L1 & L2 & L3 & L4 & _ & _ & _ & _ & _ & _ & Ecl).
    assert (Cn : forall i j, ~ C i j).
    { destruct Hinv as [(_ & _ & _ & D) | (_ & _ & _ & D & [[_ E] | [E _]])]; [exact D | exact E | lia]. }
    apply (ok_node _ b k _ Ss C); [exact Hk' | rewrite L; exact Hl' | | | exact HSs | exact HCi |].
    + apply (ok_frame v); [exact Hs | exact L |]. intros p Hp. apply G3; rewrite F2, Ekh in Hp; lia.
    + intros i Hi. pose proof (to_Z_bounded i). destruct (Ecl i ltac:(lia)) as (E1 & _ & _).
      pose proof (sz_ge2 (hi (φ k))).
      assert (0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; [lia | pose proof (sz_ge2 (lo (φ k))); lia]).
      apply (ok_frame v); [apply Hc; exact Hi | exact L |]. intros p Hp. apply G3; rewrite E1 in Hp; lia.
    + left. rewrite G1, G2. split; [reflexivity|]. split; [reflexivity|]. split; [tauto | exact Cn].
Qed.

Lemma del_spec : forall n (k : int), (φ k) = n -> forall (H : Acc (Zwf 0) (φ k)) v b x S,
  ok v b k S -> S (φ x) ->
  PArray.length (vdel t v b k x H) = PArray.length v /\
  (forall p : int, ~ ((φ b) <= (φ p) < (φ b) + sz (φ k)) -> (vdel t v b k x H).[p] = v.[p]) /\
  ok (vdel t v b k x H) b k (fun z => S z /\ z <> (φ x)).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros k En H v b x S Hok HxS.
  pose proof (to_Z_bounded x). pose proof (alength_bound v).
  destruct (ok_info _ _ _ _ Hok) as [Hk Hl]. pose proof (sz_ge2 (φ k)).
  pose proof (pow17 (φ k) ltac:(flia)) as Pk.
  pose proof (ok_range _ _ _ _ Hok _ HxS) as Hx.
  destruct (ok_minmax _ _ _ _ Hok) as [(_ & _ & E) | (Hm0 & HM & HSm & HSM & Hmm)]; [destruct (E _ HxS)|].
  destruct H as [Hacc]. cbn [vdel].
  destruct (v.[b] =? v.[(b + 1)%uint63])%uint63 eqn:Emm.
  { rewrite eqb_spec in Emm.
    destruct (set2 v b nil nil ltac:(flia)) as (L & G1 & G2 & G3).
    split; [exact L|]. split.
    - intros p Hp. apply G3; pose proof (geom_leaf b ltac:(flia)); flia.
    - apply (ok_ext _ _ _ (fun _ => False)); [apply (ok_clear v b k S Hok); rewrite Emm; reflexivity|].
      intros z. split; [intros []|]. intros [Hz1 Hz2]. apply Hz2.
      pose proof (Hmm _ Hz1). pose proof (Hmm _ HxS). rewrite Emm in *. flia. }
  rewrite eqb_Z in Emm. apply Z.eqb_neq in Emm.
  assert (Emm' : (φ (v.[b])) < (φ (v.[(b + 1)%uint63]))) by flia. clear Emm.
  destruct Hok as [b k S Hk' Hl' Hinv | b k S Ss C Hk' Hl' Hs Hc HSs HCi Hinv].
  { (* leaf: S = {0, 1} *)
    destruct (bdec (1 <? k)%uint63) as [Hk1 | Hk1].
    { exfalso. rewrite ltb_spec in Hk1. change (φ 1) with 1 in Hk1. flia. }
    rewrite Hk' in HM, Hx. change (2 ^ 1) with 2 in HM, Hx.
    destruct Hinv as [(A & _) | (A & B & HD)]; [exfalso; apply (nil_big (φ (v.[b]))); flia|].
    rewrite Hk', sz_leaf in *.
    set (r := (if x =? 0 then 1 else 0)%uint63).
    assert (Er : (φ r) = 1 - (φ x)).
    { unfold r. rewrite eqb_Z. change (φ 0) with 0.
      destruct (Z.eqb_spec (φ x) 0); [change (φ 1) with 1 | change (φ 0) with 0]; flia. }
    destruct (set2 v b r r ltac:(flia)) as (L & G1 & G2 & G3).
    split; [exact L|]. split.
    - intros p Hp. apply G3; pose proof (geom_leaf b ltac:(flia)); flia.
    - apply ok_leaf; [exact Hk' | rewrite L; exact Hl' |]. right. rewrite G1, G2.
      split; [flia|]. split; [flia|]. intros z. rewrite HD. rewrite HD in HxS. flia. }
  (* node *)
  destruct (geom b k Hk' ltac:(flia)) as (F1 & F2 & F3 & Esz & Ekh & Ekl & L1 & L2 & L3 & L4 & L5 & L6 & Pw & Pl & Ph & _ & Ecl).
  pose proof (ok_crange v b k C Hk' Hc HCi) as Crg.
  set (P := 2 ^ lo (φ k)) in *.
  assert (PB : P <= 131072) by (unfold P; pose proof (pow17 (lo (φ k)) ltac:(flia)); flia).
  pose proof (sz_ge2 (lo (φ k))) as Slo. pose proof (sz_ge2 (hi (φ k))) as Shi.
  assert (NNall : 0 <= 2 ^ hi (φ k) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
  destruct Hinv as [(A & _) | (_ & _ & HD & HCb & Hlast)];
    [exfalso; apply (nil_big (φ (v.[b]))); flia|].
  destruct Hlast as [[E _] | [_ HMC]]; [flia|].
  destruct (bdec (1 <? k)%uint63) as [Hk1 | Hk1].
  2: { exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hk1. change (φ 1) with 1 in Hk1. flia. }
  set (y := (if x =? v.[b] then (v.[(b + 2)%uint63] << kl k) + v.[clb t b k v.[(b + 2)%uint63]] else x)%uint63).
  set (v1 := (if x =? v.[b] then v.[b <- y] else v)%uint63).
  assert (Yf : 0 <= (φ y) /\ C ((φ y) / P) ((φ y) mod P) /\ (φ (v1.[b])) <= (φ y) /\ (φ y) <= (φ (v.[(b + 1)%uint63])) /\
     (forall z, (S z /\ z <> (φ x)) <-> z = (φ (v1.[b])) \/ (0 <= z /\ C (z / P) (z mod P) /\ z <> (φ y))) /\
     (forall i j, C i j -> i * P + j <> (φ y) -> (φ (v1.[b])) < i * P + j) /\
     ((φ y) <> (φ (v.[(b + 1)%uint63])) -> S (φ (v.[(b + 1)%uint63])) /\ (φ (v.[(b + 1)%uint63])) <> (φ x)) /\
     PArray.length v1 = PArray.length v /\ (forall p : int, (φ p) <> (φ b) -> v1.[p] = v.[p]) /\
     0 <= (φ (v1.[b]))).
  { destruct (Z.eq_dec (φ x) (φ (v.[b]))) as [Exm | Exm].
    - assert (Ex : (x =? v.[b])%uint63 = true) by (rewrite eqb_Z; apply Z.eqb_eq; exact Exm).
      unfold v1, y. rewrite Ex. cbv iota.
      assert (HsM : Ss ((φ (v.[(b + 1)%uint63])) / P))
        by (apply HSs; split; [apply (HCi _ _ HMC) | eexists; exact HMC]).
      destruct (ok_minmax _ _ _ _ Hs) as [(_ & _ & E) | (Hf0 & Hf1 & HSf & _ & Hfm)]; [destruct (E _ HsM)|].
      set (f := v.[(b + 2)%uint63]) in *.
      rewrite Ekh in Hf1.
      assert (Hfr : 0 <= (φ f) < 2 ^ hi (φ k)) by flia.
      pose proof (Hc f (proj2 Hfr)) as Hcf.
      assert (Hne : exists j, C (φ f) j) by (apply HSs in HSf; destruct HSf as (_ & j & Hj); exists j; exact Hj).
      destruct (ok_minmax _ _ _ _ Hcf) as [(_ & _ & E) | (Hc0 & Hc1 & HCf & _ & Hcm)];
        [destruct Hne as [j Hj]; destruct (E _ Hj)|].
      rewrite Ekl in Hc1. fold P in Hc1.
      set (mc := v.[clb t b k f]) in *.
      assert (Ey : (φ ((f << kl k) + mc))%uint63 = (φ f) * P + (φ mc)).
      { pose proof (mul_step (φ f) (2 ^ hi (φ k)) P ltac:(flia) ltac:(flia)).
        assert (Esh : (φ (f << kl k))%uint63 = (φ f) * P)
          by (rewrite shl_nov; rewrite Ekl; fold P; [reflexivity | rewrite wB_val; flia]).
        rewrite add_nov; rewrite Esh; [reflexivity | rewrite wB_val; flia]. }
      assert (Ymin : forall i j, C i j -> (φ f) * P + (φ mc) <= i * P + j).
      { intros i j Hij. assert (Ssi : Ss i) by (apply HSs; split; [apply (HCi _ _ Hij) | exists j; exact Hij]).
        pose proof (Hfm i Ssi) as Hfi. apply lex_le; [flia | apply (Crg _ _ Hij) |].
        destruct (Z.eq_dec (φ f) i) as [Ei | Ei]; [right; split; [exact Ei|]; subst i; apply Hcm; exact Hij | left; flia]. }
      assert (Hv1b : (φ (v.[b <- ((f << kl k) + mc)%uint63].[b])) = (φ f) * P + (φ mc))
        by (rewrite aget_set_same by flia; exact Ey).
      destruct (decode P (φ f) (φ mc) ltac:(flia)) as [D1 D2].
      rewrite Hv1b, Ey.
      assert (HmY : (φ (v.[b])) < (φ f) * P + (φ mc)) by (apply HCb; exact HCf).
      assert (HYM : (φ f) * P + (φ mc) <= (φ (v.[(b + 1)%uint63]))).
      { destruct (encode P (φ (v.[(b + 1)%uint63])) ltac:(flia)) as [EM _]. rewrite EM. apply Ymin. exact HMC. }
      split; [flia|]. split; [rewrite D1, D2; exact HCf|]. split; [flia|]. split; [exact HYM|].
      split; [|split; [|split; [|split; [|split]]]].
      + intros z. split.
        * intros [Hz Hzx]. apply HD in Hz. destruct Hz as [Hz | Hz]; [flia|].
          destruct (Z.eq_dec z ((φ f) * P + (φ mc))) as [Ez | Ez]; [left; exact Ez | right; exact (conj (proj1 Hz) (conj (proj2 Hz) Ez))].
        * intros [Hz | (Hz0 & Hz1 & Hz2)].
          -- split; [apply HD; right; split; [flia|]; rewrite Hz, D1, D2; exact HCf | flia].
          -- split; [apply HD; right; split; [exact Hz0 | exact Hz1]|].
             destruct (encode P z ltac:(flia)) as [Ez _].
             pose proof (HCb _ _ Hz1). flia.
      + intros i j Hij Hne'. pose proof (Ymin i j Hij). flia.
      + intros _. split; [exact HSM | flia].
      + rewrite alength_set. reflexivity.
      + intros p Hp. apply aget_set_other. flia.
      + flia.
    - assert (Ex : (x =? v.[b])%uint63 = false) by (rewrite eqb_Z; apply Z.eqb_neq; exact Exm).
      unfold v1, y. rewrite Ex. cbv iota.
      assert (HxC : 0 <= (φ x) /\ C ((φ x) / P) ((φ x) mod P)) by (apply HD in HxS; destruct HxS as [E | E]; [flia | exact E]).
      split; [flia|]. split; [exact (proj2 HxC)|]. split; [pose proof (Hmm _ HxS); flia|].
      split; [pose proof (Hmm _ HxS); flia|].
      split; [|split; [|split; [|split; [|split]]]].
      + intros z. rewrite HD. split.
        * intros [[Hz | Hz] Hzx]; [left; exact Hz | right; exact (conj (proj1 Hz) (conj (proj2 Hz) Hzx))].
        * intros [Hz | (Hz0 & Hz1 & Hz2)]; split; [left; exact Hz | flia | right; exact (conj Hz0 Hz1) | exact Hz2].
      + intros i j Hij _. apply HCb. exact Hij.
      + intros Hne'. split; [exact HSM | flia].
      + reflexivity.
      + intros; reflexivity.
      + flia. }
  clearbody y v1.
  destruct Yf as (Hy0 & HyC & Hv1y & HyM & HS' & Hmin1 & HMS' & Hv1L & Hv1o & Hv1b0).
  set (hy := (y >> kl k)%uint63).
  set (ly := (y - (hy << kl k))%uint63).
  set (c := clb t b k hy).
  assert (HyK : (φ y) < 2 ^ (φ k)) by flia.
  assert (Ehy : (φ hy) = (φ y) / P) by (unfold hy; rewrite shr_spec, Ekl; reflexivity).
  destruct (encode P (φ y) ltac:(flia)) as [Ey Rly].
  assert (Hhy : 0 <= (φ hy) < 2 ^ hi (φ k)).
  { rewrite Ehy. split; [apply Z.div_pos; flia|]. apply Z.div_lt_upper_bound; [flia|].
    rewrite Z.mul_comm, <- Pw. exact HyK. }
  assert (Eshl : (φ (hy << kl k))%uint63 = (φ hy) * P).
  { rewrite shl_nov; rewrite Ekl; fold P; [reflexivity|]. rewrite Ehy, wB_val. flia. }
  assert (Ely : (φ ly) = (φ y) mod P) by (unfold ly; rewrite sub_nov; rewrite Eshl, Ehy; flia).
  clearbody hy ly.
  destruct (Ecl hy Hhy) as (Ec1 & Ec2 & Ec3). fold c in Ec1, Ec2.
  assert (NNhy : 0 <= (φ hy) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
  assert (Hyz : forall z, 0 <= z -> ((z / P = (φ hy) /\ z mod P = (φ ly)) <-> z = (φ y))).
  { intros z Hz. rewrite Ehy, Ely. split.
    - intros [E1 E2]. destruct (encode P z ltac:(flia)) as [Ez _]. flia.
    - intros E. subst z. auto. }
  assert (HyC' : C (φ hy) (φ ly)) by (rewrite Ehy, Ely; exact HyC).
  assert (Hc1 : ok v1 c (kl k) (C (φ hy))).
  { apply (ok_frame v); [apply Hc; flia | exact Hv1L |]. intros p Hp. apply Hv1o. rewrite Ec1, Ekl in Hp. flia. }
  set (C' := fun i j => C i j /\ ~ (i = (φ hy) /\ j = (φ ly))).
  assert (HC'z : forall z, 0 <= z -> (C' (z / P) (z mod P) <-> C (z / P) (z mod P) /\ z <> (φ y))).
  { intros z Hz. unfold C'. rewrite (Hyz z Hz). split.
    - intros [A B]. split; [exact A | intro E; apply B; exact E].
    - intros [A B]. split; [exact A | intro E; apply B; exact E]. }
  assert (HC'ij : forall i j, C i j -> (i * P + j = (φ y) <-> i = (φ hy) /\ j = (φ ly))).
  { intros i j Hij. pose proof (Crg _ _ Hij). pose proof (HCi _ _ Hij).
    destruct (decode P i j ltac:(flia)) as [D1 D2].
    rewrite <- (Hyz (i * P + j)) by (pose proof (Z.mul_nonneg_nonneg i P ltac:(flia) ltac:(flia)); flia).
    rewrite D1, D2. reflexivity. }
  destruct (IH (lo (φ k)) ltac:(unfold Zwf; flia) (kl k) Ekl
              (Acc_inv (Acc_intro (φ k) Hacc) (dec_lo k Hk1)) v1 c ly (C (φ hy)) Hc1 HyC')
    as (L7 & F7 & O7).
  set (v2 := vdel t v1 c (kl k) ly (Acc_inv (Acc_intro (φ k) Hacc) (dec_lo k Hk1))) in *.
  clearbody v2.
  rewrite Ec1, Ekl in F7.
  assert (FIN : forall w r : array int,
     PArray.length w = PArray.length v ->
     (forall p : int, ~ ((φ b) + 2 <= (φ p) < (φ b) + sz (φ k)) -> w.[p] = v1.[p]) ->
     ok w (b + 2)%uint63 (kh k) (fun i => 0 <= i < 2 ^ hi (φ k) /\ exists j, C' i j) ->
     (forall i : int, (φ i) < 2 ^ hi (φ k) -> ok w (clb t b k i) (kl k) (C' (φ i))) ->
     PArray.length r = PArray.length v ->
     (forall p : int, (φ p) <> (φ b) + 1 -> r.[p] = w.[p]) ->
     (S (φ (r.[(b + 1)%uint63])) /\ (φ (r.[(b + 1)%uint63])) <> (φ x)) ->
     (forall z, S z /\ z <> (φ x) -> z <= (φ (r.[(b + 1)%uint63]))) ->
     PArray.length r = PArray.length v /\
     (forall p : int, ~ ((φ b) <= (φ p) < (φ b) + sz (φ k)) -> r.[p] = v.[p]) /\
     ok r b k (fun z => S z /\ z <> (φ x))).
  { intros w r Lw Fw Sw Cw Lr Fr HM1 HM2.
    assert (Erb : r.[b] = v1.[b]) by (rewrite Fr by flia; apply Fw; flia).
    split; [exact Lr|]. split.
    - intros p Hp. rewrite Fr by flia. rewrite Fw by flia. apply Hv1o. flia.
    - apply (ok_node r b k _ (fun i => 0 <= i < 2 ^ hi (φ k) /\ exists j, C' i j) C');
        [exact Hk' | rewrite Lr; exact Hl' | | | | | ].
      + apply (ok_frame w); [exact Sw | rewrite Lr; symmetry; exact Lw |].
        intros p Hp. apply Fr. rewrite F2, Ekh in Hp. flia.
      + intros i Hi. pose proof (to_Z_bounded i). destruct (Ecl i ltac:(flia)) as (Ei1 & _ & _).
        assert (NNi : 0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
        apply (ok_frame w); [apply Cw; exact Hi | rewrite Lr; symmetry; exact Lw |].
        intros p Hp. apply Fr. rewrite Ei1 in Hp. flia.
      + intros i. reflexivity.
      + intros i j [E _]. apply (HCi i j E).
      + rewrite Erb. apply mk_nodeinv.
        * flia.
        * exact Hv1b0.
        * pose proof (Hmm _ (proj1 HM1)). flia.
        * intros z. rewrite HS'. split.
          -- intros [E | (E1 & E2 & E3)]; [left; exact E | right; exact (conj E1 (proj2 (HC'z z E1) (conj E2 E3)))].
          -- intros [E | (E1 & E2)]; [left; exact E | right; exact (conj E1 (proj1 (HC'z z E1) E2))].
        * intros i j [E1 E2]. apply Hmin1; [exact E1|]. rewrite HC'ij by exact E1. exact E2.
        * intros i j [E _]. apply (Crg _ _ E).
        * exact HM1.
        * exact HM2. }
  assert (Hv2b1 : v2.[(b + 1)%uint63] = v.[(b + 1)%uint63]) by (rewrite F7 by flia; apply Hv1o; flia).
  assert (Hs2 : ok v2 (b + 2)%uint63 (kh k) Ss).
  { apply (ok_frame v); [exact Hs | rewrite L7; exact Hv1L |].
    intros p Hp. rewrite F2, Ekh in Hp. rewrite F7 by flia. apply Hv1o. flia. }
  assert (Hcl2 : forall i : int, (φ i) < 2 ^ hi (φ k) -> (φ i) <> (φ hy) -> ok v2 (clb t b k i) (kl k) (C' (φ i))).
  { intros i Hi Ei. pose proof (to_Z_bounded i). destruct (Ecl i ltac:(flia)) as (Ei1 & _ & _).
    assert (NNi : 0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
    apply (ok_ext _ _ _ (C (φ i))).
    - apply (ok_frame v); [apply Hc; exact Hi | rewrite L7; exact Hv1L |].
      intros p Hp. rewrite Ei1, Ekl in Hp. rewrite F7.
      + apply Hv1o. flia.
      + intros Hq. apply (disj ((φ b) + 2 + sz (hi (φ k))) (sz (lo (φ k))) (φ i) (φ hy) (φ p) (φ p)); flia.
    - intros j. unfold C'. split; [intros E; split; [exact E | flia] | intros [E _]; exact E]. }
  assert (Hcl2h : ok v2 c (kl k) (C' (φ hy))).
  { apply (ok_ext _ _ _ _ _ O7). intros j. unfold C'. split; [intros [E1 E2]; split; [exact E1 | flia] | intros [E1 E2]; split; [exact E1 | flia]]. }
  destruct (v2.[c] =? nil)%uint63 eqn:Ecn.
  - (* the cluster became empty: delete hy from the summary *)
    rewrite eqb_spec in Ecn.
    assert (HCe : forall j, ~ C' (φ hy) j).
    { destruct (ok_minmax _ _ _ _ Hcl2h) as [(_ & _ & E) | (A & B & _)]; [exact E|].
      exfalso. rewrite Ecn, nil_val in A. unfold nilZ in A. rewrite Ekl in B. fold P in B. flia. }
    assert (HSy : Ss (φ hy)) by (apply HSs; split; [flia | exists (φ ly); exact HyC']).
    destruct (IH (hi (φ k)) ltac:(unfold Zwf; flia) (kh k) Ekh
                (Acc_inv (Acc_intro (φ k) Hacc) (dec_hi k Hk1)) v2 (b + 2)%uint63 hy Ss Hs2 HSy)
      as (L8 & F8 & O8).
    set (v3 := vdel t v2 (b + 2)%uint63 (kh k) hy (Acc_inv (Acc_intro (φ k) Hacc) (dec_hi k Hk1))) in *.
    clearbody v3.
    rewrite F2, Ekh in F8.
    assert (Lw : PArray.length v3 = PArray.length v) by (rewrite L8, L7; exact Hv1L).
    assert (Fw : forall p : int, ~ ((φ b) + 2 <= (φ p) < (φ b) + sz (φ k)) -> v3.[p] = v1.[p])
      by (intros p Hp; rewrite F8 by flia; apply F7; flia).
    assert (Sw : ok v3 (b + 2)%uint63 (kh k) (fun i => 0 <= i < 2 ^ hi (φ k) /\ exists j, C' i j)).
    { apply (ok_ext _ _ _ _ _ O8). intros i. rewrite HSs. split.
      - intros ((E1 & j & E2) & E3). split; [exact E1 | exists j; unfold C'; split; [exact E2 | flia]].
      - intros (E1 & j & E2). split; [split; [exact E1 | exists j; exact (proj1 E2)]|].
        intro Ei. rewrite Ei in E2. exact (HCe j E2). }
    assert (Cw : forall i : int, (φ i) < 2 ^ hi (φ k) -> ok v3 (clb t b k i) (kl k) (C' (φ i))).
    { intros i Hi. pose proof (to_Z_bounded i). destruct (Ecl i ltac:(flia)) as (Ei1 & _ & _).
      assert (NNi : 0 <= (φ i) * sz (lo (φ k))) by (apply Z.mul_nonneg_nonneg; flia).
      apply (ok_frame v2); [| exact L8 |].
      - destruct (Z.eq_dec (φ i) (φ hy)) as [Ei | Ei].
        + assert (i = hy) by (apply to_Z_inj; exact Ei). subst i. exact Hcl2h.
        + apply Hcl2; assumption.
      - intros p Hp. apply F8. rewrite Ei1, Ekl in Hp. flia. }
    assert (Hv3b1 : v3.[(b + 1)%uint63] = v.[(b + 1)%uint63]) by (rewrite Fw by flia; apply Hv1o; flia).
    destruct (y =? v3.[(b + 1)%uint63])%uint63 eqn:EyM.
    + rewrite eqb_spec in EyM.
      destruct (v3.[(b + 2 + 1)%uint63] =? nil)%uint63 eqn:Esm.
      * (* the summary became empty *)
        rewrite eqb_spec in Esm.
        assert (Hall : forall i j, ~ C' i j).
        { intros i j Hij.
          destruct (ok_minmax _ _ _ _ Sw) as [(_ & _ & E) | (A & B & _)].
          - apply (E i). split; [apply (HCi _ _ (proj1 Hij)) | exists j; exact Hij].
          - rewrite Esm, nil_val in B. unfold nilZ in B. rewrite Ekh in B. flia. }
        apply (FIN v3); auto.
        -- rewrite alength_set. exact Lw.
        -- intros p Hp. apply aget_set_other. flia.
        -- rewrite aget_set_same by (rewrite Lw; flia). rewrite Fw by flia.
           apply HS'. left. reflexivity.
        -- rewrite aget_set_same by (rewrite Lw; flia). rewrite Fw by flia.
           intros z Hz. apply HS' in Hz. destruct Hz as [Hz | (Hz0 & Hz1 & Hz2)]; [flia|].
           exfalso. apply (Hall (z / P) (z mod P)). apply HC'z; [exact Hz0 | split; assumption].
      * (* the new maximum is the maximum of the last non-empty cluster *)
        rewrite eqb_Z, nil_val in Esm. apply Z.eqb_neq in Esm.
        destruct (ok_minmax _ _ _ _ Sw) as [(_ & A & _) | (_ & B & _ & HSsm & Hsmax)];
          [exfalso; flia |].
        set (sm := v3.[(b + 2 + 1)%uint63]) in *.
        rewrite Ekh in B.
        destruct HSsm as (Hsm1 & jj & Hjj).
        pose proof (Cw sm (proj2 Hsm1)) as Csm.
        destruct (ok_minmax _ _ _ _ Csm) as [(_ & _ & E) | (_ & Bm & _ & HCmx & Hcmax)]; [destruct (E _ Hjj)|].
        rewrite Ekl in Bm. fold P in Bm.
        set (mx := v3.[(clb t b k sm + 1)%uint63]) in *.
        assert (Emx : (φ ((sm << kl k) + mx))%uint63 = (φ sm) * P + (φ mx)).
        { pose proof (mul_step (φ sm) (2 ^ hi (φ k)) P ltac:(flia) ltac:(flia)).
          assert (Esh : (φ (sm << kl k))%uint63 = (φ sm) * P)
            by (rewrite shl_nov; rewrite Ekl; fold P; [reflexivity | rewrite wB_val; flia]).
          rewrite add_nov; rewrite Esh; [reflexivity | rewrite wB_val; flia]. }
        destruct (decode P (φ sm) (φ mx) ltac:(flia)) as [D1 D2].
        assert (HM1 : S ((φ sm) * P + (φ mx)) /\ (φ sm) * P + (φ mx) <> (φ x)).
        { assert (0 <= (φ sm) * P) by (apply Z.mul_nonneg_nonneg; flia).
          apply HS'. right. split; [flia|]. rewrite <- HC'z by flia. rewrite D1, D2. exact HCmx. }
        apply (FIN v3); auto.
        -- rewrite alength_set. exact Lw.
        -- intros p Hp. apply aget_set_other. flia.
        -- rewrite aget_set_same by (rewrite Lw; flia). rewrite Emx. exact HM1.
        -- rewrite aget_set_same by (rewrite Lw; flia). rewrite Emx.
           intros z Hz. apply HS' in Hz. destruct Hz as [Hz | (Hz0 & Hz1 & Hz2)].
           ++ rewrite Hz. apply Z.lt_le_incl. apply Hmin1; [exact (proj1 HCmx)|].
              rewrite HC'ij by exact (proj1 HCmx). exact (proj2 HCmx).
           ++ assert (Cz : C' (z / P) (z mod P)) by (apply HC'z; [exact Hz0 | split; assumption]).
              assert (Hzs : z / P <= (φ sm)) by (apply Hsmax; split; [apply (HCi _ _ (proj1 Cz)) | exists (z mod P); exact Cz]).
              destruct (encode P z ltac:(flia)) as [Ez Rz].
              rewrite Ez. apply lex_le; [exact Rz | flia |].
              destruct (Z.eq_dec (z / P) (φ sm)) as [Ei | Ei]; [right; split; [exact Ei|] | left; flia].
              apply Hcmax. rewrite <- Ei. exact Cz.
    + rewrite eqb_Z in EyM. apply Z.eqb_neq in EyM. rewrite Hv3b1 in EyM.
      apply (FIN v3 v3); auto.
      * rewrite Hv3b1. apply HMS'. exact EyM.
      * rewrite Hv3b1. intros z [Hz _]. apply (Hmm _ Hz).
  - (* the cluster is still non-empty *)
    rewrite eqb_Z, nil_val in Ecn. apply Z.eqb_neq in Ecn.
    destruct (ok_minmax _ _ _ _ Hcl2h) as [(A & _) | (_ & Bq & _ & HCq & Hqmax)]; [exfalso; flia|].
    rewrite Ekl in Bq. fold P in Bq.
    assert (Sw : ok v2 (b + 2)%uint63 (kh k) (fun i => 0 <= i < 2 ^ hi (φ k) /\ exists j, C' i j)).
    { apply (ok_ext _ _ _ _ _ Hs2). intros i. rewrite HSs. split.
      - intros (E1 & j & E2). split; [exact E1|].
        destruct (Z.eq_dec i (φ hy)) as [Ei | Ei].
        + rewrite Ei. eexists. exact HCq.
        + exists j. unfold C'. split; [exact E2 | flia].
      - intros (E1 & j & E2). split; [exact E1 | exists j; exact (proj1 E2)]. }
    assert (Cw : forall i : int, (φ i) < 2 ^ hi (φ k) -> ok v2 (clb t b k i) (kl k) (C' (φ i))).
    { intros i Hi. destruct (Z.eq_dec (φ i) (φ hy)) as [Ei | Ei].
      - assert (i = hy) by (apply to_Z_inj; exact Ei). subst i. exact Hcl2h.
      - apply Hcl2; assumption. }
    assert (Fw : forall p : int, ~ ((φ b) + 2 <= (φ p) < (φ b) + sz (φ k)) -> v2.[p] = v1.[p])
      by (intros p Hp; apply F7; flia).
    assert (Lw : PArray.length v2 = PArray.length v) by (rewrite L7; exact Hv1L).
    destruct (y =? v2.[(b + 1)%uint63])%uint63 eqn:EyM.
    + rewrite eqb_spec in EyM.
      set (mx := v2.[(c + 1)%uint63]) in *.
      assert (Emx : (φ ((hy << kl k) + mx))%uint63 = (φ hy) * P + (φ mx)).
      { pose proof (mul_step (φ hy) (2 ^ hi (φ k)) P ltac:(flia) ltac:(flia)).
        rewrite add_nov, Eshl; [reflexivity|]. rewrite Eshl, wB_val. flia. }
      destruct (decode P (φ hy) (φ mx) ltac:(flia)) as [D1 D2].
      assert (HM1 : S ((φ hy) * P + (φ mx)) /\ (φ hy) * P + (φ mx) <> (φ x)).
      { assert (0 <= (φ hy) * P) by (apply Z.mul_nonneg_nonneg; flia).
        apply HS'. right. split; [flia|]. rewrite <- HC'z by flia. rewrite D1, D2. exact HCq. }
      apply (FIN v2); auto.
      * rewrite alength_set. exact Lw.
      * intros p Hp. apply aget_set_other. flia.
      * rewrite aget_set_same by (rewrite Lw; flia). rewrite Emx. exact HM1.
      * rewrite aget_set_same by (rewrite Lw; flia). rewrite Emx.
        intros z Hz. pose proof (Hmm _ (proj1 Hz)) as HzM. rewrite Hv2b1 in EyM. rewrite <- EyM in HzM.
        apply HS' in Hz. destruct Hz as [Hz | (Hz0 & Hz1 & Hz2)].
        -- rewrite Hz. apply Z.lt_le_incl. apply Hmin1; [exact (proj1 HCq)|].
           rewrite HC'ij by exact (proj1 HCq). exact (proj2 HCq).
        -- assert (Cz : C' (z / P) (z mod P)) by (apply HC'z; [exact Hz0 | split; assumption]).
           destruct (encode P z ltac:(flia)) as [Ez Rz].
           assert (Hlt : z / P * P + z mod P <= (φ hy) * P + (φ ly)) by (rewrite <- Ez, Ehy, Ely; flia).
           apply lex_le in Hlt; [| exact Rz | flia].
           rewrite Ez. apply lex_le; [exact Rz | flia |].
           destruct Hlt as [Hlt | [Ei _]]; [left; exact Hlt | right; split; [exact Ei|]].
           apply Hqmax. rewrite <- Ei. exact Cz.
    + rewrite eqb_Z in EyM. apply Z.eqb_neq in EyM. rewrite Hv2b1 in EyM.
      apply (FIN v2 v2); auto.
      * rewrite Hv2b1. apply HMS'. exact EyM.
      * rewrite Hv2b1. intros z [Hz _]. apply (Hmm _ Hz).
Qed.

Definition predres (S : Z -> Prop) (x r : Z) : Prop :=
  (r = nilZ /\ forall z, S z -> x < z) \/ (S r /\ r <= x /\ forall z, S z -> z <= x -> z <= r).

Lemma pred_spec : forall n (k : int), (φ k) = n -> forall (H : Acc (Zwf 0) (φ k)) v b x S,
  ok v b k S -> (φ x) < 2 ^ (φ k) ->
  predres S (φ x) (φ (vpred t v b k x H)).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros k En H v b x S Hok Hx.
  pose proof (to_Z_bounded x). pose proof (alength_bound v).
  destruct (ok_info _ _ _ _ Hok) as [Hk Hl]. pose proof (sz_ge2 (φ k)).
  pose proof (pow17 (φ k) ltac:(flia)) as Pk.
  destruct H as [Hacc]. cbn [vpred].
  destruct (x <? v.[b])%uint63 eqn:E1.
  { rewrite ltb_spec in E1. left. split; [exact nil_val|].
    intros z Hz. destruct (ok_minmax _ _ _ _ Hok) as [(_ & _ & E) | (_ & _ & _ & _ & Hmm)];
      [destruct (E _ Hz) | pose proof (Hmm _ Hz); flia]. }
  rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
  destruct (ok_minmax _ _ _ _ Hok) as [(E & _) | (Hm0 & HM & HSm & HSM & Hmm)];
    [exfalso; unfold nilZ in E; flia|].
  destruct (v.[(b + 1)%uint63] <=? x)%uint63 eqn:E2.
  { rewrite leb_spec in E2. right. split; [exact HSM|]. split; [exact E2|].
    intros z Hz _. apply (Hmm _ Hz). }
  rewrite <- Bool.not_true_iff_false, leb_spec in E2.
  destruct Hok as [b k S Hk' Hl' Hinv | b k S Ss C Hk' Hl' Hs Hc HSs HCi Hinv].
  { destruct (bdec (1 <? k)%uint63) as [Hk1 | Hk1].
    { exfalso. rewrite ltb_spec in Hk1. change (φ 1) with 1 in Hk1. flia. }
    destruct Hinv as [(A & _) | (A & B & HD)]; [exfalso; unfold nilZ in A; flia|].
    right. split; [exact HSm|]. split; [flia|].
    intros z Hz Hzx. apply HD in Hz. flia. }
  destruct (geom b k Hk' ltac:(flia)) as (F1 & F2 & F3 & Esz & Ekh & Ekl & L1 & L2 & L3 & L4 & L5 & L6 & Pw & Pl & Ph & _ & Ecl).
  pose proof (ok_crange v b k C Hk' Hc HCi) as Crg.
  set (P := 2 ^ lo (φ k)) in *.
  assert (PB : P <= 131072) by (unfold P; pose proof (pow17 (lo (φ k)) ltac:(flia)); flia).
  destruct Hinv as [(A & _) | (_ & _ & HD & HCb & Hlast)];
    [exfalso; unfold nilZ in A; flia|].
  destruct (bdec (1 <? k)%uint63) as [Hk1 | Hk1].
  2: { exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hk1. change (φ 1) with 1 in Hk1. flia. }
  set (hx := (x >> kl k)%uint63).
  set (lx := (x - (hx << kl k))%uint63).
  assert (Ehx : (φ hx) = (φ x) / P) by (unfold hx; rewrite shr_spec, Ekl; reflexivity).
  destruct (encode P (φ x) ltac:(flia)) as [Ex Rlx].
  assert (Hhx : 0 <= (φ hx) < 2 ^ hi (φ k)).
  { rewrite Ehx. split; [apply Z.div_pos; flia|]. apply Z.div_lt_upper_bound; [flia|].
    rewrite Z.mul_comm, <- Pw. exact Hx. }
  assert (Eshl : (φ (hx << kl k))%uint63 = (φ hx) * P).
  { rewrite shl_nov; rewrite Ekl; fold P; [reflexivity|]. rewrite Ehx, wB_val. flia. }
  assert (Elx : (φ lx) = (φ x) mod P) by (unfold lx; rewrite sub_nov; rewrite Eshl, Ehx; flia).
  clearbody hx lx.
  set (c := clb t b k hx).
  pose proof (Hc hx (proj2 Hhx)) as Hcx. fold c in Hcx.
  (* the elements of a cluster, as elements of S *)
  assert (InS : forall i j, C i j -> S (i * P + j)).
  { intros i j Hij. pose proof (Crg _ _ Hij). pose proof (HCi _ _ Hij).
    destruct (decode P i j ltac:(flia)) as [D1 D2].
    apply HD. right. split; [pose proof (Z.mul_nonneg_nonneg i P ltac:(flia) ltac:(flia)); flia|].
    rewrite D1, D2. exact Hij. }
  (* z <= x, for z in a cluster, read on (high, low) *)
  assert (Lex : forall z, S z -> z <> (φ (v.[b])) -> z <= (φ x) ->
            C (z / P) (z mod P) /\ (z / P < (φ hx) \/ (z / P = (φ hx) /\ z mod P <= (φ lx)))).
  { intros z Hz Hzm Hzx. apply HD in Hz. destruct Hz as [Hz | (Hz0 & Hz)]; [flia|].
    split; [exact Hz|]. destruct (encode P z ltac:(flia)) as [Ez Rz].
    rewrite Ehx, Elx. apply (proj1 (lex_le P (z / P) (z mod P) ((φ x) / P) ((φ x) mod P) Rz Rlx)). flia. }
  destruct (v.[c] <=? lx)%uint63 eqn:E3.
  - (* the answer is in cluster hx *)
    rewrite leb_spec in E3.
    assert (Hne : exists j, C (φ hx) j /\ j <= (φ lx)).
    { destruct (ok_minmax _ _ _ _ Hcx) as [(A & _) | (_ & _ & A & _)]; [exfalso; unfold nilZ in A; flia|].
      exists (φ (v.[c])). split; [exact A | exact E3]. }
    pose proof (IH (lo (φ k)) ltac:(unfold Zwf; flia) (kl k) Ekl
                  (Acc_inv (Acc_intro (φ k) Hacc) (dec_lo k Hk1)) v c lx (C (φ hx)) Hcx
                  ltac:(rewrite Ekl; fold P; flia)) as Hr.
    set (r := vpred t v c (kl k) lx (Acc_inv (Acc_intro (φ k) Hacc) (dec_lo k Hk1))) in *.
    clearbody r.
    destruct Hr as [(Er & Hall) | (Hr1 & Hr2 & Hr3)].
    { exfalso. destruct Hne as (j & Hj1 & Hj2). pose proof (Hall _ Hj1). flia. }
    pose proof (Crg _ _ Hr1) as Rr.
    assert (Eres : (φ ((hx << kl k) + r))%uint63 = (φ hx) * P + (φ r)).
    { pose proof (mul_step (φ hx) (2 ^ hi (φ k)) P ltac:(flia) ltac:(flia)).
      rewrite add_nov, Eshl; [reflexivity|]. rewrite Eshl, wB_val. flia. }
    rewrite Eres. right. split; [apply InS; exact Hr1|]. split; [flia|].
    intros z Hz Hzx.
    destruct (Z.eq_dec z (φ (v.[b]))) as [Ezm | Ezm].
    + rewrite Ezm. pose proof (HCb _ _ Hr1). flia.
    + destruct (Lex z Hz Ezm Hzx) as (Cz & [Hlt | (Heq & Hle)]).
      * destruct (encode P z ltac:(flia)) as [Ez Rz]. rewrite Ez. apply lex_le; [exact Rz | exact Rr |]. left. exact Hlt.
      * destruct (encode P z ltac:(flia)) as [Ez Rz]. rewrite Ez. apply lex_le; [exact Rz | exact Rr |].
        right. split; [exact Heq|]. apply Hr3; [rewrite <- Heq; exact Cz | exact Hle].
  - (* no element of cluster hx is <= lx *)
    rewrite <- Bool.not_true_iff_false, leb_spec in E3.
    assert (Hno : forall j, C (φ hx) j -> (φ lx) < j).
    { intros j Hj. destruct (ok_minmax _ _ _ _ Hcx) as [(_ & _ & E) | (_ & _ & _ & _ & A)];
        [destruct (E _ Hj) | pose proof (A _ Hj); flia]. }
    assert (Below : forall z, S z -> z <> (φ (v.[b])) -> z <= (φ x) -> z / P < (φ hx) /\ C (z / P) (z mod P)).
    { intros z Hz Hzm Hzx. destruct (Lex z Hz Hzm Hzx) as (Cz & [Hlt | (Heq & Hle)]); [split; assumption|].
      exfalso. rewrite Heq in Cz. pose proof (Hno _ Cz). flia. }
    destruct (hx =? 0)%uint63 eqn:E4.
    + rewrite eqb_spec in E4. right. split; [exact HSm|]. split; [flia|].
      intros z Hz Hzx. destruct (Z.eq_dec z (φ (v.[b]))) as [Ezm | Ezm]; [flia|].
      destruct (Below z Hz Ezm Hzx) as [Hlt Cz]. rewrite E4 in Hlt. change (φ 0) with 0 in Hlt.
      pose proof (HCi _ _ Cz). flia.
    + rewrite eqb_Z in E4. apply Z.eqb_neq in E4. change (φ 0) with 0 in E4.
      assert (Ehx1 : (φ (hx - 1))%uint63 = (φ hx) - 1) by (rewrite sub_nov; change (φ 1) with 1; flia).
      pose proof (IH (hi (φ k)) ltac:(unfold Zwf; flia) (kh k) Ekh
                    (Acc_inv (Acc_intro (φ k) Hacc) (dec_hi k Hk1)) v (b + 2)%uint63 (hx - 1)%uint63 Ss Hs
                    ltac:(rewrite Ekh, Ehx1; flia)) as Hr.
      set (r := vpred t v (b + 2) (kh k) (hx - 1) (Acc_inv (Acc_intro (φ k) Hacc) (dec_hi k Hk1))) in *.
      clearbody r. rewrite Ehx1 in Hr.
      destruct (r =? nil)%uint63 eqn:E5.
      * rewrite eqb_spec in E5. destruct Hr as [(_ & Hall) | (Hr1 & _)].
        -- right. split; [exact HSm|]. split; [flia|].
           intros z Hz Hzx. destruct (Z.eq_dec z (φ (v.[b]))) as [Ezm | Ezm]; [flia|].
           destruct (Below z Hz Ezm Hzx) as [Hlt Cz].
           assert (Hsz : Ss (z / P)) by (apply HSs; split; [apply (HCi _ _ Cz) | eexists; exact Cz]).
           pose proof (Hall _ Hsz). flia.
        -- exfalso. rewrite E5, nil_val in Hr1. pose proof (ok_range _ _ _ _ Hs _ Hr1) as R.
           rewrite Ekh in R. unfold nilZ in R. flia.
      * rewrite eqb_Z, nil_val in E5. apply Z.eqb_neq in E5.
        destruct Hr as [(Er & _) | (Hr1 & Hr2 & Hr3)]; [exfalso; exact (E5 Er)|].
        pose proof (ok_range _ _ _ _ Hs _ Hr1) as Rr. rewrite Ekh in Rr.
        pose proof (Hc r (proj2 Rr)) as Hcr.
        assert (Hner : exists j, C (φ r) j) by (apply HSs in Hr1; destruct Hr1 as (_ & j & Hj); exists j; exact Hj).
        destruct (ok_minmax _ _ _ _ Hcr) as [(_ & _ & E) | (_ & Bm & _ & HCmx & Hcmax)];
          [destruct Hner as [j Hj]; destruct (E _ Hj)|].
        rewrite Ekl in Bm. fold P in Bm.
        set (mx := v.[(clb t b k r + 1)%uint63]) in *.
        assert (Eres : (φ ((r << kl k) + mx))%uint63 = (φ r) * P + (φ mx)).
        { pose proof (mul_step (φ r) (2 ^ hi (φ k)) P ltac:(flia) ltac:(flia)).
          assert (Esh : (φ (r << kl k))%uint63 = (φ r) * P)
            by (rewrite shl_nov; rewrite Ekl; fold P; [reflexivity | rewrite wB_val; flia]).
          rewrite add_nov; rewrite Esh; [reflexivity | rewrite wB_val; flia]. }
        rewrite Eres. right. split; [apply InS; exact HCmx|]. split.
        -- assert ((φ r) * P + P <= (φ hx) * P) by (apply mul_step; flia).
           pose proof (Z.mul_nonneg_nonneg (φ hx) P ltac:(flia) ltac:(flia)). flia.
        -- intros z Hz Hzx. destruct (Z.eq_dec z (φ (v.[b]))) as [Ezm | Ezm].
           ++ rewrite Ezm. pose proof (HCb _ _ HCmx). flia.
           ++ destruct (Below z Hz Ezm Hzx) as [Hlt Cz].
              assert (Hzr : z / P <= (φ r)).
              { apply Hr3; [apply HSs; split; [apply (HCi _ _ Cz) | eexists; exact Cz] | flia]. }
              destruct (encode P z ltac:(flia)) as [Ez Rz]. rewrite Ez.
              apply lex_le; [exact Rz | flia |].
              destruct (Z.eq_dec (z / P) (φ r)) as [Ei | Ei]; [right; split; [exact Ei|] | left; flia].
              apply Hcmax. rewrite <- Ei. exact Cz.
Qed.

End VEB.

(* ------------------------------------------------------------------ *)
(* Heaps                                                               *)
(* ------------------------------------------------------------------ *)

(* cell j of the heap stored from s *)
Definition hg (gd : array int) (s : int) (j : Z) : Z := (φ (gd.[(s + of_Z j)%uint63])).

Fixpoint cntf (G : Z -> Z) (n : nat) (g : Z) : nat :=
  match n with
  | O => O
  | S m => (cntf G m g + (if Z.eqb (G (Z.of_nat m)) g then 1 else 0))%nat
  end.

Definition hcnt (gd : array int) (s : int) (n : Z) (g : Z) : nat := cntf (hg gd s) (Z.to_nat n) g.

Definition hheap (gd : array int) (s : int) (n : Z) : Prop :=
  forall j, 0 < j < n -> hg gd s j <= hg gd s ((j - 1) / 2).

Lemma hg_int : forall gd s (p : int), hg gd s (φ p) = (φ (gd.[(s + p)%uint63])).
Proof. intros. unfold hg. rewrite of_to_Z. reflexivity. Qed.

Lemma pos_int : forall (s : int) j, 0 <= j -> (φ s) + j < wB -> (φ (s + of_Z j))%uint63 = (φ s) + j.
Proof.
  intros s j H1 H2. pose proof (to_Z_bounded s).
  assert (E : (φ (of_Z j)) = j) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  rewrite add_nov; rewrite E; lia.
Qed.

Lemma hg_set : forall gd s (q w : int) j, 0 <= j -> (φ s) + j < wB ->
  (φ q) < (φ (PArray.length gd)) ->
  hg (gd.[q <- w]) s j = if ((φ s) + j =? (φ q)) then (φ w) else hg gd s j.
Proof.
  intros gd s q w j H1 H2 H3. unfold hg. pose proof (pos_int s j H1 H2) as E.
  destruct (Z.eqb_spec ((φ s) + j) (φ q)) as [Eq | Eq].
  - assert (Ei : (s + of_Z j)%uint63 = q) by (apply to_Z_inj; lia). rewrite Ei.
    rewrite aget_set_same by exact H3. reflexivity.
  - rewrite aget_set_other by lia. reflexivity.
Qed.

Lemma cntf_ext : forall G G' n g, (forall j, 0 <= j < Z.of_nat n -> G j = G' j) ->
  cntf G n g = cntf G' n g.
Proof.
  intros G G' n g. induction n as [| n IH]; intros E; [reflexivity|].
  simpl. rewrite IH by (intros j Hj; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma cntf_upd : forall G G' n a w g, 0 <= a < Z.of_nat n -> G' a = w ->
  (forall j, 0 <= j < Z.of_nat n -> j <> a -> G' j = G j) ->
  (cntf G' n g + (if Z.eqb (G a) g then 1 else 0) = cntf G n g + (if Z.eqb w g then 1 else 0))%nat.
Proof.
  intros G G' n a w g. induction n as [| n IH]; intros Ha Ew Eo; [lia|].
  simpl. destruct (Z.eq_dec a (Z.of_nat n)) as [E | E].
  - subst a. rewrite (cntf_ext G' G n g) by (intros j Hj; apply Eo; lia).
    rewrite Ew. lia.
  - rewrite (Eo (Z.of_nat n)) by lia.
    pose proof (IH ltac:(lia) Ew ltac:(intros j Hj Hj'; apply Eo; lia)). lia.
Qed.

Lemma cntf_pos : forall G n g, (cntf G n g > 0)%nat -> exists j, 0 <= j < Z.of_nat n /\ G j = g.
Proof.
  intros G n g. induction n as [| n IH]; simpl; intros H; [lia|].
  destruct (Z.eqb_spec (G (Z.of_nat n)) g) as [E | E].
  - exists (Z.of_nat n). split; [lia | exact E].
  - destruct (IH ltac:(lia)) as (j & Hj & Ej). exists j. split; [lia | exact Ej].
Qed.

Lemma cntf_in : forall G n g j, 0 <= j < Z.of_nat n -> G j = g -> (cntf G n g > 0)%nat.
Proof.
  intros G n g. induction n as [| n IH]; simpl; intros j Hj Ej; [lia|].
  destruct (Z.eq_dec j (Z.of_nat n)) as [E | E].
  - subst j. rewrite Ej, Z.eqb_refl. lia.
  - pose proof (IH j ltac:(lia) Ej). lia.
Qed.

Lemma hheap_root : forall gd s n, hheap gd s n -> forall j, 0 <= j < n -> hg gd s j <= hg gd s 0.
Proof.
  intros gd s n H j. pattern j. apply (well_founded_induction (Zwf_well_founded 0)).
  intros x IH Hx. destruct (Z.eq_dec x 0) as [E | E]; [subst; lia|].
  pose proof (H x ltac:(lia)).
  assert (0 <= (x - 1) / 2 < x) by (Z.to_euclidean_division_equations; lia).
  pose proof (IH ((x - 1) / 2) ltac:(unfold Zwf; lia) ltac:(lia)). lia.
Qed.

(* swapping two cells of a segment keeps the counts *)
Lemma hcnt_swap : forall gd s n (p i : int), 0 <= (φ p) < n -> 0 <= (φ i) < n -> (φ p) <> (φ i) ->
  (φ s) + n <= (φ (PArray.length gd)) ->
  forall g, hcnt gd.[(s + p)%uint63 <- gd.[(s + i)%uint63]].[(s + i)%uint63 <- gd.[(s + p)%uint63]] s n g
            = hcnt gd s n g.
Proof.
  intros gd s n p i Hp Hi Hpi Hl g. pose proof (alength_bound gd). pose proof (to_Z_bounded s).
  assert (Ep : (φ (s + p))%uint63 = (φ s) + (φ p)) by (rewrite add_nov; rewrite ?wB_val; lia).
  assert (Ei : (φ (s + i))%uint63 = (φ s) + (φ i)) by (rewrite add_nov; rewrite ?wB_val; lia).
  set (gd1 := gd.[(s + p)%uint63 <- gd.[(s + i)%uint63]]).
  assert (L1 : PArray.length gd1 = PArray.length gd) by apply alength_set.
  unfold hcnt.
  assert (A1 : hg gd1 s (φ p) = (φ (gd.[(s + i)%uint63]))).
  { unfold gd1. rewrite hg_set by (rewrite ?wB_val; lia). rewrite Ep, Z.eqb_refl. reflexivity. }
  assert (A2 : forall j, 0 <= j < Z.of_nat (Z.to_nat n) -> j <> (φ p) -> hg gd1 s j = hg gd s j).
  { intros j Hj Hj'. unfold gd1. rewrite hg_set by (rewrite ?wB_val; lia).
    destruct (Z.eqb_spec ((φ s) + j) ((φ (s + p))%uint63)); [lia | reflexivity]. }
  assert (A3 : hg gd1.[(s + i)%uint63 <- gd.[(s + p)%uint63]] s (φ i) = (φ (gd.[(s + p)%uint63]))).
  { rewrite hg_set by (rewrite ?L1, ?wB_val; lia). rewrite Ei, Z.eqb_refl. reflexivity. }
  assert (A4 : forall j, 0 <= j < Z.of_nat (Z.to_nat n) -> j <> (φ i) ->
             hg gd1.[(s + i)%uint63 <- gd.[(s + p)%uint63]] s j = hg gd1 s j).
  { intros j Hj Hj'. rewrite hg_set by (rewrite ?L1, ?wB_val; lia).
    destruct (Z.eqb_spec ((φ s) + j) ((φ (s + i))%uint63)); [lia | reflexivity]. }
  assert (Bp : 0 <= (φ p) < Z.of_nat (Z.to_nat n)) by lia.
  assert (Bi : 0 <= (φ i) < Z.of_nat (Z.to_nat n)) by lia.
  assert (Hgi : hg gd1 s (φ i) = hg gd s (φ i)) by (apply A2; lia).
  pose proof (cntf_upd (hg gd s) (hg gd1 s) (Z.to_nat n) (φ p) (φ (gd.[(s + i)%uint63])) g
                Bp A1 A2) as U1.
  pose proof (cntf_upd (hg gd1 s) (hg gd1.[(s + i)%uint63 <- gd.[(s + p)%uint63]] s) (Z.to_nat n) (φ i)
                (φ (gd.[(s + p)%uint63])) g Bi A3 A4) as U2.
  rewrite Hgi in U2. rewrite !hg_int in U1, U2. lia.
Qed.

Lemma hg_swap : forall gd s n (p i : int), 0 <= (φ p) < n -> 0 <= (φ i) < n -> (φ p) <> (φ i) ->
  (φ s) + n <= (φ (PArray.length gd)) ->
  forall j, 0 <= j < n ->
  hg gd.[(s + p)%uint63 <- gd.[(s + i)%uint63]].[(s + i)%uint63 <- gd.[(s + p)%uint63]] s j
  = if j =? (φ i) then hg gd s (φ p) else if j =? (φ p) then hg gd s (φ i) else hg gd s j.
Proof.
  intros gd s n p i Hp Hi Hpi Hl j Hj. pose proof (alength_bound gd). pose proof (to_Z_bounded s).
  assert (Ep : (φ (s + p))%uint63 = (φ s) + (φ p)) by (rewrite add_nov; rewrite ?wB_val; lia).
  assert (Ei : (φ (s + i))%uint63 = (φ s) + (φ i)) by (rewrite add_nov; rewrite ?wB_val; lia).
  rewrite hg_set by (rewrite ?alength_set, ?wB_val; lia).
  rewrite hg_set by (rewrite ?wB_val; lia).
  rewrite Ep, Ei, !hg_int.
  destruct (Z.eqb_spec ((φ s) + j) ((φ s) + (φ i))); destruct (Z.eqb_spec j (φ i)); try lia;
  destruct (Z.eqb_spec ((φ s) + j) ((φ s) + (φ p))); destruct (Z.eqb_spec j (φ p)); try lia; reflexivity.
Qed.

Lemma sup_spec : forall m (i : int), (φ i) = m -> forall (H : Acc (Zwf 0) (φ i)) gd s n,
  (φ s) + n <= (φ (PArray.length gd)) -> 0 <= (φ i) < n ->
  (forall j, 0 < j < n -> j <> (φ i) -> hg gd s j <= hg gd s ((j - 1) / 2)) ->
  (0 < (φ i) -> forall j, 0 < j < n -> (j - 1) / 2 = (φ i) -> hg gd s j <= hg gd s (((φ i) - 1) / 2)) ->
  PArray.length (sup gd s i H) = PArray.length gd /\
  (forall q : int, ~ ((φ s) <= (φ q) < (φ s) + n) -> (sup gd s i H).[q] = gd.[q]) /\
  hheap (sup gd s i H) s n /\ (forall g, hcnt (sup gd s i H) s n g = hcnt gd s n g).
Proof.
  intros m. induction m as [m IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros i Em H gd s n Hl Hi Hh Hg.
  pose proof (alength_bound gd). pose proof (to_Z_bounded s).
  destruct H as [Hacc]. cbn [sup].
  destruct (bdec (0 <? i)%uint63) as [Hi0 | Hi0].
  - pose proof Hi0 as Hi0'. rewrite ltb_spec in Hi0'. change (φ 0) with 0 in Hi0'.
    set (p := ((i - 1) >> 1)%uint63).
    assert (Ep : (φ p) = ((φ i) - 1) / 2).
    { unfold p. rewrite shr1_spec, sub_nov; change (φ 1) with 1; [reflexivity | lia]. }
    assert (Hp : 0 <= (φ p) < (φ i)) by (rewrite Ep; Z.to_euclidean_division_equations; lia).
    destruct (gd.[(s + p)%uint63] <? gd.[(s + i)%uint63])%uint63 eqn:Ec.
    + rewrite ltb_spec, <- !hg_int in Ec.
      pose proof (hg_swap gd s n p i ltac:(lia) ltac:(lia) ltac:(lia) Hl) as Sw.
      pose proof (hcnt_swap gd s n p i ltac:(lia) ltac:(lia) ltac:(lia) Hl) as Cn.
      set (gd2 := gd.[(s + p)%uint63 <- gd.[(s + i)%uint63]].[(s + i)%uint63 <- gd.[(s + p)%uint63]]) in *.
      assert (L2 : PArray.length gd2 = PArray.length gd) by (unfold gd2; rewrite !alength_set; reflexivity).
      assert (F2 : forall q : int, ~ ((φ s) <= (φ q) < (φ s) + n) -> gd2.[q] = gd.[q]).
      { intros q Hq. unfold gd2. rewrite !aget_set_other; [reflexivity | |];
          rewrite add_nov; rewrite ?wB_val; lia. }
      destruct (IH (φ p) ltac:(unfold Zwf; lia) p eq_refl
                  (Acc_inv (Acc_intro (φ i) Hacc) (dec_par i Hi0)) gd2 s n
                  ltac:(rewrite L2; exact Hl) ltac:(lia)) as (L3 & F3 & H3 & C3).
      * intros j Hj Hjp.
        assert (0 <= (j - 1) / 2 < j) by (Z.to_euclidean_division_equations; lia).
        rewrite (Sw j), (Sw ((j - 1) / 2)) by lia.
        destruct (Z.eqb_spec j (φ i)) as [Eji | Eji].
        -- subst j. rewrite <- Ep.
           destruct (Z.eqb_spec (φ p) (φ i)); [lia|]. rewrite Z.eqb_refl. lia.
        -- destruct (Z.eqb_spec j (φ p)) as [Ejp | _]; [lia|].
           destruct (Z.eqb_spec ((j - 1) / 2) (φ i)) as [Eq | Eq].
           ++ pose proof (Hg Hi0' j Hj Eq) as G1. rewrite <- Ep in G1. exact G1.
           ++ destruct (Z.eqb_spec ((j - 1) / 2) (φ p)) as [Eq2 | Eq2].
              ** pose proof (Hh j Hj Eji) as G1. rewrite Eq2 in G1. lia.
              ** apply Hh; assumption.
      * intros Hp0 j Hj Hjp.
        assert (0 <= ((φ p) - 1) / 2 < (φ p)) by (Z.to_euclidean_division_equations; lia).
        rewrite (Sw j), (Sw (((φ p) - 1) / 2)) by lia.
        destruct (Z.eqb_spec (((φ p) - 1) / 2) (φ i)); [lia|].
        destruct (Z.eqb_spec (((φ p) - 1) / 2) (φ p)); [lia|].
        pose proof (Hh (φ p) ltac:(lia) ltac:(lia)) as G1.
        destruct (Z.eqb_spec j (φ i)) as [Eji | Eji]; [exact G1|].
        destruct (Z.eqb_spec j (φ p)) as [Ejp | Ejp]; [rewrite Ejp in Hjp; Z.to_euclidean_division_equations; lia|].
        pose proof (Hh j Hj Eji) as G2. rewrite Hjp in G2. lia.
      * split; [etransitivity; [exact L3 | exact L2]|]. split; [|split; [exact H3|]].
        -- intros q Hq. rewrite F3 by exact Hq. apply F2. exact Hq.
        -- intros g. rewrite C3. apply Cn.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, <- !hg_int in Ec.
      split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
      intros j Hj. destruct (Z.eq_dec j (φ i)) as [E | E]; [subst j; rewrite <- Ep; lia | apply Hh; lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi0. change (φ 0) with 0 in Hi0.
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    intros j Hj. apply Hh; lia.
Qed.

Lemma pick_spec : forall gd s (n i : int), (φ n) <= 4194303 ->
  (andb (i <? 2 * i + 1) (2 * i + 1 <? n))%uint63 = true ->
  ((φ (pickc gd s n i)) = 2 * (φ i) + 1 \/ (φ (pickc gd s n i)) = 2 * (φ i) + 2) /\
  (φ (pickc gd s n i)) < (φ n) /\
  forall j, 0 < j < (φ n) -> (j - 1) / 2 = (φ i) -> hg gd s j <= hg gd s (φ (pickc gd s n i)).
Proof.
  intros gd s n i Hn H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. pose proof (to_Z_bounded i).
  assert (E1 : (φ (2 * i + 1))%uint63 = 2 * (φ i) + 1).
  { assert (E0 : (φ (2 * i))%uint63 = (2 * (φ i)) mod wB) by (rewrite mul_spec; reflexivity).
    rewrite add_spec, E0. change (φ 1) with 1. rewrite wB_val in *.
    rewrite add_spec, E0 in H1, H2. change (φ 1) with 1 in H1, H2.
    Z.to_euclidean_division_equations; lia. }
  rewrite E1 in H1, H2.
  assert (Ech : forall j, (j - 1) / 2 = (φ i) -> j = 2 * (φ i) + 1 \/ j = 2 * (φ i) + 2)
    by (intros j Hj; Z.to_euclidean_division_equations; lia).
  unfold pickc.
  destruct (2 * i + 1 + 1 <? n)%uint63 eqn:E2.
  - rewrite ltb_spec in E2.
    assert (E3 : (φ (2 * i + 1 + 1))%uint63 = 2 * (φ i) + 2) by (rewrite add_nov, E1; change (φ 1) with 1; rewrite ?E1, ?wB_val; lia).
    rewrite E3 in E2.
    destruct (gd.[(s + (2 * i + 1))%uint63] <? gd.[(s + (2 * i + 1 + 1))%uint63])%uint63 eqn:E4.
    + rewrite ltb_spec, <- !hg_int, E1, E3 in E4. rewrite E3.
      split; [right; reflexivity|]. split; [lia|].
      intros j Hj Hji. destruct (Ech j Hji) as [Ej | Ej]; subst j; lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, <- !hg_int, E1, E3 in E4. rewrite E1.
      split; [left; reflexivity|]. split; [lia|].
      intros j Hj Hji. destruct (Ech j Hji) as [Ej | Ej]; subst j; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E2. rewrite E1.
    assert (E3 : (φ (2 * i + 1 + 1))%uint63 = 2 * (φ i) + 2) by (rewrite add_nov, E1; change (φ 1) with 1; rewrite ?E1, ?wB_val; lia).
    rewrite E3 in E2.
    split; [left; reflexivity|]. split; [lia|].
    intros j Hj Hji. destruct (Ech j Hji) as [Ej | Ej]; subst j; lia.
Qed.

Lemma sdown_spec : forall m (n i : int), (φ n) - (φ i) = m ->
  forall (H : Acc (Zwf 0) ((φ n) - (φ i))) gd s,
  (φ s) + (φ n) <= (φ (PArray.length gd)) -> 0 <= (φ i) <= (φ n) ->
  (forall j, 0 < j < (φ n) -> (j - 1) / 2 <> (φ i) -> hg gd s j <= hg gd s ((j - 1) / 2)) ->
  (0 < (φ i) -> forall j, 0 < j < (φ n) -> (j - 1) / 2 = (φ i) -> hg gd s j <= hg gd s (((φ i) - 1) / 2)) ->
  PArray.length (sdown gd s n i H) = PArray.length gd /\
  (forall q : int, ~ ((φ s) <= (φ q) < (φ s) + (φ n)) -> (sdown gd s n i H).[q] = gd.[q]) /\
  hheap (sdown gd s n i H) s (φ n) /\ (forall g, hcnt (sdown gd s n i H) s (φ n) g = hcnt gd s (φ n) g).
Proof.
  intros m. induction m as [m IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros n i Em H gd s Hl Hi Hh Hg.
  pose proof (alength_bound gd). pose proof (to_Z_bounded s).
  destruct H as [Hacc]. cbn [sdown].
  destruct (bdec (andb (i <? 2 * i + 1) (2 * i + 1 <? n))%uint63) as [Hc | Hc].
  - destruct (pick_spec gd s n i ltac:(lia) Hc) as (Pc1 & Pc2 & Pc3).
    set (c := pickc gd s n i) in *.
    assert (Hpc : ((φ c) - 1) / 2 = (φ i)) by (destruct Pc1 as [E | E]; rewrite E; Z.to_euclidean_division_equations; lia).
    destruct (gd.[(s + i)%uint63] <? gd.[(s + c)%uint63])%uint63 eqn:Ec.
    + rewrite ltb_spec, <- !hg_int in Ec.
      pose proof (hg_swap gd s (φ n) i c ltac:(lia) ltac:(lia) ltac:(lia) Hl) as Sw.
      pose proof (hcnt_swap gd s (φ n) i c ltac:(lia) ltac:(lia) ltac:(lia) Hl) as Cn.
      set (gd2 := gd.[(s + i)%uint63 <- gd.[(s + c)%uint63]].[(s + c)%uint63 <- gd.[(s + i)%uint63]]) in *.
      assert (L2 : PArray.length gd2 = PArray.length gd) by (unfold gd2; rewrite !alength_set; reflexivity).
      assert (F2 : forall q : int, ~ ((φ s) <= (φ q) < (φ s) + (φ n)) -> gd2.[q] = gd.[q]).
      { intros q Hq. unfold gd2. rewrite !aget_set_other; [reflexivity | |];
          rewrite add_nov; rewrite ?wB_val; lia. }
      destruct (IH ((φ n) - (φ c)) ltac:(unfold Zwf; lia) n c eq_refl
                  (Acc_inv (Acc_intro ((φ n) - (φ i)) Hacc) (dec_pick gd s n i Hc)) gd2 s
                  ltac:(rewrite L2; exact Hl) ltac:(lia)) as (L3 & F3 & H3 & C3).
      * intros j Hj Hjc.
        assert (0 <= (j - 1) / 2 < j) by (Z.to_euclidean_division_equations; lia).
        rewrite (Sw j), (Sw ((j - 1) / 2)) by lia.
        destruct (Z.eqb_spec j (φ c)) as [Ejc | Ejc].
        -- subst j. rewrite Hpc. destruct (Z.eqb_spec (φ i) (φ c)); [lia|]. rewrite Z.eqb_refl. lia.
        -- destruct (Z.eqb_spec j (φ i)) as [Eji | Eji].
           ++ subst j. destruct (Z.eqb_spec (((φ i) - 1) / 2) (φ c)); [lia|].
              destruct (Z.eqb_spec (((φ i) - 1) / 2) (φ i)); [lia|].
              exact (Hg ltac:(lia) (φ c) ltac:(lia) Hpc).
           ++ destruct (Z.eqb_spec ((j - 1) / 2) (φ c)); [lia|].
              destruct (Z.eqb_spec ((j - 1) / 2) (φ i)) as [Eq | Eq].
              ** pose proof (Pc3 j Hj Eq). lia.
              ** apply Hh; assumption.
      * intros Hc0 j Hj Hjc.
        rewrite (Sw j), (Sw (((φ c) - 1) / 2)) by lia. rewrite Hpc.
        destruct (Z.eqb_spec j (φ c)); destruct (Z.eqb_spec j (φ i)); destruct (Z.eqb_spec (φ i) (φ c)); try lia.
        rewrite Z.eqb_refl. pose proof (Hh j Hj ltac:(lia)) as G1. rewrite Hjc in G1. lia.
      * split; [etransitivity; [exact L3 | exact L2]|]. split; [|split; [exact H3|]].
        -- intros q Hq. rewrite F3 by exact Hq. apply F2. exact Hq.
        -- intros g. rewrite C3. apply Cn.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, <- !hg_int in Ec.
      split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
      intros j Hj. destruct (Z.eq_dec ((j - 1) / 2) (φ i)) as [E | E].
      * rewrite E. pose proof (Pc3 j Hj E). lia.
      * apply Hh; lia.
  - split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    assert (Hn : (φ n) <= 2 * (φ i) + 1).
    { apply Bool.andb_false_iff in Hc. destruct Hc as [Hc | Hc];
        rewrite <- Bool.not_true_iff_false, ltb_spec in Hc;
        rewrite add_spec, mul_spec in Hc; change (φ 1) with 1 in Hc; change (φ 2) with 2 in Hc;
        rewrite wB_val in Hc; Z.to_euclidean_division_equations; lia. }
    intros j Hj. apply Hh; [lia|]. Z.to_euclidean_division_equations. lia.
Qed.

Lemma hpush_spec : forall gd s (n g : int), (φ s) + (φ n) + 1 <= (φ (PArray.length gd)) ->
  hheap gd s (φ n) ->
  PArray.length (hpush gd s n g) = PArray.length gd /\
  (forall q : int, ~ ((φ s) <= (φ q) < (φ s) + (φ n) + 1) -> (hpush gd s n g).[q] = gd.[q]) /\
  hheap (hpush gd s n g) s ((φ n) + 1) /\
  (forall g', hcnt (hpush gd s n g) s ((φ n) + 1) g' = (hcnt gd s (φ n) g' + if Z.eqb (φ g) g' then 1 else 0)%nat).
Proof.
  intros gd s n g Hl Hh. unfold hpush.
  pose proof (alength_bound gd). pose proof (to_Z_bounded s). pose proof (to_Z_bounded n).
  assert (En : (φ (s + n))%uint63 = (φ s) + (φ n)) by (rewrite add_nov; rewrite ?wB_val; lia).
  set (gd1 := gd.[(s + n)%uint63 <- g]).
  assert (L1 : PArray.length gd1 = PArray.length gd) by apply alength_set.
  assert (G1 : forall j, 0 <= j < (φ n) + 1 -> hg gd1 s j = if j =? (φ n) then (φ g) else hg gd s j).
  { intros j Hj. unfold gd1. rewrite hg_set by (rewrite ?wB_val; lia). rewrite En.
    destruct (Z.eqb_spec ((φ s) + j) ((φ s) + (φ n))); destruct (Z.eqb_spec j (φ n)); try lia; reflexivity. }
  destruct (sup_spec (φ n) n eq_refl (Zwf_well_founded 0 (φ n)) gd1 s ((φ n) + 1)
              ltac:(rewrite L1; lia) ltac:(lia)) as (L2 & F2 & H2 & C2).
  - intros j Hj Hjn.
    assert (0 <= (j - 1) / 2 < j) by (Z.to_euclidean_division_equations; lia).
    rewrite !G1 by lia. destruct (Z.eqb_spec j (φ n)); [lia|].
    destruct (Z.eqb_spec ((j - 1) / 2) (φ n)); [lia|]. apply Hh; lia.
  - intros Hn0 j Hj Hjn. exfalso. Z.to_euclidean_division_equations; lia.
  - split; [etransitivity; [exact L2 | exact L1]|]. split; [|split; [exact H2|]].
    + intros q Hq. rewrite F2 by lia. unfold gd1. apply aget_set_other. lia.
    + intros g'. rewrite C2. unfold hcnt.
      replace (Z.to_nat ((φ n) + 1)) with (S (Z.to_nat (φ n))) by lia. cbn [cntf].
      rewrite (cntf_ext (hg gd1 s) (hg gd s))
        by (intros j Hj; rewrite G1 by lia; destruct (Z.eqb_spec j (φ n)); [lia | reflexivity]).
      rewrite Z2Nat.id by lia. rewrite G1 by lia. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma hpop_spec : forall gd s (n : int), 1 <= (φ n) -> (φ s) + (φ n) <= (φ (PArray.length gd)) ->
  hheap gd s (φ n) ->
  PArray.length (hpop gd s n) = PArray.length gd /\
  (forall q : int, ~ ((φ s) <= (φ q) < (φ s) + (φ n)) -> (hpop gd s n).[q] = gd.[q]) /\
  hheap (hpop gd s n) s ((φ n) - 1) /\
  (forall g', (hcnt (hpop gd s n) s ((φ n) - 1) g' + (if Z.eqb (hg gd s 0) g' then 1 else 0)
               = hcnt gd s (φ n) g')%nat).
Proof.
  intros gd s n Hn Hl Hh. unfold hpop.
  pose proof (alength_bound gd). pose proof (to_Z_bounded s). pose proof (to_Z_bounded n).
  assert (En1 : (φ (n - 1))%uint63 = (φ n) - 1) by (rewrite sub_nov; change (φ 1) with 1; lia).
  set (last := gd.[(s + (n - 1))%uint63]).
  assert (Elast : (φ last) = hg gd s ((φ n) - 1)) by (unfold last; rewrite <- En1, hg_int; reflexivity).
  set (gd1 := gd.[s <- last]).
  assert (L1 : PArray.length gd1 = PArray.length gd) by apply alength_set.
  assert (G1 : forall j, 0 <= j < (φ n) -> hg gd1 s j = if j =? 0 then (φ last) else hg gd s j).
  { intros j Hj. unfold gd1. rewrite hg_set by (rewrite ?wB_val; lia).
    destruct (Z.eqb_spec ((φ s) + j) (φ s)); destruct (Z.eqb_spec j 0); try lia; reflexivity. }
  destruct (sdown_spec ((φ (n - 1))%uint63 - (φ 0)) (n - 1) 0 eq_refl
              (Zwf_well_founded 0 ((φ (n - 1))%uint63 - (φ 0))) gd1 s
              ltac:(rewrite L1, En1; lia) ltac:(rewrite En1; change (φ 0) with 0; lia)) as (L2 & F2 & H2 & C2).
  - intros j Hj Hj0. change (φ 0) with 0 in Hj0. rewrite En1 in Hj.
    assert (0 <= (j - 1) / 2 < j) by (Z.to_euclidean_division_equations; lia).
    rewrite !G1 by lia. destruct (Z.eqb_spec j 0); [lia|].
    destruct (Z.eqb_spec ((j - 1) / 2) 0); [lia|]. apply Hh; lia.
  - intros H0'. change (φ 0) with 0 in H0'. lia.
  - set (r := sdown gd1 s (n - 1) 0 (Zwf_well_founded 0 ((φ (n - 1))%uint63 - (φ 0)))) in *.
    clearbody r. rewrite En1 in F2, H2, C2.
    split; [etransitivity; [exact L2 | exact L1]|]. split; [|split; [exact H2|]].
    + intros q Hq. rewrite F2 by lia. unfold gd1. apply aget_set_other. lia.
    + intros g'. rewrite C2. unfold hcnt.
      destruct (Z.eq_dec (φ n) 1) as [E1 | E1].
      * rewrite E1. change (Z.to_nat (1 - 1)) with O. change (Z.to_nat 1) with (S O). cbn [cntf].
        reflexivity.
      * pose proof (cntf_upd (hg gd s) (hg gd1 s) (Z.to_nat ((φ n) - 1)) 0 (φ last) g'
                      ltac:(lia) ltac:(rewrite G1 by lia; reflexivity)
                      ltac:(intros j Hj Hj0; rewrite G1 by lia; destruct (Z.eqb_spec j 0); [lia | reflexivity])) as U.
        replace (Z.to_nat (φ n)) with (S (Z.to_nat ((φ n) - 1))) by lia. cbn [cntf].
        rewrite Z2Nat.id by lia. rewrite <- Elast. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Math-side helpers                                                   *)
(* ------------------------------------------------------------------ *)

(* how many quests (e, g) the pool holds *)
Definition qcount (P : list (N * N)) (e g : Z) : nat :=
  List.length (filter (fun q => (Z.of_N (fst q) =? e) && (Z.of_N (snd q) =? g))%bool P).

Lemma qcount_app : forall l1 l2 e g, qcount (l1 ++ l2) e g = (qcount l1 e g + qcount l2 e g)%nat.
Proof. intros. unfold qcount. rewrite filter_app, length_app. reflexivity. Qed.

Lemma qcount_cons : forall q P e g, qcount (q :: P) e g =
  ((if andb (Z.of_N (fst q) =? e)%Z (Z.of_N (snd q) =? g)%Z then 1 else 0) + qcount P e g)%nat.
Proof. intros. unfold qcount. simpl. destruct (andb (Z.of_N (fst q) =? e)%Z (Z.of_N (snd q) =? g)%Z); reflexivity. Qed.

Lemma qcount_in : forall P q, In q P -> (qcount P (Z.of_N (fst q)) (Z.of_N (snd q)) > 0)%nat.
Proof.
  intros P q H. unfold qcount.
  assert (In q (filter (fun q0 => (Z.of_N (fst q0) =? Z.of_N (fst q)) && (Z.of_N (snd q0) =? Z.of_N (snd q)))%bool P)).
  { apply filter_In. split; [exact H|]. rewrite !Z.eqb_refl. reflexivity. }
  destruct (filter _ P); [destruct H0 | simpl; lia].
Qed.

Lemma qcount_pos : forall P e g, (qcount P e g > 0)%nat ->
  exists q, In q P /\ Z.of_N (fst q) = e /\ Z.of_N (snd q) = g.
Proof.
  intros P e g H. unfold qcount in H.
  destruct (filter _ P) as [| q l] eqn:E; [simpl in H; lia|].
  assert (Hq : In q (filter (fun q => (Z.of_N (fst q) =? e) && (Z.of_N (snd q) =? g))%bool P))
    by (rewrite E; left; reflexivity).
  apply filter_In in Hq. destruct Hq as [Hq1 Hq2]. apply andb_prop in Hq2.
  destruct Hq2 as [A B]. apply Z.eqb_eq in A, B. exists q. auto.
Qed.

Lemma qcount_zero : forall P e, (forall g, qcount P e g = O) -> forall q, In q P -> Z.of_N (fst q) <> e.
Proof.
  intros P e H q Hq E. pose proof (qcount_in P q Hq). rewrite E, H in H0. lia.
Qed.

Definition sumg (P : list (N * N)) : Z := fold_right (fun q acc => Z.of_N (snd q) + acc) 0 P.

Lemma sumg_app : forall l1 l2, sumg (l1 ++ l2) = sumg l1 + sumg l2.
Proof. induction l1 as [| q l IH]; intros; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sumg_bound : forall P, (forall q, In q P -> Z.of_N (snd q) <= 100000) ->
  0 <= sumg P <= 100000 * Z.of_nat (List.length P).
Proof.
  induction P as [| q P IH]; intros H; simpl; [lia|].
  pose proof (IH (fun q' Hq' => H q' (or_intror Hq'))). pose proof (H q (or_introl eq_refl)). lia.
Qed.

(* add commands of energy e, and query commands *)
Definition cntE (l : list op) (e : Z) : nat :=
  List.length (filter (fun c => match c with Prelude.add e' _ => Z.of_N e' =? e | query _ => false end) l).

Definition nq (l : list op) : nat :=
  List.length (filter (fun c => match c with query _ => true | Prelude.add _ _ => false end) l).

Lemma nq_add1 : forall e g, nq [Prelude.add e g] = O.
Proof. reflexivity. Qed.

Lemma nq_query1 : forall q, nq [query q] = 1%nat.
Proof. reflexivity. Qed.

Lemma cntE_app : forall l1 l2 e, cntE (l1 ++ l2) e = (cntE l1 e + cntE l2 e)%nat.
Proof. intros. unfold cntE. rewrite filter_app, length_app. reflexivity. Qed.

Lemma nq_app : forall l1 l2, nq (l1 ++ l2) = (nq l1 + nq l2)%nat.
Proof. intros. unfold nq. rewrite filter_app, length_app. reflexivity. Qed.

Lemma filter_len_le : forall A (f : A -> bool) (l : list A), (List.length (filter f l) <= List.length l)%nat.
Proof. intros A f l. induction l as [| a l IH]; simpl; [lia|]. destruct (f a); simpl; lia. Qed.

Lemma firstn_snoc : forall (l : list op) j c, nth_error l j = Some c -> firstn (S j) l = firstn j l ++ [c].
Proof.
  induction l as [| a l IH]; intros j c H; [destruct j; discriminate|].
  destruct j as [| j]; simpl in H; [injection H as ->; reflexivity|].
  change (firstn (S (S j)) (a :: l)) with (a :: firstn (S j) l).
  rewrite (IH j c H). reflexivity.
Qed.

Lemma skipn_cons : forall (l : list op) j c, nth_error l j = Some c -> skipn j l = c :: skipn (S j) l.
Proof.
  induction l as [| a l IH]; intros j c H; [destruct j; discriminate|].
  destruct j as [| j]; simpl in H |- *; [injection H as ->; reflexivity|].
  apply IH. exact H.
Qed.

Fixpoint psum (f : Z -> nat) (n : nat) : nat :=
  match n with O => O | S m => (psum f m + f (Z.of_nat m))%nat end.

Lemma psum_mono : forall f m n, (m <= n)%nat -> (psum f m <= psum f n)%nat.
Proof.
  intros f m n H. induction H as [| n H IH]; [lia|]. simpl. lia.
Qed.

Lemma psum_ind : forall (e : N) n,
  psum (fun z => if Z.eqb (Z.of_N e) z then 1%nat else 0%nat) n = (if Z.ltb (Z.of_N e) (Z.of_nat n) then 1 else 0)%nat.
Proof.
  intros e n. induction n as [| n IH]; simpl; [destruct (Z.of_N e <? 0) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]|].
  rewrite IH. change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)). rewrite Nat2Z.inj_succ.
  destruct (Z.ltb_spec (Z.of_N e) (Z.of_nat n)); destruct (Z.eqb_spec (Z.of_N e) (Z.of_nat n));
  destruct (Z.ltb_spec (Z.of_N e) (Z.succ (Z.of_nat n))); lia.
Qed.

Lemma psum_add : forall f g n, psum (fun z => (f z + g z)%nat) n = (psum f n + psum g n)%nat.
Proof. intros f g n. induction n as [| n IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma psum_ext : forall f g n, (forall z, f z = g z) -> psum f n = psum g n.
Proof. intros f g n E. induction n as [| n IH]; simpl; [reflexivity|]. rewrite IH, E. reflexivity. Qed.

Lemma psum_cntE : forall l n, (psum (cntE l) n <= List.length l)%nat.
Proof.
  induction l as [| c l IH]; intros n.
  - simpl. rewrite (psum_ext _ (fun _ => O)) by (intros; reflexivity).
    induction n as [| n IHn]; simpl; lia.
  - destruct c as [e g | q].
    + rewrite (psum_ext _ (fun z => ((if Z.eqb (Z.of_N e) z then 1 else 0) + cntE l z)%nat))
        by (intros z; unfold cntE; simpl; destruct (Z.eqb (Z.of_N e) z); reflexivity).
      rewrite psum_add, psum_ind. simpl. pose proof (IH n). destruct (Z.of_N e <? Z.of_nat n); lia.
    + rewrite (psum_ext _ (cntE l)) by (intros z; reflexivity).
      simpl. pose proof (IH n). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Preprocessing loops                                                 *)
(* ------------------------------------------------------------------ *)

Lemma pow2_int : forall k : int, (φ k) <= 17 -> (φ (1 << k))%uint63 = 2 ^ (φ k).
Proof.
  intros k Hk. pose proof (to_Z_bounded k). rewrite shl_nov; change (φ 1) with 1; [lia|].
  pose proof (pow17 (φ k) ltac:(lia)). rewrite wB_val. lia.
Qed.

Lemma kloop_spec : forall z (k : int), 62 - (φ k) = z -> forall (m : int) H,
  1 <= (φ k) <= 17 -> (φ m) <= 100000 ->
  1 <= (φ (kloop m k H)) <= 17 /\ (φ m) < 2 ^ (φ (kloop m k H)).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros k Ez m H Hk Hm. destruct H as [Hacc]. cbn [kloop].
  destruct (bdec (andb (k <? 62) ((1 << k) <=? m))%uint63) as [Hc | Hc].
  - pose proof Hc as Hc'. apply andb_prop in Hc'. destruct Hc' as [_ H2].
    rewrite leb_spec, pow2_int in H2 by lia.
    assert ((φ k) < 17).
    { destruct (Z.lt_ge_cases (φ k) 17) as [L | L]; [exact L|].
      assert (2 ^ 17 <= 2 ^ (φ k)) by (apply Z.pow_le_mono_r; lia). lia. }
    assert (E1 : (φ (k + 1))%uint63 = (φ k) + 1) by (rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia).
    apply (IH (62 - (φ (k + 1))%uint63)); [unfold Zwf; lia | reflexivity | lia | exact Hm].
  - apply Bool.andb_false_iff in Hc. split; [exact Hk|].
    destruct Hc as [Hc | Hc]; rewrite <- Bool.not_true_iff_false in Hc;
      [rewrite ltb_spec in Hc; change (φ 62) with 62 in Hc; lia |].
    rewrite leb_spec, pow2_int in Hc by lia. lia.
Qed.

Lemma stab_spec : forall z (K k : int), gap (K + 1) k = z -> forall (t : array int) H,
  1 <= (φ K) <= 17 -> 1 <= (φ k) <= (φ K) + 1 -> (φ (PArray.length t)) = (φ K) + 1 ->
  (forall h : int, 1 <= (φ h) < (φ k) -> (φ (t.[h])) = sz (φ h)) ->
  (φ (PArray.length (stab t K k H))) = (φ K) + 1 /\
  (forall h : int, 1 <= (φ h) <= (φ K) -> (φ ((stab t K k H).[h])) = sz (φ h)).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros K k Ez t H HK Hk Hl Ht. destruct H as [Hacc]. cbn [stab].
  assert (EK : (φ (K + 1))%uint63 = (φ K) + 1) by (rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia).
  destruct (bdec (k <? K + 1)%uint63) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec, EK in Hc'.
    set (s := (if k <=? 1 then 2 else 2 + t.[kh k] + (t.[kl k] << kh k))%uint63).
    assert (Es : (φ s) = sz (φ k)).
    { unfold s. destruct (k <=? 1)%uint63 eqn:E.
      - rewrite leb_spec in E. change (φ 1) with 1 in E. replace (φ k) with 1 by lia. reflexivity.
      - rewrite <- Bool.not_true_iff_false, leb_spec in E. change (φ 1) with 1 in E.
        destruct (hilo (φ k) ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6).
        rewrite sz_node by lia.
        assert (Th : (φ (t.[kh k])) = sz (hi (φ k))) by (rewrite Ht; rewrite kh_spec; [reflexivity | lia]).
        assert (Tl : (φ (t.[kl k])) = sz (lo (φ k))) by (rewrite Ht; rewrite kl_spec; [reflexivity | lia]).
        pose proof (sz_bound (φ k) ltac:(lia)). rewrite (sz_node (φ k)) in H by lia.
        pose proof (sz_ge2 (hi (φ k))). pose proof (sz_ge2 (lo (φ k))).
        pose proof (pow17 (hi (φ k)) ltac:(lia)).
        assert (Esh : (φ (t.[kl k] << kh k))%uint63 = sz (lo (φ k)) * 2 ^ hi (φ k)).
        { rewrite shl_nov; rewrite Tl, kh_spec; [reflexivity|]. rewrite wB_val. lia. }
        rewrite add_nov; rewrite ?add_nov; rewrite ?Th, ?Esh; change (φ 2) with 2; rewrite ?wB_val; lia. }
    assert (E1 : (φ (k + 1))%uint63 = (φ k) + 1) by (rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia).
    apply (IH (gap (K + 1) (k + 1))); [rewrite <- Ez; unfold Zwf, gap; rewrite EK, E1; lia | reflexivity | exact HK | lia | |].
    + rewrite alength_set. exact Hl.
    + intros h Hh. destruct (Z.eq_dec (φ h) (φ k)) as [E | E].
      * assert (h = k) by (apply to_Z_inj; exact E). subst h.
        rewrite aget_set_same by lia. exact Es.
      * rewrite aget_set_other by lia. apply Ht. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, EK in Hc.
    split; [exact Hl|]. intros h Hh. apply Ht. lia.
Qed.

Section Prep.

Variable cs : list op.
Variable x : array command.
Hypothesis Hrep : repr x cs.
Hypothesis Hval : valid_input cs.

Lemma len_x : (φ (PArray.length x)) = Z.of_nat (List.length cs).
Proof. destruct Hrep as [Hl _]. symmetry. exact Hl. Qed.

Lemma len_bound : 1 <= Z.of_nat (List.length cs) <= 200000.
Proof. destruct Hval as [Hn _ _ _]. unfold len in Hn. lia. Qed.

Lemma get_cmd : forall j : int, (φ j) < (φ (PArray.length x)) ->
  nth_error cs (Z.to_nat (φ j)) =
  Some (match x.[j] with
        | Prelude.Add e g => Prelude.add (Z.to_N (φ e)) (Z.to_N (φ g))
        | Query q => query (Z.to_N (φ q))
        end).
Proof.
  intros j Hj. rewrite len_x in Hj. destruct Hrep as [_ Hc].
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as (m & Hm & Hr).
  rewrite Hm. f_equal.
  assert (Ej : of_Z (Z.of_nat (Z.to_nat (φ j))) = j).
  { apply to_Z_inj. rewrite of_Z_spec. rewrite Z2Nat.id by (pose proof (to_Z_bounded j); lia).
    apply Z.mod_small. apply to_Z_bounded. }
  change (repr_command (x.[of_Z (Z.of_nat (Z.to_nat (φ j)))]) m) in Hr. rewrite Ej in Hr.
  destruct (x.[j]) as [e g | q]; destruct m as [e' g' | q']; simpl in Hr; try contradiction.
  - destruct Hr as [A B]. unfold repr, repr_uint in A, B. rewrite A, B. reflexivity.
  - unfold repr, repr_uint in Hr. rewrite Hr. reflexivity.
Qed.

Lemma add_bounds : forall e g, In (Prelude.add e g) cs -> (1 <= e <= 100000 /\ 1 <= g <= 100000)%N.
Proof.
  intros e g H. destruct Hval as [_ He Hg _].
  assert (Hin : In (e, g) (adds cs)).
  { unfold adds. apply in_flat_map. exists (Prelude.add e g). split; [exact H | left; reflexivity]. }
  rewrite Forall_forall in He, Hg. pose proof (He _ Hin). pose proof (Hg _ Hin). simpl in *. lia.
Qed.

Lemma query_bounds : forall q, In (query q) cs -> (1 <= q <= 100000)%N.
Proof.
  intros q H. destruct Hval as [_ _ _ Hx].
  assert (Hin : In q (queries cs)).
  { unfold queries. apply in_flat_map. exists (query q). split; [exact H | left; reflexivity]. }
  rewrite Forall_forall in Hx. pose proof (Hx _ Hin). lia.
Qed.

Lemma firstn_len : firstn (Z.to_nat (φ (PArray.length x))) cs = cs.
Proof. apply firstn_all2. rewrite len_x. lia. Qed.

Lemma step_j : forall j : int, (φ j) < (φ (PArray.length x)) -> (φ (j + 1))%uint63 = (φ j) + 1.
Proof. intros j Hj. pose proof (alength_bound_any _ x). rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia. Qed.

Lemma firstn_step : forall j : int, (φ j) < (φ (PArray.length x)) ->
  firstn (Z.to_nat ((φ (j + 1))%uint63)) cs = firstn (Z.to_nat (φ j)) cs ++
    [match x.[j] with
     | Prelude.Add e g => Prelude.add (Z.to_N (φ e)) (Z.to_N (φ g))
     | Query q => query (Z.to_N (φ q))
     end].
Proof.
  intros j Hj. rewrite step_j by exact Hj. pose proof (to_Z_bounded j).
  replace (Z.to_nat ((φ j) + 1)) with (S (Z.to_nat (φ j))) by lia.
  apply firstn_snoc. apply get_cmd. exact Hj.
Qed.

Lemma scan_spec : forall z (j : int), gap (PArray.length x) j = z -> forall (m q : int) H,
  (φ j) <= (φ (PArray.length x)) -> 1 <= (φ m) <= 100000 ->
  (forall e g, In (Prelude.add e g) (firstn (Z.to_nat (φ j)) cs) -> Z.of_N e <= (φ m)) ->
  (φ q) = Z.of_nat (nq (firstn (Z.to_nat (φ j)) cs)) ->
  1 <= (φ (fst (scan x (PArray.length x) j m q H))) <= 100000 /\
  (forall e g, In (Prelude.add e g) cs -> Z.of_N e <= (φ (fst (scan x (PArray.length x) j m q H)))) /\
  (φ (snd (scan x (PArray.length x) j m q H))) = Z.of_nat (nq cs).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros j Ez m q H Hj Hm Hme Hq. destruct H as [Hacc]. cbn [scan].
  pose proof len_bound as LB. pose proof len_x as LX.
  destruct (bdec (j <? PArray.length x)%uint63) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'.
    pose proof (firstn_step j Hc') as Ef. pose proof (step_j j Hc') as E1.
    pose proof (get_cmd j Hc') as Eg.
    destruct (x.[j]) as [e g | qq].
    + pose proof (add_bounds _ _ (nth_error_In _ _ Eg)) as [Be _].
      pose proof (to_Z_bounded e).
      apply (IH (gap (PArray.length x) (j + 1))); [unfold Zwf, gap in *; lia | reflexivity | lia | | |].
      * rewrite ltb_Z. destruct (Z.ltb_spec (φ m) (φ e)); lia.
      * intros e' g' Hin. rewrite Ef in Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | []]].
        -- pose proof (Hme _ _ Hin). rewrite ltb_Z. destruct (Z.ltb_spec (φ m) (φ e)); lia.
        -- injection Hin as Ee Eg'. subst e'. rewrite ltb_Z. destruct (Z.ltb_spec (φ m) (φ e)); lia.
      * rewrite Ef, nq_app, nq_add1. lia.
    + apply (IH (gap (PArray.length x) (j + 1))); [unfold Zwf, gap in *; lia | reflexivity | lia | exact Hm | |].
      * intros e' g' Hin. rewrite Ef in Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | []]];
          [exact (Hme _ _ Hin) | discriminate].
      * rewrite Ef, nq_app, nq_query1.
        assert ((φ q) < 200000).
        { rewrite Hq. pose proof (firstn_le_length (Z.to_nat (φ j)) cs).
          assert (nq (firstn (Z.to_nat (φ j)) cs) <= List.length (firstn (Z.to_nat (φ j)) cs))%nat
            by (unfold nq; apply filter_len_le).
          lia. }
        rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
    assert (Ej : Z.to_nat (φ j) = Z.to_nat (φ (PArray.length x))) by lia.
    rewrite Ej, firstn_len in Hme, Hq. simpl. split; [exact Hm|]. split; [exact Hme | exact Hq].
Qed.

Lemma cnt_step : forall l c e, cntE (l ++ [c]) e =
  (cntE l e + match c with Prelude.add e' _ => if Z.eqb (Z.of_N e') e then 1 else 0 | query _ => 0 end)%nat.
Proof.
  intros l c e. rewrite cntE_app. destruct c as [e' g' | q']; unfold cntE; simpl;
    [destruct (Z.of_N e' =? e)|]; simpl; lia.
Qed.

Lemma cntE_le : forall l e, (cntE l e <= List.length l)%nat.
Proof. intros. unfold cntE. apply filter_len_le. Qed.

Lemma cntloop_spec : forall z (j : int), gap (PArray.length x) j = z ->
  forall (U : int) (c : array int) H,
  (φ j) <= (φ (PArray.length x)) -> (φ (PArray.length c)) = (φ U) ->
  (forall e g, In (Prelude.add e g) cs -> Z.of_N e < (φ U)) ->
  (forall e : int, (φ e) < (φ U) -> (φ (c.[e])) = Z.of_nat (cntE (firstn (Z.to_nat (φ j)) cs) (φ e))) ->
  (φ (PArray.length (cntloop x (PArray.length x) j c H))) = (φ U) /\
  (forall e : int, (φ e) < (φ U) ->
     (φ ((cntloop x (PArray.length x) j c H).[e])) = Z.of_nat (cntE cs (φ e))).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros j Ez U c H Hj Hl HU Hc. destruct H as [Hacc]. cbn [cntloop].
  pose proof len_bound as LB. pose proof len_x as LX.
  destruct (bdec (j <? PArray.length x)%uint63) as [Hb | Hb].
  - pose proof Hb as Hb'. rewrite ltb_spec in Hb'.
    pose proof (firstn_step j Hb') as Ef. pose proof (step_j j Hb') as E1.
    pose proof (get_cmd j Hb') as Eg.
    destruct (x.[j]) as [e g | qq].
    + pose proof (HU _ _ (nth_error_In _ _ Eg)) as HeU. pose proof (to_Z_bounded e).
      apply (IH (gap (PArray.length x) (j + 1))); [unfold Zwf, gap in *; lia | reflexivity | lia | | exact HU |].
      * rewrite alength_set. exact Hl.
      * intros e' He'. rewrite Ef, cnt_step.
        pose proof (cntE_le (firstn (Z.to_nat (φ j)) cs) (φ e')).
        pose proof (firstn_le_length (Z.to_nat (φ j)) cs).
        destruct (Z.eq_dec (φ e') (φ e)) as [E | E].
        -- assert (e' = e) by (apply to_Z_inj; exact E). subst e'.
           rewrite aget_set_same by lia. rewrite Z2N.id by lia. rewrite Z.eqb_refl.
           rewrite add_nov; rewrite Hc by lia; change (φ 1) with 1; rewrite ?wB_val; lia.
        -- rewrite aget_set_other by lia. rewrite Z2N.id by lia.
           destruct (Z.eqb_spec (φ e) (φ e')); [lia|]. rewrite Hc by lia. lia.
    + apply (IH (gap (PArray.length x) (j + 1))); [unfold Zwf, gap in *; lia | reflexivity | lia | exact Hl | exact HU |].
      intros e' He'. rewrite Ef, cnt_step, Hc by lia. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hb.
    assert (Ej : Z.to_nat (φ j) = Z.to_nat (φ (PArray.length x))) by lia.
    rewrite Ej, firstn_len in Hc. split; [exact Hl | exact Hc].
Qed.

Lemma pref_spec : forall z (U e : int), gap U e = z -> forall (c : array int) (acc : int) H,
  (φ U) <= 4194303 -> (φ e) <= (φ U) -> (φ (PArray.length c)) = (φ U) ->
  (forall e' : int, (φ e') < (φ e) -> (φ (c.[e'])) = Z.of_nat (psum (cntE cs) (Z.to_nat (φ e')))) ->
  (forall e' : int, (φ e) <= (φ e') < (φ U) -> (φ (c.[e'])) = Z.of_nat (cntE cs (φ e'))) ->
  (φ acc) = Z.of_nat (psum (cntE cs) (Z.to_nat (φ e))) ->
  (φ (PArray.length (pref c U e acc H))) = (φ U) /\
  (forall e' : int, (φ e') < (φ U) ->
     (φ ((pref c U e acc H).[e'])) = Z.of_nat (psum (cntE cs) (Z.to_nat (φ e')))).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros U e Ez c acc H HU He Hl Hlo Hhi Hacc0. destruct H as [Hacc]. cbn [pref].
  pose proof len_bound as LB.
  destruct (bdec (e <? U)%uint63) as [Hb | Hb].
  - pose proof Hb as Hb'. rewrite ltb_spec in Hb'.
    assert (E1 : (φ (e + 1))%uint63 = (φ e) + 1) by (rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia).
    pose proof (to_Z_bounded e).
    assert (Ps : psum (cntE cs) (Z.to_nat ((φ e) + 1)) = (psum (cntE cs) (Z.to_nat (φ e)) + cntE cs (φ e))%nat).
    { replace (Z.to_nat ((φ e) + 1)) with (S (Z.to_nat (φ e))) by lia. simpl. rewrite Z2Nat.id by lia. reflexivity. }
    pose proof (psum_cntE cs (Z.to_nat ((φ e) + 1))) as PB.
    apply (IH (gap U (e + 1))); [unfold Zwf, gap in *; lia | reflexivity | exact HU | lia | | | |].
    + rewrite alength_set. exact Hl.
    + intros e' He'. rewrite E1 in He'. destruct (Z.eq_dec (φ e') (φ e)) as [E | E].
      * assert (e' = e) by (apply to_Z_inj; exact E). subst e'. rewrite aget_set_same by lia. exact Hacc0.
      * rewrite aget_set_other by lia. apply Hlo. lia.
    + intros e' He'. rewrite E1 in He'. rewrite aget_set_other by lia. apply Hhi. lia.
    + rewrite E1, Ps. rewrite add_nov; rewrite Hacc0, Hhi by lia; [lia|]. rewrite wB_val. rewrite Ps in PB. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hb.
    split; [exact Hl|]. intros e' He'. apply Hlo. lia.
Qed.

End Prep.

(* ------------------------------------------------------------------ *)
(* The state of a run                                                  *)
(* ------------------------------------------------------------------ *)

Lemma hg_frame : forall gd gd' s n, (φ s) + n < wB ->
  (forall q : int, (φ s) <= (φ q) < (φ s) + n -> gd'.[q] = gd.[q]) ->
  forall j, 0 <= j < n -> hg gd' s j = hg gd s j.
Proof.
  intros gd gd' s n Hn Hf j Hj. unfold hg. rewrite Hf; [reflexivity|].
  rewrite pos_int; lia.
Qed.

Lemma hheap_frame : forall gd gd' s n, (φ s) + n < wB ->
  (forall q : int, (φ s) <= (φ q) < (φ s) + n -> gd'.[q] = gd.[q]) ->
  hheap gd s n -> hheap gd' s n.
Proof.
  intros gd gd' s n Hn Hf H j Hj. rewrite !(hg_frame gd gd' s n Hn Hf) by (Z.to_euclidean_division_equations; lia).
  apply H. exact Hj.
Qed.

Lemma hcnt_frame : forall gd gd' s n, (φ s) + n < wB -> 0 <= n ->
  (forall q : int, (φ s) <= (φ q) < (φ s) + n -> gd'.[q] = gd.[q]) ->
  forall g, hcnt gd' s n g = hcnt gd s n g.
Proof.
  intros gd gd' s n Hn Hn0 Hf g. unfold hcnt. apply cntf_ext.
  intros j Hj. apply (hg_frame gd gd' s n Hn Hf). lia.
Qed.

Lemma hg_0 : forall gd s, hg gd s 0 = (φ (gd.[s])).
Proof.
  intros gd s. unfold hg. f_equal. f_equal. apply to_Z_inj.
  pose proof (to_Z_bounded s). rewrite add_spec. change (φ (of_Z 0)) with 0. rewrite Z.add_0_r.
  apply Z.mod_small. exact H.
Qed.

Section Run.

Variable cs : list op.
Variable x : array command.
Hypothesis Hrep : repr x cs.
Hypothesis Hval : valid_input cs.
Variables t st : array int.
Variables K U mE : int.
Hypothesis HK : 1 <= (φ K) <= 17.
Hypothesis Ht : forall h : int, 1 <= (φ h) <= (φ K) -> (φ (t.[h])) = sz (φ h).
Hypothesis HU : (φ U) = 2 ^ (φ K).
Hypothesis HmE : forall e g, In (Prelude.add e g) cs -> Z.of_N e <= (φ mE).
Hypothesis HmEU : (φ mE) < (φ U).
Hypothesis Hst : forall e : int, (φ e) < (φ U) -> (φ (st.[e])) = Z.of_nat (psum (cntE cs) (Z.to_nat (φ e))).

Lemma U_bound : 2 <= (φ U) <= 131072.
Proof.
  rewrite HU. split; [change 2 with (2 ^ 1); apply Z.pow_le_mono_r; lia | apply pow17; lia].
Qed.

Lemma seg_end : forall e : int, (φ e) < (φ U) ->
  (φ (st.[e])) + Z.of_nat (cntE cs (φ e)) <= Z.of_nat (List.length cs).
Proof.
  intros e He. rewrite Hst by exact He. pose proof (to_Z_bounded e).
  pose proof (psum_cntE cs (S (Z.to_nat (φ e)))) as P. simpl in P. rewrite Z2Nat.id in P by lia. lia.
Qed.

Lemma seg_disj : forall e1 e2 : int, (φ e1) < (φ e2) < (φ U) ->
  (φ (st.[e1])) + Z.of_nat (cntE cs (φ e1)) <= (φ (st.[e2])).
Proof.
  intros e1 e2 He. rewrite !Hst by lia. pose proof (to_Z_bounded e1).
  pose proof (psum_mono (cntE cs) (S (Z.to_nat (φ e1))) (Z.to_nat (φ e2)) ltac:(lia)) as P.
  simpl in P. rewrite Z2Nat.id in P by lia. lia.
Qed.

(* the energies of the pool *)
Definition energies (P : list (N * N)) : Z -> Prop := fun z => exists q, In q P /\ Z.of_N (fst q) = z.

Definition REL (P : list (N * N)) (v gd hz : array int) (j : nat) : Prop :=
  ok t (φ K) v 0 K (energies P) /\
  (φ (PArray.length gd)) = Z.of_nat (List.length cs) /\ (φ (PArray.length hz)) = (φ U) /\
  (forall e : int, (φ e) < (φ U) ->
     (φ (hz.[e])) <= Z.of_nat (cntE (firstn j cs) (φ e)) /\ hheap gd (st.[e]) (φ (hz.[e]))) /\
  (forall e : int, (φ e) < (φ U) -> forall g, qcount P (φ e) g = hcnt gd (st.[e]) (φ (hz.[e])) g) /\
  (forall q, In q P -> 1 <= Z.of_N (fst q) <= (φ mE) /\ 1 <= Z.of_N (snd q) <= 100000) /\
  (List.length P <= j)%nat /\ (j <= List.length cs)%nat.

Lemma cntE_firstn_le : forall j e, (cntE (firstn j cs) e <= cntE cs e)%nat.
Proof.
  intros j e. rewrite <- (firstn_skipn j cs) at 2. rewrite cntE_app. lia.
Qed.

(* a cell of the segment of energy e is not in the segment of another energy *)
Lemma seg_other : forall (e e' : int) (n n' : Z), (φ e) < (φ U) -> (φ e') < (φ U) -> (φ e) <> (φ e') ->
  0 <= n <= Z.of_nat (cntE cs (φ e)) -> 0 <= n' <= Z.of_nat (cntE cs (φ e')) ->
  forall q : int, (φ (st.[e'])) <= (φ q) < (φ (st.[e'])) + n' -> ~ ((φ (st.[e])) <= (φ q) < (φ (st.[e])) + n).
Proof.
  intros e e' n n' He He' Hne Hn Hn' q Hq.
  destruct (Z.lt_ge_cases (φ e) (φ e')) as [L | L].
  - pose proof (seg_disj e e' ltac:(lia)). lia.
  - pose proof (seg_disj e' e ltac:(lia)). lia.
Qed.

Lemma sess_spec : forall z (xq : int), (φ xq) = z -> forall H v gd hz acc P j,
  REL P v gd hz j -> (φ xq) <= 100000 -> (φ acc) + sumg P < wB ->
  exists gold P', session P (Z.to_N (φ xq)) gold P' /\
    REL P' (fst (fst (fst (sess t st K U v gd hz xq acc H))))
           (snd (fst (fst (sess t st K U v gd hz xq acc H))))
           (snd (fst (sess t st K U v gd hz xq acc H))) j /\
    (φ (snd (sess t st K U v gd hz xq acc H))) = (φ acc) + Z.of_N gold /\
    sumg P' + Z.of_N gold = sumg P.
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros xq Ez H v gd hz acc P j Hrel Hxq Hacc.
  pose proof (to_Z_bounded xq) as Bx. pose proof (to_Z_bounded acc) as Ba.
  pose proof U_bound as UB. pose proof len_bound cs Hval as LB.
  destruct Hrel as (Rok & Rgd & Rhz & Rheap & Rcnt & Rq & Rlen & Rj).
  destruct H as [Hacc0]. cbn [sess].
  set (x' := (if xq <? U then xq else U - 1)%uint63).
  assert (Ex' : (φ x') = if (φ xq) <? (φ U) then (φ xq) else (φ U) - 1).
  { unfold x'. rewrite ltb_Z. destruct ((φ xq) <? (φ U)); [reflexivity|]. rewrite sub_nov; change (φ 1) with 1; lia. }
  assert (Hx'U : (φ x') < 2 ^ (φ K)) by (rewrite <- HU, Ex'; destruct (Z.ltb_spec (φ xq) (φ U)); lia).
  pose proof (pred_spec t (φ K) HK Ht (φ K) K eq_refl (Zwf_well_founded 0 (φ K)) v 0 x' (energies P) Rok Hx'U) as Hp.
  set (e := vpred t v 0 K x' (Zwf_well_founded 0 (φ K))) in *.
  clearbody e.
  assert (EnU : forall q, In q P -> Z.of_N (fst q) < (φ U)) by (intros q Hq; pose proof (Rq q Hq); lia).
  destruct (bdec (andb (0 <? e) (e <=? xq))%uint63) as [He | He].
  - pose proof He as He'. apply andb_prop in He'. destruct He' as [He1 He2].
    rewrite ltb_spec in He1. rewrite leb_spec in He2. change (φ 0) with 0 in He1.
    destruct Hp as [(Enil & _) | (HSe & Hex' & Hemax)]; [rewrite Enil in He2; unfold nilZ in He2; lia|].
    destruct HSe as (q1 & Hq1 & Eq1).
    assert (HeU : (φ e) < (φ U)) by (rewrite <- Eq1; apply EnU; exact Hq1).
    destruct (Rheap e HeU) as (Hn & Hh).
    pose proof (cntE_firstn_le j (φ e)) as Cj. pose proof (seg_end e HeU) as Se.
    pose proof (Rcnt e HeU) as Rce.
    set (s := st.[e]) in *. set (n := hz.[e]) in *.
    pose proof (to_Z_bounded s) as Bs. pose proof (to_Z_bounded n) as Bn.
    assert (Hn1 : 1 <= (φ n)).
    { pose proof (qcount_in P q1 Hq1) as C. rewrite Eq1, Rce in C.
      unfold hcnt in C. apply cntf_pos in C. destruct C as (jj & Hjj & _). lia. }
    set (g := gd.[s]).
    assert (Hg0 : hg gd s 0 = (φ g)) by apply hg_0.
    assert (Hroot : forall jj, 0 <= jj < (φ n) -> hg gd s jj <= (φ g)) by (intros jj Hjj; rewrite <- Hg0; apply (hheap_root gd s (φ n) Hh); exact Hjj).
    assert (Hgin : (qcount P (φ e) (φ g) > 0)%nat).
    { rewrite Rce. unfold hcnt. apply (cntf_in _ _ _ 0); [lia | exact Hg0]. }
    destruct (qcount_pos P (φ e) (φ g) Hgin) as (q0 & Hq0 & Eq0e & Eq0g).
    destruct (in_split q0 P Hq0) as (l1 & l2 & EP).
    set (rest := l1 ++ l2).
    assert (Hperm : Permutation P (q0 :: rest)) by (rewrite EP; unfold rest; apply Permutation_sym, Permutation_middle).
    assert (Hrest_in : forall q, In q rest -> In q P).
    { intros q Hq. rewrite EP. unfold rest in Hq. apply in_app_or in Hq. apply in_or_app.
      destruct Hq as [Hq | Hq]; [left; exact Hq | right; right; exact Hq]. }
    assert (Hin_rest : forall q, In q P -> q = q0 \/ In q rest).
    { intros q Hq. rewrite EP in Hq. apply in_app_or in Hq. unfold rest.
      destruct Hq as [Hq | [Hq | Hq]]; [right; apply in_or_app; left; exact Hq | left; symmetry; exact Hq |
                                        right; apply in_or_app; right; exact Hq]. }
    assert (Hqc : forall e' g', qcount P e' g' =
              ((if andb (Z.of_N (fst q0) =? e')%Z (Z.of_N (snd q0) =? g')%Z then 1 else 0) + qcount rest e' g')%nat).
    { intros e' g'. rewrite EP. unfold rest. rewrite !qcount_app, qcount_cons. lia. }
    assert (Hsum : sumg P = Z.of_N (snd q0) + sumg rest).
    { rewrite EP. unfold rest. rewrite !sumg_app. simpl. lia. }
    assert (Hchosen : chosen P (Z.to_N (φ xq)) q0).
    { split; [exact Hq0|]. split; [lia|].
      intros q' Hq' Hq'x.
      assert (Hq'U : Z.of_N (fst q') < (φ U)) by (apply EnU; exact Hq').
      assert (Hle : Z.of_N (fst q') <= (φ e)).
      { apply Hemax; [exists q'; split; [exact Hq' | reflexivity] |]. rewrite Ex'.
        destruct (Z.ltb_spec (φ xq) (φ U)); lia. }
      destruct (Z.eq_dec (Z.of_N (fst q')) (φ e)) as [E | E]; [right | left; lia].
      split; [lia|].
      pose proof (qcount_in P q' Hq') as C. rewrite E, Rce in C.
      unfold hcnt in C. apply cntf_pos in C. destruct C as (jj & Hjj & Ejj).
      pose proof (Hroot jj ltac:(lia)). lia. }
    (* the new state *)
    destruct (hpop_spec gd s n Hn1 ltac:(lia) Hh) as (Lp & Fp & Hp' & Cp).
    set (gd1 := hpop gd s n) in *.
    set (hz1 := hz.[e <- (n - 1)%uint63]).
    assert (Ehz1 : forall e' : int, (φ e') < (φ U) -> (φ (hz1.[e'])) = if (φ e') =? (φ e) then (φ n) - 1 else (φ (hz.[e']))).
    { intros e' He'. unfold hz1. destruct (Z.eqb_spec (φ e') (φ e)) as [E | E].
      - assert (e' = e) by (apply to_Z_inj; exact E). subst e'. rewrite aget_set_same by lia.
        rewrite sub_nov; change (φ 1) with 1; lia.
      - rewrite aget_set_other by lia. reflexivity. }
    assert (Hcnt1 : forall e' : int, (φ e') < (φ U) -> forall g', qcount rest (φ e') g' = hcnt gd1 (st.[e']) (φ (hz1.[e'])) g').
    { intros e' He' g'. pose proof (Rcnt e' He' g') as C0. rewrite Hqc in C0. rewrite Ehz1 by exact He'.
      destruct (Z.eqb_spec (φ e') (φ e)) as [E | E].
      - assert (e' = e) by (apply to_Z_inj; exact E). subst e'. change (st.[e]) with s. clear C0.
        pose proof (Rce g') as C2. rewrite Hqc in C2. rewrite Eq0e, Eq0g, Z.eqb_refl in C2. simpl in C2.
        pose proof (Cp g') as C1. rewrite Hg0 in C1. lia.
      - assert (Eq : (Z.of_N (fst q0) =? (φ e'))%Z = false) by (apply Z.eqb_neq; lia).
        rewrite Eq in C0. simpl in C0. rewrite C0.
        destruct (Rheap e' He') as (Hn' & _). pose proof (cntE_firstn_le j (φ e')). pose proof (seg_end e' He').
        pose proof (to_Z_bounded (st.[e'])). pose proof (to_Z_bounded (hz.[e'])).
        symmetry. apply hcnt_frame; [rewrite wB_val; lia | lia |].
        intros q Hq. apply Fp. apply (seg_other e e' (φ n) (φ (hz.[e']))); lia. }
    assert (Rel1 : forall v1, ok t (φ K) v1 0 K (energies rest) -> REL rest v1 gd1 hz1 j).
    { intros v1 Hv1. split; [exact Hv1|]. split; [rewrite Lp; exact Rgd|]. split; [unfold hz1; rewrite alength_set; exact Rhz|].
      split; [|split; [exact Hcnt1 | split; [intros q Hq; apply Rq, Hrest_in, Hq | split; [|exact Rj]]]].
      - intros e' He'. rewrite Ehz1 by exact He'. destruct (Z.eqb_spec (φ e') (φ e)) as [E | E].
        + assert (e' = e) by (apply to_Z_inj; exact E). subst e'. fold s. split; [lia | exact Hp'].
        + destruct (Rheap e' He') as (Hn' & Hh'). split; [exact Hn'|].
          pose proof (cntE_firstn_le j (φ e')). pose proof (seg_end e' He').
          pose proof (to_Z_bounded (st.[e'])). pose proof (to_Z_bounded (hz.[e'])).
          apply (hheap_frame gd); [rewrite wB_val; lia | | exact Hh'].
          intros q Hq. apply Fp. apply (seg_other e e' (φ n) (φ (hz.[e']))); lia.
      - assert (List.length P = S (List.length rest)) by (rewrite EP; unfold rest; rewrite !length_app; simpl; lia).
        lia. }
    assert (Hv1 : ok t (φ K) (if (n =? 1)%uint63 then vdel t v 0 K e (Zwf_well_founded 0 (φ K)) else v) 0 K (energies rest)).
    { destruct (n =? 1)%uint63 eqn:En1.
      - rewrite eqb_spec in En1. change (φ 1) with 1 in En1. rewrite En1 in *.
        assert (HSe : energies P (φ e)) by (exists q1; split; [exact Hq1 | exact Eq1]).
        destruct (del_spec t (φ K) HK Ht (φ K) K eq_refl (Zwf_well_founded 0 (φ K)) v 0 e (energies P) Rok HSe)
          as (_ & _ & Od).
        apply (ok_ext _ _ _ _ _ _ _ Od). intros zz. split.
        + intros ((q & Hq & Ez0) & Hz). apply Hin_rest in Hq. destruct Hq as [Hq | Hq].
          * exfalso. apply Hz. rewrite <- Ez0, Hq. exact Eq0e.
          * exists q. split; [exact Hq | exact Ez0].
        + intros (q & Hq & Ez0). split; [exists q; split; [apply Hrest_in; exact Hq | exact Ez0]|].
          intros Eze. pose proof (qcount_in rest q Hq) as C. rewrite Ez0, Eze in C.
          rewrite Hcnt1 in C by exact HeU. rewrite Ehz1 in C by exact HeU. rewrite Z.eqb_refl in C.
          unfold hcnt in C. change (Z.to_nat (1 - 1)) with O in C. simpl in C. lia.
      - rewrite eqb_Z in En1. apply Z.eqb_neq in En1. change (φ 1) with 1 in En1.
        apply (ok_ext _ _ _ _ _ _ _ Rok). intros zz. split.
        + intros (q & Hq & Ez0). apply Hin_rest in Hq. destruct Hq as [Hq | Hq].
          * (* another quest of the same energy remains *)
            subst q. assert (C : (hcnt gd1 s ((φ n) - 1) (hg gd1 s 0) > 0)%nat).
            { unfold hcnt. apply (cntf_in _ _ _ 0); [lia | reflexivity]. }
            pose proof (Hcnt1 e HeU (hg gd1 s 0)) as C'. rewrite Ehz1 in C' by exact HeU.
            rewrite Z.eqb_refl in C'. fold s in C'. rewrite <- C' in C.
            destruct (qcount_pos rest _ _ C) as (q' & Hq' & Eq' & _).
            exists q'. split; [exact Hq' | lia].
          * exists q. split; [exact Hq | exact Ez0].
        + intros (q & Hq & Ez0). exists q. split; [apply Hrest_in; exact Hq | exact Ez0]. }
    set (v1 := if (n =? 1)%uint63 then vdel t v 0 K e (Zwf_well_founded 0 (φ K)) else v) in *.
    assert (Exe : (φ (xq - e))%uint63 = (φ xq) - (φ e)) by (rewrite sub_nov; lia).
    assert (Eag : (φ (acc + g))%uint63 = (φ acc) + (φ g)).
    { rewrite add_nov; [reflexivity|]. pose proof (sumg_bound rest (fun q Hq => proj2 (proj2 (Rq q (Hrest_in q Hq))))).
      lia. }
    destruct (IH ((φ (xq - e))%uint63) ltac:(unfold Zwf; lia) (xq - e)%uint63 eq_refl
                (Acc_inv (Acc_intro (φ xq) Hacc0) (dec_sub xq e He)) v1 gd1 hz1 (acc + g)%uint63 rest j
                (Rel1 v1 Hv1) ltac:(lia)
                ltac:(rewrite Eag; pose proof (sumg_bound rest (fun q Hq => proj2 (proj2 (Rq q (Hrest_in q Hq))))); lia))
      as (gold & P' & Hs & Hr & Ha & Hsg).
    exists (snd q0 + gold)%N, P'. split; [|split; [exact Hr | split]].
    + apply (session_step P (Z.to_N (φ xq)) q0 rest gold P' Hchosen Hperm).
      replace (Z.to_N (φ xq) - fst q0)%N with (Z.to_N ((φ (xq - e))%uint63)) by lia. exact Hs.
    + rewrite Ha, Eag. lia.
    + lia.
  - (* the session stops *)
    exists 0%N, P. split; [|split; [|split]].
    + apply session_stop. intros q Hq.
      destruct Hp as [(_ & Hall) | (HSe & Hex' & _)].
      * pose proof (Hall (Z.of_N (fst q)) (ex_intro _ q (conj Hq eq_refl))) as A.
        pose proof (EnU q Hq). rewrite Ex' in A. destruct (Z.ltb_spec (φ xq) (φ U)); lia.
      * exfalso. destruct HSe as (q1 & Hq1 & Eq1). pose proof (Rq q1 Hq1).
        rewrite Ex' in Hex'. apply Bool.andb_false_iff in He.
        destruct He as [He | He]; rewrite <- Bool.not_true_iff_false in He;
          [rewrite ltb_spec in He; change (φ 0) with 0 in He | rewrite leb_spec in He];
          destruct (Z.ltb_spec (φ xq) (φ U)); lia.
    + exact (conj Rok (conj Rgd (conj Rhz (conj Rheap (conj Rcnt (conj Rq (conj Rlen Rj))))))).
    + simpl. lia.
    + simpl. lia.
Qed.

Lemma cntE_firstn_mono : forall j e, (j < List.length cs)%nat ->
  (cntE (firstn j cs) e <= cntE (firstn (S j) cs) e)%nat.
Proof.
  intros j e Hj. destruct (nth_error cs j) as [c|] eqn:E.
  - rewrite (firstn_snoc cs j c E), cntE_app. lia.
  - apply nth_error_None in E. lia.
Qed.

Lemma REL_weaken : forall P v gd hz j, REL P v gd hz j -> (j < List.length cs)%nat ->
  REL P v gd hz (S j).
Proof.
  intros P v gd hz j (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8) Hj.
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split; [|split; [exact R5 | split; [exact R6 | split; lia]]].
  intros e He. destruct (R4 e He) as [A B]. split; [|exact B].
  pose proof (cntE_firstn_mono j (φ e) Hj). lia.
Qed.

Lemma mloop_spec : forall z (j : int), gap (PArray.length x) j = z ->
  forall H v gd hz out qi P,
  REL P v gd hz (Z.to_nat (φ j)) -> (φ j) <= (φ (PArray.length x)) ->
  (φ qi) = Z.of_nat (nq (firstn (Z.to_nat (φ j)) cs)) ->
  (φ (PArray.length out)) = Z.of_nat (nq cs) ->
  exists ans, runs P (skipn (Z.to_nat (φ j)) cs) ans /\
    PArray.length (mloop x t st K U (PArray.length x) j v gd hz out qi H) = PArray.length out /\
    (forall i : int, (φ i) < (φ qi) -> (mloop x t st K U (PArray.length x) j v gd hz out qi H).[i] = out.[i]) /\
    Z.of_nat (List.length ans) = Z.of_nat (nq cs) - (φ qi) /\
    (forall k : nat, (k < List.length ans)%nat -> forall i : int, (φ i) = (φ qi) + Z.of_nat k ->
       exists a, nth_error ans k = Some a /\
                 Z.to_N (φ ((mloop x t st K U (PArray.length x) j v gd hz out qi H).[i])) = a).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros j Ez H v gd hz out qi P Hrel Hj Hqi Hout.
  pose proof (len_x cs x Hrep) as LX. pose proof (len_bound cs Hval) as LB.
  pose proof U_bound as UB. pose proof (to_Z_bounded qi) as Bqi.
  destruct H as [Hacc]. cbn [mloop].
  destruct (bdec (j <? PArray.length x)%uint63) as [Hb | Hb].
  - pose proof Hb as Hb'. rewrite ltb_spec in Hb'.
    pose proof (firstn_step cs x Hrep j Hb') as Ef. pose proof (step_j x j Hb') as E1.
    pose proof (get_cmd cs x Hrep j Hb') as Eg.
    assert (Esk : skipn (Z.to_nat (φ j)) cs = _ :: skipn (S (Z.to_nat (φ j))) cs) by (apply skipn_cons; exact Eg).
    assert (Ej1 : Z.to_nat ((φ (j + 1))%uint63) = S (Z.to_nat (φ j))) by (rewrite E1; pose proof (to_Z_bounded j); lia).
    assert (Hjl : (Z.to_nat (φ j) < List.length cs)%nat) by lia.
    destruct (x.[j]) as [e g | q].
    + (* add e g *)
      pose proof (nth_error_In _ _ Eg) as Hin.
      pose proof (add_bounds cs Hval _ _ Hin) as [Be Bg]. pose proof (HmE _ _ Hin) as HeM.
      pose proof (to_Z_bounded e). pose proof (to_Z_bounded g).
      assert (HeU : (φ e) < (φ U)) by lia.
      destruct Hrel as (Rok & Rgd & Rhz & Rheap & Rcnt & Rq & Rlen & Rj).
      destruct (Rheap e HeU) as (Hn & Hh). pose proof (Rcnt e HeU) as Rce.
      pose proof (cntE_firstn_le (S (Z.to_nat (φ j))) (φ e)) as Cj.
      assert (Cs : cntE (firstn (S (Z.to_nat (φ j))) cs) (φ e) = S (cntE (firstn (Z.to_nat (φ j)) cs) (φ e))).
      { rewrite <- Ej1, Ef, cnt_step. rewrite Z2N.id by lia. rewrite Z.eqb_refl. lia. }
      pose proof (seg_end e HeU) as Se.
      set (s := st.[e]) in *. set (n := hz.[e]) in *.
      pose proof (to_Z_bounded s). pose proof (to_Z_bounded n).
      destruct (hpush_spec gd s n g ltac:(lia) Hh) as (Lh & Fh & Hh' & Ch).
      set (gd1 := hpush gd s n g) in *.
      set (hz1 := hz.[e <- (n + 1)%uint63]).
      assert (Ehz1 : forall e' : int, (φ e') < (φ U) -> (φ (hz1.[e'])) = if (φ e') =? (φ e) then (φ n) + 1 else (φ (hz.[e']))).
      { intros e' He'. unfold hz1. destruct (Z.eqb_spec (φ e') (φ e)) as [E | E].
        - assert (e' = e) by (apply to_Z_inj; exact E). subst e'. rewrite aget_set_same by lia.
          rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia.
        - rewrite aget_set_other by lia. reflexivity. }
      set (P' := (Z.to_N (φ e), Z.to_N (φ g)) :: P).
      assert (Hv1 : ok t (φ K) (if (n =? 0)%uint63 then vins t v 0 K e (Zwf_well_founded 0 (φ K)) else v) 0 K (energies P')).
      { destruct (n =? 0)%uint63 eqn:En0.
        - rewrite eqb_spec in En0.
          assert (Hne : ~ energies P (φ e)).
          { intros (q & Hq & Eq). apply (qcount_zero P (φ e)) with q; [| exact Hq | exact Eq].
            intros g'. rewrite Rce. rewrite En0. reflexivity. }
          destruct (ins_spec t (φ K) HK Ht (φ K) K eq_refl (Zwf_well_founded 0 (φ K)) v 0 e (energies P) Rok Hne
                      ltac:(rewrite <- HU; exact HeU)) as (_ & _ & Oi).
          apply (ok_ext _ _ _ _ _ _ _ Oi). intros zz. unfold P', energies. split.
          + intros [(q & Hq & Eq) | Eq].
            * exists q. split; [right; exact Hq | exact Eq].
            * exists (Z.to_N (φ e), Z.to_N (φ g)). split; [left; reflexivity | simpl; lia].
          + intros (q & [Hq | Hq] & Eq).
            * right. rewrite <- Eq, <- Hq. simpl. lia.
            * left. exists q. split; [exact Hq | exact Eq].
        - rewrite eqb_Z in En0. apply Z.eqb_neq in En0. change (φ 0) with 0 in En0.
          assert (Hye : energies P (φ e)).
          { assert (C : (hcnt gd s (φ n) (hg gd s 0) > 0)%nat) by (unfold hcnt; apply (cntf_in _ _ _ 0); [lia | reflexivity]).
            rewrite <- Rce in C. destruct (qcount_pos P _ _ C) as (q & Hq & Eq & _). exists q. split; [exact Hq | exact Eq]. }
          apply (ok_ext _ _ _ _ _ _ _ Rok). intros zz. unfold P', energies. split.
          + intros (q & Hq & Eq). exists q. split; [right; exact Hq | exact Eq].
          + intros (q & [Hq | Hq] & Eq).
            * rewrite <- Hq in Eq. simpl in Eq. destruct Hye as (q' & Hq' & Eq'). exists q'. split; [exact Hq' | lia].
            * exists q. split; [exact Hq | exact Eq]. }
      set (v1 := if (n =? 0)%uint63 then vins t v 0 K e (Zwf_well_founded 0 (φ K)) else v) in *.
      assert (Rel' : REL P' v1 gd1 hz1 (Z.to_nat ((φ (j + 1))%uint63))).
      { rewrite Ej1. split; [exact Hv1|]. split; [rewrite Lh; exact Rgd|].
        split; [unfold hz1; rewrite alength_set; exact Rhz|]. split; [|split; [|split; [|split]]].
        - intros e' He'. rewrite Ehz1 by exact He'. destruct (Z.eqb_spec (φ e') (φ e)) as [E | E].
          + assert (e' = e) by (apply to_Z_inj; exact E). subst e'. fold s. split; [lia | exact Hh'].
          + destruct (Rheap e' He') as (Hn' & Hh0). split.
            * rewrite <- Ej1, Ef, cnt_step. rewrite Z2N.id by lia.
              destruct (Z.eqb_spec (φ e) (φ e')); [lia|]. lia.
            * pose proof (cntE_firstn_le (Z.to_nat (φ j)) (φ e')). pose proof (seg_end e' He').
              pose proof (to_Z_bounded (st.[e'])). pose proof (to_Z_bounded (hz.[e'])).
              apply (hheap_frame gd); [rewrite wB_val; lia | | exact Hh0].
              intros qq Hqq. apply Fh.
              pose proof (seg_other e e' ((φ n) + 1) (φ (hz.[e'])) HeU He' ltac:(lia) ltac:(lia) ltac:(lia) qq ltac:(lia)) as So.
              change (st.[e]) with s in So. lia.
        - intros e' He' g'. unfold P'. rewrite qcount_cons. simpl fst. simpl snd.
          rewrite Ehz1 by exact He'. rewrite !Z2N.id by lia.
          destruct (Z.eqb_spec (φ e') (φ e)) as [E | E].
          + assert (e' = e) by (apply to_Z_inj; exact E). subst e'. fold s.
            rewrite Z.eqb_refl, Ch, Rce. simpl. lia.
          + destruct (Z.eqb_spec (φ e) (φ e')); [lia|]. simpl. rewrite (Rcnt e' He').
            pose proof (cntE_firstn_le (Z.to_nat (φ j)) (φ e')). pose proof (seg_end e' He').
            destruct (Rheap e' He') as (Hn' & _).
            pose proof (to_Z_bounded (st.[e'])). pose proof (to_Z_bounded (hz.[e'])).
            symmetry. apply hcnt_frame; [rewrite wB_val; lia | lia |].
            intros qq Hqq. apply Fh.
              pose proof (seg_other e e' ((φ n) + 1) (φ (hz.[e'])) HeU He' ltac:(lia) ltac:(lia) ltac:(lia) qq ltac:(lia)) as So.
              change (st.[e]) with s in So. lia.
        - intros qq [Hq | Hq]; [subst qq; simpl; lia | apply Rq; exact Hq].
        - unfold P'. simpl. lia.
        - lia. }
      destruct (IH (gap (PArray.length x) (j + 1)) ltac:(unfold Zwf, gap in *; lia) (j + 1)%uint63 eq_refl
                  (Acc_inv (Acc_intro (gap (PArray.length x) j) Hacc) (dec_step (PArray.length x) j Hb))
                  v1 gd1 hz1 out qi P' Rel' ltac:(lia)
                  ltac:(rewrite Hqi, Ef, nq_app, nq_add1; lia) Hout)
        as (ans & Hr & L & Fo & La & Co).
      exists ans. split; [|split; [exact L | split; [exact Fo | split; [exact La | exact Co]]]].
      rewrite Esk. apply runs_add. rewrite Ej1 in Hr. exact Hr.
    + (* query q *)
      pose proof (nth_error_In _ _ Eg) as Hin.
      pose proof (query_bounds cs Hval _ Hin) as Bq. pose proof (to_Z_bounded q).
      pose proof Hrel as (Rok & Rgd & Rhz & Rheap & Rcnt & Rq & Rlen & Rj).
      assert (Hs0 : (φ 0) + sumg P < wB).
      { pose proof (sumg_bound P (fun qq Hqq => proj2 (proj2 (Rq qq Hqq)))). change (φ 0) with 0. rewrite wB_val. lia. }
      destruct (sess_spec (φ q) q eq_refl (Zwf_well_founded 0 (φ q)) v gd hz 0 P (Z.to_nat (φ j)) Hrel
                  ltac:(lia) Hs0) as (gold & P2 & Hs & Hr & Ha & Hsg).
      destruct (sess t st K U v gd hz q 0 (Zwf_well_founded 0 (φ q))) as [[[v1 gd1] hz1] a].
      simpl in Hr, Ha. change (φ 0) with 0 in Ha.
      assert (Hnq : nq (firstn (S (Z.to_nat (φ j))) cs) = S (nq (firstn (Z.to_nat (φ j)) cs))).
      { rewrite <- Ej1, Ef, nq_app, nq_query1. lia. }
      assert (HnqL : (nq (firstn (S (Z.to_nat (φ j))) cs) <= nq cs)%nat).
      { rewrite <- (firstn_skipn (S (Z.to_nat (φ j))) cs) at 2. rewrite nq_app. lia. }
      assert (Eq1 : (φ (qi + 1))%uint63 = (φ qi) + 1) by (rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia).
      set (out1 := out.[qi <- a]).
      assert (Lo1 : PArray.length out1 = PArray.length out) by apply alength_set.
      destruct (IH (gap (PArray.length x) (j + 1)) ltac:(unfold Zwf, gap in *; lia) (j + 1)%uint63 eq_refl
                  (Acc_inv (Acc_intro (gap (PArray.length x) j) Hacc) (dec_step (PArray.length x) j Hb))
                  v1 gd1 hz1 out1 (qi + 1)%uint63 P2
                  ltac:(rewrite Ej1; apply REL_weaken; [exact Hr | exact Hjl]) ltac:(lia)
                  ltac:(rewrite Eq1, Ej1, Hnq, Hqi; lia) ltac:(rewrite Lo1; exact Hout))
        as (ans & Hr2 & L & Fo & La & Co).
      exists (gold :: ans). split; [|split; [rewrite L; exact Lo1 | split; [| split]]].
      * rewrite Esk. apply (runs_query P (Z.to_N (φ q)) (skipn (S (Z.to_nat (φ j))) cs) gold P2 ans Hs).
        rewrite Ej1 in Hr2. exact Hr2.
      * intros i Hi. rewrite Fo by lia. unfold out1. apply aget_set_other. lia.
      * simpl. rewrite Eq1 in La. lia.
      * intros k Hk i Hi. destruct k as [| k].
        -- exists gold. split; [reflexivity|]. rewrite Fo by lia.
           assert (i = qi) by (apply to_Z_inj; lia). subst i.
           unfold out1. rewrite aget_set_same by (rewrite Hout; lia). lia.
        -- simpl in Hk. destruct (Co k ltac:(lia) i ltac:(rewrite Eq1; lia)) as (a' & Ha' & Ea').
           exists a'. split; [exact Ha' | exact Ea'].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hb.
    assert (Ej : Z.to_nat (φ j) = List.length cs) by lia.
    exists []. rewrite Ej, skipn_all. split; [apply runs_nil|].
    split; [reflexivity|]. split; [intros; reflexivity|]. split.
    + rewrite Hqi, Ej, firstn_all. simpl. lia.
    + intros k Hk. simpl in Hk. lia.
Qed.

End Run.

(* ------------------------------------------------------------------ *)
(* The whole program                                                   *)
(* ------------------------------------------------------------------ *)

Lemma kattissquest_impl_correct : forall (cs : list op) (x : array command),
  valid_input cs -> repr x cs ->
  exists answers : list N, repr (kattissquest_impl x) answers /\ kattissquest_spec cs answers.
Proof.
  intros cs x Hval Hrep.
  pose proof (len_x cs x Hrep) as LX. pose proof (len_bound cs Hval) as LB.
  pose proof (alength_bound_any _ x) as BX.
  unfold kattissquest_impl. cbv zeta.
  destruct (scan_spec cs x Hrep Hval _ 0 eq_refl 1 0 (Zwf_well_founded 0 (gap (PArray.length x) 0))
              ltac:(change (φ 0) with 0; lia) ltac:(change (φ 1) with 1; lia)
              ltac:(intros e g Hin; simpl in Hin; destruct Hin) ltac:(reflexivity)) as (S1 & S2 & S3).
  destruct (scan x (PArray.length x) 0 1 0 (Zwf_well_founded 0 (gap (PArray.length x) 0))) as [mE Q].
  simpl in S1, S2, S3.
  (* K *)
  lazymatch goal with |- context [kloop mE 1 ?HH] =>
    destruct (kloop_spec _ 1 eq_refl mE HH ltac:(change (φ 1) with 1; lia) ltac:(lia)) as (HK & HmK);
    set (K := kloop mE 1 HH) in * end.
  clearbody K.
  (* the size table *)
  assert (EK1 : (φ (K + 1))%uint63 = (φ K) + 1) by (rewrite add_nov; change (φ 1) with 1; rewrite ?wB_val; lia).
  lazymatch goal with |- context [stab ?t0 K 1 ?HH] =>
    destruct (stab_spec _ K 1 eq_refl t0 HH HK ltac:(change (φ 1) with 1; lia)
                ltac:(rewrite alength_make by lia; exact EK1)
                ltac:(intros h Hh; change (φ 1) with 1 in Hh; lia)) as (Lt & Ht);
    set (t := stab t0 K 1 HH) in * end.
  clearbody t.
  (* the universe of energies *)
  assert (HU : (φ (1 << K))%uint63 = 2 ^ (φ K)) by (apply pow2_int; lia).
  set (U := (1 << K)%uint63) in *. clearbody U.
  pose proof (pow17 (φ K) ltac:(lia)) as P17.
  assert (HmEU : (φ mE) < (φ U)) by lia.
  assert (HeU : forall e g, In (Prelude.add e g) cs -> Z.of_N e < (φ U))
    by (intros e g Hin; pose proof (S2 e g Hin); lia).
  (* the counts, then the segment starts *)
  lazymatch goal with |- context [cntloop x (PArray.length x) 0 ?c0 ?HH] =>
    destruct (cntloop_spec cs x Hrep Hval _ 0 eq_refl U c0 HH ltac:(change (φ 0) with 0; lia)
                ltac:(rewrite alength_make by lia; reflexivity) HeU
                ltac:(intros e He; rewrite aget_make; reflexivity)) as (Lc & Hc);
    set (cnt := cntloop x (PArray.length x) 0 c0 HH) in * end.
  clearbody cnt.
  lazymatch goal with |- context [pref cnt U 0 0 ?HH] =>
    destruct (pref_spec cs Hval _ U 0 eq_refl cnt 0 HH ltac:(lia) ltac:(change (φ 0) with 0; lia) Lc
                ltac:(intros e' He'; change (φ 0) with 0 in He'; pose proof (to_Z_bounded e'); lia)
                ltac:(intros e' He'; apply Hc; lia) ltac:(reflexivity)) as (Ls & Hst);
    set (st := pref cnt U 0 0 HH) in * end.
  clearbody st.
  (* the initial state *)
  assert (Htk : (φ (t.[K])) = sz (φ K)) by (apply Ht; lia).
  pose proof (sz_bound (φ K) ltac:(lia)) as SzB.
  set (v0 := PArray.make t.[K] nil).
  assert (Lv0 : (φ (PArray.length v0)) = sz (φ K)) by (unfold v0; rewrite alength_make by lia; exact Htk).
  pose proof (ok_init t (φ K) HK Ht (φ K) K 0 v0 eq_refl ltac:(lia) ltac:(change (φ 0) with 0; lia)
                ltac:(intros p _; unfold v0; apply aget_make)) as Ov0.
  set (gd0 := PArray.make (PArray.length x) 0%uint63).
  set (hz0 := PArray.make U 0%uint63).
  set (out0 := PArray.make Q 0%uint63).
  assert (Rel0 : REL cs t st K U mE [] v0 gd0 hz0 (Z.to_nat (φ 0))).
  { change (Z.to_nat (φ 0)) with O. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply (ok_ext _ _ _ _ _ _ _ Ov0). intros zz. split; [intros [] | intros (q & [] & _)].
    - unfold gd0. rewrite alength_make by lia. exact LX.
    - unfold hz0. rewrite alength_make by lia. reflexivity.
    - intros e He. unfold hz0. rewrite aget_make. change (φ 0) with 0. split; [lia|].
      intros jj Hjj. lia.
    - intros e He g. unfold hz0. rewrite aget_make. reflexivity.
    - intros q [].
    - simpl. lia. }
  assert (NQ : (nq cs <= List.length cs)%nat) by (unfold nq; apply filter_len_le).
  assert (Lout : (φ (PArray.length out0)) = Z.of_nat (nq cs)) by (unfold out0; rewrite alength_make by lia; exact S3).
  destruct (mloop_spec cs x Hrep Hval t st K U mE HK Ht HU S2 HmEU Hst _ 0 eq_refl
              (Zwf_well_founded 0 (gap (PArray.length x) 0)) v0 gd0 hz0 out0 0 [] Rel0
              ltac:(change (φ 0) with 0; lia) ltac:(reflexivity) Lout)
    as (ans & Hr & L & Fo & La & Co).
  change (Z.to_nat (φ 0)) with O in Hr. simpl in Hr. change (φ 0) with 0 in La.
  exists ans. split.
  - split.
    + transitivity (Z.of_nat (nq cs)); [lia|]. symmetry. rewrite <- Lout. f_equal. exact L.
    + intros k Hk.
      destruct (Co k Hk (of_Z (Z.of_nat k))
                  ltac:(rewrite of_Z_spec, Z.mod_small by (rewrite wB_val; lia); reflexivity))
        as (a & Ha & Ea).
      exists a. split; [exact Ha|]. exact Ea.
  - exact Hr.
Qed.

Definition kattissquest_correct : forall (cs : list op) (x : array command),
  valid_input cs -> repr x cs ->
  exists answers : list N,
    repr (kattissquest x) answers /\ kattissquest_spec cs answers
  := kattissquest_impl_correct.
