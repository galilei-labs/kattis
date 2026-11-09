(* Correctness proofs for pascal_implem.v. *)
(* Implementation of pascal (pascal.spec): trial division.

   Code.  [pascal n] finds the smallest divisor p >= 2 of n by trying
   p = 2, 3, 4, ... while p <= n and p * p <= n ([sd_loop]); when no
   candidate divides n (n prime, or n = 1) the loop returns n itself.  The
   answer is n - n / p: Frane's loop counts down from n - 1 to the largest
   proper divisor n / p of n.  For n = 1 the loop returns 1 and the answer
   is 1 - 1 = 0.  All arithmetic is on Uint63 [int]; no array, no Z.

   Termination: [sd_loop] recurses structurally on an erased
   [Acc (Zwf 0) (gap n p)] proof, gap n p = n + 1 - p (the template's
   device); the test [p <? n] makes the decrease unconditional (p + 1
   cannot wrap) and, with the contract's bound, keeps p * p exact. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf.

Open Scope uint63_scope.

Unset Lia Cache.

Require Export pascal_implem.
Open Scope uint63_scope.


Lemma sd_loop_eq : forall n p H,
  sd_loop n p H =
  match bdec ((p <? n) && (p * p <=? n))%bool with
  | left Hc =>
      if n mod p =? 0 then p
      else sd_loop n (p + 1) (Acc_inv H (dec_step n p Hc))
  | right _ => n
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: Frane's loop stops at the largest proper divisor          *)
(* ------------------------------------------------------------------ *)

Lemma frane_loop_S : forall n i c,
  frane_loop n (S i) c =
  (if (n mod N.of_nat (S i) =? 0)%N then (c + 1)%N else frane_loop n i (c + 1)%N).
Proof. reflexivity. Qed.

Lemma frane_loop_div : forall n d i c,
  (1 <= d)%N -> (d <= N.of_nat i)%N -> (n mod d = 0)%N ->
  (forall j, (d < j <= N.of_nat i)%N -> (n mod j <> 0)%N) ->
  frane_loop n i c = (c + (N.of_nat i - d + 1))%N.
Proof.
  intros n d i. induction i as [| i IH]; intros c H1 Hd Hm Hj.
  - simpl in Hd. lia.
  - rewrite frane_loop_S.
    destruct (N.eqb_spec (n mod N.of_nat (S i)) 0) as [E | E].
    + assert (N.of_nat (S i) = d).
      { destruct (N.lt_ge_cases d (N.of_nat (S i))) as [Hl | Hl]; [| lia].
        exfalso. exact (Hj _ (conj Hl (N.le_refl _)) E). }
      rewrite H. lia.
    + assert (Hne : N.of_nat (S i) <> d) by (intro Heq; rewrite Heq in E; exact (E Hm)).
      rewrite IH; [lia | lia | lia | exact Hm |].
      intros j Hj'. apply Hj. lia.
Qed.

(* With p the smallest divisor >= 2 of n (p = n = 1 allowed), Frane's
   program prints n - n / p. *)
Lemma frane_output_sd : forall n p,
  (1 <= n)%N -> (1 <= p)%N -> (n mod p = 0)%N -> ((2 <= n)%N -> (2 <= p)%N) ->
  (forall k, (2 <= k < p)%N -> (n mod k <> 0)%N) ->
  frane_output n = (n - n / p)%N.
Proof.
  intros n p Hn Hp Hm H2 Hk.
  destruct (N.eq_dec n 1) as [E | E].
  { subst n. assert (p = 1%N).
    { pose proof (N.mod_le 1 p ltac:(lia)).
      destruct (N.eq_dec p 1); [assumption|].
      rewrite N.mod_small in Hm by lia. discriminate. }
    subst p. reflexivity. }
  specialize (H2 ltac:(lia)).
  pose proof (N.div_mod n p ltac:(lia)) as Hdm. rewrite Hm, N.add_0_r in Hdm.
  set (d := (n / p)%N) in *. clearbody d.
  assert (Hd1 : (1 <= d)%N) by nia.
  assert (Hdn : (d <= n - 1)%N) by nia.
  unfold frane_output.
  rewrite (frane_loop_div n d); rewrite ?N2Nat.id.
  - lia.
  - exact Hd1.
  - exact Hdn.
  - rewrite Hdm. apply N.mod_mul. lia.
  - intros j Hj Hjm.
    pose proof (N.div_mod n j ltac:(lia)) as Hjd. rewrite Hjm, N.add_0_r in Hjd.
    set (k := (n / j)%N) in *. clearbody k.
    assert (Hk2 : (2 <= k)%N).
    { destruct (N.eq_dec k 0) as [E0 | E0]; [rewrite E0 in Hjd; lia|].
      destruct (N.eq_dec k 1) as [E1 | E1]; [rewrite E1 in Hjd; lia|].
      lia. }
    assert (Hkm : (n mod k = 0)%N).
    { rewrite Hjd. apply N.mod_mul. lia. }
    destruct (N.lt_ge_cases k p) as [Hkp | Hkp].
    + exact (Hk k (conj Hk2 Hkp) Hkm).
    + assert ((j * p <= j * k)%N) by (apply N.mul_le_mono_l; lia).
      assert ((d * p < j * p)%N) by (apply N.mul_lt_mono_pos_r; lia).
      lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The loop                                                            *)
(* ------------------------------------------------------------------ *)

Lemma sq_exact : forall p n : int,
  ((φ p) < (φ n))%Z -> ((φ n) <= 1000000000)%Z -> (φ (p * p)) = ((φ p) * (φ p))%Z.
Proof.
  intros p n H1 H2. pose proof (to_Z_bounded p).
  rewrite mul_spec. apply Z.mod_small.
  assert ((φ p) * (φ p) <= 1000000000 * 1000000000)%Z by (apply Z.mul_le_mono_nonneg; lia).
  change wB with 9223372036854775808%Z. lia.
Qed.

Lemma sd_loop_spec : forall n p H,
  (1 <= (φ n) <= 1000000000)%Z -> (2 <= (φ p))%Z ->
  (forall k, (2 <= k < (φ p))%Z -> ((φ n) mod k <> 0)%Z) ->
  let r := sd_loop n p H in
  (1 <= (φ r))%Z /\ ((φ n) mod (φ r) = 0)%Z /\ ((2 <= (φ n))%Z -> (2 <= (φ r))%Z) /\
  (forall k, (2 <= k < (φ r))%Z -> ((φ n) mod k <> 0)%Z).
Proof.
  intros n p H. revert p H.
  fix IH 2. intros p H Hn Hp Hk r. subst r.
  rewrite sd_loop_eq.
  destruct (bdec ((p <? n) && (p * p <=? n))%bool) as [Hc | Hc].
  - assert (Hc' := Hc). apply andb_prop in Hc'. destruct Hc' as [Hpn Hpp].
    rewrite ltb_spec in Hpn.
    assert (Hpp' : ((φ p) * (φ p) <= (φ n))%Z).
    { rewrite leb_spec in Hpp.
      rewrite (sq_exact p n) in Hpp by lia. lia. }
    destruct (n mod p =? 0) eqn:E.
    + rewrite eqb_spec in E. assert (E' : ((φ n) mod (φ p) = 0)%Z).
      { rewrite <- mod_spec, E. reflexivity. }
      repeat split; try lia. exact Hk.
    + rewrite <- Bool.not_true_iff_false, eqb_spec in E.
      assert (E' : ((φ n) mod (φ p) <> 0)%Z).
      { intro E'. apply E. apply to_Z_inj. rewrite mod_spec. exact E'. }
      assert (Hp1 : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
      apply IH; [lia | lia |].
      intros k Hk'. destruct (Z.eq_dec k (φ p)) as [-> | Hne]; [exact E'|].
      apply Hk. lia.
  - assert (Hstop : ((φ n) < (φ p) * (φ p))%Z \/ ((φ n) <= (φ p))%Z).
    { destruct (p <? n) eqn:E1.
      - simpl in Hc. left. rewrite ltb_spec in E1.
        assert ((φ (p * p)) = ((φ p) * (φ p))%Z) by (apply (sq_exact p n); lia).
        rewrite <- Bool.not_true_iff_false, leb_spec in Hc. lia.
      - right. rewrite <- Bool.not_true_iff_false, ltb_spec in E1. lia. }
    repeat split.
    + lia.
    + apply Z_mod_same_full.
    + lia.
    + intros k Hk' Hkm.
      destruct (Z.lt_ge_cases k (φ p)) as [Hkp | Hkp]; [exact (Hk k ltac:(lia) Hkm)|].
      destruct Hstop as [Hstop | Hstop]; [| lia].
      pose proof (Z.div_mod (φ n) k ltac:(lia)) as Hd. rewrite Hkm, Z.add_0_r in Hd.
      set (m := ((φ n) / k)%Z) in *.
      assert (Hm0 : (0 <= m)%Z) by (apply Z.div_pos; lia). clearbody m.
      assert (Hm2 : (2 <= m)%Z).
      { destruct (Z.eq_dec m 0) as [E0 | E0]; [rewrite E0 in Hd; lia|].
        destruct (Z.eq_dec m 1) as [E1 | E1]; [rewrite E1 in Hd; lia|].
        lia. }
      assert (Hmm : ((φ n) mod m = 0)%Z).
      { rewrite Hd. apply Z_mod_mult. }
      destruct (Z.lt_ge_cases m (φ p)) as [Hmp | Hmp].
      * exact (Hk m ltac:(lia) Hmm).
      * assert (((φ p) * (φ p) <= k * m)%Z) by (apply Z.mul_le_mono_nonneg; lia).
        lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma pascal_impl_correct : forall (n : N) (x : uint),
  valid_input n -> repr x n ->
  exists c : N, repr (pascal_impl x) c /\ pascal_spec n c.
Proof.
  intros n x [Hv] Hx. unfold repr, repr_uint in Hx.
  pose proof (to_Z_bounded x) as Hxb.
  assert (Hxv : (1 <= (φ x) <= 1000000000)%Z).
  { subst n. lia. }
  destruct (sd_loop_spec x 2 (Zwf_well_founded 0 (gap x 2)) Hxv
              ltac:(change (φ 2) with 2%Z; lia)
              ltac:(intros k Hk; change (φ 2) with 2%Z in Hk; lia))
    as (Hr1 & Hrm & Hr2 & Hrk).
  set (r := sd_loop x 2 (Zwf_well_founded 0 (gap x 2))) in *.
  exists (frane_output n). split; [| reflexivity].
  unfold pascal_impl. fold r.
  assert (Hrx : ((φ r) <= (φ x))%Z).
  { apply Z.mod_divide in Hrm; [| lia]. apply Z.divide_pos_le; [lia | exact Hrm]. }
  assert (Hq : (0 <= (φ x) / (φ r) <= (φ x))%Z).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]. }
  assert (Hval : (φ (x - x / r)) = ((φ x) - (φ x) / (φ r))%Z).
  { rewrite sub_spec, div_spec. rewrite Z.mod_small; [reflexivity | lia]. }
  unfold repr, repr_uint. rewrite Hval.
  rewrite (frane_output_sd n (Z.to_N (φ r))).
  - subst n. apply N2Z.inj.
    rewrite Z2N.id by lia.
    rewrite N2Z.inj_sub.
    + rewrite N2Z.inj_div, !Z2N.id by lia. reflexivity.
    + apply N2Z.inj_le. rewrite N2Z.inj_div, !Z2N.id by lia. lia.
  - lia.
  - lia.
  - subst n. apply N2Z.inj. rewrite N2Z.inj_mod, !Z2N.id by lia. exact Hrm.
  - lia.
  - intros k Hk Hkm. apply (Hrk (Z.of_N k)); [lia|].
    subst n. apply (f_equal Z.of_N) in Hkm.
    rewrite N2Z.inj_mod, Z2N.id in Hkm by lia. exact Hkm.
Qed.

Definition pascal_correct : forall (n : N) (x : uint),
  valid_input n -> repr x n ->
  exists c : N, repr (pascal x) c /\ pascal_spec n c
  := pascal_impl_correct.
