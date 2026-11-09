(* Correctness proofs for candydistribution_implem.v. *)
(* Implementation of candydistribution (candydistribution.spec): the
   modular linear equation  b * C = 1 (mod K)  solved by the extended
   Euclidean algorithm (CLRS 31.2 / 31.4).

   Code.  [egcd_loop] is the iterative extended Euclid on the pair
   (K, C mod K): the state (a, b, sa, sb) keeps  sa * C = a  and
   sb * C = b  modulo K, the Bezout coefficients being held as their
   residues in [0, K) (so every word stays unsigned and below K^2 <= 10^18:
   no overflow, no signed reading needed).  At the end a = gcd(K, C) and
   sa * C = gcd(K, C) (mod K).  If the gcd is not 1 there is no answer;
   otherwise sa is the inverse b0 of C modulo K, and the smallest fair
   number of bags is b0 (or K when b0 = 0, i.e. K = 1), plus K when that
   gives exactly one candy (b = C = 1, x would be 0).  It is returned when
   at most 10^9, otherwise "IMPOSSIBLE".  O(log K) steps, O(1) memory.

   Termination: the loop recurses on an erased [Acc (Zwf 0) (φ b)]
   proof (b decreases strictly, a mod b < b), the device of
   template/polymul1.  No nat, no Z in the code. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.

Unset Lia Cache.

Require Export candydistribution_implem.
Open Scope uint63_scope.


Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma egcd_loop_eq : forall k a b sa sb H,
  egcd_loop k a b sa sb H =
  match bdec (b =? 0) with
  | left _ => (a, sa)
  | right Hb =>
      egcd_loop k b (a mod b) sb ((sa + (k - ((a / b) * sb) mod k)) mod k)
        (Acc_inv H (dec_mod a b Hb))
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: arithmetic in Z                                          *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* One Euclid step keeps  K | s * C - r  on the new coefficient. *)
Lemma step_div : forall K C A B sa sb,
  0 < K -> 0 < B ->
  (K | sa * C - A) -> (K | sb * C - B) ->
  (K | ((sa + (K - ((A / B) * sb) mod K)) mod K) * C - A mod B).
Proof.
  intros K C A B sa sb HK HB [u Hu] [v Hv].
  rewrite (Z.mod_eq A B) by lia.
  rewrite (Z.mod_eq ((A / B) * sb) K) by lia.
  rewrite (Z.mod_eq (sa + (K - (A / B * sb - K * (A / B * sb / K)))) K) by lia.
  remember (A / B) as q.
  remember (q * sb / K) as d1.
  remember ((sa + (K - (q * sb - K * d1))) / K) as d2.
  exists (u + C - q * v + (d1 - d2) * C).
  assert (EA : A = sa * C - u * K) by lia.
  assert (EB : B = sb * C - v * K) by lia.
  rewrite EA, EB. ring.
Qed.

Lemma init_div : forall K C, 0 < K -> (K | (1 mod K) * C - C mod K).
Proof.
  intros K C HK.
  rewrite (Z.mod_eq 1 K), (Z.mod_eq C K) by lia.
  exists (C / K - (1 / K) * C). ring.
Qed.

(* The loop, on the Z readings. *)
Lemma egcd_loop_spec : forall (K C : Z) (k : int),
  (φ k) = K -> 1 <= K <= 1000000000 ->
  forall (z : Z) (a b sa sb : int) (H : Acc (Zwf 0) (φ b)),
  (φ b) = z ->
  0 <= (φ b) < (φ a) -> (φ a) <= K -> (φ sa) < K -> (φ sb) < K ->
  (K | (φ sa) * C - (φ a)) -> (K | (φ sb) * C - (φ b)) ->
  Z.gcd (φ a) (φ b) = Z.gcd K C ->
  (φ (fst (egcd_loop k a b sa sb H))) = Z.gcd K C /\
  (φ (snd (egcd_loop k a b sa sb H))) < K /\
  (K | (φ (snd (egcd_loop k a b sa sb H))) * C
       - (φ (fst (egcd_loop k a b sa sb H)))).
Proof.
  intros K C k Hk HK z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a b sa sb H Hz Hab HaK Hsa Hsb Da Db Hg.
  pose proof (to_Z_bounded a) as Ba. pose proof (to_Z_bounded b) as Bb.
  pose proof (to_Z_bounded sa) as Bsa. pose proof (to_Z_bounded sb) as Bsb.
  rewrite egcd_loop_eq.
  destruct (bdec (b =? 0)%uint63) as [E | E].
  - rewrite eqb_spec in E. subst b. simpl.
    change ((φ 0)%uint63) with 0 in *.
    rewrite Z.gcd_0_r, Z.abs_eq in Hg by lia.
    repeat split; [lia | lia | exact Da].
  - assert (Hb0 : (φ b) <> 0).
    { intros E0. assert (b = 0%uint63) by (apply to_Z_inj; exact E0).
      subst b. discriminate E. }
    assert (Hm : (φ (a mod b)) = (φ a) mod (φ b)) by apply mod_spec.
    pose proof (Z.mod_pos_bound (φ a) (φ b) ltac:(lia)) as Bm.
    assert (Hq : (φ (a / b)) = (φ a) / (φ b)) by apply div_spec.
    assert (Bq : 0 <= (φ a) / (φ b) <= (φ a)).
    { split; [apply Z.div_pos; lia|].
      rewrite <- (Z.div_1_r (φ a)) at 2. apply Z.div_le_compat_l; lia. }
    assert (Hp : (φ ((a / b) * sb)) = (φ a) / (φ b) * (φ sb)).
    { rewrite mul_spec, Hq. apply Z.mod_small.
      assert ((φ a) / (φ b) * (φ sb) <= 1000000000 * 1000000000).
      { apply Z.mul_le_mono_nonneg; lia. }
      rewrite wB_val. lia. }
    assert (Hpm : (φ (((a / b) * sb) mod k)) = ((φ a) / (φ b) * (φ sb)) mod K).
    { rewrite mod_spec, Hp, Hk. reflexivity. }
    pose proof (Z.mod_pos_bound ((φ a) / (φ b) * (φ sb)) K ltac:(lia)) as Bpm.
    assert (Hsub : (φ (k - ((a / b) * sb) mod k)) = K - ((φ a) / (φ b) * (φ sb)) mod K).
    { rewrite sub_spec, Hpm, Hk. apply Z.mod_small. rewrite wB_val. lia. }
    assert (Hadd : (φ (sa + (k - ((a / b) * sb) mod k)))
                   = (φ sa) + (K - ((φ a) / (φ b) * (φ sb)) mod K)).
    { rewrite add_spec, Hsub. apply Z.mod_small. rewrite wB_val. lia. }
    assert (Hnew : (φ ((sa + (k - ((a / b) * sb) mod k)) mod k))
                   = ((φ sa) + (K - ((φ a) / (φ b) * (φ sb)) mod K)) mod K).
    { rewrite mod_spec, Hadd, Hk. reflexivity. }
    pose proof (Z.mod_pos_bound ((φ sa) + (K - ((φ a) / (φ b) * (φ sb)) mod K)) K
                  ltac:(lia)) as Bnew.
    eapply IH.
    + rewrite <- Hz. apply dec_mod. exact E.
    + reflexivity.
    + lia.
    + lia.
    + exact Hsb.
    + lia.
    + exact Db.
    + rewrite Hnew, Hm. apply step_div; [lia | lia | exact Da | exact Db].
    + rewrite Hm, <- Hg, Z.gcd_comm, Z.gcd_mod by lia. apply Z.gcd_comm.
Qed.

(* A residue that inverts C: b * C = K * x + 1 with x >= 1 as soon as
   b * C <> 1. *)
Lemma fair_of_div : forall K C B, 1 <= K -> 1 <= C -> 1 <= B ->
  (K | B * C - 1) -> B * C <> 1 ->
  exists X, 1 <= X /\ B * C = K * X + 1.
Proof.
  intros K C B HK HC HB [x Hx] Hne.
  exists x. split; [| lia].
  destruct (Z.le_gt_cases 1 x) as [H | H]; [exact H |].
  exfalso. assert (x <= 0) by lia.
  assert (B * C >= 1) by nia. nia.
Qed.

(* Two solutions of b * C = 1 (mod K) are congruent, C being prime to K. *)
Lemma congr_sol : forall K C B B0, 1 <= K -> Z.gcd K C = 1 ->
  (K | B * C - 1) -> (K | B0 * C - 1) -> (K | B - B0).
Proof.
  intros K C B B0 HK Hg H1 H2.
  apply (Z.gauss K C (B - B0)).
  - replace (C * (B - B0)) with ((B * C - 1) - (B0 * C - 1)) by ring.
    apply Z.divide_sub_r; assumption.
  - exact Hg.
Qed.

Lemma prod_ne1 : forall a b, 1 <= a -> 1 <= b -> a <> 1 \/ b <> 1 -> a * b <> 1.
Proof. intros a b Ha Hb [H | H]; nia. Qed.

Lemma min_rep : forall K B B1 t, 1 <= K -> 1 <= B -> 1 <= B1 <= K ->
  B - B1 = t * K -> B1 <= B.
Proof.
  intros K B B1 t HK HB HB1 Ht.
  destruct (Z.le_gt_cases 0 t) as [Ht0 | Ht0]; [nia|].
  assert (t * K <= - K) by nia. lia.
Qed.

Lemma min_rep1 : forall K B t, 1 <= K -> 1 <= B -> B <> 1 ->
  B - 1 = t * K -> 1 + K <= B.
Proof.
  intros K B t HK HB Hne Ht.
  destruct (Z.le_gt_cases 1 t) as [Ht0 | Ht0]; [nia|].
  destruct (Z.le_gt_cases 0 t) as [Ht1 | Ht1].
  - assert (t = 0) by lia. subst t. lia.
  - assert (t * K <= - K) by nia. lia.
Qed.

Close Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma repr_uint_Z : forall (x : uint) (n : N), repr x n -> (φ x) = Z.of_N n.
Proof.
  intros x n H. unfold repr, repr_uint in H. subst n.
  rewrite Z2N.id; [reflexivity|]. pose proof (to_Z_bounded x). lia.
Qed.

Lemma candy_impl_correct : forall (k c : N) (x y : uint),
  valid_input k c -> repr x k -> repr y c ->
  exists o : option N, repr (candy_impl x y) o /\
                       candydistribution_spec k c o.
Proof.
  intros k c x y [Vk Vc] Rx Ry.
  apply repr_uint_Z in Rx. apply repr_uint_Z in Ry.
  set (K := Z.of_N k) in *. set (C := Z.of_N c) in *.
  assert (BK : (1 <= K <= 1000000000)%Z) by (unfold K; lia).
  assert (BC : (1 <= C <= 1000000000)%Z) by (unfold C; lia).
  (* the loop *)
  assert (Hcm : (φ (y mod x)) = (C mod K)%Z) by (rewrite mod_spec, Rx, Ry; reflexivity).
  pose proof (Z.mod_pos_bound C K ltac:(lia)) as Bcm.
  assert (H1m : (φ (1 mod x)) = (1 mod K)%Z) by (rewrite mod_spec, Rx; reflexivity).
  pose proof (Z.mod_pos_bound 1 K ltac:(lia)) as B1m.
  destruct (egcd_loop_spec K C x Rx BK _ x (y mod x) 0 (1 mod x)
              (Zwf_well_founded 0 (φ (y mod x))) eq_refl
              ltac:(lia) ltac:(lia) ltac:(change (φ 0) with 0%Z; lia) ltac:(lia)
              ltac:(rewrite Rx; change (φ 0) with 0%Z; exists (-1)%Z; ring)
              ltac:(rewrite H1m, Hcm; apply init_div; lia)
              ltac:(rewrite Rx, Hcm, Z.gcd_comm, Z.gcd_mod by lia; reflexivity))
    as (Hg & Hs & Hd).
  set (p := egcd_loop x x (y mod x) 0 (1 mod x) (Zwf_well_founded 0 (φ (y mod x)))) in *.
  unfold candy_impl. fold p.
  set (g := fst p) in *. set (s := snd p) in *.
  pose proof (to_Z_bounded s) as Bs.
  (* no solution when the gcd is not 1 *)
  assert (Hnone_g : (Z.gcd K C <> 1)%Z -> ~ exists b, fair_bags k c b).
  { intros Hne [b [Hb [xx [Hx Heq]]]]. apply Hne.
    assert (Hz : (Z.of_N b * C = K * Z.of_N xx + 1)%Z).
    { apply (f_equal Z.of_N) in Heq. rewrite N2Z.inj_add, !N2Z.inj_mul in Heq.
      exact Heq. }
    pose proof (Z.gcd_nonneg K C).
    assert (D : (Z.gcd K C | 1)%Z).
    { replace 1%Z with (Z.of_N b * C - K * Z.of_N xx)%Z by lia.
      apply Z.divide_sub_r.
      - apply Z.divide_mul_r. apply Z.gcd_divide_r.
      - apply Z.divide_mul_l. apply Z.gcd_divide_l. }
    apply Z.divide_1_r_nonneg in D; lia. }
  destruct (g =? 1) eqn:Eg.
  2:{ exists None. split; [exact I|]. simpl. apply Hnone_g.
      intros E. rewrite E in Hg. assert (g = 1) by (apply to_Z_inj; exact Hg).
      rewrite H, eqb_refl in Eg. discriminate. }
  rewrite eqb_spec in Eg. rewrite Eg in Hg, Hd. change (φ 1) with 1%Z in Hg, Hd. symmetry in Hg.
  (* b1: the representative of the inverse in [1, K] *)
  set (b1 := if s =? 0 then x else s).
  assert (Hb1 : (1 <= (φ b1) <= K)%Z /\ (K | (φ b1) * C - 1)%Z).
  { unfold b1. destruct (s =? 0) eqn:Es.
    - rewrite eqb_spec in Es. rewrite Es in Hd. change (φ 0) with 0%Z in Hd.
      rewrite Rx. split; [lia|].
      replace (K * C - 1)%Z with (K * C + (0 * C - 1))%Z by ring.
      apply Z.divide_add_r; [apply Z.divide_mul_l, Z.divide_refl | exact Hd].
    - assert ((φ s) <> 0%Z).
      { intros E0. assert (s = 0) by (apply to_Z_inj; exact E0).
        rewrite H, eqb_refl in Es. discriminate. }
      split; [lia | exact Hd]. }
  destruct Hb1 as [Bb1 Db1].
  (* b2: the smallest fair number of bags *)
  set (b2 := if andb (b1 =? 1) (y =? 1) then b1 + x else b1).
  assert (Hb2 : (1 <= (φ b2) <= 2 * K)%Z /\ (K | (φ b2) * C - 1)%Z /\
                ((φ b2) * C <> 1)%Z /\
                forall B, (1 <= B)%Z -> (K | B * C - 1)%Z -> (B * C <> 1)%Z ->
                          ((φ b2) <= B)%Z).
  { assert (Hmin1 : forall B, (1 <= B)%Z -> (K | B * C - 1)%Z -> ((φ b1) <= B)%Z).
    { intros B HB DB.
      destruct (congr_sol K C B (φ b1) ltac:(lia) Hg DB Db1) as [t Ht].
      exact (min_rep K B (φ b1) t ltac:(lia) HB Bb1 Ht). }
    unfold b2. destruct (b1 =? 1) eqn:E1; destruct (y =? 1) eqn:E2; cbn [andb].
    - rewrite eqb_spec in E1, E2. rewrite E1 in Bb1, Db1, Hmin1 |- *.
      change (φ 1) with 1%Z in *. rewrite E2 in Ry. change (φ 1) with 1%Z in Ry.
      assert (Hadd : (φ (1 + x)) = (1 + K)%Z).
      { rewrite add_spec, Rx. change (φ 1) with 1%Z. apply Z.mod_small.
        rewrite wB_val. lia. }
      rewrite Hadd, <- Ry. split; [lia|]. split.
      { exists 1%Z. ring. }
      split; [lia|].
      intros B HB DB Hne.
      destruct (congr_sol K 1 B 1 ltac:(lia) ltac:(rewrite <- Ry in Hg; exact Hg)
                  DB ltac:(exists 0%Z; ring)) as [t Ht].
      apply (min_rep1 K B t); [lia | exact HB | | exact Ht].
      intros E0. apply Hne. rewrite E0. ring.
    - (* c <> 1 *)
      assert ((φ y) <> 1%Z).
      { intros E0. assert (y = 1) by (apply to_Z_inj; exact E0).
        rewrite H, eqb_refl in E2. discriminate. }
      split; [lia|]. split; [exact Db1|].
      split; [apply prod_ne1; lia|].
      intros B HB DB _. apply Hmin1; assumption.
    - assert ((φ b1) <> 1%Z).
      { intros E0. assert (b1 = 1) by (apply to_Z_inj; exact E0).
        rewrite H, eqb_refl in E1. discriminate. }
      split; [lia|]. split; [exact Db1|].
      split; [apply prod_ne1; lia|].
      intros B HB DB _. apply Hmin1; assumption.
    - assert ((φ b1) <> 1%Z).
      { intros E0. assert (b1 = 1) by (apply to_Z_inj; exact E0).
        rewrite H, eqb_refl in E1. discriminate. }
      split; [lia|]. split; [exact Db1|].
      split; [apply prod_ne1; lia|].
      intros B HB DB _. apply Hmin1; assumption. }
  destruct Hb2 as (Bb2 & Db2 & Ne2 & Min2).
  clear Hnone_g Hs Hd Bs Bb1 Db1 Hcm Bcm H1m B1m Hg Eg.
  clearbody b2. clear b1 s g p.
  destruct (b2 <=? 1000000000) eqn:Eb.
  - rewrite leb_spec in Eb. change (φ 1000000000) with 1000000000%Z in Eb.
    exists (Some (Z.to_N (φ b2))). split; [reflexivity|].
    simpl. unfold fair_bags, max_bags.
    destruct (fair_of_div K C (φ b2) ltac:(lia) ltac:(lia) ltac:(lia) Db2 Ne2)
      as [X [HX EX]].
    change (10 ^ 9)%N with 1000000000%N.
    split; [split; apply N2Z.inj_le; rewrite Z2N.id by lia; simpl; lia|].
    exists (Z.to_N X). split; [apply N2Z.inj_le; rewrite Z2N.id by lia; simpl; lia|].
    apply N2Z.inj. rewrite N2Z.inj_add, !N2Z.inj_mul, !Z2N.id by lia.
    fold C K. lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec in Eb.
    change (φ 1000000000) with 1000000000%Z in Eb.
    exists None. split; [exact I|]. simpl.
    intros [b [Hb [xx [Hx Heq]]]]. unfold max_bags in Hb.
    change (10 ^ 9)%N with 1000000000%N in Hb.
    assert (Hb' : (1 <= Z.of_N b <= 1000000000)%Z).
    { destruct Hb as [Hb1 Hb2]. apply N2Z.inj_le in Hb1, Hb2. simpl in Hb1, Hb2. lia. }
    assert (Hx' : (1 <= Z.of_N xx)%Z) by (apply N2Z.inj_le in Hx; exact Hx).
    assert (Hz : (Z.of_N b * C = K * Z.of_N xx + 1)%Z).
    { apply (f_equal Z.of_N) in Heq. rewrite N2Z.inj_add, !N2Z.inj_mul in Heq.
      exact Heq. }
    clear Hb Hx Heq.
    assert (Z.of_N b >= (φ b2))%Z.
    { apply Z.le_ge, Min2.
      - lia.
      - exists (Z.of_N xx). lia.
      - rewrite Hz.
        pose proof (Z.mul_le_mono_nonneg 1 K 1 (Z.of_N xx)
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
    lia.
Qed.

Definition candydistribution_correct : forall (k c : N) (x y : uint),
  valid_input k c -> repr x k -> repr y c ->
  exists o : option N, repr (candydistribution x y) o /\
                       candydistribution_spec k c o
  := candy_impl_correct.
