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

From Candydistribution.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.
Elpi complexity sumbool.
Elpi complexity bdec.

Lemma dec_mod : forall a b : int,
  (b =? 0) = false -> Zwf 0 (φ (a mod b)) (φ b).
Proof.
  intros a b H.
  assert (Hb : (φ b) <> 0%Z).
  { intros E. assert (b = 0) by (apply to_Z_inj; exact E). subst b. discriminate H. }
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite mod_spec. unfold Zwf.
  pose proof (Z.mod_pos_bound (φ a) (φ b) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Extended Euclid modulo k: returns (gcd, coefficient of C mod k). *)
Fixpoint egcd_loop (k a b sa sb : int)
    (H : Acc (Zwf 0) (φ b)) {struct H} : int * int :=
  match bdec (b =? 0) with
  | left _ => (a, sa)
  | right Hb =>
      egcd_loop k b (a mod b) sb ((sa + (k - ((a / b) * sb) mod k)) mod k)
        (Acc_inv H (dec_mod a b Hb))
  end.
Elpi complexity egcd_loop.

Lemma egcd_loop_eq : forall k a b sa sb H,
  egcd_loop k a b sa sb H =
  match bdec (b =? 0) with
  | left _ => (a, sa)
  | right Hb =>
      egcd_loop k b (a mod b) sb ((sa + (k - ((a / b) * sb) mod k)) mod k)
        (Acc_inv H (dec_mod a b Hb))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Elpi complexity andb.
Elpi complexity fst.
Elpi complexity snd.
Definition candy_impl (k c : uint) : option uint :=
  let p := egcd_loop k k (c mod k) 0 (1 mod k)
             (Zwf_well_founded 0 (φ (c mod k))) in
  let g := fst p in
  let s := snd p in
  if g =? 1 then
    let b1 := if s =? 0 then k else s in
    let b2 := if andb (b1 =? 1) (c =? 1) then b1 + k else b1 in
    if b2 <=? 1000000000 then Some b2 else None
  else None.
Elpi complexity candy_impl.

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

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition candydistribution : uint -> uint -> option uint := candy_impl.
Elpi complexity candydistribution.

Definition candydistribution_correct : forall (k c : N) (x y : uint),
  valid_input k c -> repr x k -> repr y c ->
  exists o : option N, repr (candydistribution x y) o /\
                       candydistribution_spec k c o
  := candy_impl_correct.

(* Unconditional logarithmic cost: consecutive Euclidean remainders have
   a product that halves at every ordered step. Coefficient arithmetic is
   fixed-word arithmetic even outside valid_input. *)
From Stdlib Require Import ssreflect Arith.
Arguments Uint63.to_Z : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) :
  (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma eqb0_false (r : int) : (r =? 0) = false -> (φ r <> 0)%Z.
Proof.
  intros H E. assert (r = 0) by (apply to_Z_inj; exact E).
  subst. discriminate.
Qed.

Lemma mod_half (a b : Z) : (0 < b <= a)%Z -> (2 * (a mod b) <= a)%Z.
Proof.
  intros Hb. pose proof (Z.mod_pos_bound a b ltac:(lia)).
  pose proof (Z.div_mod a b ltac:(lia)).
  assert (1 <= a / b)%Z by (apply Z.div_le_lower_bound; lia).
  nia.
Qed.

Lemma halve (a b : Z) (m : nat) : (0 < b <= a)%Z ->
  (a * b < 2 ^ Z.of_nat (S m))%Z ->
  (b * (a mod b) < 2 ^ Z.of_nat m)%Z.
Proof.
  intros Hb Hlt. pose proof (mod_half a b Hb).
  pose proof (Z.mod_pos_bound a b ltac:(lia)).
  rewrite Nat2Z.inj_succ Z.pow_succ_r in Hlt; [lia|]. nia.
Qed.

Lemma egcd_loop_ord_time k kC a aC b bC sa saC sb sbC H HC n :
  (φ b <= φ a)%Z -> (φ a * φ b < 2 ^ Z.of_nat n)%Z ->
  (cost (extract (extract (extract (extract (extract
     (egcd_loop_cost stepsCM k kC) a aC) b bC) sa saC) sb sbC) H HC)
     <= 100 * n + 100)%nat.
Proof.
  unfold egcd_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G k kC a aC b bC sa saC sb sbC H HC)] =>
    assert (HG : forall m a aC b bC sa saC sb sbC H HC,
       (φ b <= φ a)%Z -> (φ a * φ b < 2 ^ Z.of_nat m)%Z ->
       (cost (G k kC a aC b bC sa saC sb sbC H HC) <= 100 * m + 100)%nat) end.
  { clear H HC. induction m as [|m IH];
      intros a' aC' b' bC' sa' saC' sb' sbC' [g] HC' Hle Hlt;
      cost_simpl;
      pose proof (bdec_time (b' =? 0) (bool_w (b' =? 0))) as HB;
      cost_destruct (bdec (b' =? 0)); cost_simpl.
    - lia.
    - exfalso. pose proof (to_Z_bounded b'). pose proof (to_Z_bounded a').
      pose proof (eqb0_false b' e).
      change (2 ^ Z.of_nat 0)%Z with 1%Z in Hlt. nia.
    - lia.
    - pose proof (to_Z_bounded b'). pose proof (to_Z_bounded a').
      pose proof (eqb0_false b' e).
      assert (Hle' : (φ (a' mod b') <= φ b')%Z).
      { rewrite Uint63.mod_spec. pose proof (Z.mod_pos_bound (φ a') (φ b')). lia. }
      assert (Hlt' : (φ b' * φ (a' mod b') < 2 ^ Z.of_nat m)%Z).
      { rewrite Uint63.mod_spec. apply halve; [lia|exact Hlt]. }
      match goal with |- context [@cost ?T (?G' k kC b' ?w1 (a' mod b')%uint63 ?w2 sb' ?w3 ?s ?w4 ?h ?e)] =>
        have HI := (IH b' w1 (a' mod b')%uint63 w2 sb' w3 s w4 h e
                    : _ -> _ -> (@cost T (G' k kC b' w1 (a' mod b')%uint63 w2 sb' w3 s w4 h e) <= _)%nat) end.
      specialize (HI Hle' Hlt'). lia. }
  match goal with |- context [@cost ?T (?G k kC a aC b bC sa saC sb sbC H HC)] =>
    exact (HG _ a aC b bC sa saC sb sbC H HC : _ -> _ ->
      (@cost T (G k kC a aC b bC sa saC sb sbC H HC) <= _)%nat) end.
Qed.

Lemma egcd_loop_time k kC a aC b bC sa saC sb sbC H HC n :
  (φ a * φ b < 2 ^ Z.of_nat n)%Z ->
  (cost (extract (extract (extract (extract (extract
     (egcd_loop_cost stepsCM k kC) a aC) b bC) sa saC) sb sbC) H HC)
     <= 100 * n + 200)%nat.
Proof.
  intros Hlt. destruct (Z.le_gt_cases (φ b) (φ a)) as [Hle|Hgt].
  { pose proof (egcd_loop_ord_time k kC a aC b bC sa saC sb sbC H HC n Hle Hlt). lia. }
  pose proof (to_Z_bounded b). pose proof (to_Z_bounded a).
  assert (Hm : φ (a mod b) = φ a).
  { rewrite Uint63.mod_spec. apply Z.mod_small. lia. }
  destruct H as [g]. unfold egcd_loop_cost. cost_simpl.
  pose proof (bdec_time (b =? 0) (bool_w (b =? 0))) as HB.
  cost_destruct (bdec (b =? 0)); cost_simpl.
  - lia.
  - assert (Hle' : (φ (a mod b) <= φ b)%Z) by lia.
    assert (Hlt' : (φ b * φ (a mod b) < 2 ^ Z.of_nat n)%Z) by (rewrite Hm; lia).
    match goal with |- context [@cost ?T (?G' k kC b ?w1 (a mod b)%uint63 ?w2 sb ?w3 ?s ?w4 ?h ?e)] =>
      have HI := (egcd_loop_ord_time k kC b w1 (a mod b)%uint63 w2 sb w3 s w4 h e n
                  : _ -> _ -> (@cost T (G' k kC b w1 (a mod b)%uint63 w2 sb w3 s w4 h e) <= _)%nat) end.
    specialize (HI Hle' Hlt'). lia.
Qed.

Lemma pow_log2_bound (X : Z) : (0 < X)%Z ->
  (X < 2 ^ Z.of_nat (S (Nat.log2 (Z.to_nat X))))%Z.
Proof.
  intros HX. pose proof (Nat.log2_spec (Z.to_nat X) ltac:(lia)) as [_ H2].
  apply Nat2Z.inj_lt in H2. rewrite Nat2Z.inj_pow Z2Nat.id in H2; [lia|]. exact H2.
Qed.

Lemma prod_bound (X Y : Z) : (0 <= X)%Z -> (0 <= Y)%Z ->
  (X * (Y mod X) < 2 ^ Z.of_nat (Nat.log2 (Z.to_nat X) + Nat.log2 (Z.to_nat Y) + 2))%Z.
Proof.
  intros HX HY.
  assert (P : (0 < 2 ^ Z.of_nat (Nat.log2 (Z.to_nat X) + Nat.log2 (Z.to_nat Y) + 2))%Z)
    by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.eq_dec X 0) as [->|HX0]; [lia|].
  destruct (Z.eq_dec Y 0) as [->|HY0]; [rewrite Z.mod_0_l; lia|].
  pose proof (pow_log2_bound X ltac:(lia)). pose proof (pow_log2_bound Y ltac:(lia)).
  pose proof (Z.mod_le Y X HY ltac:(lia)). pose proof (Z.mod_pos_bound Y X ltac:(lia)).
  replace (Nat.log2 (Z.to_nat X) + Nat.log2 (Z.to_nat Y) + 2)%nat
    with (S (Nat.log2 (Z.to_nat X)) + S (Nat.log2 (Z.to_nat Y)))%nat by lia.
  rewrite Nat2Z.inj_add Z.pow_add_r; [lia|lia|]. nia.
Qed.

Theorem candydistribution_time : exists c1 c2 : nat, forall kid_count_int bag_size_int : uint,
  (cost2 candydistribution_cost kid_count_int bag_size_int <=
    c1 * (Nat.log2 (size kid_count_int) + Nat.log2 (size bag_size_int) + 1) + c2)%nat.
Proof.
  exists 100%nat, 500%nat. intros x y.
  assert (Hp : (φ x * φ (y mod x) < 2 ^ Z.of_nat (Nat.log2 (size x) + Nat.log2 (size y) + 2))%Z).
  { rewrite Uint63.mod_spec. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
    exact (prod_bound (φ x) (φ y) ltac:(lia) ltac:(lia)). }
  revert Hp. generalize (Nat.log2 (size x) + Nat.log2 (size y))%nat. intros L Hp.
  unfold cost2, candydistribution_cost, candy_impl_cost. cost_simpl.
  match goal with |- context [@cost ?T (?G x ?kw x ?w0 (y mod x)%uint63 ?w1 0%uint63 ?w2 (1 mod x)%uint63 ?w3 ?h ?e)] =>
    have HI := (egcd_loop_time x kw x w0 (y mod x)%uint63 w1 0%uint63 w2 (1 mod x)%uint63 w3 h e (L + 2)
                : _ -> (@cost T (G x kw x w0 (y mod x)%uint63 w1 0%uint63 w2 (1 mod x)%uint63 w3 h e) <= _)%nat) end.
  specialize (HI Hp).
  match type of HI with (?C <= _)%nat =>
    let c := fresh "loop_cost" in set (c := C) in *; clearbody c end.
  cost_destruct_prep (egcd_loop x x (y mod x) 0 (1 mod x)
    (Zwf_well_founded 0 (φ (y mod x)))).
  remember (egcd_loop x x (y mod x) 0 (1 mod x)
    (Zwf_well_founded 0 (φ (y mod x)))) as p eqn:E.
  match goal with w : prod_cost _ _ _ _ _ p |- _ =>
    destruct w as [g gC s sC] end.
  cbn [fst snd] in *.
  cost_simpl.
  cost_destruct (g =? 1); cost_simpl; [|lia].
  cost_destruct (s =? 0); cost_simpl.
  all: repeat match goal with |- context [match ?b as _ return _ with true => _ | false => _ end] =>
    lazymatch b with context [match _ as _ return _ with true => _ | false => _ end] => fail | _ => idtac end;
    cost_destruct b; cbn [fst snd andb] in *; cost_simpl end.
  all: lia.
Qed.

Print Assumptions candydistribution_correct.
Print Assumptions candydistribution_time.
