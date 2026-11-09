(* Correctness proofs for derangementrotations_implem.v. *)
From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation Znumtheory Bool.
Import ListNotations.

Unset Lia Cache.

Local Notation length := List.length (only parsing).

(* ================================================================== *)
(* Generic list counting                                               *)
(* ================================================================== *)

Open Scope nat_scope.

Require Export derangementrotations_implem.
Open Scope nat_scope.


Close Scope nat_scope.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

Open Scope uint63_scope.

Lemma gcd_loop_eq : forall a b H, gcd_loop a b H =
  match bdec (b =? 0) with
  | left _ => a
  | right Hb => gcd_loop b (a mod b) (Acc_inv H (gcd_dec a b Hb))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma pow_loop_eq : forall p base e acc H, pow_loop p base e acc H =
  match bdec (e =? 0) with
  | left _ => acc
  | right He =>
      pow_loop p ((base * base) mod p) (e / 2)
        (if e mod 2 =? 0 then acc else (acc * base) mod p)
        (Acc_inv H (half_dec e He))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sum_loop_eq : forall n m p d acc H, sum_loop n m p d acc H =
  match bdec (d <? m) with
  | left Hd =>
      sum_loop n m p (d + 1)
        ((acc + ((m - d) * ((pow2mod p (gcd63 d n) + p - 2) mod p)) mod p) mod p)
        (Acc_inv H (dec_step m d Hd))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ================================================================== *)
(* Correctness of the program                                          *)
(* ================================================================== *)

Lemma gcd_loop_spec : forall z (a b : int) H, (φ b) = z ->
  (φ (gcd_loop a b H)) = Z.of_nat (Nat.gcd (Z.to_nat (φ a)) (Z.to_nat (φ b))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a b H Hz. rewrite gcd_loop_eq.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  destruct (bdec (b =? 0)) as [Hb|Hb].
  - apply Uint63.eqb_spec in Hb. subst b. change (φ 0) with 0%Z. simpl.
    rewrite Nat.gcd_0_r. lia.
  - pose proof (nz_pos b Hb).
    rewrite (IH (φ (a mod b))) with (H := Acc_inv H (gcd_dec a b Hb));
      [| rewrite <- Hz; apply gcd_dec; exact Hb | reflexivity].
    rewrite mod_spec, Z2Nat.inj_mod by lia.
    rewrite Nat.gcd_comm, Nat.Lcm0.gcd_mod, Nat.gcd_comm. reflexivity.
Qed.

Lemma gcd63_spec : forall a b : int,
  (φ (gcd63 a b)) = Z.of_nat (Nat.gcd (Z.to_nat (φ a)) (Z.to_nat (φ b))).
Proof. intros. apply (gcd_loop_spec (φ b)). reflexivity. Qed.

Lemma pow_step : forall P A Bs E : Z, (0 < P)%Z -> (0 <= E)%Z ->
  (((if (E mod 2 =? 0)%Z then A else (A * Bs) mod P) * ((Bs * Bs) mod P) ^ (E / 2)) mod P
  = (A * Bs ^ E) mod P)%Z.
Proof.
  intros P A Bs E HP HE.
  rewrite <- Z.mul_mod_idemp_r, <- Zpow_facts.Zpower_mod, Z.mul_mod_idemp_r by lia.
  assert (HE2 : (E = 2 * (E / 2) + E mod 2)%Z) by (apply Z.div_mod; lia).
  assert (Hpow : (Bs ^ E = (Bs * Bs) ^ (E / 2) * Bs ^ (E mod 2))%Z).
  { pose proof (Z.mod_pos_bound E 2 ltac:(lia)).
    assert (0 <= E / 2)%Z by (apply Z.div_pos; lia).
    rewrite HE2 at 1. rewrite Z.pow_add_r, Z.pow_mul_r, Z.pow_2_r by lia. reflexivity. }
  rewrite Hpow.
  pose proof (Z.mod_pos_bound E 2 ltac:(lia)).
  destruct (Z.eqb_spec (E mod 2) 0) as [E0|E0].
  - rewrite E0. f_equal. simpl. ring.
  - assert (E1 : (E mod 2 = 1)%Z) by lia. rewrite E1, Z.mul_mod_idemp_l by lia.
    f_equal. rewrite Z.pow_1_r. ring.
Qed.

Lemma pow_loop_spec : forall (p : int), (2 <= (φ p) < 2 ^ 31)%Z ->
  forall z (base e acc : int) H, (φ e) = z ->
  (0 <= (φ base) < (φ p))%Z -> (0 <= (φ acc) < (φ p))%Z ->
  (φ (pow_loop p base e acc H)) = (((φ acc) * (φ base) ^ (φ e)) mod (φ p))%Z.
Proof.
  intros p Hp z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros base e acc H Hz Hb Ha. rewrite pow_loop_eq.
  pose proof (to_Z_bounded e).
  destruct (bdec (e =? 0)) as [He|He].
  - apply Uint63.eqb_spec in He. subst e. change (φ 0) with 0%Z.
    rewrite Z.pow_0_r, Z.mul_1_r, Z.mod_small by lia. reflexivity.
  - pose proof (nz_pos e He).
    assert (Hbb : (φ ((base * base) mod p)) = (((φ base) * (φ base)) mod (φ p))%Z).
    { rewrite mod_spec, mul_spec, (Z.mod_small _ wB); [reflexivity|].
      change wB with (2 ^ 63)%Z. nia. }
    assert (Hacc : (φ (if e mod 2 =? 0 then acc else (acc * base) mod p))
                   = (if ((φ e) mod 2 =? 0)%Z then (φ acc) else ((φ acc) * (φ base)) mod (φ p))%Z).
    { assert (Hm : (φ (e mod 2)) = ((φ e) mod 2)%Z) by (rewrite mod_spec; reflexivity).
      destruct (e mod 2 =? 0) eqn:E1; destruct ((φ e) mod 2 =? 0)%Z eqn:E2.
      - reflexivity.
      - apply Uint63.eqb_spec in E1. rewrite E1 in Hm. change (φ 0) with 0%Z in Hm.
        apply Z.eqb_neq in E2. lia.
      - apply Z.eqb_eq in E2. rewrite <- not_true_iff_false, Uint63.eqb_spec in E1.
        exfalso. apply E1. apply to_Z_inj. rewrite Hm, E2. reflexivity.
      - rewrite mod_spec, mul_spec, (Z.mod_small _ wB); [reflexivity|].
        change wB with (2 ^ 63)%Z. nia. }
    rewrite (IH (φ (e / 2))) with (H := Acc_inv H (half_dec e He));
      [| rewrite <- Hz; apply half_dec; exact He | reflexivity | | ].
    + rewrite Hacc, Hbb, div_spec. change (φ 2) with 2%Z.
      apply pow_step; lia.
    + rewrite Hbb. pose proof (Z.mod_pos_bound ((φ base) * (φ base)) (φ p)). lia.
    + rewrite Hacc. destruct ((φ e) mod 2 =? 0)%Z; [lia|].
      pose proof (Z.mod_pos_bound ((φ acc) * (φ base)) (φ p)). lia.
Qed.

Lemma pow2mod_spec : forall p g : int, (2 < (φ p) < 2 ^ 31)%Z ->
  (φ (pow2mod p g)) = ((2 ^ (φ g)) mod (φ p))%Z.
Proof.
  intros p g Hp. unfold pow2mod.
  rewrite (pow_loop_spec p ltac:(lia) (φ g)); [| reflexivity | change (φ 2) with 2%Z; lia
                                                | change (φ 1) with 1%Z; lia].
  change (φ 1) with 1%Z. change (φ 2) with 2%Z. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma step_arith : forall P A S M X : Z, (0 < P)%Z -> A = (S mod P)%Z ->
  ((A + (M * ((X mod P + P - 2) mod P)) mod P) mod P = (S + M * (X - 2)) mod P)%Z.
Proof.
  intros P A S M X HP ->.
  rewrite Z.add_mod_idemp_l, Z.mul_mod_idemp_r, Z.add_mod_idemp_r by lia.
  rewrite (Zmod_eq_full X P) by lia.
  replace (S + M * (X - X / P * P + P - 2))%Z
    with ((S + M * (X - 2)) + (M * (1 - X / P)) * P)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Lemma sub_small : forall a b : int, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof.
  intros a b H. rewrite sub_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia.
Qed.

Lemma add_small : forall a b : int, ((φ a) + (φ b) < 2 ^ 62)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof.
  intros a b H. rewrite add_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  change wB with 9223372036854775808%Z in *. lia.
Qed.

Lemma mul_small : forall a b : int, ((φ a) * (φ b) < 2 ^ 62)%Z -> (φ (a * b)) = ((φ a) * (φ b))%Z.
Proof.
  intros a b H. rewrite mul_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  change wB with 9223372036854775808%Z in *. nia.
Qed.

(* an equation lia does not look into *)
Definition hidden_eq (a b : Z) : Prop := a = b.
Lemma hide_eq : forall a b : Z, a = b -> hidden_eq a b.
Proof. intros a b H. exact H. Qed.

Lemma sum_loop_spec : forall (nn : nat) (n m p : int),
  (φ n) = Z.of_nat nn -> (3 <= nn)%nat -> ((φ n) <= 1000000)%Z -> (φ m) = ((φ n) - 1)%Z ->
  (100000000 <= (φ p) <= 1000000007)%Z ->
  forall z (d acc : int) H, gap m d = z -> (1 <= (φ d) <= (φ m))%Z ->
  (φ acc) = (Z.of_nat (list_sum (map (term nn) (seq 1 (Z.to_nat (φ d) - 1)))) mod (φ p))%Z ->
  (φ (sum_loop n m p d acc H))
  = (Z.of_nat (list_sum (map (term nn) (seq 1 (nn - 2)))) mod (φ p))%Z.
Proof.
  intros nn n m p Hn Hnn Hn6 Hm Hp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d acc H Hz Hd Hacc. rewrite sum_loop_eq.
  assert (Hacc_b : (0 <= (φ acc) < (φ p))%Z) by (rewrite Hacc; apply Z.mod_pos_bound; lia).
  apply hide_eq in Hacc.
  destruct (bdec (d <? m)) as [Hdm|Hdm].
  - pose proof Hdm as Hlt. rewrite ltb_spec in Hlt.
    set (k := Z.to_nat (φ d)) in *.
    assert (Hk : (φ d) = Z.of_nat k) by (unfold k; lia).
    assert (Hd1 : (φ (d + 1)) = ((φ d) + 1)%Z).
    { rewrite add_spec. change (φ 1) with 1%Z. change wB with 9223372036854775808%Z.
      pose proof (to_Z_bounded m) as Bm. apply Z.mod_small. clear - Hlt Bm Hd. lia. }
    assert (Hg : (φ (gcd63 d n)) = Z.of_nat (Nat.gcd k nn)).
    { rewrite gcd63_spec. fold k. rewrite Hn, Nat2Z.id. reflexivity. }
    set (G := Nat.gcd k nn) in *.
    assert (HG1 : (1 <= G)%nat).
    { unfold G. destruct (Nat.gcd k nn) eqn:E; [|lia]. apply Nat.gcd_eq_0 in E. lia. }
    remember (2 ^ Z.of_nat G)%Z as X eqn:EX.
    assert (Hpw : (φ (pow2mod p (gcd63 d n))) = (X mod (φ p))%Z)
      by (rewrite pow2mod_spec, Hg, EX by (clear - Hp; lia); reflexivity).
    pose proof (Z.mod_pos_bound X (φ p) ltac:(clear - Hp; lia)) as HXb.
    remember (X mod (φ p))%Z as Xm eqn:EXm.
    assert (Ht : (φ ((pow2mod p (gcd63 d n) + p - 2) mod p))
                 = ((Xm + (φ p) - 2) mod (φ p))%Z).
    { assert (E1 : (φ (pow2mod p (gcd63 d n) + p)) = (Xm + (φ p))%Z)
        by (rewrite add_small; [rewrite Hpw; reflexivity|rewrite Hpw; clear - Hp HXb; lia]).
      assert (E2 : (φ (pow2mod p (gcd63 d n) + p - 2)) = (Xm + (φ p) - 2)%Z)
        by (rewrite sub_small; [rewrite E1; reflexivity
                               |rewrite E1; change (φ 2) with 2%Z; clear - Hp HXb; lia]).
      rewrite mod_spec, E2. reflexivity. }
    remember ((Xm + (φ p) - 2) mod (φ p))%Z as T eqn:ET.
    assert (HT : (0 <= T < (φ p))%Z)
      by (rewrite ET; apply Z.mod_pos_bound; clear - Hp; lia).
    assert (Hmd : (φ (m - d)) = ((φ m) - (φ d))%Z) by (apply sub_small; clear - Hlt; lia).
    assert (Hprod : (φ (((m - d) * ((pow2mod p (gcd63 d n) + p - 2) mod p)) mod p))
                    = ((((φ m) - (φ d)) * T) mod (φ p))%Z).
    { rewrite mod_spec, mul_small; [rewrite Hmd, Ht; reflexivity|].
      rewrite ?Hmd, ?Ht. clear - Hd Hlt Hm Hn6 HT Hp. nia. }
    pose proof (Z.mod_pos_bound (((φ m) - (φ d)) * T) (φ p) ltac:(clear - Hp; lia)) as HPb.
    remember ((((φ m) - (φ d)) * T) mod (φ p))%Z as P eqn:EP.
    assert (Hnew : (φ ((acc + ((m - d) * ((pow2mod p (gcd63 d n) + p - 2) mod p)) mod p) mod p))
                   = (((φ acc) + P) mod (φ p))%Z).
    { rewrite mod_spec, add_small; [rewrite Hprod; reflexivity|].
      rewrite ?Hprod. clear - Hacc_b HPb Hp. lia. }
    rewrite (IH (gap m (d + 1))) with (H := Acc_inv H (dec_step m d Hdm));
      [reflexivity | rewrite <- Hz; apply dec_step; exact Hdm | reflexivity
      | rewrite Hd1; clear - Hd Hlt; lia | ].
    rewrite Hnew, Hd1.
    replace (Z.to_nat ((φ d) + 1) - 1)%nat with (S (k - 1)) by (clear - Hk Hd; lia).
    rewrite seq_S, map_app, list_sum_app. simpl list_sum.
    replace (S (k - 1)) with k by (clear - Hk Hd; lia).
    assert (Hterm : Z.of_nat (term nn k) = (((φ m) - (φ d)) * (X - 2))%Z).
    { unfold term, gg. fold G.
      assert (H2 : (2 <= 2 ^ G)%nat)
        by (change 2%nat with (2 ^ 1)%nat at 1; apply Nat.pow_le_mono_r; clear - HG1; lia).
      rewrite Nat2Z.inj_mul, !Nat2Z.inj_sub by (clear - Hk Hm Hn Hlt Hd H2; lia).
      rewrite Nat2Z.inj_pow.
      rewrite EX. f_equal; clear - Hk Hm Hn Hlt Hd; lia. }
    rewrite Nat.add_0_r, Nat2Z.inj_add, Hterm.
    rewrite EP, ET, EXm. apply step_arith; [clear - Hp; lia|].
    unfold hidden_eq in Hacc. rewrite Hacc. reflexivity.
  - rewrite <- not_true_iff_false, ltb_spec in Hdm.
    unfold hidden_eq in Hacc. rewrite Hacc.
    replace (Z.to_nat (φ d) - 1)%nat with (nn - 2)%nat by (clear - Hdm Hd Hm Hn Hnn; lia).
    reflexivity.
Qed.

Lemma derangement_rotations_impl_correct : forall (n p : N) (x y : uint),
  valid_input n p -> repr x n -> repr y p ->
  exists o : N, repr (derangement_rotations_impl x y) o /\
                derangement_rotations_spec n p o.
Proof.
  intros n p x y [Hvn Hvp _] Hx Hy.
  change (10 ^ 6)%N with 1000000%N in Hvn.
  change (10 ^ 8)%N with 100000000%N in Hvp.
  change (10 ^ 9 + 7)%N with 1000000007%N in Hvp.
  unfold repr, repr_uint in Hx, Hy.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
  assert (Ex : (φ x) = Z.of_N n) by lia.
  assert (Ey : (φ y) = Z.of_N p) by lia.
  set (nn := N.to_nat n).
  set (S := list_sum (map (term nn) (seq 1 (nn - 2)))).
  exists (N.of_nat S mod p)%N. split.
  - unfold repr, repr_uint, derangement_rotations_impl.
    rewrite (sum_loop_spec nn x (x - 1) y) with (z := gap (x - 1) 1).
    + fold S. rewrite Ey, <- nat_N_Z, <- N2Z.inj_mod, N2Z.id. reflexivity.
    + unfold nn. lia.
    + unfold nn. lia.
    + lia.
    + rewrite sub_spec, Z.mod_small; change (φ 1) with 1%Z; [reflexivity|lia].
    + lia.
    + reflexivity.
    + assert ((φ (x - 1)) = ((φ x) - 1)%Z)
        by (rewrite sub_spec, Z.mod_small; change (φ 1) with 1%Z; [reflexivity|lia]).
      change (φ 1) with 1%Z. lia.
    + change (φ 0) with 0%Z. change (φ 1) with 1%Z. simpl.
      rewrite Z.mod_0_l by lia. reflexivity.
  - exists (N.of_nat S). split; [|reflexivity].
    pose proof (count_correct nn ltac:(unfold nn; lia)) as C.
    unfold nn in C. rewrite N2Nat.id in C. exact C.
Qed.

Definition derangement_rotations_correct : forall (n p : N) (x y : uint),
  valid_input n p -> repr x n -> repr y p ->
  exists o : N, repr (derangement_rotations x y) o /\
                derangement_rotations_spec n p o
  := derangement_rotations_impl_correct.
