(* Implementation of relatives (relatives.spec): Euler's phi function by
   trial division, as the steering asks.

   Code.  [relatives n] returns 0 for n <= 1 and otherwise runs the loop
   [outer p m res] from p = 2, m = n, res = n: while p * p <= m (and p < m,
   which the first test implies on every input but keeps the termination
   measure m - p honest), if p divides m then res := res / p * (p - 1) and
   every factor p is divided out of m ([divout]); then p := p + 1.  When the
   loop stops, a remaining m > 1 is a prime and res := res / m * (m - 1).
   Pure Uint63 arithmetic, no array, no Z; every value stays below n.

   Termination: both loops recurse structurally on an erased
   [Acc (Zwf 0) _] proof (measure m for [divout], m - p for [outer]), as in
   template/polymul1.

   Proof.  The math side counts with [cnt P a l], the number of
   k in [a, a + l) with P k.  With [cop r k := gcd k r =? 1], the loop
   invariant is res = #{k in [0, n) | gcd k r = 1}, for r the product of
   the primes found so far, and gcd k n = 1 <-> gcd k r = 1 /\ gcd k m = 1.
   The step for a new prime p (Lemma step_count) uses that the predicate
   is periodic with period n / p (a multiple of r), so the count over
   [0, n) is p times the count over [0, n / p), and that the k < n that
   are multiples of p and coprime to r are the p * j with j < n / p coprime
   to r.  The final count over [0, n) is the spec's count over [1, n) for
   n >= 2, and gcd k n = 1 is the statement's "relatively prime". *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf Znumtheory Bool.
Import ListNotations.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Counting (Prop side)                                                *)
(* ------------------------------------------------------------------ *)

Section Counting.
Local Open Scope Z_scope.

(* the number of k in [a, a + l) with P k *)
Fixpoint cnt (P : Z -> bool) (a : Z) (l : nat) : nat :=
  match l with
  | O => O
  | S l' => ((if P a then 1 else 0) + cnt P (a + 1) l')%nat
  end.

Lemma cnt_add : forall P l1 l2 a,
  cnt P a (l1 + l2) = (cnt P a l1 + cnt P (a + Z.of_nat l1) l2)%nat.
Proof.
  intros P l1. induction l1 as [| l1 IH]; intros l2 a; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. replace (a + 1 + Z.of_nat l1) with (a + Z.pos (Pos.of_succ_nat l1))
      by lia. lia.
Qed.

Lemma cnt_ext : forall P Q l a,
  (forall k, a <= k < a + Z.of_nat l -> P k = Q k) -> cnt P a l = cnt Q a l.
Proof.
  intros P Q l. induction l as [| l IH]; intros a H; simpl; [reflexivity|].
  rewrite (H a) by lia. rewrite (IH (a + 1)); [reflexivity|].
  intros k Hk. apply H. lia.
Qed.

Lemma cnt_zero : forall P l a,
  (forall k, a <= k < a + Z.of_nat l -> P k = false) -> cnt P a l = O.
Proof.
  intros P l. induction l as [| l IH]; intros a H; simpl; [reflexivity|].
  rewrite (H a) by lia. apply IH. intros k Hk. apply H. lia.
Qed.

Lemma cnt_all : forall P l a, (forall k, P k = true) -> cnt P a l = l.
Proof.
  intros P l. induction l as [| l IH]; intros a H; simpl; [reflexivity|].
  rewrite H, IH by exact H. reflexivity.
Qed.

Lemma cnt_le : forall P l a, (cnt P a l <= l)%nat.
Proof.
  intros P l. induction l as [| l IH]; intros a; simpl; [lia|].
  specialize (IH (a + 1)). destruct (P a); lia.
Qed.

Lemma cnt_shift : forall P d, (forall k, P (k + d) = P k) ->
  forall l a, cnt P (a + d) l = cnt P a l.
Proof.
  intros P d H l. induction l as [| l IH]; intros a; simpl; [reflexivity|].
  rewrite H. replace (a + d + 1) with (a + 1 + d) by lia. rewrite IH. reflexivity.
Qed.

Lemma periodic_mult : forall (P : Z -> bool) d, (forall k, P (k + d) = P k) ->
  forall t k, P (k + d * Z.of_nat t) = P k.
Proof.
  intros P d H t. induction t as [| t IH]; intros k.
  - rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (k + d * Z.succ (Z.of_nat t)) with ((k + d * Z.of_nat t) + d) by lia.
    rewrite H. apply IH.
Qed.

Lemma cnt_period : forall P dn, (forall k, P (k + Z.of_nat dn) = P k) ->
  forall t, cnt P 0 (dn * t) = (t * cnt P 0 dn)%nat.
Proof.
  intros P dn H t. induction t as [| t IH].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, cnt_add, IH.
    replace (0 + Z.of_nat (dn * t)) with (0 + Z.of_nat dn * Z.of_nat t)
      by (rewrite Nat2Z.inj_mul; lia).
    rewrite cnt_shift by (intros k; apply periodic_mult; exact H).
    lia.
Qed.

Lemma cnt_split : forall P Q l a,
  cnt P a l = (cnt (fun k => andb (P k) (negb (Q k))) a l
               + cnt (fun k => andb (P k) (Q k)) a l)%nat.
Proof.
  intros P Q l. induction l as [| l IH]; intros a; simpl; [reflexivity|].
  rewrite IH. destruct (P a), (Q a); simpl; lia.
Qed.

Lemma cnt_multiples : forall P p, 1 <= p -> forall m,
  cnt (fun k => andb (P k) (k mod p =? 0)) 0 (Z.to_nat p * m)
  = cnt (fun j => P (p * j)) 0 m.
Proof.
  intros P p Hp m. induction m as [| m IH].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, cnt_add, IH.
    replace (S m) with (m + 1)%nat by lia. rewrite (cnt_add _ m 1). f_equal.
    assert (Hpm : 0 + Z.of_nat (Z.to_nat p * m) = p * Z.of_nat m)
      by (rewrite Nat2Z.inj_mul, Z2Nat.id; lia).
    rewrite Hpm.
    destruct (Z.to_nat p) as [| q] eqn:Eq; [lia|].
    assert (Hq : p = Z.of_nat q + 1) by lia.
    cbn [cnt].
    rewrite cnt_zero.
    + replace (p * Z.of_nat m mod p) with 0
        by (rewrite Z.mul_comm, Z.mod_mul; lia).
      rewrite Z.eqb_refl, andb_true_r, Z.add_0_l. reflexivity.
    + intros k Hk.
      assert (Hk' : k mod p <> 0).
      { intro E.
        pose proof (Z.mod_unique k p (Z.of_nat m) (k - p * Z.of_nat m)
                      ltac:(lia) ltac:(lia)) as U.
        lia. }
      rewrite (proj2 (Z.eqb_neq _ _) Hk'). apply andb_false_r.
Qed.

(* ------------------------------------------------------------------ *)
(* Coprimality                                                         *)
(* ------------------------------------------------------------------ *)

Definition cop (r k : Z) : bool := Z.gcd k r =? 1.

Lemma coprime_mul_iff : forall k a b,
  Z.gcd k (a * b) = 1 <-> Z.gcd k a = 1 /\ Z.gcd k b = 1.
Proof.
  intros k a b. split.
  - intros H. apply Zgcd_1_rel_prime in H. apply rel_prime_sym in H.
    split; apply Zgcd_1_rel_prime; apply rel_prime_sym;
      apply (rel_prime_div (a * b) k); try exact H.
    + exists b. ring.
    + exists a. ring.
  - intros [H1 H2]. apply Zgcd_1_rel_prime. apply rel_prime_mult;
      apply Zgcd_1_rel_prime; assumption.
Qed.

Lemma coprime_prime_iff : forall p k, prime p ->
  (Z.gcd k p = 1 <-> k mod p <> 0).
Proof.
  intros p k Hp. pose proof (prime_ge_2 p Hp) as Hp2. split.
  - intros H Hm. apply Z.mod_divide in Hm; [|lia].
    assert (Hd : (p | Z.gcd k p)) by (apply Z.gcd_greatest; [exact Hm | apply Z.divide_refl]).
    rewrite H in Hd. apply Z.divide_pos_le in Hd; lia.
  - intros Hm. apply Zgcd_1_rel_prime, rel_prime_sym, prime_rel_prime; [exact Hp|].
    intros Hd. apply Hm. apply Z.mod_divide; [lia | exact Hd].
Qed.

Lemma eqb_iff : forall a b c d : Z, (a = b <-> c = d) -> (a =? b) = (c =? d).
Proof.
  intros a b c d H. destruct (a =? b) eqn:E1, (c =? d) eqn:E2; try reflexivity.
  - apply Z.eqb_eq in E1. apply Z.eqb_neq in E2. tauto.
  - apply Z.eqb_neq in E1. apply Z.eqb_eq in E2. tauto.
Qed.

Lemma cop_periodic : forall r d k, (r | d) -> cop r (k + d) = cop r k.
Proof.
  intros r d k [c ->]. unfold cop.
  rewrite (Z.gcd_comm (k + c * r)), (Z.gcd_comm k), Z.gcd_add_mult_diag_r.
  reflexivity.
Qed.

Lemma cop_rp : forall r p k, prime p ->
  cop (r * p) k = andb (cop r k) (negb (k mod p =? 0)).
Proof.
  intros r p k Hp. unfold cop.
  destruct (Z.gcd k (r * p) =? 1) eqn:E; symmetry.
  - apply Z.eqb_eq, coprime_mul_iff in E as [E1 E2].
    apply (coprime_prime_iff p k Hp) in E2.
    rewrite E1, (proj2 (Z.eqb_neq _ _) E2). reflexivity.
  - apply Z.eqb_neq in E.
    destruct (Z.gcd k r =? 1) eqn:E1; [|reflexivity].
    destruct (k mod p =? 0) eqn:E2; [reflexivity|].
    exfalso. apply E, coprime_mul_iff. split.
    + apply Z.eqb_eq. exact E1.
    + apply (coprime_prime_iff p k Hp), Z.eqb_neq. exact E2.
Qed.

Lemma cop_pj : forall r p j, Z.gcd p r = 1 -> cop r (p * j) = cop r j.
Proof.
  intros r p j H. unfold cop. apply eqb_iff.
  rewrite (Z.gcd_comm (p * j)), (Z.gcd_comm j), coprime_mul_iff, Z.gcd_comm, H.
  tauto.
Qed.

(* The step of the product formula, for a new prime p. *)
Lemma step_count : forall r p N, 1 <= r -> prime p -> Z.gcd r p = 1 ->
  (r * p | N) -> 0 <= N ->
  Z.of_nat (cnt (cop r) 0 (Z.to_nat N))
    = p * Z.of_nat (cnt (cop r) 0 (Z.to_nat (N / p)))
  /\ Z.of_nat (cnt (cop (r * p)) 0 (Z.to_nat N))
    = Z.of_nat (cnt (cop r) 0 (Z.to_nat N))
      - Z.of_nat (cnt (cop r) 0 (Z.to_nat (N / p))).
Proof.
  intros r p N Hr Hp Hrp Hd HN.
  pose proof (prime_ge_2 p Hp) as Hp2.
  destruct Hd as [c Hc].
  assert (Hdv : N / p = c * r) by (rewrite Hc, Z.mul_assoc, Z.div_mul; lia).
  rewrite Hdv.
  assert (Hd0 : 0 <= c * r) by nia.
  assert (Hlen : Z.to_nat N = (Z.to_nat (c * r) * Z.to_nat p)%nat)
    by (rewrite <- Z2Nat.inj_mul by lia; f_equal; lia).
  assert (Hper : forall k, cop r (k + Z.of_nat (Z.to_nat (c * r))) = cop r k)
    by (intros k; rewrite Z2Nat.id by lia; apply cop_periodic; exists c; ring).
  assert (E1 : cnt (cop r) 0 (Z.to_nat N)
               = (Z.to_nat p * cnt (cop r) 0 (Z.to_nat (c * r)))%nat)
    by (rewrite Hlen; apply cnt_period; exact Hper).
  assert (E3 : cnt (fun k => andb (cop r k) (k mod p =? 0)) 0 (Z.to_nat N)
               = cnt (cop r) 0 (Z.to_nat (c * r))).
  { replace (Z.to_nat N) with (Z.to_nat p * Z.to_nat (c * r))%nat by lia.
    rewrite (cnt_multiples (cop r) p ltac:(lia)).
    apply cnt_ext. intros k _. apply cop_pj. rewrite Z.gcd_comm. exact Hrp. }
  assert (E2 : cnt (cop (r * p)) 0 (Z.to_nat N)
               = (cnt (cop r) 0 (Z.to_nat N) - cnt (cop r) 0 (Z.to_nat (c * r)))%nat).
  { rewrite (cnt_split (cop r) (fun k => k mod p =? 0) (Z.to_nat N) 0).
    rewrite (cnt_ext (cop (r * p)) (fun k => andb (cop r k) (negb (k mod p =? 0))))
      by (intros k _; apply cop_rp; exact Hp).
    rewrite E3. lia. }
  rewrite E2, E1.
  set (C := cnt (cop r) 0 (Z.to_nat (c * r))).
  assert (HC : (C <= Z.to_nat p * C)%nat) by nia.
  rewrite Nat2Z.inj_sub by exact HC. rewrite Nat2Z.inj_mul, Z2Nat.id by lia.
  split; ring.
Qed.

End Counting.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Section Program.
Local Open Scope uint63_scope.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Lemma divout_dec : forall p m : int,
  ((m mod p =? 0) && ((0 <? m) && (1 <? p))) = true ->
  Zwf 0 (φ (m / p)) (φ m).
Proof.
  intros p m H. apply andb_prop in H as [_ H]. apply andb_prop in H as [H1 H2].
  rewrite ltb_spec in H1, H2. change (φ 0) with 0%Z in H1.
  change (φ 1) with 1%Z in H2.
  unfold Zwf. rewrite div_spec.
  pose proof (Z.div_pos (φ m) (φ p) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt (φ m) (φ p) ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* m with every factor p divided out (p >= 2, m >= 1) *)
Fixpoint divout (p m : int) (H : Acc (Zwf 0) (φ m)) {struct H} : int :=
  match bdec ((m mod p =? 0) && ((0 <? m) && (1 <? p))) with
  | left Hc => divout p (m / p) (Acc_inv H (divout_dec p m Hc))
  | right _ => m
  end.

Lemma divout_eq : forall p m H,
  divout p m H =
  match bdec ((m mod p =? 0) && ((0 <? m) && (1 <? p))) with
  | left Hc => divout p (m / p) (Acc_inv H (divout_dec p m Hc))
  | right _ => m
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma divout_le_aux : forall z p m H, (φ m) = z -> ((φ (divout p m H)) <= (φ m))%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p m H Hz. rewrite divout_eq.
  destruct (bdec _) as [Hc | Hc].
  - pose proof (divout_dec p m Hc) as D.
    eapply Z.le_trans.
    + apply (IH (φ (m / p))); [rewrite <- Hz; exact D | reflexivity].
    + unfold Zwf in D. lia.
  - lia.
Qed.

Lemma divout_le : forall p m H, ((φ (divout p m H)) <= (φ m))%Z.
Proof. intros p m H. exact (divout_le_aux _ p m H eq_refl). Qed.

Lemma outer_dec : forall p m m' : int,
  ((p * p <=? m) && (p <? m)) = true -> ((φ m') <= (φ m))%Z ->
  Zwf 0 ((φ m') - (φ (p + 1))) ((φ m) - (φ p)).
Proof.
  intros p m m' Hc Hm. apply andb_prop in Hc as [_ Hc]. rewrite ltb_spec in Hc.
  pose proof (to_Z_bounded p). pose proof (to_Z_bounded m).
  assert ((φ (p + 1)) = (φ p) + 1)%Z by sia.
  unfold Zwf. lia.
Qed.

(* trial division from p on, m what remains of n, res the running count *)
Fixpoint outer (p m res : int) (H : Acc (Zwf 0) ((φ m) - (φ p))%Z) {struct H} : int :=
  match bdec ((p * p <=? m) && (p <? m)) with
  | left Hc =>
      if m mod p =? 0 then
        let m' := divout p m (Zwf_well_founded 0 (φ m)) in
        outer (p + 1) m' (res / p * (p - 1))
          (Acc_inv H (outer_dec p m m' Hc (divout_le p m _)))
      else
        outer (p + 1) m res (Acc_inv H (outer_dec p m m Hc (Z.le_refl _)))
  | right _ => if 1 <? m then res / m * (m - 1) else res
  end.

Lemma outer_eq : forall p m res H,
  outer p m res H =
  match bdec ((p * p <=? m) && (p <? m)) with
  | left Hc =>
      if m mod p =? 0 then
        let m' := divout p m (Zwf_well_founded 0 (φ m)) in
        outer (p + 1) m' (res / p * (p - 1))
          (Acc_inv H (outer_dec p m m' Hc (divout_le p m _)))
      else
        outer (p + 1) m res (Acc_inv H (outer_dec p m m Hc (Z.le_refl _)))
  | right _ => if 1 <? m then res / m * (m - 1) else res
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition relatives_impl (n : uint) : uint :=
  if n <=? 1 then 0
  else outer 2 n n (Zwf_well_founded 0 ((φ n) - (φ 2))%Z).

End Program.

(* ------------------------------------------------------------------ *)
(* Loop proofs                                                         *)
(* ------------------------------------------------------------------ *)

Section Proofs.
Local Open Scope uint63_scope.
Local Open Scope Z_scope.

Lemma divout_spec_aux : forall z (p m : int) H, (φ m) = z ->
  2 <= (φ p) -> 1 <= (φ m) ->
  let m' := (φ (divout p m H)) in
  1 <= m' /\ (m' | (φ m)) /\ ~ ((φ p) | m') /\
  (forall k, Z.gcd k (φ p) = 1 /\ Z.gcd k (φ m) = 1 <->
             Z.gcd k (φ p) = 1 /\ Z.gcd k m' = 1).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p m H Hz Hp Hm m'. subst m'. rewrite divout_eq.
  destruct (bdec _) as [Hc | Hc].
  - pose proof (divout_dec p m Hc) as D.
    pose proof Hc as Hc'.
    apply andb_prop in Hc' as [Hmod _]. apply Uint63.eqb_spec in Hmod.
    assert (Hmod' : (φ m) mod (φ p) = 0) by (rewrite <- mod_spec, Hmod; reflexivity).
    assert (Hq : (φ m) = (φ p) * (φ (m / p))%uint63) by (rewrite div_spec; apply Z_div_exact_full_2; lia).
    assert (Hq1 : 1 <= (φ (m / p))%uint63) by nia.
    destruct (IH ((φ (m / p))%uint63) ltac:(rewrite <- Hz; exact D) p (m / p)%uint63 (Acc_inv H (divout_dec p m Hc)) eq_refl Hp Hq1)
      as (B1 & B2 & B3 & B4).
    set (w := divout p (m / p)%uint63 (Acc_inv H (divout_dec p m Hc))) in *.
    split; [exact B1|]. split.
    + destruct B2 as [c Hc2]. exists (c * (φ p)). rewrite Hq, Hc2. ring.
    + split; [exact B3|]. intros k. specialize (B4 k).
      rewrite Hq, coprime_mul_iff. tauto.
  - repeat split; try (apply Z.divide_refl); try lia; try tauto.
    intros Hd. apply (proj2 (Z.mod_divide (φ m) (φ p) ltac:(lia))) in Hd.
    rewrite <- mod_spec in Hd.
    assert (E : (m mod p =? 0)%uint63 = true)
      by (apply Uint63.eqb_spec; apply to_Z_inj; rewrite Hd; reflexivity).
    rewrite E in Hc. simpl in Hc.
    assert (E1 : (0 <? m)%uint63 = true) by (apply ltb_spec; change (φ 0) with 0; lia).
    assert (E2 : (1 <? p)%uint63 = true) by (apply ltb_spec; change (φ 1) with 1; lia).
    rewrite E1, E2 in Hc. discriminate.
Qed.

Lemma mod_small_step : forall C P R N, 0 <= C -> 2 <= P -> R = P * C ->
  R <= N -> N <= 10^9 -> 0 <= C * (P - 1) < wB.
Proof. intros. change wB with 9223372036854775808. nia. Qed.

Lemma sq_small : forall a, 0 <= a <= 10^9 -> 0 <= a * a < wB.
Proof. intros. change wB with 9223372036854775808. nia. Qed.

Lemma prime_of_no_small : forall P M, 2 <= P -> (P | M) -> 1 <= M ->
  (forall d, 2 <= d < P -> ~ (d | M)) -> prime P.
Proof.
  intros P M HP HPM HM Hd. apply prime_alt. split; [lia|].
  intros n Hn Hnp. apply (Hd n); [lia|]. eapply Z.divide_trans; eassumption.
Qed.

Lemma outer_spec : forall N, 2 <= N <= 10^9 ->
  forall z (p m res : int) H, (φ m) - (φ p) = z ->
  2 <= (φ p) -> 1 <= (φ m) ->
  (forall d, 2 <= d < (φ p) -> ~ (d | (φ m))) ->
  forall r q, 1 <= r -> 1 <= q -> (r | q) -> N = q * (φ m) ->
  Z.gcd r (φ m) = 1 ->
  (forall k, Z.gcd k N = 1 <-> Z.gcd k r = 1 /\ Z.gcd k (φ m) = 1) ->
  (φ res) = Z.of_nat (cnt (cop r) 0 (Z.to_nat N)) ->
  (φ (outer p m res H)) = Z.of_nat (cnt (cop N) 0 (Z.to_nat N)).
Proof.
  intros N HN z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p m res H Hz Hp Hm Hd r q Hr Hq Hrq HNq Hrm Hk Hres.
  assert (HmN : (φ m) <= N) by nia.
  pose proof (cnt_le (cop r) (Z.to_nat N) 0) as Hcle.
  assert (HR : 0 <= (φ res) <= N) by lia.
  rewrite outer_eq.
  destruct (bdec _) as [Hc | Hc].
  - pose proof Hc as Hc'. apply andb_prop in Hc' as [Hc1 Hc2].
    rewrite ltb_spec in Hc2. rewrite leb_spec in Hc1.
    assert (Hpp : (φ (p * p))%uint63 = (φ p) * (φ p)) by (rewrite mul_spec; apply Z.mod_small, sq_small; lia).
    assert (Hp1 : (φ (p + 1))%uint63 = (φ p) + 1) by sia.
    destruct (Uint63.eqb (m mod p) 0) eqn:Emod.
    + (* p divides m: p is a prime factor *)
      apply Uint63.eqb_spec in Emod.
      assert (Hmod : (φ m) mod (φ p) = 0) by (rewrite <- mod_spec, Emod; reflexivity).
      assert (HpM : ((φ p) | (φ m))) by (apply Z.mod_divide; lia).
      assert (Hprime : prime (φ p)) by (exact (prime_of_no_small _ _ Hp HpM Hm Hd)).
      cbv zeta.
      set (A := Zwf_well_founded 0 (φ m)).
      destruct (divout_spec_aux _ p m A eq_refl Hp Hm) as (B1 & B2 & B3 & B4).
      set (m' := divout p m A) in *.
      assert (Hrp : Z.gcd r (φ p) = 1).
      { apply Zgcd_1_rel_prime. apply Zgcd_1_rel_prime in Hrm.
        apply rel_prime_sym. apply (rel_prime_div (φ m) r (φ p)); [|exact HpM].
        apply rel_prime_sym. exact Hrm. }
      assert (HrpN : (r * (φ p) | N)).
      { destruct Hrq as [c Hc3]. destruct HpM as [e He].
        exists (c * e). rewrite HNq, Hc3, He. ring. }
      destruct (step_count r (φ p) N Hr Hprime Hrp HrpN ltac:(lia)) as [S1 S2].
      destruct B2 as [t Ht].
      assert (Hpt : ((φ p) | t)).
      { destruct (prime_mult _ Hprime t (φ m')) as [Ht' | Ht']; [| exact Ht' | ].
        - rewrite <- Ht. apply Z.mod_divide; lia.
        - exfalso. exact (B3 Ht'). }
      assert (Ht1 : 1 <= t)
        by (pose proof (proj1 (Z.mul_pos_cancel_r t (φ m') ltac:(lia)) ltac:(lia)); lia).
      eapply (IH ((φ m') - (φ (p + 1))%uint63)) with (r := r * (φ p)) (q := q * t); [ | reflexivity | lia | exact B1 | | | | | | | | ].
      * rewrite <- Hz. apply outer_dec; [exact Hc | apply divout_le].
      * intros d Hd1 Hd2. rewrite Hp1 in Hd1.
        destruct (Z.eq_dec d (φ p)) as [-> | Hne]; [exact (B3 Hd2) |].
        apply (Hd d); [lia|]. eapply Z.divide_trans; [exact Hd2|]. exists t. exact Ht.
      * pose proof (Z.mul_le_mono_nonneg 1 q 1 t ltac:(lia) Hq ltac:(lia) Ht1). lia.
      * pose proof (Z.mul_le_mono_nonneg 1 q 1 t ltac:(lia) Hq ltac:(lia) Ht1). lia.
      * destruct Hrq as [c Hc3]. destruct Hpt as [e He].
        exists (c * e). rewrite Hc3, He. ring.
      * rewrite HNq, Ht. ring.
      * apply Zgcd_1_rel_prime. apply rel_prime_sym. apply rel_prime_mult.
        -- apply (rel_prime_div (φ m) r (φ m')); [| exists t; exact Ht].
           apply rel_prime_sym, Zgcd_1_rel_prime. exact Hrm.
        -- apply rel_prime_sym, prime_rel_prime; [exact Hprime | exact B3].
      * intros k. rewrite Hk, coprime_mul_iff.
        assert (Hkm : Z.gcd k (φ m) = 1 -> Z.gcd k (φ p) = 1).
        { intros K. apply Zgcd_1_rel_prime in K. apply Zgcd_1_rel_prime.
          apply rel_prime_sym. apply (rel_prime_div (φ m) k (φ p)); [|exact HpM].
          apply rel_prime_sym. exact K. }
        specialize (B4 k). tauto.
      * rewrite S2.
        assert (Hpm1 : (φ (p - 1))%uint63 = (φ p) - 1) by sia.
        set (C := Z.of_nat (cnt (cop r) 0 (Z.to_nat (N / (φ p))))) in *.
        assert (HC : 0 <= C) by (subst C; lia).
        assert (Hdiv : (φ (res / p))%uint63 = C).
        { rewrite div_spec, Hres, S1, Z.mul_comm, Z.div_mul; lia. }
        rewrite mul_spec, Hdiv, Hpm1.
        rewrite Z.mod_small
          by (apply (mod_small_step C (φ p) (Z.of_nat (cnt (cop r) 0 (Z.to_nat N))) N); lia).
        rewrite S1. ring.
    + (* p does not divide m *)
      assert (Hmod : (φ m) mod (φ p) <> 0).
      { intros E. assert (E' : (m mod p = 0)%uint63)
          by (apply to_Z_inj; rewrite mod_spec, E; reflexivity).
        rewrite E', Uint63.eqb_refl in Emod. discriminate. }
      eapply (IH ((φ m) - (φ (p + 1))%uint63)) with (r := r) (q := q); [ | reflexivity | lia | exact Hm | | | | | | | | ];
        try eassumption.
      * rewrite <- Hz. apply outer_dec; [exact Hc | lia].
      * intros d Hd1 Hd2. rewrite Hp1 in Hd1.
        destruct (Z.eq_dec d (φ p)) as [-> | Hne].
        -- apply Hmod. apply Z.mod_divide; [lia | exact Hd2].
        -- apply (Hd d); [lia | exact Hd2].
  - (* exit: p * p > m *)
    assert (Hsq : (φ m) < (φ p) * (φ p)).
    { assert (H2p : 2 * (φ p) <= (φ p) * (φ p)) by (apply Z.mul_le_mono_nonneg_r; lia).
      apply andb_false_iff in Hc as [Hc | Hc].
      - apply Bool.not_true_iff_false in Hc. rewrite leb_spec in Hc.
        destruct (Z_lt_le_dec (φ p) (φ m)) as [Hlt | Hge]; [| lia].
        rewrite mul_spec, Z.mod_small in Hc by (apply sq_small; lia). lia.
      - apply Bool.not_true_iff_false in Hc. rewrite ltb_spec in Hc. lia. }
    destruct (1 <? m)%uint63 eqn:E1.
    + rewrite ltb_spec in E1. change (φ 1) with 1 in E1.
      assert (Hprime : prime (φ m)).
      { apply prime_alt. split; [lia|]. intros d Hd1 [e He].
        destruct (Z_lt_le_dec d (φ p)) as [Hlt | Hge].
        - apply (Hd d); [lia | exists e; exact He].
        - assert (He2 : 2 <= e).
          { destruct (Z_le_gt_dec e 1) as [He1 | He1]; [| lia].
            assert (e * d <= 1 * d) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
          assert (He3 : e < (φ p)).
          { assert ((φ p) * (φ p) <= (φ p) * d) by (apply Z.mul_le_mono_nonneg_l; lia).
            apply (Z.mul_lt_mono_pos_r d); lia. }
          apply (Hd e); [lia | exists d; lia]. }
      assert (HrmN : (r * (φ m) | N)).
      { destruct Hrq as [c Hc3]. exists c. rewrite HNq, Hc3. ring. }
      destruct (step_count r (φ m) N Hr Hprime Hrm HrmN ltac:(lia)) as [S1 S2].
      assert (Hext : cnt (cop N) 0 (Z.to_nat N) = cnt (cop (r * (φ m))) 0 (Z.to_nat N)).
      { apply cnt_ext. intros k _. unfold cop. apply eqb_iff.
        rewrite Hk, coprime_mul_iff. tauto. }
      rewrite Hext, S2.
      assert (Hpm1 : (φ (m - 1))%uint63 = (φ m) - 1) by sia.
      set (C := Z.of_nat (cnt (cop r) 0 (Z.to_nat (N / (φ m))))) in *.
      assert (HC : 0 <= C) by (subst C; lia).
      assert (Hdiv : (φ (res / m))%uint63 = C).
      { rewrite div_spec, Hres, S1, Z.mul_comm, Z.div_mul; lia. }
      rewrite mul_spec, Hdiv, Hpm1.
      rewrite Z.mod_small
        by (apply (mod_small_step C (φ m) (Z.of_nat (cnt (cop r) 0 (Z.to_nat N))) N); lia).
      rewrite S1. ring.
    + apply Bool.not_true_iff_false in E1. rewrite ltb_spec in E1.
      change (φ 1) with 1 in E1.
      assert (Hm1 : (φ m) = 1) by lia.
      rewrite Hres. f_equal. apply cnt_ext. intros k _. unfold cop. apply eqb_iff.
      rewrite Hk, Hm1, Z.gcd_1_r. tauto.
Qed.

(* ------------------------------------------------------------------ *)
(* From the count over [0, n) to the spec                              *)
(* ------------------------------------------------------------------ *)

Fixpoint zseq (a : Z) (l : nat) : list Z :=
  match l with
  | O => []
  | S l' => a :: zseq (a + 1) l'
  end.

Lemma zseq_In : forall l a k, In k (zseq a l) <-> a <= k < a + Z.of_nat l.
Proof.
  intros l. induction l as [| l IH]; intros a k; simpl; [lia|].
  rewrite IH. lia.
Qed.

Lemma zseq_NoDup : forall l a, NoDup (zseq a l).
Proof.
  intros l. induction l as [| l IH]; intros a; simpl; constructor.
  - rewrite zseq_In. lia.
  - apply IH.
Qed.

Lemma cnt_filter : forall P l a, cnt P a l = length (filter P (zseq a l)).
Proof.
  intros P l. induction l as [| l IH]; intros a; simpl; [reflexivity|].
  rewrite IH. destruct (P a); reflexivity.
Qed.

Lemma NoDup_map_inj_on : forall {A B} (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l. induction l as [| a l IH]; intros Hi Hn; simpl; [constructor|].
  inversion Hn as [| a' l' Ha Hl]; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as [y [Hy Hyl]].
    assert (y = a) by (apply Hi; simpl; auto). subst. contradiction.
  - apply IH; [| exact Hl]. intros x y Hx Hy. apply Hi; simpl; auto.
Qed.

Lemma relatively_prime_iff : forall z N, 1 <= z -> 1 <= N ->
  (relatively_prime (Z.to_N z) (Z.to_N N) <-> Z.gcd z N = 1).
Proof.
  intros z N Hz HN. unfold relatively_prime. split.
  - intros Hnr.
    remember (Z.gcd z N) as g eqn:Hg.
    destruct (Z.gcd_divide_l z N) as [c1 Hc1]. rewrite <- Hg in Hc1.
    destruct (Z.gcd_divide_r z N) as [c2 Hc2]. rewrite <- Hg in Hc2.
    assert (Hg0 : 0 <= g) by (rewrite Hg; apply Z.gcd_nonneg).
    destruct (Z.eq_dec g 1) as [| Hne]; [assumption|]. exfalso.
    assert (Hg00 : g <> 0) by (intros E0; rewrite E0 in Hc1; lia).
    assert (Hg2 : 2 <= g) by lia.
    apply Hnr. exists (Z.to_N g), (Z.to_N c1), (Z.to_N c2).
    repeat split; try lia.
  - intros Hg [x [y [w [Hx [Hy [Hw [E1 E2]]]]]]].
    assert (Ez : z = Z.of_N x * Z.of_N y)
      by (rewrite <- N2Z.inj_mul, <- E1, Z2N.id; lia).
    assert (EN : N = Z.of_N x * Z.of_N w)
      by (rewrite <- N2Z.inj_mul, <- E2, Z2N.id; lia).
    assert (Hd : (Z.of_N x | Z.gcd z N)).
    { apply Z.gcd_greatest; [exists (Z.of_N y) | exists (Z.of_N w)]; lia. }
    rewrite Hg in Hd. apply Z.divide_pos_le in Hd; lia.
Qed.

Lemma count_final : forall N, 2 <= N ->
  relatives_spec (Z.to_N N) (Z.to_N (Z.of_nat (cnt (cop N) 0 (Z.to_nat N)))).
Proof.
  intros N HN.
  assert (E : cnt (cop N) 0 (Z.to_nat N) = cnt (cop N) 1 (Z.to_nat N - 1)).
  { destruct (Z.to_nat N) as [| l] eqn:El; [lia|]. cbn [cnt].
    assert (H0 : cop N 0 = false)
      by (unfold cop; rewrite Z.gcd_0_l, Z.abs_eq by lia; apply Z.eqb_neq; lia).
    rewrite H0. simpl. f_equal. lia. }
  rewrite E.
  exists (map Z.to_N (filter (cop N) (zseq 1 (Z.to_nat N - 1)))).
  split; [| split].
  - apply NoDup_map_inj_on; [| apply NoDup_filter, zseq_NoDup].
    intros x y Hx Hy Exy. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
    rewrite zseq_In in Hx, Hy. lia.
  - intros k. rewrite in_map_iff. unfold relative. split.
    + intros [z [Hz Hin]]. apply filter_In in Hin as [Hin Hc].
      rewrite zseq_In in Hin. subst k.
      split; [lia|]. apply relatively_prime_iff; [lia | lia |].
      unfold cop in Hc. apply Z.eqb_eq. exact Hc.
    + intros [Hk Hrp]. exists (Z.of_N k). split; [apply N2Z.id|].
      apply filter_In. split; [rewrite zseq_In; lia|].
      unfold cop. apply Z.eqb_eq. apply relatively_prime_iff; [lia | lia |].
      rewrite N2Z.id. exact Hrp.
  - unfold len. rewrite length_map, <- cnt_filter. lia.
Qed.

Lemma relatives_impl_correct : forall (n : N) (x : uint),
  valid_input n -> repr x n ->
  exists c : N, repr (relatives_impl x) c /\ relatives_spec n c.
Proof.
  intros n x [Hv] Hx. unfold repr, repr_uint in Hx. subst n.
  change (10 ^ 9)%N with 1000000000%N in Hv.
  pose proof (to_Z_bounded x) as Bx.
  assert (HN : 1 <= (φ x) <= 1000000000) by lia.
  unfold relatives_impl.
  destruct (x <=? 1)%uint63 eqn:E.
  - rewrite leb_spec in E. change (φ 1) with 1 in E.
    assert (Hx1 : (φ x) = 1) by lia.
    exists 0%N. split; [reflexivity|]. rewrite Hx1.
    exists []. split; [constructor | split; [| reflexivity]].
    intros k. unfold relative. simpl. lia.
  - apply Bool.not_true_iff_false in E. rewrite leb_spec in E. change (φ 1) with 1 in E.
    eexists. split; [reflexivity|].
    rewrite (outer_spec (φ x) ltac:(lia) _ 2 x x _ eq_refl) with (r := 1) (q := 1).
    + apply count_final. lia.
    + change (φ 2) with 2. lia.
    + lia.
    + intros d Hd. change (φ 2) with 2 in Hd. lia.
    + lia.
    + lia.
    + apply Z.divide_refl.
    + lia.
    + apply Z.gcd_1_l.
    + intros k. rewrite Z.gcd_1_r. tauto.
    + rewrite cnt_all by (intros k; unfold cop; rewrite Z.gcd_1_r; reflexivity).
      lia.
Qed.

End Proofs.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition relatives : uint -> uint := relatives_impl.

Definition relatives_correct : forall (n : N) (x : uint),
  valid_input n -> repr x n ->
  exists c : N, repr (relatives x) c /\ relatives_spec n c
  := relatives_impl_correct.
