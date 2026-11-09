(* Correctness proofs for atrivialpursuit_implem.v. *)
From Atrivialpursuit.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Znumtheory Permutation.
Import ListNotations.

Unset Lia Cache.
Local Notation length := List.length.
Open Scope bool_scope.

From Atrivialpursuit Require Export atrivialpursuit_implem.
Open Scope bool_scope.


(* ================================================================== *)
(* Part 1. Number theory in N: primes, valuations                      *)
(* ================================================================== *)

Section NT.
Local Open Scope N_scope.

Definition primeN (p : N) : Prop := 1 < p /\ forall d, (d | p) -> d = 1 \/ d = p.

Lemma divide_dec : forall a b : N, a <> 0 -> {(a | b)} + {~ (a | b)}.
Proof.
  intros a b Ha. destruct (N.eq_dec (b mod a) 0) as [E | E].
  - left. apply N.mod_divide; auto.
  - right. intro D. apply E. apply N.mod_divide; auto.
Qed.

Lemma primeN_gt1 : forall p, primeN p -> 1 < p.
Proof. intros p [H _]; exact H. Qed.

Lemma primeN_gcd : forall p a, primeN p -> ~ (p | a) -> N.gcd p a = 1.
Proof.
  intros p a [Hp Hd] Hna.
  destruct (Hd (N.gcd p a) (N.gcd_divide_l p a)) as [E | E]; auto.
  exfalso. apply Hna. rewrite <- E. apply N.gcd_divide_r.
Qed.

Lemma primeN_mult : forall p a b, primeN p -> (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intros p a b Hp Hab.
  assert (Hp0 : p <> 0) by (pose proof (primeN_gt1 p Hp); lia).
  destruct (divide_dec p a Hp0) as [D | D]; [left; exact D | right].
  apply N.gauss with a; auto. apply primeN_gcd; auto.
Qed.

Lemma primeN_not_div1 : forall p, primeN p -> ~ (p | 1).
Proof.
  intros p Hp D. apply N.divide_1_r in D. pose proof (primeN_gt1 p Hp). lia.
Qed.

Lemma primeN_pow_div : forall p q k, primeN p -> primeN q -> (q | p ^ k) -> q = p.
Proof.
  intros p q k Hp Hq. induction k as [| k IH] using N.peano_ind; intros D.
  - rewrite N.pow_0_r in D. exfalso. exact (primeN_not_div1 q Hq D).
  - rewrite N.pow_succ_r' in D. destruct (primeN_mult q p (p ^ k) Hq D) as [D1 | D1]; auto.
    destruct Hp as [Hp1 Hpd]. destruct (Hpd q D1) as [E | E]; auto.
    pose proof (primeN_gt1 q Hq). lia.
Qed.

(* bounded search, on nat *)
Lemma dec_exists_below : forall (P : nat -> Prop),
  (forall k, P k \/ ~ P k) -> forall n,
  (exists k, (k < n)%nat /\ P k) \/ (forall k, (k < n)%nat -> ~ P k).
Proof.
  intros P Hd n. induction n as [| n IH].
  - right. intros k Hk. lia.
  - destruct IH as [[k [Hk Pk]] | H].
    + left. exists k. split; [lia | exact Pk].
    + destruct (Hd n) as [Pn | Pn].
      * left. exists n. split; [lia | exact Pn].
      * right. intros k Hk. destruct (Nat.eq_dec k n) as [-> | E]; auto. apply H. lia.
Qed.

Lemma prime_divisor_exists : forall n, 1 < n -> exists p, primeN p /\ (p | n).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction N.lt_wf_0).
  intros Hn.
  destruct (dec_exists_below (fun k => 1 < N.of_nat k /\ N.of_nat k < n /\ (N.of_nat k | n)))
    with (n := N.to_nat n) as [[k [Hk [H1 [H2 H3]]]] | H].
  - intros k. destruct (N.lt_ge_cases 1 (N.of_nat k)) as [A | A]; [| right; lia].
    destruct (N.lt_ge_cases (N.of_nat k) n) as [B | B]; [| right; lia].
    destruct (divide_dec (N.of_nat k) n ltac:(lia)) as [C | C]; [left; auto | right; tauto].
  - destruct (IH (N.of_nat k) H2 H1) as [p [Hp Dp]].
    exists p. split; auto. eapply N.divide_trans; eauto.
  - exists n. split; [| apply N.divide_refl]. split; auto.
    intros d Dd.
    assert (Hd0 : d <> 0) by (intro E; subst; destruct Dd as [z Hz]; lia).
    assert (Hdn : d <= n) by (apply N.divide_pos_le; auto; lia).
    destruct (N.eq_dec d 1) as [E | E]; [left; auto|].
    destruct (N.eq_dec d n) as [E' | E']; [right; auto|].
    exfalso. apply (H (N.to_nat d)); [lia|]. rewrite N2Nat.id. repeat split; auto; lia.
Qed.

(* valuations: vp p n, for 1 < p and 0 < n *)
Fixpoint vpf (f : nat) (p n : N) : nat :=
  match f with
  | O => O
  | S f => if N.eqb (n mod p) 0 then S (vpf f p (n / p)) else O
  end.

Definition vp (p n : N) : nat := vpf (N.to_nat n) p n.

Lemma vpf_spec : forall f p n, 1 < p -> 0 < n -> n <= N.of_nat f ->
  exists m, n = p ^ N.of_nat (vpf f p n) * m /\ ~ (p | m).
Proof.
  induction f as [| f IH]; intros p n Hp Hn Hf; [lia|].
  simpl. destruct (N.eqb_spec (n mod p) 0) as [E | E].
  - assert (Hd : n = p * (n / p)) by (pose proof (N.div_mod n p ltac:(lia)); lia).
    assert (Hq : 0 < n / p) by (destruct (N.eq_dec (n / p) 0) as [Z|Z]; [rewrite Z in Hd; lia | lia]).
    assert (Hq2 : n / p < n) by (apply N.div_lt; lia).
    destruct (IH p (n / p) Hp Hq ltac:(lia)) as [m [Hm Dm]].
    exists m. split; auto. rewrite Nat2N.inj_succ, N.pow_succ_r'.
    rewrite Hd at 1. rewrite Hm at 1. ring.
  - exists n. split; [rewrite N.pow_0_r; ring|].
    intro D. apply E. apply N.mod_divide; auto. lia.
Qed.

Lemma vp_spec : forall p n, 1 < p -> 0 < n ->
  exists m, n = p ^ N.of_nat (vp p n) * m /\ ~ (p | m).
Proof. intros p n Hp Hn. apply vpf_spec; auto. lia. Qed.

Lemma vp_unique : forall p n k m, 1 < p -> n = p ^ N.of_nat k * m -> ~ (p | m) ->
  vp p n = k.
Proof.
  intros p n k m Hp Hn Dm.
  assert (Hm0 : m <> 0) by (intro E; apply Dm; rewrite E; apply N.divide_0_r).
  assert (Hn0 : 0 < n) by (subst; pose proof (N.pow_nonzero p (N.of_nat k) ltac:(lia)); nia).
  destruct (vp_spec p n Hp Hn0) as [m' [Hm' Dm']].
  set (j := vp p n) in *. clearbody j.
  destruct (Nat.lt_trichotomy j k) as [L | [L | L]]; auto; exfalso.
  - (* p^j m' = p^j p^(k-j) m *)
    assert (E : p ^ N.of_nat j * m' = p ^ N.of_nat j * (p ^ N.of_nat (k - j) * m)).
    { rewrite <- Hm', N.mul_assoc, <- N.pow_add_r.
      replace (N.of_nat j + N.of_nat (k - j)) with (N.of_nat k) by lia. exact Hn. }
    apply N.mul_cancel_l in E; [| apply N.pow_nonzero; lia].
    apply Dm'. rewrite E. apply N.divide_mul_l.
    replace (N.of_nat (k - j)) with (N.succ (N.of_nat (k - j - 1))) by lia.
    rewrite N.pow_succ_r'. apply N.divide_factor_l.
  - assert (E : p ^ N.of_nat k * m = p ^ N.of_nat k * (p ^ N.of_nat (j - k) * m')).
    { rewrite <- Hn, N.mul_assoc, <- N.pow_add_r.
      replace (N.of_nat k + N.of_nat (j - k)) with (N.of_nat j) by lia. exact Hm'. }
    apply N.mul_cancel_l in E; [| apply N.pow_nonzero; lia].
    apply Dm. rewrite E. apply N.divide_mul_l.
    replace (N.of_nat (j - k)) with (N.succ (N.of_nat (j - k - 1))) by lia.
    rewrite N.pow_succ_r'. apply N.divide_factor_l.
Qed.

Lemma vp_mul : forall p a b, primeN p -> 0 < a -> 0 < b ->
  vp p (a * b) = (vp p a + vp p b)%nat.
Proof.
  intros p a b Hp Ha Hb. pose proof (primeN_gt1 p Hp) as Hp1.
  destruct (vp_spec p a Hp1 Ha) as [m [Hm Dm]].
  destruct (vp_spec p b Hp1 Hb) as [m' [Hm' Dm']].
  apply vp_unique with (m := m * m'); auto.
  - rewrite Hm at 1. rewrite Hm' at 1. rewrite Nat2N.inj_add, N.pow_add_r. ring.
  - intro D. destruct (primeN_mult p m m' Hp D); auto.
Qed.

Lemma vp_pow_self : forall p k, primeN p -> vp p (p ^ N.of_nat k) = k.
Proof.
  intros p k Hp. apply vp_unique with (m := 1); [apply primeN_gt1; auto | ring |].
  apply primeN_not_div1; auto.
Qed.

Lemma vp_not_div : forall p n, 1 < p -> ~ (p | n) -> vp p n = O.
Proof.
  intros p n Hp D. apply vp_unique with (m := n); auto.
  simpl N.of_nat. rewrite N.pow_0_r, N.mul_1_l. reflexivity.
Qed.

Lemma vp_self : forall p, primeN p -> vp p p = 1%nat.
Proof.
  intros p Hp. pose proof (vp_pow_self p 1 Hp) as V. simpl N.of_nat in V.
  rewrite N.pow_1_r in V. exact V.
Qed.

Lemma pow_divide_mono : forall p a b, (a <= b)%nat ->
  (p ^ N.of_nat a | p ^ N.of_nat b).
Proof.
  intros p a b H. exists (p ^ N.of_nat (b - a)). rewrite <- N.pow_add_r. f_equal. lia.
Qed.

Lemma vp_1 : forall p, primeN p -> vp p 1 = O.
Proof. intros p Hp. apply vp_not_div; [apply primeN_gt1; auto | apply primeN_not_div1; auto]. Qed.

Lemma vp_pow_other : forall p q k, primeN p -> primeN q -> p <> q -> vp q (p ^ k) = O.
Proof.
  intros p q k Hp Hq E. apply vp_not_div; [apply primeN_gt1; auto|].
  intro D. apply E. symmetry. eapply primeN_pow_div; eauto.
Qed.

Lemma vp_le_div : forall p a b, primeN p -> 0 < a -> 0 < b -> (a | b) ->
  (vp p a <= vp p b)%nat.
Proof.
  intros p a b Hp Ha Hb [c Hc].
  assert (0 < c) by (destruct (N.eq_dec c 0); [subst; lia | lia]).
  rewrite Hc, vp_mul; auto. lia.
Qed.

Lemma vp_pos_div : forall p n, primeN p -> 0 < n -> (1 <= vp p n)%nat -> (p | n).
Proof.
  intros p n Hp Hn H. destruct (vp_spec p n (primeN_gt1 p Hp) Hn) as [m [Hm _]].
  rewrite Hm. apply N.divide_mul_l.
  replace (N.of_nat (vp p n)) with (N.succ (N.of_nat (vp p n - 1))) by lia.
  rewrite N.pow_succ_r'. apply N.divide_factor_l.
Qed.

Lemma vp_zero_iff : forall p n, primeN p -> 0 < n -> (vp p n = O <-> ~ (p | n)).
Proof.
  intros p n Hp Hn. split.
  - intros H D. destruct D as [c Hc].
    assert (0 < c) by (destruct (N.eq_dec c 0); [subst; lia | lia]).
    rewrite Hc, vp_mul in H; auto; [| pose proof (primeN_gt1 p Hp); lia].
    rewrite vp_self in H; auto. lia.
  - intros D. apply vp_not_div; auto. apply primeN_gt1; auto.
Qed.

Lemma pow_vp_div : forall p n, primeN p -> 0 < n -> (p ^ N.of_nat (vp p n) | n).
Proof.
  intros p n Hp Hn. destruct (vp_spec p n (primeN_gt1 p Hp) Hn) as [m [Hm _]].
  rewrite Hm at 2. apply N.divide_factor_l.
Qed.

Lemma pow_div_le_vp : forall p n k, primeN p -> 0 < n -> (p ^ N.of_nat k | n) ->
  (k <= vp p n)%nat.
Proof.
  intros p n k Hp Hn D. rewrite <- (vp_pow_self p k Hp) at 1.
  apply vp_le_div; auto. apply N.neq_0_lt_0, N.pow_nonzero. pose proof (primeN_gt1 p Hp); lia.
Qed.

Lemma div_of_vp : forall a b, 0 < a -> 0 < b ->
  (forall p, primeN p -> (vp p a <= vp p b)%nat) -> (a | b).
Proof.
  intros a. induction a as [a IH] using (well_founded_induction N.lt_wf_0).
  intros b Ha Hb H.
  destruct (N.eq_dec a 1) as [E | E]; [subst; apply N.divide_1_l|].
  destruct (prime_divisor_exists a ltac:(lia)) as [p [Hp [a' Ha']]].
  pose proof (primeN_gt1 p Hp) as Hp1.
  assert (Ha'0 : 0 < a') by (destruct (N.eq_dec a' 0); [subst; lia | lia]).
  assert (Hpb : (p | b)).
  { apply vp_pos_div; auto. specialize (H p Hp). rewrite Ha', vp_mul in H; auto; [|lia].
    rewrite vp_self in H; auto. lia. }
  destruct Hpb as [b' Hb'].
  assert (Hb'0 : 0 < b') by (destruct (N.eq_dec b' 0); [subst; lia | lia]).
  subst a b. apply N.mul_divide_mono_r. apply IH; auto.
  - assert (a' * 1 < a' * p) by (apply N.mul_lt_mono_pos_l; lia). lia.
  - intros q Hq. specialize (H q Hq). rewrite !vp_mul in H; auto; lia.
Qed.

Lemma eq_of_vp : forall a b, 0 < a -> 0 < b ->
  (forall p, primeN p -> vp p a = vp p b) -> a = b.
Proof.
  intros a b Ha Hb H. apply N.divide_antisym; apply div_of_vp; auto;
    intros p Hp; rewrite H; auto.
Qed.

Lemma vp_gcd : forall p a b, primeN p -> 0 < a -> 0 < b ->
  vp p (N.gcd a b) = Nat.min (vp p a) (vp p b).
Proof.
  intros p a b Hp Ha Hb.
  assert (Hg : 0 < N.gcd a b) by (destruct (N.eq_dec (N.gcd a b) 0) as [E|E];
    [apply N.gcd_eq_0 in E; lia | lia]).
  apply Nat.le_antisymm.
  - apply Nat.min_glb; apply vp_le_div; auto; [apply N.gcd_divide_l | apply N.gcd_divide_r].
  - apply pow_div_le_vp; auto. apply N.gcd_greatest.
    + eapply N.divide_trans; [| apply pow_vp_div; eauto].
      apply pow_divide_mono. lia.
    + eapply N.divide_trans; [| apply pow_vp_div; eauto].
      apply pow_divide_mono. lia.
Qed.

Lemma gcd_pos : forall a b, 0 < a -> 0 < N.gcd a b.
Proof.
  intros a b Ha. destruct (N.eq_dec (N.gcd a b) 0) as [E|E]; [apply N.gcd_eq_0 in E; lia | lia].
Qed.

Lemma vp_lcm : forall p a b, primeN p -> 0 < a -> 0 < b ->
  0 < N.lcm a b /\ vp p (N.lcm a b) = Nat.max (vp p a) (vp p b).
Proof.
  intros p a b Hp Ha Hb.
  pose proof (gcd_pos a b Ha) as Hg.
  destruct (N.gcd_divide_r a b) as [k Hk].
  assert (Hk0 : 0 < k) by (destruct (N.eq_dec k 0); [subst; lia | lia]).
  assert (Hkd : b / N.gcd a b = k) by (rewrite Hk at 1; apply N.div_mul; lia).
  unfold N.lcm. rewrite Hkd. split; [lia|].
  rewrite vp_mul; auto.
  pose proof (vp_gcd p a b Hp Ha Hb) as G.
  assert (Vb : vp p b = (vp p k + vp p (N.gcd a b))%nat) by (rewrite Hk at 1; apply vp_mul; auto).
  lia.
Qed.

(* minima and maxima of lists of exponents *)
Fixpoint lmin (l : list nat) : nat :=
  match l with
  | [] => O
  | x :: r => match r with [] => x | _ => Nat.min x (lmin r) end
  end.

Definition lmax (l : list nat) : nat := fold_right Nat.max O l.

Lemma lmin_le : forall l v, In v l -> (lmin l <= v)%nat.
Proof.
  induction l as [| x r IH]; intros v Hv; [destruct Hv|].
  destruct Hv as [-> | Hv].
  - simpl. destruct r; lia.
  - specialize (IH v Hv). simpl. destruct r; [destruct Hv | lia].
Qed.

Lemma lmin_in : forall l, l <> [] -> In (lmin l) l.
Proof.
  induction l as [| x r IH]; intros H; [congruence|].
  destruct r as [| y r']; [left; reflexivity|].
  change (lmin (x :: y :: r')) with (Nat.min x (lmin (y :: r'))).
  destruct (Nat.min_spec x (lmin (y :: r'))) as [[_ M] | [_ M]]; rewrite M.
  - left; reflexivity.
  - right. apply IH. discriminate.
Qed.

Lemma lmax_ge : forall l v, In v l -> (v <= lmax l)%nat.
Proof.
  induction l as [| x r IH]; intros v Hv; [destruct Hv|].
  destruct Hv as [-> | Hv]; simpl; [lia | specialize (IH v Hv); lia].
Qed.

Lemma lmax_in : forall l, l <> [] -> In (lmax l) l.
Proof.
  induction l as [| x r IH]; intros H; [congruence|].
  destruct r as [| y r'] eqn:E; [simpl; left; lia|].
  rewrite <- E in *. simpl.
  destruct (Nat.max_spec x (lmax r)) as [[_ M] | [_ M]]; rewrite M.
  - right. apply IH. subst; discriminate.
  - left; reflexivity.
Qed.

Lemma lmin_all0 : forall l, Forall (fun v => v = O) l -> lmin l = O.
Proof.
  induction l as [| x r IH]; intros H; [reflexivity|].
  inversion H; subst. destruct r as [| y r']; [reflexivity|].
  change (Nat.min 0 (lmin (y :: r')) = 0%nat). lia.
Qed.

Lemma lmax_all0 : forall l, Forall (fun v => v = O) l -> lmax l = O.
Proof.
  induction l as [| x r IH]; intros H; [reflexivity|].
  inversion H; subst. simpl. rewrite IH; auto.
Qed.

Lemma lmax0_all0 : forall l, lmax l = O -> Forall (fun v => v = O) l.
Proof.
  intros l H. apply Forall_forall. intros v Hv. pose proof (lmax_ge l v Hv). lia.
Qed.

Lemma vp_seq_gcd : forall p xs, primeN p -> xs <> [] -> Forall (fun x => 0 < x) xs ->
  0 < seq_gcd xs /\ vp p (seq_gcd xs) = lmin (map (vp p) xs).
Proof.
  intros p xs Hp. induction xs as [| x r IH]; intros Hne Hpos; [congruence|].
  inversion Hpos; subst.
  destruct r as [| y r'] eqn:E.
  - simpl. rewrite N.gcd_0_r. split; auto.
  - rewrite <- E in *. assert (r <> []) by (subst; discriminate).
    destruct (IH H H2) as [P1 P2].
    change (seq_gcd (x :: r)) with (N.gcd x (seq_gcd r)).
    split; [apply gcd_pos; auto|].
    rewrite vp_gcd, P2; auto. simpl. subst r. reflexivity.
Qed.

Lemma vp_seq_lcm : forall p xs, primeN p -> Forall (fun x => 0 < x) xs ->
  0 < seq_lcm xs /\ vp p (seq_lcm xs) = lmax (map (vp p) xs).
Proof.
  intros p xs Hp. induction xs as [| x r IH]; intros Hpos.
  - simpl. split; [lia | apply vp_1; auto].
  - inversion Hpos; subst. destruct (IH H2) as [P1 P2].
    change (seq_lcm (x :: r)) with (N.lcm x (seq_lcm r)).
    destruct (vp_lcm p x (seq_lcm r) Hp H1 P1) as [L1 L2].
    split; auto. rewrite L2, P2. reflexivity.
Qed.

(* the valuation form of is_sequence *)
Definition vseq (P G L : N) (xs : list N) : Prop :=
  len xs = P /\ Forall (fun x => 0 < x) xs /\
  forall p, primeN p ->
    lmin (map (vp p) xs) = vp p G /\ lmax (map (vp p) xs) = vp p L.

Lemma is_seq_vseq : forall P G L xs, 1 <= P -> 0 < G -> 0 < L ->
  (is_sequence P G L xs <-> vseq P G L xs).
Proof.
  intros P G L xs HP HG HL. split.
  - intros [Hl [Hpos [Hg Hlc]]]. split; [exact Hl|]. split; [exact Hpos|].
    assert (Hne : xs <> []) by (intro E; rewrite E in Hl; unfold len in Hl; simpl in Hl; lia).
    intros p Hp. destruct (vp_seq_gcd p xs Hp Hne Hpos) as [_ A].
    destruct (vp_seq_lcm p xs Hp Hpos) as [_ B].
    rewrite <- Hg, <- Hlc. auto.
  - intros [Hl [Hpos Hv]]. split; [exact Hl|]. split; [exact Hpos|].
    assert (Hne : xs <> []) by (intro E; rewrite E in Hl; unfold len in Hl; simpl in Hl; lia).
    split.
    + apply eq_of_vp; auto.
      * destruct (vp_seq_gcd 2 xs) as [A _]; auto.
        split; [lia|]. intros d Dd. assert (d <= 2) by (apply N.divide_pos_le; auto; lia).
        destruct (N.eq_dec d 0) as [->|]; [destruct Dd as [z Hz]; lia|].
        destruct (N.eq_dec d 1); [left; auto|]. right; lia.
      * intros p Hp. destruct (vp_seq_gcd p xs Hp Hne Hpos) as [_ A]. rewrite A. apply Hv; auto.
    + apply eq_of_vp; auto.
      * destruct (vp_seq_lcm 2 xs) as [A _]; auto.
        split; [lia|]. intros d Dd. assert (d <= 2) by (apply N.divide_pos_le; auto; lia).
        destruct (N.eq_dec d 0) as [->|]; [destruct Dd as [z Hz]; lia|].
        destruct (N.eq_dec d 1); [left; auto|]. right; lia.
      * intros p Hp. destruct (vp_seq_lcm p xs Hp Hpos) as [_ A]. rewrite A. apply Hv; auto.
Qed.

End NT.

(* ================================================================== *)
(* Part 2. Counting sequences                                          *)
(* ================================================================== *)

Lemma NoDup_map_inj {A B} (f : A -> B) (l : list A) : NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
Proof.
  induction l as [| x r IH]; intros Hn Hi; simpl; [constructor|].
  inversion Hn; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as [y [Hy Hyr]].
    assert (y = x) by (apply Hi; simpl; auto). subst. contradiction.
  - apply IH; auto. intros a b Ha Hb. apply Hi; simpl; auto.
Qed.

Lemma prod_count {A B C} (f : A -> B -> C) (s1 : list A) (s2 : list B) :
  NoDup s1 -> NoDup s2 ->
  (forall a a' b b', In a s1 -> In a' s1 -> In b s2 -> In b' s2 ->
     f a b = f a' b' -> a = a' /\ b = b') ->
  NoDup (flat_map (fun a => map (f a) s2) s1) /\
  length (flat_map (fun a => map (f a) s2) s1) = (length s1 * length s2)%nat.
Proof.
  induction s1 as [| a r IH]; intros N1 N2 Hi; simpl; [split; [constructor | reflexivity]|].
  inversion N1; subst.
  destruct IH as [IH1 IH2]; auto.
  { intros. apply Hi; simpl; auto. }
  split.
  - apply NoDup_app; auto.
    + apply NoDup_map_inj; auto. intros b b' Hb Hb' E.
      apply (Hi a a b b'); simpl; auto.
    + intros c Hc Hc'. apply in_map_iff in Hc as [b [Hb Hbs]].
      apply in_flat_map in Hc' as [a' [Ha' Hc']]. apply in_map_iff in Hc' as [b' [Hb' Hb's]].
      destruct (Hi a a' b b') as [E _]; simpl; auto; [congruence|]. subst. contradiction.
  - rewrite length_app, length_map, IH2. lia.
Qed.

Lemma NoDup_same_length {A} (l1 l2 : list A) : NoDup l1 -> NoDup l2 ->
  (forall x, In x l1 <-> In x l2) -> length l1 = length l2.
Proof. intros. apply Permutation_length, NoDup_Permutation; auto. Qed.

Section Count.
Local Open Scope N_scope.

Fixpoint zmul (ys zs : list N) : list N :=
  match ys, zs with
  | y :: ys', z :: zs' => y * z :: zmul ys' zs'
  | _, _ => []
  end.

Lemma zmul_length : forall ys zs, length ys = length zs -> length (zmul ys zs) = length ys.
Proof.
  induction ys as [| y ys IH]; intros [| z zs] H; simpl in *; try lia.
  rewrite IH; lia.
Qed.

Lemma zmul_pos : forall ys zs, Forall (fun x => 0 < x) ys -> Forall (fun x => 0 < x) zs ->
  Forall (fun x => 0 < x) (zmul ys zs).
Proof.
  induction ys as [| y ys IH]; intros [| z zs] H1 H2; simpl; try constructor.
  - inversion H1; inversion H2; lia.
  - apply IH; [inversion H1 | inversion H2]; auto.
Qed.

Lemma map_vp_zmul_l : forall p ys zs, primeN p -> length ys = length zs ->
  Forall (fun x => 0 < x) ys -> Forall (fun x => 0 < x) zs ->
  Forall (fun z => vp p z = O) zs -> map (vp p) (zmul ys zs) = map (vp p) ys.
Proof.
  intros p. induction ys as [| y ys IH]; intros [| z zs] Hp Hl H1 H2 H3; simpl in *; try lia;
    [reflexivity|].
  inversion H1; inversion H2; inversion H3; subst. rewrite vp_mul, IH; auto. f_equal. lia.
Qed.

Lemma map_vp_zmul_r : forall p ys zs, primeN p -> length ys = length zs ->
  Forall (fun x => 0 < x) ys -> Forall (fun x => 0 < x) zs ->
  Forall (fun y => vp p y = O) ys -> map (vp p) (zmul ys zs) = map (vp p) zs.
Proof.
  intros p. induction ys as [| y ys IH]; intros [| z zs] Hp Hl H1 H2 H3; simpl in *; try lia;
    [reflexivity|].
  inversion H1; inversion H2; inversion H3; subst. rewrite vp_mul, IH; auto. f_equal. lia.
Qed.

Lemma vseq_len : forall P G L xs, vseq P G L xs -> length xs = N.to_nat P.
Proof. intros P G L xs [H _]. unfold len in H. lia. Qed.

Lemma vseq_zero : forall P G L xs p, vseq P G L xs -> primeN p -> vp p L = O ->
  Forall (fun x => vp p x = O) xs.
Proof.
  intros P G L xs p [_ [_ H]] Hp HL. destruct (H p Hp) as [_ H2].
  rewrite HL in H2. apply lmax0_all0 in H2. apply Forall_map in H2. exact H2.
Qed.

Definition coprime_vp (G1 A G2 B : N) : Prop :=
  forall p, primeN p -> (vp p G1 = O /\ vp p A = O) \/ (vp p G2 = O /\ vp p B = O).

Lemma mul_fwd : forall P G1 A G2 B ys zs,
  0 < G1 -> 0 < A -> 0 < G2 -> 0 < B -> coprime_vp G1 A G2 B ->
  vseq P G1 A ys -> vseq P G2 B zs -> vseq P (G1 * G2) (A * B) (zmul ys zs).
Proof.
  intros P G1 A G2 B ys zs H1 H2 H3 H4 Hc Hy Hz.
  pose proof (vseq_len _ _ _ _ Hy) as Ly. pose proof (vseq_len _ _ _ _ Hz) as Lz.
  destruct Hy as [Hy1 [Hy2 Hy3]]. destruct Hz as [Hz1 [Hz2 Hz3]].
  split; [unfold len; rewrite zmul_length; [exact Hy1 | lia]|].
  split; [apply zmul_pos; auto|].
  intros p Hp. rewrite !vp_mul; auto.
  destruct (Hc p Hp) as [[E1 E2] | [E1 E2]].
  - rewrite map_vp_zmul_r; auto; [| lia |].
    + rewrite E1, E2. simpl. apply Hz3; auto.
    + eapply vseq_zero; [split; [exact Hy1 | split; eauto] | auto | auto].
  - rewrite map_vp_zmul_l; auto; [| lia |].
    + rewrite E1, E2, !Nat.add_0_r. apply Hy3; auto.
    + eapply vseq_zero; [split; [exact Hz1 | split; eauto] | auto | auto].
Qed.

Lemma zmul_inj : forall ys ys' zs zs',
  length ys = length zs -> length ys' = length zs' -> length ys = length ys' ->
  Forall (fun x => 0 < x) ys -> Forall (fun x => 0 < x) ys' ->
  Forall (fun x => 0 < x) zs -> Forall (fun x => 0 < x) zs' ->
  (forall p, primeN p ->
     (Forall (fun y => vp p y = O) ys /\ Forall (fun y => vp p y = O) ys') \/
     (Forall (fun z => vp p z = O) zs /\ Forall (fun z => vp p z = O) zs')) ->
  zmul ys zs = zmul ys' zs' -> ys = ys' /\ zs = zs'.
Proof.
  induction ys as [| y ys IH]; intros [| y' ys'] [| z zs] [| z' zs'] L1 L2 L3 P1 P2 P3 P4 Hc E;
    simpl in *; try lia; try (split; reflexivity).
  inversion E as [[E1 E2]].
  inversion P1; inversion P2; inversion P3; inversion P4; subst.
  assert (Ey : y = y').
  { apply eq_of_vp; auto. intros p Hp.
    destruct (Hc p Hp) as [[F1 F2] | [F1 F2]].
    - inversion F1; inversion F2; congruence.
    - inversion F1; inversion F2.
      assert (V : vp p (y * z) = vp p (y' * z')) by (rewrite E1; reflexivity).
      rewrite !vp_mul in V; auto. lia. }
  subst y'.
  assert (Ez : z = z') by (apply N.mul_cancel_l with y; lia).
  subst z'.
  destruct (IH ys' zs zs') as [-> ->]; auto; try lia.
  intros p Hp. destruct (Hc p Hp) as [[F1 F2] | [F1 F2]];
    [left | right]; inversion F1; inversion F2; auto.
Qed.

Lemma zmul_map : forall (f g : N -> N) xs, zmul (map f xs) (map g xs) = map (fun x => f x * g x) xs.
Proof. intros f g. induction xs as [| x xs IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma mul_surj : forall P G1 A G2 B xs,
  1 <= P -> 0 < G1 -> 0 < A -> 0 < G2 -> 0 < B -> coprime_vp G1 A G2 B ->
  vseq P (G1 * G2) (A * B) xs ->
  exists ys zs, vseq P G1 A ys /\ vseq P G2 B zs /\ xs = zmul ys zs.
Proof.
  intros P G1 A G2 B xs HP H1 H2 H3 H4 Hc [Hx1 [Hx2 Hx3]].
  assert (Hne : xs <> []) by (intro E; rewrite E in Hx1; unfold len in Hx1; simpl in Hx1; lia).
  set (f := fun x => N.gcd x A). set (g := fun x => x / N.gcd x A).
  assert (Hfg : forall x, 0 < x -> f x * g x = x /\ 0 < f x /\ 0 < g x).
  { intros x Hx. unfold f, g. destruct (N.gcd_divide_l x A) as [k Hk].
    pose proof (gcd_pos x A Hx).
    assert (Hkd : x / N.gcd x A = k) by (rewrite Hk at 1; apply N.div_mul; lia).
    rewrite Hkd. split; [lia|]. split; [lia|].
    destruct (N.eq_dec k 0); [subst; lia | lia]. }
  assert (Hvf : forall p x, primeN p -> 0 < x ->
            vp p (f x) = Nat.min (vp p x) (vp p A) /\
            vp p (g x) = (vp p x - Nat.min (vp p x) (vp p A))%nat).
  { intros p x Hp Hx. destruct (Hfg x Hx) as [E [F G]].
    assert (V : vp p (f x * g x) = vp p x) by (rewrite E; reflexivity).
    rewrite vp_mul in V; auto. unfold f in *. rewrite vp_gcd in *; auto. split; [reflexivity|]. lia. }
  assert (Hbx : forall p x, primeN p -> In x xs -> (vp p x <= vp p A + vp p B)%nat).
  { intros p x Hp Hin. rewrite <- vp_mul; auto. destruct (Hx3 p Hp) as [_ M]. rewrite <- M.
    apply lmax_ge, in_map. exact Hin. }
  exists (map f xs), (map g xs).
  assert (Pf : Forall (fun x => 0 < x) (map f xs)).
  { apply Forall_map. eapply Forall_impl; [| exact Hx2]. intros x Hx. apply Hfg; auto. }
  assert (Pg : Forall (fun x => 0 < x) (map g xs)).
  { apply Forall_map. eapply Forall_impl; [| exact Hx2]. intros x Hx. apply Hfg; auto. }
  assert (Hne' : forall h : N -> N, map h xs <> []) by (intros h E; apply map_eq_nil in E; contradiction).
  split; [| split].
  - split; [unfold len; rewrite length_map; exact Hx1|]. split; [exact Pf|].
    intros p Hp. destruct (Hx3 p Hp) as [M1 M2]. rewrite vp_mul in M1, M2; auto.
    destruct (Hc p Hp) as [[E1 E2] | [E1 E2]].
    + assert (Z : map (vp p) (map f xs) = map (fun _ => O) xs).
      { rewrite map_map. apply map_ext_in. intros x Hin.
        rewrite Forall_forall in Hx2. destruct (Hvf p x Hp (Hx2 x Hin)) as [V _]. lia. }
      rewrite Z, E1, E2. split; [apply lmin_all0 | apply lmax_all0];
        apply Forall_forall; intros v Hv; apply in_map_iff in Hv as [? [? _]]; auto.
    + assert (Z : map (vp p) (map f xs) = map (vp p) xs).
      { rewrite map_map. apply map_ext_in. intros x Hin.
        rewrite Forall_forall in Hx2. destruct (Hvf p x Hp (Hx2 x Hin)) as [V _].
        specialize (Hbx p x Hp Hin). lia. }
      rewrite Z, M1, M2. lia.
  - split; [unfold len; rewrite length_map; exact Hx1|]. split; [exact Pg|].
    intros p Hp. destruct (Hx3 p Hp) as [M1 M2]. rewrite vp_mul in M1, M2; auto.
    destruct (Hc p Hp) as [[E1 E2] | [E1 E2]].
    + assert (Z : map (vp p) (map g xs) = map (vp p) xs).
      { rewrite map_map. apply map_ext_in. intros x Hin.
        rewrite Forall_forall in Hx2. destruct (Hvf p x Hp (Hx2 x Hin)) as [_ V]. lia. }
      rewrite Z, M1, M2. lia.
    + assert (Z : map (vp p) (map g xs) = map (fun _ => O) xs).
      { rewrite map_map. apply map_ext_in. intros x Hin.
        rewrite Forall_forall in Hx2. destruct (Hvf p x Hp (Hx2 x Hin)) as [_ V].
        specialize (Hbx p x Hp Hin). lia. }
      rewrite Z, E1, E2. split; [apply lmin_all0 | apply lmax_all0];
        apply Forall_forall; intros v Hv; apply in_map_iff in Hv as [? [? _]]; auto.
  - rewrite zmul_map. rewrite <- (map_id xs) at 1. apply map_ext_in. intros x Hin.
    rewrite Forall_forall in Hx2. symmetry. apply Hfg; auto.
Qed.

Lemma count_mul : forall P G1 A G2 B c1 c2,
  1 <= P -> 0 < G1 -> 0 < A -> 0 < G2 -> 0 < B -> coprime_vp G1 A G2 B ->
  num_sequences P G1 A c1 -> num_sequences P G2 B c2 ->
  num_sequences P (G1 * G2) (A * B) (c1 * c2).
Proof.
  intros P G1 A G2 B c1 c2 HP H1 H2 H3 H4 Hc [s1 [N1 [I1 L1]]] [s2 [N2 [I2 L2]]].
  assert (I1' : forall ys, In ys s1 <-> vseq P G1 A ys)
    by (intros; rewrite I1; apply is_seq_vseq; auto).
  assert (I2' : forall zs, In zs s2 <-> vseq P G2 B zs)
    by (intros; rewrite I2; apply is_seq_vseq; auto).
  destruct (prod_count zmul s1 s2 N1 N2) as [Nd Ln].
  { intros ys ys' zs zs' Hy Hy' Hz Hz' E.
    apply I1' in Hy, Hy'. apply I2' in Hz, Hz'.
    pose proof (vseq_len _ _ _ _ Hy). pose proof (vseq_len _ _ _ _ Hy').
    pose proof (vseq_len _ _ _ _ Hz). pose proof (vseq_len _ _ _ _ Hz').
    apply zmul_inj; auto; try lia;
      try (destruct Hy as [_ [? _]]; assumption); try (destruct Hy' as [_ [? _]]; assumption);
      try (destruct Hz as [_ [? _]]; assumption); try (destruct Hz' as [_ [? _]]; assumption).
    intros p Hp. destruct (Hc p Hp) as [[E1 E2] | [E1 E2]].
    - left. split; eapply vseq_zero; eauto.
    - right. split; eapply vseq_zero; eauto. }
  exists (flat_map (fun ys => map (zmul ys) s2) s1). split; [exact Nd|]. split.
  - intros xs. rewrite is_seq_vseq by (auto; nia). split.
    + intros Hin. apply in_flat_map in Hin as [ys [Hys Hin]].
      apply in_map_iff in Hin as [zs [<- Hzs]].
      apply mul_fwd; auto; [apply I1' | apply I2']; auto.
    + intros Hv. destruct (mul_surj P G1 A G2 B xs HP H1 H2 H3 H4 Hc Hv) as [ys [zs [Y [Z ->]]]].
      apply in_flat_map. exists ys. split; [apply I1'; auto|]. apply in_map. apply I2'; auto.
  - unfold len in *. rewrite Ln, Nat2N.inj_mul, L1, L2. reflexivity.
Qed.

Lemma seq_gcd_div : forall xs x, In x xs -> (seq_gcd xs | x).
Proof.
  induction xs as [| y r IH]; intros x Hx; [destruct Hx|].
  destruct Hx as [-> | Hx]; simpl; [apply N.gcd_divide_l|].
  eapply N.divide_trans; [apply N.gcd_divide_r | apply IH; auto].
Qed.

Lemma seq_lcm_div : forall xs x, In x xs -> (x | seq_lcm xs).
Proof.
  induction xs as [| y r IH]; intros x Hx; [destruct Hx|].
  destruct Hx as [-> | Hx]; simpl; [apply N.divide_lcm_l|].
  eapply N.divide_trans; [apply IH; auto | apply N.divide_lcm_r].
Qed.

Lemma count_zero : forall P G L, 1 <= P -> ~ (G | L) -> num_sequences P G L 0.
Proof.
  intros P G L HP D. exists []. split; [constructor|]. split; [| reflexivity].
  intros xs. split; [intros []|]. intros [Hl [_ [Hg Hlc]]].
  destruct xs as [| x r]; [unfold len in Hl; simpl in Hl; lia|].
  exfalso. apply D. rewrite <- Hg, <- Hlc. eapply N.divide_trans;
    [apply seq_gcd_div | apply seq_lcm_div]; left; reflexivity.
Qed.

Lemma seq_gcd_repeat : forall G n, seq_gcd (repeat G (S n)) = G.
Proof.
  intros G n. induction n as [| n IH]; simpl in *; [apply N.gcd_0_r|].
  rewrite IH. apply N.gcd_diag.
Qed.

Lemma seq_lcm_repeat : forall G n, seq_lcm (repeat G (S n)) = G.
Proof.
  intros G n. induction n as [| n IH]; simpl in *; [apply N.lcm_1_r|].
  rewrite IH. apply N.lcm_diag.
Qed.

Lemma count_eq : forall P G, 1 <= P -> 0 < G -> num_sequences P G G 1.
Proof.
  intros P G HP HG. exists [repeat G (N.to_nat P)]. split; [repeat constructor; intros []|].
  split; [| reflexivity].
  intros xs. split.
  - intros [<- | []]. split; [unfold len; rewrite repeat_length; lia|].
    split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
    replace (N.to_nat P) with (S (N.to_nat P - 1)) by lia.
    rewrite seq_gcd_repeat, seq_lcm_repeat. split; reflexivity.
  - intros [Hl [_ [Hg Hlc]]]. left.
    assert (F : Forall (eq G) xs).
    { apply Forall_forall. intros x Hx. apply N.divide_antisym.
      - rewrite <- Hg. apply seq_gcd_div; auto.
      - rewrite <- Hlc. apply seq_lcm_div; auto. }
    rewrite (Forall_eq_repeat F). unfold len in Hl. f_equal. lia.
Qed.

End Count.

(* exponent tuples *)
Fixpoint tuples (vs : list nat) (n : nat) : list (list nat) :=
  match n with
  | O => [[]]
  | S n => flat_map (fun v => map (cons v) (tuples vs n)) vs
  end.

Lemma tuples_in : forall vs n t,
  In t (tuples vs n) <-> length t = n /\ Forall (fun v => In v vs) t.
Proof.
  intros vs n. induction n as [| n IH]; intros t; simpl.
  - split; [intros [<- | []]; split; auto | intros [H _]; destruct t; [left; auto | discriminate]].
  - rewrite in_flat_map. split.
    + intros [v [Hv Hin]]. apply in_map_iff in Hin as [t' [<- Ht']].
      apply IH in Ht' as [L F]. simpl. split; [lia | constructor; auto].
    + intros [L F]. destruct t as [| v t']; [discriminate|].
      inversion F; subst. exists v. split; auto. apply in_map. apply IH. simpl in L. split; auto.
Qed.

Lemma tuples_nodup_len : forall vs n, NoDup vs ->
  NoDup (tuples vs n) /\ length (tuples vs n) = (length vs ^ n)%nat.
Proof.
  intros vs n Hv. induction n as [| n [IH1 IH2]]; simpl.
  - split; [repeat constructor; intros [] | reflexivity].
  - destruct (prod_count cons vs (tuples vs n) Hv IH1) as [A B].
    { intros a a' b b' _ _ _ _ E. inversion E; auto. }
    split; [exact A|]. rewrite B, IH2. reflexivity.
Qed.

Lemma tuples_seq_in : forall a k n t,
  In t (tuples (seq a k) n) <-> length t = n /\ Forall (fun v => (a <= v < a + k)%nat) t.
Proof.
  intros a k n t. rewrite tuples_in. split; intros [L F]; split; auto;
    eapply Forall_impl; try exact F; intros v Hv; apply in_seq; auto.
Qed.

Lemma len_tuples_seq : forall a k n, length (tuples (seq a k) n) = (k ^ n)%nat.
Proof.
  intros a k n. pose proof (tuples_nodup_len (seq a k) n (seq_NoDup _ _)) as [_ B].
  rewrite length_seq in B. exact B.
Qed.

Lemma filter_split {A} (f h : A -> bool) (l : list A) :
  length (filter f l) =
  (length (filter (fun x => f x && h x) l) + length (filter (fun x => f x && negb (h x)) l))%nat.
Proof.
  induction l as [| x r IH]; simpl; [reflexivity|].
  destruct (f x), (h x); simpl; lia.
Qed.

Lemma filter_true_len {A} (l : list A) : length (filter (fun _ => true) l) = length l.
Proof. induction l; simpl; auto. Qed.

Lemma existsb_eq_in : forall (g : nat) t, existsb (Nat.eqb g) t = true <-> In g t.
Proof.
  intros g t. rewrite existsb_exists. split.
  - intros [x [Hx E]]. apply Nat.eqb_eq in E. subst. exact Hx.
  - intros H. exists g. split; auto. apply Nat.eqb_refl.
Qed.

Lemma Forall_not_in : forall (g : nat) (lo hi : nat) t,
  Forall (fun v => (lo <= v <= hi)%nat) t -> ~ In g t -> Forall (fun v => (lo <= v <= hi /\ v <> g)%nat) t.
Proof.
  intros g lo hi t F N. apply Forall_forall. intros v Hv. rewrite Forall_forall in F.
  split; [apply F; auto | intro E; subst; contradiction].
Qed.

Lemma count_tuples : forall g e n, (1 <= e)%nat ->
  let T := tuples (seq g (S e)) n in
  let K := length (filter (fun t => existsb (Nat.eqb g) t && existsb (Nat.eqb (g + e)) t) T) in
  (K + e ^ n + e ^ n = S e ^ n + (e - 1) ^ n)%nat.
Proof.
  intros g e n He T K.
  set (Ag := fun t => existsb (Nat.eqb g) t).
  set (Al := fun t => existsb (Nat.eqb (g + e)) t).
  assert (NT : NoDup T /\ length T = (S e ^ n)%nat).
  { unfold T. split; [apply tuples_nodup_len, seq_NoDup | apply len_tuples_seq]. }
  destruct NT as [NT LT].
  assert (InT : forall t, In t T <-> length t = n /\ Forall (fun v => (g <= v <= g + e)%nat) t).
  { intros t. unfold T. rewrite tuples_seq_in. split; intros [L F]; split; auto;
      eapply Forall_impl; try exact F; intros; simpl in *; lia. }
  assert (C1 : length (filter (fun t => negb (Ag t)) T) = (e ^ n)%nat).
  { rewrite <- (len_tuples_seq (S g) e n).
    apply NoDup_same_length; [apply NoDup_filter; auto | apply tuples_nodup_len, seq_NoDup |].
    intros t. rewrite filter_In, InT, tuples_seq_in. unfold Ag.
    rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false, existsb_eq_in.
    split.
    - intros [[L F] N]. split; auto. apply (Forall_not_in g) in F; auto.
      eapply Forall_impl; [| exact F]. intros; simpl in *; lia.
    - intros [L F]. split; [split; auto; eapply Forall_impl; [| exact F]; intros; simpl in *; lia|].
      intro Hin. rewrite Forall_forall in F. specialize (F g Hin). lia. }
  assert (C2 : length (filter (fun t => negb (Al t)) T) = (e ^ n)%nat).
  { rewrite <- (len_tuples_seq g e n).
    apply NoDup_same_length; [apply NoDup_filter; auto | apply tuples_nodup_len, seq_NoDup |].
    intros t. rewrite filter_In, InT, tuples_seq_in. unfold Al.
    rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false, existsb_eq_in.
    split.
    - intros [[L F] N]. split; auto. apply (Forall_not_in (g + e)) in F; auto.
      eapply Forall_impl; [| exact F]. intros; simpl in *; lia.
    - intros [L F]. split; [split; auto; eapply Forall_impl; [| exact F]; intros; simpl in *; lia|].
      intro Hin. rewrite Forall_forall in F. specialize (F (g + e)%nat Hin). lia. }
  assert (C3 : length (filter (fun t => negb (Al t) && negb (Ag t)) T) = ((e - 1) ^ n)%nat).
  { rewrite <- (len_tuples_seq (S g) (e - 1) n).
    apply NoDup_same_length; [apply NoDup_filter; auto | apply tuples_nodup_len, seq_NoDup |].
    intros t. rewrite filter_In, InT, tuples_seq_in, Bool.andb_true_iff. unfold Al, Ag.
    rewrite !Bool.negb_true_iff, <- !Bool.not_true_iff_false, !existsb_eq_in.
    split.
    - intros [[L F] [N1 N2]]. split; auto. apply (Forall_not_in (g + e)) in F; auto.
      apply Forall_forall. intros v Hv. rewrite Forall_forall in F. specialize (F v Hv).
      assert (v <> g) by (intro; subst; contradiction). lia.
    - intros [L F]. split; [split; auto; eapply Forall_impl; [| exact F]; intros; simpl in *; lia|].
      rewrite Forall_forall in F. split; intro Hin; [specialize (F (g + e)%nat Hin) | specialize (F g Hin)]; lia. }
  pose proof (filter_split (fun _ => true) Ag T) as S1. rewrite filter_true_len in S1.
  pose proof (filter_split Ag Al T) as S2.
  pose proof (filter_split (fun t => negb (Al t)) Ag T) as S3.
  assert (E1 : filter (fun x => true && Ag x) T = filter Ag T) by (apply filter_ext; reflexivity).
  assert (E2 : filter (fun x => true && negb (Ag x)) T = filter (fun t => negb (Ag t)) T)
    by (apply filter_ext; reflexivity).
  assert (E3 : length (filter (fun x => negb (Al x) && Ag x) T) =
               length (filter (fun x => Ag x && negb (Al x)) T))
    by (f_equal; apply filter_ext; intros; apply Bool.andb_comm).
  rewrite E1, E2 in S1. cbv beta in S3. rewrite E3 in S3.
  unfold K. change ((length (filter (fun x => Ag x && Al x) T) + e ^ n + e ^ n)%nat =
    (S e ^ n + (e - 1) ^ n)%nat). lia.
Qed.

Section PP.
Local Open Scope N_scope.

Lemma map_pow_inj : forall p t t', 1 < p ->
  map (fun a => p ^ N.of_nat a) t = map (fun a => p ^ N.of_nat a) t' -> t = t'.
Proof.
  intros p t. induction t as [| a t IH]; intros [| a' t'] Hp E; simpl in *; try discriminate; auto.
  inversion E as [[E1 E2]]. apply N.pow_inj_r in E1; auto. f_equal; [lia | auto].
Qed.

Lemma count_pp : forall p g l P, primeN p -> (g < l)%nat -> 1 <= P ->
  exists c, num_sequences P (p ^ N.of_nat g) (p ^ N.of_nat l) c /\
    Z.of_N c = ((Z.of_nat (l - g) + 1) ^ Z.of_N P - 2 * Z.of_nat (l - g) ^ Z.of_N P
                + (Z.of_nat (l - g) - 1) ^ Z.of_N P)%Z.
Proof.
  intros p g l P Hp Hgl HP.
  pose proof (primeN_gt1 p Hp) as Hp1.
  set (e := (l - g)%nat). set (n := N.to_nat P).
  pose proof (count_tuples g e n ltac:(unfold e; lia)) as CT. cbv zeta in CT.
  set (T := tuples (seq g (S e)) n) in *.
  set (tgt := filter (fun t => existsb (Nat.eqb g) t && existsb (Nat.eqb (g + e)) t) T) in *.
  set (pw := fun a : nat => p ^ N.of_nat a).
  assert (Hpw : forall a, 0 < pw a) by (intros; unfold pw; apply N.neq_0_lt_0, N.pow_nonzero; lia).
  assert (InT : forall t, In t tgt <-> length t = n /\ Forall (fun v => (g <= v <= l)%nat) t /\
                                     In g t /\ In l t).
  { intros t. unfold tgt. rewrite filter_In, Bool.andb_true_iff, !existsb_eq_in.
    unfold T. rewrite tuples_seq_in. replace (g + e)%nat with l by (unfold e; lia).
    split.
    - intros [[L F] [A B]]. split; [auto | split; [| auto]].
      eapply Forall_impl; try exact F; intros; simpl in *; unfold e in *; lia.
    - intros [L [F [A B]]]. split; [split; [auto|] | auto].
      eapply Forall_impl; try exact F; intros; simpl in *; unfold e in *; lia. }
  exists (N.of_nat (length tgt)). split.
  - exists (map (map pw) tgt). split; [| split].
    + apply NoDup_map_inj.
      * apply NoDup_filter. apply tuples_nodup_len, seq_NoDup.
      * intros t t' _ _ E. eapply map_pow_inj; eauto.
    + intros xs. rewrite is_seq_vseq by (auto; unfold pw in Hpw; apply (Hpw _)).
      rewrite in_map_iff. split.
      * intros [t [<- Ht]]. apply InT in Ht as [L [F [Ig Il]]].
        assert (Hne : t <> []) by (intro; subst; destruct Ig).
        split; [unfold len; rewrite length_map; unfold n in L; lia|].
        split; [apply Forall_map, Forall_forall; intros; apply Hpw|].
        intros q Hq. rewrite map_map. destruct (N.eq_dec q p) as [-> | Nq].
        -- assert (Z : map (fun a => vp p (pw a)) t = t).
           { rewrite <- (map_id t) at 2. apply map_ext. intros a. apply vp_pow_self; auto. }
           rewrite Z, !vp_pow_self; auto. rewrite Forall_forall in F.
           pose proof (lmin_le t g Ig). pose proof (lmin_in t Hne) as M1.
           pose proof (lmax_ge t l Il). pose proof (lmax_in t Hne) as M2.
           apply F in M1, M2. lia.
        -- assert (Z : map (fun a => vp q (pw a)) t = map (fun _ => O) t).
           { apply map_ext. intros a. apply vp_pow_other; auto. }
           rewrite Z, !vp_pow_other; auto.
           split; [apply lmin_all0 | apply lmax_all0]; apply Forall_forall;
             intros v Hv; apply in_map_iff in Hv as [? [? _]]; auto.
      * intros Hv. pose proof (vseq_len _ _ _ _ Hv) as Lx.
        destruct Hv as [_ [Hpos H]].
        assert (Hne : xs <> []) by (intro E; subst; simpl in Lx; lia).
        exists (map (vp p) xs). split.
        -- rewrite map_map. rewrite <- (map_id xs) at 2. apply map_ext_in. intros x Hx.
           rewrite Forall_forall in Hpos. apply eq_of_vp; [apply Hpw | auto |].
           intros q Hq. destruct (N.eq_dec q p) as [-> | Nq].
           ++ unfold pw. rewrite vp_pow_self; auto.
           ++ unfold pw. rewrite vp_pow_other; auto.
              destruct (H q Hq) as [_ M]. rewrite vp_pow_other in M; auto.
              pose proof (lmax_ge (map (vp q) xs) (vp q x) (in_map _ _ _ Hx)). lia.
        -- apply InT. destruct (H p Hp) as [M1 M2]. rewrite !vp_pow_self in M1, M2; auto.
           assert (Hne' : map (vp p) xs <> []) by (intro E; apply map_eq_nil in E; contradiction).
           split; [rewrite length_map; exact Lx|]. split; [| split].
           ++ apply Forall_forall. intros v Hv.
              pose proof (lmin_le _ _ Hv). pose proof (lmax_ge _ _ Hv). lia.
           ++ rewrite <- M1. apply lmin_in; auto.
           ++ rewrite <- M2. apply lmax_in; auto.
    + unfold len. rewrite length_map. reflexivity.
  - rewrite nat_N_Z. apply (f_equal Z.of_nat) in CT. rewrite !Nat2Z.inj_add, !Nat2Z.inj_pow in CT.
    replace (Z.of_nat n) with (Z.of_N P) in CT by (unfold n; lia).
    rewrite Nat2Z.inj_succ, <- Z.add_1_r, Nat2Z.inj_sub in CT by (unfold e; lia).
    change (Z.of_nat 1) with 1%Z in CT. lia.
Qed.
End PP.

(* ================================================================== *)
(* Part 3. Primality certificates, in N                                *)
(* ================================================================== *)

Section Cert.
Local Open Scope N_scope.

Lemma pow_ge1 : forall a k, a <> 0 -> 1 <= a ^ k.
Proof. intros a k H. pose proof (N.pow_nonzero a k H). lia. Qed.

Lemma pow_pred_r : forall a k, k <> 0 -> a ^ k = a * a ^ (k - 1).
Proof. intros a k H. rewrite <- N.pow_succ_r'. f_equal. lia. Qed.

Lemma div_pow : forall p a k, (p | a) -> k <> 0 -> (p | a ^ k).
Proof. intros p a k D H. rewrite pow_pred_r by auto. apply N.divide_mul_l. exact D. Qed.

Lemma mod1_div : forall p x, 1 < p -> 1 <= x -> (x mod p = 1 <-> (p | x - 1)).
Proof.
  intros p x Hp Hx. split.
  - intros H. exists (x / p). pose proof (N.div_mod x p ltac:(lia)). lia.
  - intros [k Hk]. symmetry. apply N.mod_unique with k; lia.
Qed.

Lemma mod_eq_div : forall p x y, p <> 0 -> x mod p = y mod p -> y <= x -> (p | x - y).
Proof.
  intros p x y Hp E H. exists (x / p - y / p). rewrite N.mul_sub_distr_r.
  pose proof (N.div_mod x p Hp). pose proof (N.div_mod y p Hp). lia.
Qed.

Lemma mod_of_div : forall p n x, n <> 0 -> (p | n) -> (x mod n) mod p = x mod p.
Proof.
  intros p n x Hn [t Ht]. rewrite (N.div_mod x n Hn) at 2.
  set (r := x mod n). set (q := x / n). rewrite Ht.
  replace (t * p * q + r) with (r + (t * q) * p) by ring.
  rewrite N.Div0.mod_add. reflexivity.
Qed.

Lemma pow_mod_N : forall a k n, (a ^ k) mod n = ((a mod n) ^ k) mod n.
Proof.
  intros a k n. induction k as [| k IH] using N.peano_ind; [reflexivity|].
  rewrite !N.pow_succ_r'. rewrite N.Div0.mul_mod, IH, <- N.Div0.mul_mod.
  rewrite N.Div0.mul_mod_idemp_l. reflexivity.
Qed.

Lemma pow1_mul : forall a k s p, 1 < p -> a ^ k mod p = 1 -> a ^ (k * s) mod p = 1.
Proof.
  intros a k s p Hp H. rewrite N.pow_mul_r, pow_mod_N, H, N.pow_1_l. apply N.mod_small; lia.
Qed.

Lemma pow1_sub : forall a m k p, 1 < p -> a ^ m mod p = 1 -> a ^ k mod p = 1 -> k <= m ->
  a ^ (m - k) mod p = 1.
Proof.
  intros a m k p Hp Hm Hk Hl.
  replace m with (k + (m - k)) in Hm by lia. rewrite N.pow_add_r, N.Div0.mul_mod, Hk in Hm.
  rewrite N.mul_1_l, N.Div0.mod_mod in Hm. exact Hm.
Qed.

Lemma pow1_gcd : forall p a k m, 1 < p -> a ^ m mod p = 1 -> a ^ k mod p = 1 ->
  a ^ (N.gcd m k) mod p = 1.
Proof.
  intros p a k. induction k as [k IH] using (well_founded_induction N.lt_wf_0).
  intros m Hp Hm Hk.
  destruct (N.eq_dec k 0) as [-> | Hk0]; [rewrite N.gcd_0_r; exact Hm|].
  assert (Hmod : a ^ (m mod k) mod p = 1).
  { rewrite (N.mod_eq m k Hk0). apply pow1_sub; auto.
    - apply pow1_mul; auto.
    - pose proof (N.mul_div_le m k Hk0). lia. }
  replace (N.gcd m k) with (N.gcd k (m mod k)).
  - apply IH; auto. apply N.mod_lt; auto.
  - rewrite (N.gcd_comm k (m mod k)), N.Lcm0.gcd_mod. apply N.gcd_comm.
Qed.

(* Fermat's little theorem, through the permutation of the residues *)
Lemma prod_perm : forall l l', Permutation l l' -> prod l = prod l'.
Proof.
  intros l l' H. induction H; simpl; auto; [rewrite IHPermutation; auto | ring | congruence].
Qed.

Lemma prod_map_mul : forall a l,
  prod (map (fun i => a * i) l) = a ^ N.of_nat (length l) * prod l.
Proof.
  intros a l. induction l as [| x l IH]; [simpl; ring|].
  replace (N.of_nat (length (x :: l))) with (N.succ (N.of_nat (length l))) by (simpl length; lia).
  unfold prod in *. simpl map. simpl fold_right. rewrite IH, N.pow_succ_r'. ring.
Qed.

Lemma prod_map_mod : forall a p l,
  prod (map (fun i => (a * i) mod p) l) mod p = prod (map (fun i => a * i) l) mod p.
Proof.
  intros a p l. induction l as [| x l IH]; simpl; [reflexivity|].
  rewrite N.Div0.mul_mod, IH, N.Div0.mod_mod, <- N.Div0.mul_mod. reflexivity.
Qed.

Lemma not_div_prod : forall p l, primeN p -> Forall (fun i => 0 < i < p) l -> ~ (p | prod l).
Proof.
  intros p l Hp. induction l as [| x l IH]; intros F D; simpl in D.
  - exact (primeN_not_div1 p Hp D).
  - inversion F; subst. destruct (primeN_mult p x (prod l) Hp D) as [D1 | D1].
    + apply N.divide_pos_le in D1; lia.
    + apply IH; auto.
Qed.

Lemma fermat : forall p a, primeN p -> ~ (p | a) -> a ^ (p - 1) mod p = 1.
Proof.
  intros p a Hp Ha. pose proof (primeN_gt1 p Hp) as Hp1.
  assert (Ha0 : a <> 0) by (intro; subst; apply Ha; apply N.divide_0_r).
  set (l := map N.of_nat (seq 1 (N.to_nat p - 1))).
  assert (Hl : forall i, In i l <-> 0 < i < p).
  { intros i. unfold l. rewrite in_map_iff. split.
    - intros [k [<- Hk]]. apply in_seq in Hk. lia.
    - intros Hi. exists (N.to_nat i). split; [lia | apply in_seq; lia]. }
  assert (Ll : N.of_nat (length l) = p - 1) by (unfold l; rewrite length_map, length_seq; lia).
  set (f := fun i => (a * i) mod p).
  assert (Hf : forall i, In i l -> 0 < f i < p).
  { intros i Hi. apply Hl in Hi. unfold f. split; [| apply N.mod_lt; lia].
    destruct (N.eq_dec ((a * i) mod p) 0) as [E | E]; [| lia].
    apply N.Lcm0.mod_divide in E. destruct (primeN_mult p a i Hp E) as [D | D]; [contradiction|].
    apply N.divide_pos_le in D; lia. }
  assert (NDl : NoDup l).
  { unfold l. apply NoDup_map_inj; [apply seq_NoDup | intros; lia]. }
  assert (Perm : Permutation (map f l) l).
  { apply Permutation_map_same_l.
    - apply NoDup_map_inj; auto. intros i j Hi Hj E.
      apply Hl in Hi, Hj. unfold f in E.
      assert (Key : forall u v, 0 < u < p -> 0 < v < p -> (a * u) mod p = (a * v) mod p -> u <= v -> u = v).
      { intros u v Hu Hv Euv Luv. destruct (N.eq_dec u v) as [|Nuv]; auto. exfalso.
        assert (D : (p | a * v - a * u)) by (apply mod_eq_div; [lia | auto | apply N.mul_le_mono_l; lia]).
        rewrite <- N.mul_sub_distr_l in D.
        destruct (primeN_mult p a (v - u) Hp D) as [D' | D']; [contradiction|].
        clear - D' Hu Hv Luv Nuv. apply N.divide_pos_le in D'; lia. }
      destruct (N.le_ge_cases i j); [apply Key | symmetry; apply Key]; auto.
    - intros y Hy. apply in_map_iff in Hy as [i [<- Hi]]. apply Hl. apply Hf; auto. }
  set (W := prod l).
  assert (HW : ~ (p | W)).
  { apply not_div_prod; auto. apply Forall_forall. intros; apply Hl; auto. }
  assert (E : W mod p = (a ^ (p - 1) * W) mod p).
  { unfold W. rewrite <- (prod_perm _ _ Perm) at 1. unfold f. rewrite prod_map_mod, prod_map_mul, Ll.
    reflexivity. }
  assert (Hap : 1 <= a ^ (p - 1)) by (apply pow_ge1; auto).
  apply mod1_div; auto.
  assert (D : (p | a ^ (p - 1) * W - W)).
  { apply mod_eq_div; [lia | auto |]. rewrite <- (N.mul_1_l W) at 1. apply N.mul_le_mono_r; lia. }
  replace (a ^ (p - 1) * W - W) with ((a ^ (p - 1) - 1) * W) in D by (rewrite N.mul_sub_distr_r; lia).
  destruct (primeN_mult p _ _ Hp D); auto. contradiction.
Qed.

(* Miller-Rabin soundness: the two witnesses of compositeness *)
Lemma mr_fermat : forall n a, primeN n -> 0 < a < n -> a ^ (n - 1) mod n = 1.
Proof.
  intros n a Hn Ha. apply fermat; auto. intro D. apply N.divide_pos_le in D; lia.
Qed.

Lemma mr_sqrt : forall n y, primeN n -> y < n -> (y * y) mod n = 1 -> y = 1 \/ y = n - 1.
Proof.
  intros n y Hn Hy E. pose proof (primeN_gt1 n Hn).
  destruct (N.eq_dec y 0) as [-> | Hy0]; [rewrite N.mul_0_l, N.Div0.mod_0_l in E; lia|].
  apply mod1_div in E; [| lia | nia].
  replace (y * y - 1) with ((y - 1) * (y + 1)) in E by nia.
  destruct (primeN_mult n _ _ Hn E) as [D | D].
  - destruct (N.eq_dec (y - 1) 0); [left; lia|]. apply N.divide_pos_le in D; lia.
  - apply N.divide_pos_le in D; lia.
Qed.

(* Pocklington's criterion *)
Definition has_base (n q : N) : Prop :=
  exists a, a ^ (n - 1) mod n = 1 /\ N.gcd (a ^ ((n - 1) / q) - 1) n = 1.

Lemma pock_factor : forall n F p, 1 < n -> (F | n - 1) -> 0 < F ->
  (forall q, primeN q -> (q | F) -> has_base n q) ->
  primeN p -> (p | n) -> (F | p - 1).
Proof.
  intros n F p Hn HF HF0 Hb Hp Hpn. pose proof (primeN_gt1 p Hp) as Hp1.
  apply div_of_vp; [exact HF0 | clear - Hp1; lia |].
  intros q Hq. set (k := vp q F).
  destruct (Nat.eq_dec k 0) as [K0 | K0]; [rewrite K0; apply Nat.le_0_l|].
  destruct (Nat.le_gt_cases k (vp q (p - 1))) as [L | L]; [exact L | exfalso].
  assert (HqF : (q | F)) by (apply vp_pos_div; auto; clear - K0; unfold k in K0; lia).
  destruct (Hb q Hq HqF) as [a [Ha1 Ha2]].
  pose proof (primeN_gt1 q Hq) as Hq1.
  assert (Hap : a ^ (n - 1) mod p = 1).
  { rewrite <- (mod_of_div p n); [| clear - Hn; lia | exact Hpn].
    rewrite Ha1. apply N.mod_small. exact Hp1. }
  assert (Hpa : ~ (p | a)).
  { intros D. assert (D' : (p | a ^ (n - 1))) by (apply div_pow; [auto | clear - Hn; lia]).
    apply N.Lcm0.mod_divide in D'. rewrite D' in Hap. discriminate. }
  pose proof (fermat p a Hp Hpa) as Hf.
  set (G := N.gcd (n - 1) (p - 1)).
  assert (HG : a ^ G mod p = 1) by (apply pow1_gcd; auto).
  destruct (N.divide_trans _ _ _ HqF HF) as [t Ht].
  assert (Ht0 : 0 < t) by (clear - Ht Hn; destruct (N.eq_dec t 0); [subst; lia | lia]).
  assert (Hdiv : (n - 1) / q = t) by (rewrite Ht; apply N.div_mul; clear - Hq1; lia).
  assert (HGpos : 0 < G) by (unfold G; rewrite N.gcd_comm; apply gcd_pos; clear - Hp1; lia).
  assert (Hn1 : 0 < n - 1) by (clear - Hn; lia).
  assert (Hp0 : 0 < p - 1) by (clear - Hp1; lia).
  assert (HGt : (G | t)).
  { apply div_of_vp; auto. intros r Hr.
    assert (V1 : (vp r G <= vp r (n - 1))%nat) by (apply vp_le_div; [auto | auto | auto | apply N.gcd_divide_l]).
    rewrite Ht, vp_mul in V1; auto; [| clear - Hq1; lia].
    destruct (N.eq_dec r q) as [-> | Nr].
    - rewrite vp_self in V1; auto.
      assert (V2 : (vp q G <= vp q (p - 1))%nat) by (apply vp_le_div; [auto | auto | auto | apply N.gcd_divide_r]).
      assert (V3 : (k <= vp q (n - 1))%nat) by (apply vp_le_div; auto).
      rewrite Ht, vp_mul, vp_self in V3; auto; [| clear - Hq1; lia].
      clear - V1 V2 V3 L. lia.
    - replace (vp r q) with O in V1; [clear - V1; lia|].
      symmetry. apply vp_not_div; [apply primeN_gt1; auto|].
      intro D. destruct Hq as [_ Hqd]. destruct (Hqd r D) as [E | E]; [| auto].
      pose proof (primeN_gt1 r Hr). clear - E H. lia. }
  destruct HGt as [s Hs].
  assert (Hat : a ^ t mod p = 1) by (rewrite Hs, N.mul_comm; apply pow1_mul; auto).
  assert (Hat1 : 1 <= a ^ t).
  { apply pow_ge1. intro; subst; apply Hpa; apply N.divide_0_r. }
  apply mod1_div in Hat; auto.
  rewrite Hdiv in Ha2.
  assert (D : (p | N.gcd (a ^ t - 1) n)) by (apply N.gcd_greatest; auto).
  rewrite Ha2 in D. exact (primeN_not_div1 p Hp D).
Qed.

Lemma pocklington : forall n F, 1 < n -> (F | n - 1) -> 0 < F ->
  (forall q, primeN q -> (q | F) -> has_base n q) -> n < F * F -> primeN n.
Proof.
  intros n F Hn HF HF0 Hb Hlt. split; auto.
  intros d Dd.
  assert (Hd0 : d <> 0) by (intro; subst; destruct Dd as [z Hz]; lia).
  destruct (N.eq_dec d 1) as [E | E]; [left; auto|].
  destruct (N.eq_dec d n) as [E' | E']; [right; auto|]. exfalso.
  destruct Dd as [e He].
  assert (He1 : 1 < e) by (destruct (N.eq_dec e 0); [subst; lia|]; destruct (N.eq_dec e 1); [subst; lia | lia]).
  assert (Hd1 : 1 < d) by lia.
  destruct (prime_divisor_exists d Hd1) as [p [Hp Dp]].
  destruct (prime_divisor_exists e He1) as [p' [Hp' Dp']].
  assert (A : (F | p - 1)) by (apply (pock_factor n); auto; rewrite He; apply N.divide_mul_r; auto).
  assert (B : (F | p' - 1)) by (apply (pock_factor n); auto; rewrite He; apply N.divide_mul_l; auto).
  pose proof (primeN_gt1 p Hp). pose proof (primeN_gt1 p' Hp').
  apply N.divide_pos_le in A; [| lia]. apply N.divide_pos_le in B; [| lia].
  apply N.divide_pos_le in Dp; [| lia]. apply N.divide_pos_le in Dp'; [| lia].
  nia.
Qed.

(* the numbers with no prime factor up to 10^6 *)
Definition B6 : N := 1000000.

Definition roughN (c : N) : Prop := forall p, primeN p -> (p | c) -> B6 < p.

Lemma rough_div : forall c d, roughN c -> (d | c) -> roughN d.
Proof. intros c d H D p Hp Dp. apply H; auto. eapply N.divide_trans; eauto. Qed.

Lemma rough_gt : forall c, roughN c -> 1 < c -> B6 < c.
Proof.
  intros c H Hc. destruct (prime_divisor_exists c Hc) as [p [Hp Dp]].
  pose proof (H p Hp Dp). apply N.divide_pos_le in Dp; lia.
Qed.

Lemma rough_prime : forall c, roughN c -> 1 < c -> c <= B6 * B6 -> primeN c.
Proof.
  intros c H Hc Hle. split; auto. intros d Dd.
  assert (Hd0 : d <> 0) by (intro; subst; destruct Dd as [z Hz]; lia).
  destruct (N.eq_dec d 1) as [E | E]; [left; auto|].
  destruct (N.eq_dec d c) as [E' | E']; [right; auto|]. exfalso.
  destruct Dd as [e He].
  assert (He1 : 1 < e) by (destruct (N.eq_dec e 0); [subst; lia|]; destruct (N.eq_dec e 1); [subst; lia | lia]).
  pose proof (rough_gt d (rough_div c d H ltac:(rewrite He; apply N.divide_factor_r)) ltac:(lia)).
  pose proof (rough_gt e (rough_div c e H ltac:(rewrite He; apply N.divide_factor_l)) He1).
  unfold B6 in *. nia.
Qed.

Lemma rough_semi : forall c, roughN c -> 1 < c -> c <= B6 * B6 * B6 -> ~ primeN c ->
  exists q r, c = q * r /\ primeN q /\ primeN r.
Proof.
  intros c H Hc Hle Hnp. destruct (prime_divisor_exists c Hc) as [q [Hq [r Hr]]].
  exists q, r. split; [lia|]. split; auto.
  pose proof (primeN_gt1 q Hq).
  assert (Hr1 : 1 < r).
  { destruct (N.eq_dec r 0); [subst; lia|]. destruct (N.eq_dec r 1); [| lia].
    subst. rewrite N.mul_1_l in Hnp. contradiction. }
  pose proof (H q Hq ltac:(rewrite Hr; apply N.divide_factor_r)).
  apply rough_prime; auto.
  - apply (rough_div c); auto. rewrite Hr; apply N.divide_factor_l.
  - unfold B6 in *. nia.
Qed.

Lemma rough_atomic : forall c x k c' p, roughN c -> 0 < c -> c <= B6 * B6 * B6 ->
  (x | c) -> c = x ^ k * c' -> ~ (x | c') -> primeN p -> (p | x) -> (p | c') -> False.
Proof.
  intros c x k c' p H Hc Hle Dx Hk Nx Hp Dpx Dpc.
  destruct (N.eq_dec k 0) as [-> | K0].
  - rewrite N.pow_0_r, N.mul_1_l in Hk. subst. contradiction.
  - destruct (N.eq_dec x p) as [-> | Nxp]; [contradiction|].
    destruct Dpx as [x' Hx'].
    assert (Hx0 : x <> 0) by (intro; subst; destruct Dx as [z Hz]; lia).
    assert (Hx'1 : 1 < x') by (destruct (N.eq_dec x' 0); [subst; lia|];
                                destruct (N.eq_dec x' 1); [subst; lia | lia]).
    assert (Rx' : B6 < x').
    { apply rough_gt; auto. apply (rough_div c); auto.
      eapply N.divide_trans; [| exact Dx]. rewrite Hx'. apply N.divide_factor_l. }
    pose proof (H p Hp ltac:(eapply N.divide_trans; [| exact Dx]; rewrite Hx'; apply N.divide_factor_r)).
    destruct Dpc as [c'' Hc''].
    assert (Hc''0 : c'' <> 0) by (intro; subst; lia).
    assert (Hxk : x <= x ^ k).
    { replace k with (N.succ (k - 1)) by lia. rewrite N.pow_succ_r'.
      pose proof (N.pow_nonzero x (k - 1) Hx0). nia. }
    unfold B6 in *. nia.
Qed.

(* the trial-division safety net *)
Lemma td_prime_crit : forall n, 1 < n ->
  (forall d, 1 < d -> d * d <= n -> ~ (d | n)) -> primeN n.
Proof.
  intros n Hn H. split; auto. intros d Dd.
  assert (Hd0 : d <> 0) by (intro; subst; destruct Dd as [z Hz]; lia).
  destruct (N.eq_dec d 1) as [E | E]; [left; auto|].
  destruct (N.eq_dec d n) as [E' | E']; [right; auto|]. exfalso.
  destruct Dd as [e He].
  assert (He1 : 1 < e) by (destruct (N.eq_dec e 0); [subst; lia|]; destruct (N.eq_dec e 1); [subst; lia | lia]).
  destruct (N.le_ge_cases d e).
  - apply (H d); [lia | nia | exists e; lia].
  - apply (H e); [lia | nia | exists d; lia].
Qed.

End Cert.

(* ================================================================== *)
(* Part 4. The count of one slot                                       *)
(* ================================================================== *)

(* the number of exponent tuples of one prime with e = l - g >= 1 *)
Definition fP (P : N) (e : Z) : Z :=
  ((e + 1) ^ Z.of_N P - 2 * e ^ Z.of_N P + (e - 1) ^ Z.of_N P)%Z.

Section Slot.
Local Open Scope N_scope.

Lemma vp_pow : forall p x k, primeN p -> 0 < x -> vp p (x ^ N.of_nat k) = (k * vp p x)%nat.
Proof.
  intros p x k Hp Hx. induction k as [| k IH].
  - simpl. apply vp_1; auto.
  - rewrite Nat2N.inj_succ, N.pow_succ_r', vp_mul, IH; auto.
    apply N.neq_0_lt_0, N.pow_nonzero. lia.
Qed.

Lemma pow_pos : forall x k, 0 < x -> 0 < x ^ k.
Proof. intros x k H. apply N.neq_0_lt_0, N.pow_nonzero. lia. Qed.

Lemma slot_zero : forall P x eg el, 1 <= P -> 1 < x -> (el < eg)%nat ->
  num_sequences P (x ^ N.of_nat eg) (x ^ N.of_nat el) 0.
Proof.
  intros P x eg el HP Hx H. apply count_zero; auto. intro D.
  apply N.divide_pos_le in D; [| apply pow_pos; lia].
  assert (x ^ N.of_nat el < x ^ N.of_nat eg) by (apply N.pow_lt_mono_r; lia). lia.
Qed.

Lemma slot_eq : forall P x e, 1 <= P -> 1 < x ->
  num_sequences P (x ^ N.of_nat e) (x ^ N.of_nat e) 1.
Proof. intros P x e HP Hx. apply count_eq; auto. apply pow_pos; lia. Qed.

Lemma slot_prime : forall P x eg el, 1 <= P -> primeN x -> (eg < el)%nat ->
  exists c, num_sequences P (x ^ N.of_nat eg) (x ^ N.of_nat el) c /\
            Z.of_N c = fP P (Z.of_nat (el - eg)).
Proof. intros. apply count_pp; auto. Qed.

Lemma pow_sq : forall s k, (s * s) ^ N.of_nat k = s ^ N.of_nat (2 * k).
Proof.
  intros s k. rewrite N.pow_mul_l, <- N.pow_add_r. f_equal. lia.
Qed.

Lemma slot_square : forall P x s eg el, 1 <= P -> x = s * s -> primeN s -> (eg < el)%nat ->
  exists c, num_sequences P (x ^ N.of_nat eg) (x ^ N.of_nat el) c /\
            Z.of_N c = fP P (2 * Z.of_nat (el - eg))%Z.
Proof.
  intros P x s eg el HP -> Hs H. rewrite !pow_sq.
  destruct (count_pp s (2 * eg) (2 * el) P Hs ltac:(lia) HP) as [c [C1 C2]].
  exists c. split; auto. rewrite C2. unfold fP.
  replace (Z.of_nat (2 * el - 2 * eg)) with (2 * Z.of_nat (el - eg))%Z by lia. reflexivity.
Qed.

Lemma slot_semi : forall P x q r eg el, 1 <= P -> x = q * r -> primeN q -> primeN r -> q <> r ->
  (eg < el)%nat ->
  exists c, num_sequences P (x ^ N.of_nat eg) (x ^ N.of_nat el) c /\
            Z.of_N c = (fP P (Z.of_nat (el - eg)) * fP P (Z.of_nat (el - eg)))%Z.
Proof.
  intros P x q r eg el HP -> Hq Hr Nqr H.
  destruct (count_pp q eg el P Hq H HP) as [c1 [C1 E1]].
  destruct (count_pp r eg el P Hr H HP) as [c2 [C2 E2]].
  exists (c1 * c2). rewrite !N.pow_mul_l. split.
  - pose proof (primeN_gt1 q Hq). pose proof (primeN_gt1 r Hr).
    apply count_mul; auto; try (apply pow_pos; lia).
    intros p Hp. destruct (N.eq_dec p q) as [-> | Np].
    + right. split; apply vp_pow_other; auto.
    + left. split; apply vp_pow_other; auto.
  - rewrite N2Z.inj_mul, E1, E2. reflexivity.
Qed.

End Slot.

(* ================================================================== *)
(* Part 6. Specifications of the primitives                            *)
(* ================================================================== *)

Section Prim.
Local Open Scope uint63_scope.
Local Open Scope Z_scope.

Lemma wB_val : wB = 9223372036854775808.
Proof. reflexivity. Qed.

Lemma bz : forall x : int, 0 <= (φ x) < wB.
Proof. exact to_Z_bounded. Qed.

Lemma ltb_Z : forall x y : int, (x <? y)%uint63 = ((φ x) <? (φ y)).
Proof. intros. apply ltb_lt. Qed.
Lemma leb_Z : forall x y : int, (x <=? y)%uint63 = ((φ x) <=? (φ y)).
Proof. intros. apply leb_le. Qed.
Lemma eqb_Z : forall x y : int, (x =? y)%uint63 = ((φ x) =? (φ y)).
Proof. intros. apply eqb_eq. Qed.

Lemma mulmod_spec : forall a b n, 0 < (φ n) -> (φ a) < (φ n) -> (φ b) < (φ n) ->
  (φ (mulmod a b n)) = (φ a) * (φ b) mod (φ n).
Proof.
  intros a b n Hn Ha Hb. unfold mulmod.
  pose proof (mulc_spec a b) as M. destruct (mulc a b) as [h l]. simpl in M.
  pose proof (diveucl_21_spec h l n) as D. destruct (diveucl_21 h l n) as [q r].
  destruct (Z.div_eucl ((φ h) * wB + (φ l)) (φ n)) as [q' r'] eqn:E.
  pose proof (bz a). pose proof (bz b). pose proof (bz h). pose proof (bz l). pose proof (bz n).
  assert (Hh : (φ h) < (φ n)).
  { assert ((φ a) * (φ b) < (φ n) * (φ n)) by nia.
    assert ((φ h) * wB < (φ n) * wB) by nia.
    apply Z.mul_lt_mono_pos_r with wB; lia. }
  destruct (D Hh) as [_ Hr]. simpl. rewrite Hr, M. unfold Z.modulo. rewrite E. reflexivity.
Qed.

Lemma Zpow_mod : forall a k n, 0 <= k -> (a ^ k) mod n = ((a mod n) ^ k) mod n.
Proof.
  intros a k n Hk. pattern k. apply natlike_ind; [reflexivity | | exact Hk].
  intros x Hx IH. rewrite !Z.pow_succ_r by auto. rewrite Zmult_mod, IH, <- Zmult_mod.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Lemma pow_step_arith : forall r b e n, 0 <= e ->
  ((r * b ^ (e mod 2)) mod n * ((b * b) mod n) ^ (e / 2)) mod n = (r * b ^ e) mod n.
Proof.
  intros r b e n He.
  assert (0 <= e / 2) by (apply Z.div_pos; lia).
  assert (0 <= e mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite Zmult_mod_idemp_l.
  rewrite <- Zmult_mod_idemp_r. rewrite <- Zpow_mod by auto. rewrite Zmult_mod_idemp_r.
  f_equal.
  assert (E : b ^ e = (b * b) ^ (e / 2) * b ^ (e mod 2)).
  { set (q := e / 2) in *. set (m := e mod 2) in *.
    assert (Ee : e = 2 * q + m) by (apply Z.div_mod; lia).
    rewrite Ee at 1. rewrite Z.pow_add_r, Z.pow_mul_r by lia. rewrite Z.pow_2_r. reflexivity. }
  rewrite E. ring.
Qed.

Lemma land1 : forall e : int, (φ (e land 1))%uint63 = (φ e) mod 2.
Proof.
  intros e. rewrite land_spec'. replace ((φ 1)%uint63) with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma pow_loop_spec : forall z b e r n (H : Acc (Zwf 0) (φ e)), (φ e) = z ->
  1 < (φ n) -> (φ b) < (φ n) -> (φ r) < (φ n) ->
  (φ (pow_loop b e r n H)) = ((φ r) * (φ b) ^ (φ e)) mod (φ n).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros b e r n H Hz Hn Hb Hr. destruct H as [H']. simpl.
  destruct (bdec (0 <? e)%uint63) as [He | He].
  - pose proof He as He'. rewrite ltb_Z in He'. apply Z.ltb_lt in He'. change ((φ 0)%uint63) with 0 in He'.
    pose proof (bz b). pose proof (bz r). pose proof (bz e).
    assert (Hb2 : (φ (mulmod b b n)) = (φ b) * (φ b) mod (φ n)) by (apply mulmod_spec; lia).
    set (r' := if (e land 1 =? 1)%uint63 then mulmod r b n else r).
    assert (Hr' : (φ r') = ((φ r) * (φ b) ^ ((φ e) mod 2)) mod (φ n) /\ (φ r') < (φ n)).
    { unfold r'. rewrite eqb_Z, land1. change ((φ 1)%uint63) with 1.
      assert (M2 : 0 <= (φ e) mod 2 < 2) by (apply Z.mod_pos_bound; lia).
      destruct (Z.eqb_spec ((φ e) mod 2) 1) as [E | E].
      - rewrite mulmod_spec by lia. rewrite E, Z.pow_1_r. split; [reflexivity|].
        apply Z.mod_pos_bound; lia.
      - replace ((φ e) mod 2) with 0 by lia. rewrite Z.pow_0_r, Z.mul_1_r, Z.mod_small by lia. lia. }
    destruct Hr' as [Hr1 Hr2].
    rewrite (IH ((φ (e >> 1))%uint63)); auto.
    + rewrite Hr1, Hb2, lsr1. apply pow_step_arith. lia.
    + rewrite <- Hz. apply dec_shr; auto.
    + rewrite Hb2. apply Z.mod_pos_bound; lia.
  - rewrite ltb_Z in He. apply Z.ltb_ge in He. change ((φ 0)%uint63) with 0 in He.
    pose proof (bz e). replace (φ e) with 0 by lia. rewrite Z.pow_0_r, Z.mul_1_r.
    rewrite Z.mod_small; [reflexivity|]. pose proof (bz r). lia.
Qed.

Lemma powmod_spec : forall b e n, 1 < (φ n) -> (φ (powmod b e n)) = ((φ b) ^ (φ e)) mod (φ n).
Proof.
  intros b e n Hn. unfold powmod. rewrite (pow_loop_spec (φ e)); auto.
  - rewrite !mod_spec. change ((φ 1)%uint63) with 1.
    rewrite (Z.mod_small 1) by lia. rewrite Z.mul_1_l. rewrite <- Zpow_mod; [reflexivity | apply bz].
  - rewrite mod_spec. apply Z.mod_pos_bound. lia.
  - rewrite mod_spec. apply Z.mod_pos_bound. lia.
Qed.

Lemma gcd_loop_spec : forall z a b (H : Acc (Zwf 0) (φ b)), (φ b) = z ->
  (φ (gcd_loop a b H)) = Z.gcd (φ a) (φ b).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a b H Hz. destruct H as [H']. simpl.
  destruct (bdec (0 <? b)%uint63) as [Hb | Hb].
  - pose proof Hb as Hb'. rewrite ltb_Z in Hb'. apply Z.ltb_lt in Hb'. change ((φ 0)%uint63) with 0 in Hb'.
    rewrite (IH ((φ (a mod b))%uint63)); auto.
    + rewrite mod_spec. rewrite Z.gcd_comm, Z.gcd_mod by lia. apply Z.gcd_comm.
    + rewrite <- Hz. apply dec_mod; auto.
  - rewrite ltb_Z in Hb. apply Z.ltb_ge in Hb. change ((φ 0)%uint63) with 0 in Hb.
    pose proof (bz b). replace (φ b) with 0 by lia. rewrite Z.gcd_0_r.
    symmetry. apply Z.abs_eq. apply bz.
Qed.

Lemma igcd_spec : forall a b, (φ (igcd a b)) = Z.gcd (φ a) (φ b).
Proof. intros. unfold igcd. apply (gcd_loop_spec (φ b)). reflexivity. Qed.

Lemma isq_loop_spec : forall z x s w (H : Acc (Zwf 0) (φ w)), (φ w) = z ->
  (φ s) * (φ s) <= (φ x) -> (φ x) < ((φ s) + (φ w)) * ((φ s) + (φ w)) -> 1 <= (φ w) -> (φ s) + (φ w) <= 2147483648 ->
  let s' := isq_loop x s w H in (φ s') * (φ s') <= (φ x) < ((φ s') + 1) * ((φ s') + 1).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x s w H Hz H1 H2 H3 H4. destruct H as [H']. simpl.
  destruct (bdec (1 <? w)%uint63) as [Hw | Hw].
  - pose proof Hw as Hw'. rewrite ltb_Z in Hw'. apply Z.ltb_lt in Hw'. change ((φ 1)%uint63) with 1 in Hw'.
    pose proof (bz s). pose proof (bz w). pose proof (bz x).
    assert (Hb : (φ (w >> 1))%uint63 = (φ w) / 2) by apply lsr1.
    assert (Hb1 : 1 <= (φ w) / 2) by (apply Z.div_le_lower_bound; lia).
    assert (Hb2 : 2 * ((φ w) / 2) <= (φ w)) by (apply Z.mul_div_le; lia).
    assert (Ht : (φ (s + (w >> 1)))%uint63 = (φ s) + (φ w) / 2) by (rewrite add_spec, Hb; rewrite Z.mod_small; lia).
    assert (Htt : (φ ((s + (w >> 1)) * (s + (w >> 1))))%uint63 = ((φ s) + (φ w) / 2) * ((φ s) + (φ w) / 2)).
    { rewrite mul_spec, Ht. rewrite Z.mod_small; [reflexivity|]. rewrite wB_val.
      assert (Q : ((φ s) + (φ w) / 2) * ((φ s) + (φ w) / 2) <= 2147483648 * 2147483648)
        by (apply Z.mul_le_mono_nonneg; lia).
      split; [apply Z.mul_nonneg_nonneg; lia | lia]. }
    rewrite leb_Z, Htt. destruct (Z.leb_spec (((φ s) + (φ w) / 2) * ((φ s) + (φ w) / 2)) (φ x)) as [L | L].
    + apply (IH ((φ (w - (w >> 1)))%uint63)); auto.
      * rewrite <- Hz. apply dec_isq1; auto.
      * rewrite Ht. exact L.
      * rewrite Ht, sub_spec, Hb, Z.mod_small by lia. replace ((φ s) + (φ w) / 2 + ((φ w) - (φ w) / 2)) with ((φ s) + (φ w)) by lia. exact H2.
      * rewrite sub_spec, Hb, Z.mod_small by lia. lia.
      * rewrite Ht, sub_spec, Hb, Z.mod_small by lia. lia.
    + apply (IH ((φ (w >> 1))%uint63)); auto.
      * rewrite <- Hz. apply dec_isq2; auto.
      * rewrite Hb. exact L.
      * rewrite Hb. lia.
      * rewrite Hb. lia.
  - rewrite ltb_Z in Hw. apply Z.ltb_ge in Hw. change ((φ 1)%uint63) with 1 in Hw.
    replace (φ w) with 1 in H2 by lia. lia.
Qed.

Lemma isqrt_spec : forall x, (φ x) < 4611686018427387904 ->
  (φ (isqrt x)) * (φ (isqrt x)) <= (φ x) < ((φ (isqrt x)) + 1) * ((φ (isqrt x)) + 1).
Proof.
  intros x Hx. unfold isqrt. apply (isq_loop_spec ((φ 2147483648)%uint63)); auto;
    change ((φ 0)%uint63) with 0; change ((φ 2147483648)%uint63) with 2147483648; pose proof (bz x); lia.
Qed.

Lemma divfull_spec : forall z x c k Hx (H : Acc (Zwf 0) (φ c)), (φ c) = z ->
  0 < (φ c) -> (φ k) + (φ c) < wB ->
  exists j, 0 <= j /\ (φ (snd (divfull x c k Hx H))) = (φ k) + j /\
    (φ c) = (φ x) ^ j * (φ (fst (divfull x c k Hx H))) /\
    ~ ((φ x) | (φ (fst (divfull x c k Hx H)))) /\ 0 < (φ (fst (divfull x c k Hx H))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x c k Hx H Hz Hc Hkc. destruct H as [H']. simpl.
  pose proof Hx as Hx'. rewrite ltb_Z in Hx'. apply Z.ltb_lt in Hx'. change ((φ 1)%uint63) with 1 in Hx'.
  pose proof (bz c). pose proof (bz k). pose proof (bz x).
  destruct (bdec (0 <? c)%uint63) as [Hc' | Hc'].
  - rewrite eqb_Z, mod_spec. change ((φ 0)%uint63) with 0.
    destruct (Z.eqb_spec ((φ c) mod (φ x)) 0) as [E | E].
    + assert (Hd : (φ c) = (φ x) * ((φ c) / (φ x))) by (apply Z_div_exact_full_2; lia).
      assert (Hcx : (φ (c / x))%uint63 = (φ c) / (φ x)) by apply div_spec.
      assert (Hxc : (φ x) <= (φ c)) by (apply Z.divide_pos_le; [lia | apply Z.mod_divide; lia]).
      assert (Hq : 0 < (φ c) / (φ x)) by (apply Z.div_str_pos; lia).
      assert (Hq2 : (φ c) / (φ x) < (φ c)) by (apply Z.div_lt; lia).
      assert (Hk1 : (φ (k + 1))%uint63 = (φ k) + 1) by (rewrite add_spec; change ((φ 1)%uint63) with 1; rewrite Z.mod_small; lia).
      destruct (IH ((φ (c / x))%uint63) ltac:(rewrite <- Hz; apply dec_div; auto) x (c / x)%uint63 (k + 1)%uint63 Hx
                  (H' _ (dec_div x c Hx Hc')) eq_refl ltac:(lia) ltac:(lia))
        as [j [J1 [J2 [J3 [J4 J5]]]]].
      exists (j + 1). split; [lia|]. split; [rewrite J2, Hk1; lia|]. split; [| split; auto].
      rewrite Hd at 1. rewrite <- Hcx. rewrite J3 at 1. rewrite Z.pow_add_r, Z.pow_1_r by lia. ring.
    + exists 0. cbn [fst snd]. rewrite Z.pow_0_r, Z.mul_1_l. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [| lia].
      intro D. apply E. apply Z.mod_divide; auto; lia.
  - rewrite ltb_Z in Hc'. apply Z.ltb_ge in Hc'. change ((φ 0)%uint63) with 0 in Hc'. lia.
Qed.

End Prim.

(* ================================================================== *)
(* Part 7. The N view of machine words; the sieve                      *)
(* ================================================================== *)

Section Sieve.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Definition nv (x : int) : N := Z.to_N (φ x).

Lemma nv_Z : forall x, Z.of_N (nv x) = (φ x).
Proof. intros x. unfold nv. rewrite Z2N.id; [reflexivity | apply bz]. Qed.

Lemma nv_inj : forall x y, nv x = nv y -> x = y.
Proof. intros x y H. apply to_Z_inj. rewrite <- !nv_Z, H. reflexivity. Qed.

Lemma nv_lt_wB : forall x, (Z.of_N (nv x) < wB)%Z.
Proof. intros x. rewrite nv_Z. apply bz. Qed.

Lemma divide_NZ : forall a b : N, (a | b) <-> (Z.of_N a | Z.of_N b)%Z.
Proof.
  intros a b. split.
  - intros [k Hk]. exists (Z.of_N k). rewrite Hk, N2Z.inj_mul. reflexivity.
  - intros [k Hk]. destruct (N.eq_dec a 0) as [-> | Ha].
    + simpl in Hk. rewrite Z.mul_0_r in Hk. assert (b = 0) by lia. subst. apply N.divide_0_r.
    + exists (Z.to_N k). assert (0 <= k)%Z by nia. lia.
Qed.

Lemma N2Z_gcd : forall a b, Z.of_N (N.gcd a b) = Z.gcd (Z.of_N a) (Z.of_N b).
Proof.
  intros a b. symmetry. apply Z.gcd_unique; [lia | apply divide_NZ, N.gcd_divide_l | apply divide_NZ, N.gcd_divide_r |].
  intros d Da Db. apply Z.divide_abs_l. rewrite <- (Z2N.id (Z.abs d)) by lia.
  apply divide_NZ, N.gcd_greatest; apply divide_NZ; rewrite Z2N.id by lia; apply Z.divide_abs_l; auto.
Qed.

Lemma nv_gcd : forall a b, nv (igcd a b) = N.gcd (nv a) (nv b).
Proof. intros a b. apply N2Z.inj. rewrite nv_Z, igcd_spec, N2Z_gcd, !nv_Z. reflexivity. Qed.

Lemma nv_mulmod : forall a b n, 0 < nv n -> nv a < nv n -> nv b < nv n ->
  nv (mulmod a b n) = (nv a * nv b) mod nv n.
Proof.
  intros a b n Hn Ha Hb. apply N2Z.inj. rewrite nv_Z, N2Z.inj_mod, N2Z.inj_mul, !nv_Z.
  apply mulmod_spec; rewrite <- !nv_Z; lia.
Qed.

Lemma nv_powmod : forall b e n, 1 < nv n -> nv (powmod b e n) = (nv b ^ nv e) mod nv n.
Proof.
  intros b e n Hn. apply N2Z.inj. rewrite nv_Z, N2Z.inj_mod, N2Z.inj_pow, !nv_Z.
  apply powmod_spec. rewrite <- nv_Z. lia.
Qed.

Lemma nv_ltb : forall x y, (x <? y)%uint63 = (nv x <? nv y)%N.
Proof.
  intros x y. rewrite ltb_Z. destruct (Z.ltb_spec (φ x) (φ y)), (N.ltb_spec (nv x) (nv y));
    auto; rewrite <- !nv_Z in *; lia.
Qed.

Lemma nv_leb : forall x y, (x <=? y)%uint63 = (nv x <=? nv y)%N.
Proof.
  intros x y. rewrite leb_Z. destruct (Z.leb_spec (φ x) (φ y)), (N.leb_spec (nv x) (nv y));
    auto; rewrite <- !nv_Z in *; lia.
Qed.

Lemma nv_eqb : forall x y, (x =? y)%uint63 = (nv x =? nv y)%N.
Proof.
  intros x y. rewrite eqb_Z. destruct (Z.eqb_spec (φ x) (φ y)), (N.eqb_spec (nv x) (nv y));
    auto; rewrite <- !nv_Z in *; lia.
Qed.

Lemma nv_add : forall x y, (Z.of_N (nv x + nv y) < wB)%Z -> nv (x + y)%uint63 = nv x + nv y.
Proof.
  intros x y H. apply N2Z.inj. rewrite nv_Z, add_spec, <- !nv_Z. rewrite Z.mod_small; lia.
Qed.

Lemma nv_sub : forall x y, nv y <= nv x -> nv (x - y)%uint63 = nv x - nv y.
Proof.
  intros x y H. apply N2Z.inj. rewrite nv_Z, sub_spec, <- !nv_Z. pose proof (nv_lt_wB x).
  rewrite Z.mod_small; lia.
Qed.

Lemma nv_mul : forall x y, (Z.of_N (nv x * nv y) < wB)%Z -> nv (x * y)%uint63 = nv x * nv y.
Proof.
  intros x y H. apply N2Z.inj. rewrite nv_Z, mul_spec, <- !nv_Z. rewrite Z.mod_small; lia.
Qed.

Lemma nv_div : forall x y, nv (x / y)%uint63 = nv x / nv y.
Proof. intros x y. apply N2Z.inj. rewrite nv_Z, div_spec, N2Z.inj_div, !nv_Z. reflexivity. Qed.

Lemma nv_mod : forall x y, nv (x mod y)%uint63 = (nv x mod nv y).
Proof. intros x y. apply N2Z.inj. rewrite nv_Z, mod_spec, N2Z.inj_mod, !nv_Z. reflexivity. Qed.

Lemma nv_lit : forall z : Z, (0 <= z < wB)%Z -> nv (of_Z z) = Z.to_N z.
Proof. intros z H. unfold nv. rewrite of_Z_spec, Z.mod_small; auto. Qed.

(* monomorphic views of the PArray axioms *)
Lemma bget_set_same : forall (t : array bool) i b, (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.
Lemma bget_set_other : forall (t : array bool) i j b, i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.
Lemma blength_set : forall (t : array bool) i b, PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.
Lemma bget_make : forall n (b : bool) t, (PArray.make n b).[t] = b.
Proof. intros n b t. exact (get_make bool b n t). Qed.
Lemma iget_set_same : forall (t : array int) i b, (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.
Lemma iget_set_other : forall (t : array int) i j b, i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.
Lemma ilength_set : forall (t : array int) i b, PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.
Lemma ilength_bound : forall (t : array int), (nv (PArray.length t) <= 4194303)%N.
Proof.
  intros t. pose proof (leb_length int t) as H. rewrite leb_Z in H. apply Z.leb_le in H.
  unfold nv. change (φ PArray.max_length) with 4194303%Z in H. pose proof (bz (PArray.length t)).
  apply N2Z.inj_le. rewrite Z2N.id by lia. simpl. exact H.
Qed.

(* the sieve *)
Definition sieve_ok (pr : array int) (np : int) : Prop :=
  nv np <= 1000000 /\ PArray.length pr = LIM /\
  (forall k, nv k < nv np -> primeN (nv pr.[k]) /\ nv pr.[k] < 1000000) /\
  (forall p, primeN p -> p < 1000000 -> exists k, nv k < nv np /\ nv pr.[k] = p).

Lemma nvLIM : nv LIM = 1000000.
Proof. reflexivity. Qed.

Lemma prime_ge2 : forall p, primeN p -> 2 <= p.
Proof. intros p Hp. pose proof (primeN_gt1 p Hp). lia. Qed.

Lemma mark_loop_spec : forall z m i j Hi (H : Acc (Zwf 0) (gap LIM j)), gap LIM j = z ->
  PArray.length m = LIM -> (nv i | nv j) ->
  PArray.length (mark_loop m i j Hi H) = LIM /\
  forall t, nv t < 1000000 ->
    ((mark_loop m i j Hi H).[t] = true <-> m.[t] = true \/ ((nv i | nv t) /\ nv j <= nv t)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros m i j Hi H Hz Hm Dj. destruct H as [H']. simpl.
  pose proof Hi as Hi'. apply Bool.andb_true_iff in Hi' as [Hi1 Hi2]. rewrite nv_ltb in Hi1, Hi2.
  apply N.ltb_lt in Hi1, Hi2. rewrite nvLIM in Hi2. change (nv 0%uint63) with 0 in Hi1.
  destruct (bdec (j <? LIM)%uint63) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite nv_ltb, nvLIM in Hj'. apply N.ltb_lt in Hj'.
    assert (Hji : nv (j + i)%uint63 = nv j + nv i) by (apply nv_add; rewrite wB_val; lia).
    assert (Hlen : PArray.length m.[j <- true] = LIM) by (rewrite blength_set; auto).
    destruct (IH _ (eq_ind _ (fun w => Zwf 0 (gap LIM (j + i)%uint63) w) (dec_add i j Hi Hj) _ Hz)
                m.[j <- true] i (j + i)%uint63 Hi (H' _ (dec_add i j Hi Hj)) eq_refl Hlen) as [L1 L2].
    { rewrite Hji. apply N.divide_add_r; auto. apply N.divide_refl. }
    split; auto. intros t Ht. rewrite L2 by auto. rewrite Hji.
    destruct (N.eq_dec (nv t) (nv j)) as [E | E].
    + apply nv_inj in E. subst t.
      assert (G : m.[j <- true].[j] = true).
      { apply bget_set_same. rewrite Hm. exact Hj. }
      rewrite G.
      split; [intros _; right; split; [auto | lia] | intros _; left; reflexivity].
    + assert (G : m.[j <- true].[t] = m.[t]) by (apply bget_set_other; intro F; apply E; subst; reflexivity).
      rewrite G. split.
      * intros [A | [A1 A2]]; [left; auto | right; split; [auto | lia]].
      * intros [A | [A1 A2]]; [left; auto | right; split; auto].
        destruct A1 as [u Hu]. destruct Dj as [v Hv].
        assert (v < u) by (assert (nv j < nv t) by lia; nia).
        rewrite Hu, Hv. nia.
  - rewrite nv_ltb, nvLIM in Hj. apply N.ltb_ge in Hj. split; auto.
    intros t Ht. split; [intros A; left; auto | intros [A | [_ A]]; [auto | lia]].
Qed.

Lemma nv_succ : forall i, nv i < 1000000 -> nv (i + 1)%uint63 = nv i + 1.
Proof. intros i H. apply nv_add. change (nv 1%uint63) with 1. rewrite wB_val. lia. Qed.

Lemma sieve_loop_spec : forall z m pr np i (H : Acc (Zwf 0) (gap LIM i)), gap LIM i = z ->
  PArray.length m = LIM -> PArray.length pr = LIM -> 2 <= nv i <= 1000000 -> nv np <= nv i ->
  (forall t, nv t < 1000000 ->
     (m.[t] = true <-> exists p, primeN p /\ p < nv i /\ (p | nv t) /\ p < nv t)) ->
  (forall k, nv k < nv np -> primeN (nv pr.[k]) /\ nv pr.[k] < nv i) ->
  (forall p, primeN p -> p < nv i -> exists k, nv k < nv np /\ nv pr.[k] = p) ->
  sieve_ok (fst (sieve_loop m pr np i H)) (snd (sieve_loop m pr np i H)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros m pr np i H Hz Lm Lpr Hi Hnp S3 S4 S5. destruct H as [H']. simpl.
  destruct (bdec (i <? LIM)%uint63) as [HiL | HiL].
  - pose proof HiL as HiL'. rewrite nv_ltb, nvLIM in HiL'. apply N.ltb_lt in HiL'.
    pose proof (nv_succ i HiL') as Hs.
    assert (Hdec : Zwf 0 (gap LIM (i + 1)) z) by (rewrite <- Hz; apply dec_step; auto).
    destruct (m.[i]) eqn:Mi.
    + apply (IH _ Hdec); auto; rewrite ?Hs; try lia.
      * intros t Ht. rewrite S3 by auto. split.
        { intros [p [P1 [P2 [P3 P4]]]]. exists p. split; [exact P1|]. split; [lia | split; auto]. }
        intros [p [P1 [P2 [P3 P4]]]]. exists p. split; [exact P1|]. split; [| split; auto].
        destruct (N.eq_dec p (nv i)) as [E | E]; [| lia]. exfalso.
        apply S3 in Mi; [| lia]. destruct Mi as [q [Q1 [Q2 [Q3 Q4]]]].
        rewrite <- E in Q3. destruct P1 as [_ Pd]. destruct (Pd q Q3) as [F | F];
          [pose proof (primeN_gt1 q Q1); lia | lia].
      * intros k Hk. destruct (S4 k Hk). split; auto. lia.
      * intros p Hp Hpi. destruct (N.eq_dec p (nv i)) as [E | E]; [| apply S5; auto; lia].
        exfalso. apply S3 in Mi; [| lia]. destruct Mi as [q [Q1 [Q2 [Q3 Q4]]]].
        rewrite <- E in Q3. destruct Hp as [_ Pd]. destruct (Pd q Q3) as [F | F];
          [pose proof (primeN_gt1 q Q1); lia | lia].
    + assert (Pi : primeN (nv i)).
      { split; [lia|]. intros d Dd.
        assert (Hd0 : d <> 0) by (intro; subst; destruct Dd as [u Hu]; lia).
        destruct (N.eq_dec d 1) as [E | E]; [left; auto|].
        destruct (N.eq_dec d (nv i)) as [E' | E']; [right; auto|]. exfalso.
        assert (Hdi : d < nv i) by (apply N.divide_pos_le in Dd; lia).
        destruct (prime_divisor_exists d ltac:(lia)) as [q [Q1 Q2]].
        assert (Q3 : q <= d) by (apply N.divide_pos_le in Q2; lia).
        assert (m.[i] = true) by (apply S3; [lia | exists q; split; [exact Q1|]; split; [lia|]; split; [eapply N.divide_trans; eauto | lia]]).
        congruence. }
      destruct (bdec ((0 <? i)%uint63 && (i <? LIM)%uint63)) as [Hi' | Hi'].
      2: { exfalso. rewrite nv_ltb, nv_ltb, nvLIM in Hi'. change (nv 0%uint63) with 0 in Hi'.
           apply Bool.andb_false_iff in Hi' as [F | F]; apply N.ltb_ge in F; lia. }
      assert (Hii : nv (i + i)%uint63 = nv i + nv i) by (apply nv_add; rewrite wB_val; lia).
      destruct (mark_loop_spec _ m i (i + i)%uint63 Hi' (Zwf_well_founded 0 _) eq_refl Lm)
        as [ML1 ML2].
      { rewrite Hii. exists 2. ring. }
      assert (Hnp1 : nv (np + 1)%uint63 = nv np + 1) by (apply nv_succ; lia).
      assert (Hnpl : (np <? PArray.length pr)%uint63 = true) by (rewrite Lpr, nv_ltb, nvLIM; apply N.ltb_lt; lia).
      apply (IH _ Hdec); auto; rewrite ?Hs, ?Hnp1; try lia.
      * rewrite ilength_set. auto.
      * intros t Ht. rewrite ML2 by auto. rewrite Hii, S3 by auto. split.
        -- intros [[p [P1 [P2 [P3 P4]]]] | [A1 A2]]; [exists p; split; [exact P1|]; split; [lia | split; auto]|].
           exists (nv i). split; [exact Pi|]. split; [lia | split; [auto | lia]].
        -- intros [p [P1 [P2 [P3 P4]]]]. destruct (N.eq_dec p (nv i)) as [E | E].
           ++ right. subst p. split; auto. destruct P3 as [u Hu].
              assert (2 <= u) by (destruct (N.eq_dec u 0); [subst; lia|]; destruct (N.eq_dec u 1); [subst; lia | lia]).
              rewrite Hu. nia.
           ++ left. exists p. split; [exact P1|]. split; [lia | split; auto].
      * intros k Hk. destruct (N.eq_dec (nv k) (nv np)) as [E | E].
        -- apply nv_inj in E. subst k. rewrite iget_set_same by auto. split; auto. lia.
        -- rewrite iget_set_other by (intro F; apply E; subst; reflexivity).
           destruct (S4 k ltac:(lia)). split; auto. lia.
      * intros p Hp Hpi. destruct (N.eq_dec p (nv i)) as [E | E].
        -- exists np. split; [lia|]. rewrite iget_set_same by auto. auto.
        -- destruct (S5 p Hp ltac:(lia)) as [k [K1 K2]]. exists k. split; [lia|].
           rewrite iget_set_other by (intro F; subst; lia). auto.
  - rewrite nv_ltb, nvLIM in HiL. apply N.ltb_ge in HiL.
    cbn [fst snd]. split; [lia|]. split; [exact Lpr|]. split.
    + intros k Hk. destruct (S4 k Hk). split; auto. lia.
    + intros p Hp Hpi. apply S5; auto. lia.
Qed.

Lemma sieve_spec : sieve_ok (fst sieve) (snd sieve).
Proof.
  unfold sieve. apply (sieve_loop_spec _ _ _ _ _ _ eq_refl).
  - reflexivity.
  - reflexivity.
  - change (nv 2%uint63) with 2. lia.
  - change (nv 0%uint63) with 0. lia.
  - intros t Ht. rewrite bget_make. split; [discriminate|]. intros [p [P1 [P2 _]]].
    change (nv 2%uint63) with 2 in P2. pose proof (primeN_gt1 p P1). lia.
  - intros k Hk. change (nv 0%uint63) with 0 in Hk. lia.
  - intros p Hp Hpi. change (nv 2%uint63) with 2 in Hpi. pose proof (primeN_gt1 p Hp). lia.
Qed.

End Sieve.

(* ================================================================== *)
(* Part 8. Specifications of the certificate code                      *)
(* ================================================================== *)

Section CertCode.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Lemma nv_bound : forall x, (Z.of_N (nv x) < wB)%Z.
Proof. exact nv_lt_wB. Qed.

Lemma nv_lsr1 : forall d, nv (d >> 1)%uint63 = nv d / 2.
Proof. intros d. apply N2Z.inj. rewrite nv_Z, lsr1, N2Z.inj_div, nv_Z. reflexivity. Qed.

Lemma nv_land1 : forall d, nv (d land 1)%uint63 = nv d mod 2.
Proof. intros d. apply N2Z.inj. rewrite nv_Z, land1, N2Z.inj_mod, nv_Z. reflexivity. Qed.

Lemma strip2_spec : forall z d s (H : Acc (Zwf 0) (φ d)), (φ d) = z ->
  (Z.of_N (nv s + nv d) < wB)%Z ->
  nv s <= nv (snd (strip2 d s H)) /\
  nv d = 2 ^ (nv (snd (strip2 d s H)) - nv s) * nv (fst (strip2 d s H)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d s H Hz Hb. destruct H as [H']. simpl.
  destruct (bdec ((0 <? d)%uint63 && (d land 1 =? 0)%uint63)) as [Hd | Hd].
  - pose proof Hd as Hd'. apply Bool.andb_true_iff in Hd' as [D1 D2].
    rewrite nv_ltb in D1. apply N.ltb_lt in D1. change (nv 0%uint63) with 0 in D1.
    rewrite nv_eqb, nv_land1 in D2. apply N.eqb_eq in D2. change (nv 0%uint63) with 0 in D2.
    assert (E2 : nv d = 2 * (nv d / 2)) by (pose proof (N.div_mod (nv d) 2 ltac:(lia)); lia).
    assert (Hs1 : nv (s + 1)%uint63 = nv s + 1) by (apply nv_add; change (nv 1%uint63) with 1; lia).
    destruct (IH ((φ (d >> 1))%uint63) ltac:(rewrite <- Hz; apply dec_shr2; auto) (d >> 1)%uint63 (s + 1)%uint63
                (H' _ (dec_shr2 d Hd)) eq_refl) as [A B].
    { rewrite Hs1, nv_lsr1. lia. }
    rewrite Hs1, nv_lsr1 in *. split; [lia|].
    rewrite E2 at 1. rewrite B.
    replace (nv (snd (strip2 (d >> 1) (s + 1) (H' (φ (d >> 1))%uint63 (dec_shr2 d Hd)))) - nv s)
      with (N.succ (nv (snd (strip2 (d >> 1) (s + 1) (H' (φ (d >> 1))%uint63 (dec_shr2 d Hd)))) - (nv s + 1))) by lia.
    rewrite N.pow_succ_r'. ring.
  - simpl. split; [lia|]. rewrite N.sub_diag, N.pow_0_r. ring.
Qed.

Lemma pow_sq_mod : forall a k n, ((a ^ k mod n) * (a ^ k mod n)) mod n = a ^ (2 * k) mod n.
Proof.
  intros a k n. rewrite <- N.Div0.mul_mod. f_equal. rewrite <- N.pow_add_r. f_equal. lia.
Qed.

Lemma mr_loop_spec : forall z n (a d : N) y i s (H : Acc (Zwf 0) (gap s i)), gap s i = z ->
  primeN (nv n) -> 0 < a < nv n -> 2 ^ nv s * d = nv n - 1 ->
  nv y = a ^ (2 ^ nv i * d) mod nv n -> nv y <> 1 -> nv i <= nv s ->
  mr_loop n y i s H = false.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros n a d y i s H Hz Hn Ha Hs Hy Hy1 His. destruct H as [H']. simpl.
  pose proof (primeN_gt1 _ Hn) as Hn1.
  destruct (bdec (i <? s)%uint63) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite nv_ltb in Hi'. apply N.ltb_lt in Hi'.
    rewrite nv_eqb, nv_sub by (change (nv 1%uint63) with 1; lia). change (nv 1%uint63) with 1.
    destruct (N.eqb_spec (nv y) (nv n - 1)) as [E | E]; [reflexivity|].
    assert (Hyn : nv y < nv n) by (rewrite Hy; apply N.mod_lt; lia).
    assert (Hm : nv (mulmod y y n) = (nv y * nv y) mod nv n) by (apply nv_mulmod; lia).
    rewrite nv_eqb, Hm. change (nv 1%uint63) with 1.
    destruct (N.eqb_spec ((nv y * nv y) mod nv n) 1) as [E1 | E1].
    + exfalso. destruct (mr_sqrt (nv n) (nv y) Hn Hyn E1); contradiction.
    + assert (Hi1 : nv (i + 1)%uint63 = nv i + 1) by (apply nv_add; change (nv 1%uint63) with 1;
        pose proof (nv_bound s); lia).
      apply (IH (gap s (i + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; auto) n a d); auto.
      * rewrite Hm, Hy, pow_sq_mod, Hi1, N.pow_add_r, N.pow_1_r. f_equal. f_equal. ring.
      * rewrite Hm. exact E1.
      * rewrite Hi1. lia.
  - exfalso. rewrite nv_ltb in Hi. apply N.ltb_ge in Hi.
    assert (E : nv i = nv s) by lia. rewrite E, Hs in Hy.
    rewrite mr_fermat in Hy; auto.
Qed.

Lemma mr_base_spec : forall n a, primeN (nv n) -> 0 < nv a < nv n -> mr_base n a = false.
Proof.
  intros n a Hn Ha. pose proof (primeN_gt1 _ Hn) as Hn1. unfold mr_base.
  assert (Hm1 : nv (n - 1)%uint63 = nv n - 1) by (apply nv_sub; change (nv 1%uint63) with 1; lia).
  pose proof (strip2_spec _ (n - 1)%uint63 0%uint63 (Zwf_well_founded 0 _) eq_refl) as S.
  destruct (strip2 (n - 1) 0 (Zwf_well_founded 0 (φ (n - 1))%uint63)) as [d s] eqn:E.
  simpl in S. change (nv 0%uint63) with 0 in S. destruct S as [_ S].
  { rewrite Hm1. pose proof (nv_bound n). lia. }
  rewrite N.sub_0_r, Hm1 in S.
  rewrite nv_eqb, nv_powmod by lia. change (nv 1%uint63) with 1.
  destruct (N.eqb_spec ((nv a ^ nv d) mod nv n) 1) as [E1 | E1]; [reflexivity|].
  apply (mr_loop_spec _ n (nv a) (nv d) _ _ _ _ eq_refl);
    try (change (nv 0%uint63) with 0); try rewrite nv_powmod by lia;
    try rewrite N.pow_0_r, N.mul_1_l; auto; lia.
Qed.

Lemma mr_comp_spec : forall n, primeN (nv n) -> 37 < nv n -> mr_comp n = false.
Proof.
  intros n Hn H37. unfold mr_comp.
  assert (B : forall k, 0 < nv k < nv n -> mr_base n k = false) by (intros; apply mr_base_spec; auto).
  rewrite !B; [reflexivity | ..];
    match goal with |- (0 < nv ?c < _) => let v := eval vm_compute in (nv c) in change (nv c) with v; lia end.
Qed.

Lemma modsub1 : forall x n, 0 < n -> 1 <= x -> ((x mod n) + n - 1) mod n = (x - 1) mod n.
Proof.
  intros x n Hn Hx.
  replace (x mod n + n - 1) with (x mod n + (n - 1)) by lia.
  rewrite N.Div0.add_mod_idemp_l.
  replace (x + (n - 1)) with ((x - 1) + 1 * n) by lia.
  apply N.Div0.mod_add.
Qed.

Lemma nvALIM : nv ALIM = 1000.
Proof. reflexivity. Qed.

Lemma find_base_spec : forall z n m q a (H : Acc (Zwf 0) (gap ALIM a)), gap ALIM a = z ->
  1000 < nv n -> (Z.of_N (2 * nv n) < wB)%Z -> nv m = nv n - 1 -> 2 <= nv a ->
  (find_base n m q a H = BFound -> has_base (nv n) (nv q)) /\
  (find_base n m q a H = BComp -> ~ primeN (nv n)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros n m q a H Hz Hn Hw Hm Ha. destruct H as [H']. simpl.
  destruct (bdec (a <? ALIM)%uint63) as [HaL | HaL]; [| split; discriminate].
  pose proof HaL as HaL'. rewrite nv_ltb, nvALIM in HaL'. apply N.ltb_lt in HaL'.
  rewrite nv_eqb, nv_powmod by lia. change (nv 1%uint63) with 1.
  destruct (N.eqb_spec ((nv a ^ nv m) mod nv n) 1) as [E1 | E1]; simpl.
  2: { split; [discriminate|]. intros _ Hp. apply E1. rewrite Hm. apply mr_fermat; auto. lia. }
  set (u := powmod a (m / q)%uint63 n).
  assert (Hu : nv u = (nv a ^ (nv m / nv q)) mod nv n) by (unfold u; rewrite nv_powmod, nv_div by lia; reflexivity).
  assert (Hun : nv u < nv n) by (rewrite Hu; apply N.mod_lt; lia).
  assert (Hg : nv (igcd ((u + n - 1) mod n)%uint63 n) = N.gcd (nv a ^ (nv m / nv q) - 1) (nv n)).
  { rewrite nv_gcd, nv_mod.
    rewrite nv_sub by (rewrite nv_add by lia; change (nv 1%uint63) with 1; lia).
    rewrite nv_add by lia. change (nv 1%uint63) with 1.
    rewrite Hu, modsub1 by (try lia; apply pow_ge1; lia).
    rewrite N.Lcm0.gcd_mod. apply N.gcd_comm. }
  rewrite nv_eqb, Hg. change (nv 1%uint63) with 1.
  destruct (N.eqb_spec (N.gcd (nv a ^ (nv m / nv q) - 1) (nv n)) 1) as [E2 | E2].
  - split; [| discriminate]. intros _. exists (nv a). rewrite <- Hm. split; auto.
  - rewrite nv_ltb, Hg. destruct (N.ltb_spec (N.gcd (nv a ^ (nv m / nv q) - 1) (nv n)) (nv n)) as [E3 | E3].
    + split; [discriminate|]. intros _ [_ Hp].
      destruct (Hp _ (N.gcd_divide_r (nv a ^ (nv m / nv q) - 1) (nv n))) as [F | F]; [contradiction | lia].
    + assert (Ha1 : nv (a + 1)%uint63 = nv a + 1) by (apply nv_add; change (nv 1%uint63) with 1; lia).
      apply (IH (gap ALIM (a + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; auto)); auto.
      rewrite Ha1. lia.
Qed.

Lemma divfull_specN : forall x c k Hx H, 1 < nv x -> 0 < nv c -> (Z.of_N (nv k + nv c) < wB)%Z ->
  exists j, nv c = nv x ^ j * nv (fst (divfull x c k Hx H)) /\
    ~ (nv x | nv (fst (divfull x c k Hx H))) /\ 0 < nv (fst (divfull x c k Hx H)) /\
    nv (snd (divfull x c k Hx H)) = nv k + j.
Proof.
  intros x c k Hx H H1 H2 H3.
  destruct (divfull_spec (φ c) x c k Hx H eq_refl) as [j [J1 [J2 [J3 [J4 J5]]]]].
  - rewrite <- nv_Z. lia.
  - rewrite <- !nv_Z. lia.
  - exists (Z.to_N j). rewrite <- !nv_Z in *. split; [| split; [| split]].
    + apply N2Z.inj. rewrite N2Z.inj_mul, N2Z.inj_pow, Z2N.id by auto. exact J3.
    + rewrite divide_NZ. exact J4.
    + lia.
    + apply N2Z.inj. rewrite N2Z.inj_add, Z2N.id by auto. exact J2.
Qed.

Lemma div_lt_sq : forall n F, 0 < F -> n / F < F -> n < F * F.
Proof.
  intros n F HF H. pose proof (N.div_mod n F ltac:(lia)). pose proof (N.mod_lt n F ltac:(lia)).
  assert (F * (n / F) + F <= F * F).
  { replace (F * (n / F) + F) with (F * (n / F + 1)) by ring. apply N.mul_le_mono_l. lia. }
  lia.
Qed.

Definition bases (n F : N) : Prop := forall q, primeN q -> (q | F) -> has_base n q.

Lemma bases_mul_prime : forall n F r, bases n F -> primeN r -> has_base n r -> bases n (F * r).
Proof.
  intros n F r HF Hr Hb q Hq D. destruct (primeN_mult q F r Hq D) as [D1 | D1]; auto.
  destruct Hr as [_ Hd]. destruct (Hd q D1) as [E | E]; [pose proof (primeN_gt1 q Hq); lia | subst; auto].
Qed.

Lemma bases_mul_pow : forall n F r j, bases n F -> primeN r -> has_base n r -> bases n (F * r ^ j).
Proof.
  intros n F r j HF Hr Hb q Hq D. destruct (primeN_mult q F _ Hq D) as [D1 | D1]; auto.
  rewrite (primeN_pow_div r q j Hr Hq D1). auto.
Qed.

Lemma td_cert_spec : forall z pr np k n m F R (H : Acc (Zwf 0) (gap np k)), gap np k = z ->
  sieve_ok pr np -> 1000 < nv n -> (Z.of_N (2 * nv n) < wB)%Z -> nv m = nv n - 1 ->
  nv F * nv R = nv m -> 0 < nv F -> bases (nv n) (nv F) ->
  (forall k', nv k' < nv k -> ~ (nv pr.[k'] | nv R)) -> nv k <= nv np ->
  let res := td_cert pr np k n m F R H in
  (fst (fst res) = BComp -> ~ primeN (nv n)) /\
  (fst (fst res) = BFound ->
     nv (snd (fst res)) * nv (snd res) = nv m /\ 0 < nv (snd (fst res)) /\
     bases (nv n) (nv (snd (fst res))) /\
     (nv n < nv (snd (fst res)) * nv (snd (fst res)) \/
      forall k', nv k' < nv np -> ~ (nv pr.[k'] | nv (snd res)))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros pr np k n m F R H Hz Hs Hn Hw Hm HFR HF0 Hb Hk Hknp. destruct H as [H']. simpl.
  destruct Hs as [Snp [Slen [Sp Sc]]].
  destruct (bdec (k <? np)%uint63) as [Hkn | Hkn].
  2: { simpl. split; [discriminate|]. intros _. split; [auto|]. split; [auto|]. split; [auto|].
       right. intros k' Hk'. apply Hk. rewrite nv_ltb in Hkn. apply N.ltb_ge in Hkn. lia. }
  pose proof Hkn as Hkn'. rewrite nv_ltb in Hkn'. apply N.ltb_lt in Hkn'.
  assert (HR0 : 0 < nv R) by (destruct (N.eq_dec (nv R) 0) as [E|E]; [rewrite E in HFR; lia | lia]).
  rewrite nv_ltb, nv_div. destruct (N.ltb_spec (nv n / nv F) (nv F)) as [E1 | E1].
  { simpl. split; [discriminate|]. intros _. split; [auto|]. split; [auto|]. split; [auto|].
    left. apply div_lt_sq; auto. }
  destruct (Sp k Hkn') as [Pq Pq1]. pose proof (primeN_gt1 _ Pq) as Pq2.
  assert (Hk1 : nv (k + 1)%uint63 = nv k + 1) by (apply nv_add; change (nv 1%uint63) with 1; lia).
  assert (Hdec : Zwf 0 (gap np (k + 1)%uint63) z) by (rewrite <- Hz; apply dec_step; auto).
  rewrite nv_eqb, nv_mod. change (nv 0%uint63) with 0.
  destruct (N.eqb_spec (nv R mod nv pr.[k]) 0) as [E2 | E2].
  - destruct (bdec (1 <? pr.[k])%uint63) as [Hq | Hq].
    2: { exfalso. rewrite nv_ltb in Hq. apply N.ltb_ge in Hq. change (nv 1%uint63) with 1 in Hq. lia. }
    destruct (divfull_specN pr.[k] R 0%uint63 Hq (Zwf_well_founded 0 _)) as [j [J1 [J2 [J3 _]]]];
      [lia | lia | change (nv 0%uint63) with 0; rewrite N.add_0_l; apply nv_bound |].
    set (R' := fst (divfull pr.[k] R 0 Hq (Zwf_well_founded 0 (φ R)))) in *.
    pose proof (find_base_spec _ n m pr.[k] 2%uint63 (Zwf_well_founded 0 _) eq_refl Hn Hw Hm
                  ltac:(change (nv 2%uint63) with 2; lia)) as [FB1 FB2].
    destruct (find_base n m pr.[k] 2 (Zwf_well_founded 0 (gap ALIM 2))) eqn:EB.
    + assert (HdR : nv (R / R')%uint63 = nv pr.[k] ^ j).
      { rewrite nv_div, J1. apply N.div_mul. lia. }
      assert (HF' : nv (F * (R / R'))%uint63 = nv F * nv pr.[k] ^ j).
      { rewrite nv_mul; rewrite HdR; [reflexivity|].
        assert (nv F * nv pr.[k] ^ j <= nv m) by (rewrite <- HFR, J1; rewrite N.mul_assoc; apply N.le_mul_r; lia).
        lia. }
      refine (IH _ Hdec pr np (k + 1)%uint63 n m _ _ _ eq_refl _ Hn Hw Hm _ _ _ _ _).
      * split; [exact Snp | split; [exact Slen | split; [exact Sp | exact Sc]]].
      * rewrite HF', <- HFR, J1. ring.
      * rewrite HF'. pose proof (pow_pos (nv pr.[k]) j ltac:(lia)). lia.
      * rewrite HF'. apply bases_mul_pow; auto.
      * intros k' Hk'. rewrite Hk1 in Hk'. destruct (N.eq_dec (nv k') (nv k)) as [E | E].
        -- apply nv_inj in E. subst k'. exact J2.
        -- intro D. apply (Hk k'); [lia|]. eapply N.divide_trans; [exact D|]. rewrite J1. apply N.divide_factor_r.
      * rewrite Hk1. lia.
    + simpl. split; [intros _; apply FB2; auto | discriminate].
    + simpl. split; discriminate.
  - refine (IH _ Hdec pr np (k + 1)%uint63 n m F R _ eq_refl _ Hn Hw Hm HFR HF0 Hb _ _).
    + split; [exact Snp | split; [exact Slen | split; [exact Sp | exact Sc]]].
    + intros k' Hk'. rewrite Hk1 in Hk'. destruct (N.eq_dec (nv k') (nv k)) as [E | E].
      * apply nv_inj in E. subst k'. intro D. apply E2. apply N.Lcm0.mod_divide. exact D.
      * apply Hk. lia.
    + rewrite Hk1. lia.
Qed.

End CertCode.

Section Classify.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Definition E12 : N := 1000000000000.
Definition E18 : N := 1000000000000000000.

Lemma wB_E18 : (Z.of_N (2 * E18) < wB)%Z.
Proof. rewrite wB_val. unfold E18. lia. Qed.

Lemma nvT12 : nv T12 = E12.
Proof. reflexivity. Qed.

Lemma rough_of_sieve : forall pr np R, sieve_ok pr np ->
  (forall k, nv k < nv np -> ~ (nv pr.[k] | R)) -> roughN R.
Proof.
  intros pr np R [_ [_ [_ Sc]]] H p Hp D.
  destruct (N.lt_ge_cases p 1000000) as [L | L].
  - destruct (Sc p Hp L) as [k [K1 K2]]. exfalso. apply (H k K1). rewrite K2. exact D.
  - unfold B6. destruct (N.eq_dec p 1000000) as [E | E]; [| lia]. exfalso. subst p.
    destruct Hp as [_ Hd]. destruct (Hd 2 ltac:(exists 500000; reflexivity)); discriminate.
Qed.

Lemma pock_use : forall n F R, 1 < n -> F * R = n - 1 -> 0 < F -> bases n F -> n < F * F -> primeN n.
Proof.
  intros n F R Hn HFR HF Hb Hlt. apply (pocklington n F); auto. exists R. lia.
Qed.

Lemma rough_split : forall R g, roughN R -> R <= E18 -> 1 < g -> g < R -> (g | R) ->
  primeN g /\ primeN (R / g) /\ g * (R / g) = R.
Proof.
  intros R g HR HR18 Hg1 HgR D.
  destruct D as [r Hr].
  assert (Hr0 : r <> 0) by (intro; subst; lia).
  assert (Hrd : R / g = r) by (rewrite Hr; apply N.div_mul; lia).
  rewrite Hrd.
  assert (Hr1 : 1 < r) by (destruct (N.eq_dec r 1); [subst; lia | lia]).
  assert (Rg : roughN g) by (apply (rough_div R); auto; rewrite Hr; apply N.divide_factor_r).
  assert (Rr : roughN r) by (apply (rough_div R); auto; rewrite Hr; apply N.divide_factor_l).
  pose proof (rough_gt g Rg Hg1). pose proof (rough_gt r Rr Hr1).
  unfold E18, B6 in *.
  split; [| split; [| lia]]; apply rough_prime; auto; unfold B6; nia.
Qed.

Lemma certify_spec : forall z pr np n (H : Acc (Zwf 0) (φ n)), (φ n) = z ->
  sieve_ok pr np -> E12 < nv n -> nv n <= E18 ->
  (certify pr np n H = CPrime -> primeN (nv n)) /\ (certify pr np n H = CComp -> ~ primeN (nv n)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros pr np n H Hz Hs Hn12 Hn18. destruct H as [H']. simpl.
  pose proof wB_E18 as W.
  assert (Hw : (Z.of_N (2 * nv n) < wB)%Z) by lia.
  assert (Hn1 : 1000 < nv n) by (unfold E12 in *; lia).
  assert (Hm : nv (n - 1)%uint63 = nv n - 1) by (apply nv_sub; change (nv 1%uint63) with 1; lia).
  generalize (td_cert_spec _ pr np 0%uint63 n (n - 1)%uint63 1%uint63 (n - 1)%uint63 (Zwf_well_founded 0 _)
               eq_refl Hs Hn1 Hw Hm).
  destruct (td_cert pr np 0 n (n - 1) 1 (n - 1) (Zwf_well_founded 0 (gap np 0))) as [[r F] R].
  change (nv 1%uint63) with 1. change (nv 0%uint63) with 0. cbn [fst snd].
  intros TS. destruct TS as [T1 T2]; [lia | lia | intros q Hq D; exfalso; apply N.divide_1_r in D;
    pose proof (primeN_gt1 q Hq); lia | intros k' Hk'; lia | lia |].
  destruct r.
  2: { split; [discriminate | intros _; apply T1; reflexivity]. }
  2: { split; discriminate. }
  destruct (T2 eq_refl) as [FR [F0 [Fb Fd]]]. rewrite Hm in FR. clear T1 T2.
  rewrite nv_ltb, nv_div. destruct (N.ltb_spec (nv n / nv F) (nv F)) as [E1 | E1].
  { split; [| discriminate]. intros _. refine (pock_use _ (nv F) (nv R) _ FR F0 Fb _); [lia | apply div_lt_sq; auto]. }
  assert (HFF : nv F * nv F <= nv n).
  { pose proof (N.mul_div_le (nv n) (nv F) ltac:(lia)). pose proof (N.mul_le_mono_l _ _ (nv F) E1). lia. }
  assert (Rr : roughN (nv R)) by (destruct Fd as [Fd | Fd]; [lia | eapply rough_of_sieve; eauto]).
  assert (HR18 : nv R <= E18) by (pose proof (N.le_mul_l (nv R) (nv F) ltac:(lia)); lia).
  assert (Hmm : nv n < (nv n - 1) * (nv n - 1)) by (unfold E12 in *; nia).
  (* the rest R is prime: one more base *)
  assert (Rprime : forall b, primeN (nv R) ->
            (b = BFound -> has_base (nv n) (nv R)) -> (b = BComp -> ~ primeN (nv n)) ->
            (base_res b = CPrime -> primeN (nv n)) /\ (base_res b = CComp -> ~ primeN (nv n))).
  { intros b HRp B1 B2. destruct b; simpl; split; try discriminate; auto.
    intros _.
    assert (HFR' : nv F * nv R * 1 = nv n - 1) by lia.
    assert (HFR0 : 0 < nv F * nv R) by (apply N.mul_pos_pos; lia).
    refine (pock_use _ _ 1 _ HFR' HFR0 _ _); [lia | apply bases_mul_prime; auto | rewrite FR; exact Hmm]. }
  rewrite nv_leb. change (nv 1%uint63) with 1.
  destruct (N.leb_spec (nv R) 1) as [E2 | E2]; [split; discriminate|].
  rewrite nv_leb, nvT12. destruct (N.leb_spec (nv R) E12) as [E3 | E3].
  { pose proof (find_base_spec _ n (n - 1)%uint63 R 2%uint63 (Zwf_well_founded 0 _) eq_refl Hn1 Hw Hm
      ltac:(change (nv 2%uint63) with 2; lia)) as [B1 B2].
    apply Rprime; auto. apply rough_prime; auto; unfold E12, B6 in *; lia. }
  destruct (mr_comp R) eqn:EM.
  - set (g := rho_try R 1 (Zwf_well_founded 0 (gap RHOC 1))).
    destruct ((1 <? g)%uint63 && (g <? R)%uint63 && (R mod g =? 0)%uint63) eqn:EG; [| split; discriminate].
    apply Bool.andb_true_iff in EG as [EG EG3]. apply Bool.andb_true_iff in EG as [EG1 EG2].
    rewrite nv_ltb in EG1, EG2. apply N.ltb_lt in EG1, EG2. change (nv 1%uint63) with 1 in EG1.
    rewrite nv_eqb, nv_mod in EG3. apply N.eqb_eq in EG3. change (nv 0%uint63) with 0 in EG3.
    apply N.Lcm0.mod_divide in EG3.
    destruct (rough_split (nv R) (nv g) Rr HR18 EG1 EG2 EG3) as [Pg [Pr Egr]].
    pose proof (find_base_spec _ n (n - 1)%uint63 g 2%uint63 (Zwf_well_founded 0 _) eq_refl Hn1 Hw Hm
                  ltac:(change (nv 2%uint63) with 2; lia)) as [G1 G2].
    destruct (find_base n (n - 1) g 2 (Zwf_well_founded 0 (gap ALIM 2))).
    + assert (HFg : nv (F * g)%uint63 = nv F * nv g).
      { apply nv_mul. assert (nv F * nv g <= nv F * nv R) by (apply N.mul_le_mono_l; lia). lia. }
      rewrite nv_ltb, nv_div, HFg. destruct (N.ltb_spec (nv n / (nv F * nv g)) (nv F * nv g)) as [E4 | E4].
      * split; [| discriminate]. intros _.
        assert (HFR' : nv F * nv g * (nv R / nv g) = nv n - 1) by (rewrite <- N.mul_assoc, Egr; lia).
        assert (HFg0 : 0 < nv F * nv g) by (apply N.mul_pos_pos; lia).
        refine (pock_use _ _ (nv R / nv g) _ HFR' HFg0 _ _); [lia | | apply div_lt_sq; auto].
        apply bases_mul_prime; auto.
      * set (r2 := (R / g)%uint63).
        assert (Hr2 : nv r2 = nv R / nv g) by apply nv_div.
        pose proof (find_base_spec _ n (n - 1)%uint63 r2 2%uint63 (Zwf_well_founded 0 _) eq_refl Hn1 Hw Hm
                      ltac:(change (nv 2%uint63) with 2; lia)) as [R1 R2].
        destruct (find_base n (n - 1) r2 2 (Zwf_well_founded 0 (gap ALIM 2))); simpl;
          split; try discriminate; auto.
        intros _.
        assert (HFR' : nv F * nv g * nv r2 * 1 = nv n - 1) by (rewrite N.mul_1_r, <- N.mul_assoc, Hr2, Egr; lia).
        assert (HFg0 : 0 < nv F * nv g * nv r2) by (rewrite <- N.mul_assoc, Hr2, Egr; apply N.mul_pos_pos; lia).
        refine (pock_use _ _ 1 _ HFR' HFg0 _ _); [lia | |].
        -- apply bases_mul_prime; [apply bases_mul_prime; auto | rewrite Hr2; auto | auto].
        -- replace (nv F * nv g * nv r2) with (nv n - 1) by lia. exact Hmm.
    + simpl. split; [discriminate | intros _; auto].
    + simpl. split; discriminate.
  - destruct (bdec (R <? n)%uint63) as [HRn | HRn]; [| split; discriminate].
    pose proof HRn as HRn'. rewrite nv_ltb in HRn'. apply N.ltb_lt in HRn'.
    destruct (IH (φ R) ltac:(rewrite <- Hz; apply dec_lt; auto) pr np R (H' (φ R) (dec_lt n R HRn)) eq_refl Hs E3 HR18)
      as [C1 C2].
    destruct (certify pr np R (H' (φ R) (dec_lt n R HRn))); try (split; discriminate).
    pose proof (find_base_spec _ n (n - 1)%uint63 R 2%uint63 (Zwf_well_founded 0 _) eq_refl Hn1 Hw Hm
      ltac:(change (nv 2%uint63) with 2; lia)) as [B1 B2].
    apply Rprime; auto.
Qed.

End Classify.

Section Classify2.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Lemma td_loop_spec : forall z n d (H : Acc (Zwf 0) (gap n d)), gap n d = z ->
  1 < nv n -> nv n <= E18 -> 2 <= nv d ->
  (forall e, 1 < e -> e < nv d -> ~ (e | nv n)) -> (nv d - 1) * (nv d - 1) <= nv n ->
  (td_loop n d H = true -> primeN (nv n)) /\ (td_loop n d H = false -> ~ primeN (nv n)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros n d H Hz Hn H18 Hd Hinv Hsq. destruct H as [H']. simpl.
  destruct (bdec (d <? n)%uint63) as [Hdn | Hdn].
  - pose proof Hdn as Hdn'. rewrite nv_ltb in Hdn'. apply N.ltb_lt in Hdn'.
    assert (Hd9 : nv d - 1 <= 1000000000).
    { destruct (N.le_gt_cases (nv d - 1) 1000000000) as [L | L]; [exact L|]. exfalso.
      assert (1000000000 * 1000000000 < (nv d - 1) * (nv d - 1)) by (apply N.mul_lt_mono; lia).
      unfold E18 in *. lia. }
    assert (Hdd : nv (d * d)%uint63 = nv d * nv d).
    { apply nv_mul. assert (nv d * nv d <= 1000000001 * 1000000001) by (apply N.mul_le_mono; lia).
      rewrite wB_val. lia. }
    rewrite nv_leb, Hdd. destruct (N.leb_spec (nv d * nv d) (nv n)) as [E1 | E1].
    + rewrite nv_eqb, nv_mod. change (nv 0%uint63) with 0.
      destruct (N.eqb_spec (nv n mod nv d) 0) as [E2 | E2].
      * split; [discriminate|]. intros _ [_ Hp]. apply N.Lcm0.mod_divide in E2.
        destruct (Hp _ E2); lia.
      * assert (Hd1 : nv (d + 1)%uint63 = nv d + 1) by (apply nv_add; change (nv 1%uint63) with 1;
          rewrite wB_val; unfold E18 in *; lia).
        apply (IH (gap n (d + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; auto)); auto; rewrite Hd1.
        -- lia.
        -- intros e He1 He2. destruct (N.eq_dec e (nv d)) as [-> | E]; [| apply Hinv; lia].
           intro D. apply E2. apply N.Lcm0.mod_divide. exact D.
        -- replace (nv d + 1 - 1) with (nv d) by lia. exact E1.
    + split; [| discriminate]. intros _. apply td_prime_crit; auto.
      intros e He1 He2. apply Hinv; auto.
      destruct (N.lt_ge_cases e (nv d)) as [L | L]; auto.
      assert (nv d * nv d <= e * e) by (apply N.mul_le_mono; lia). lia.
  - rewrite nv_ltb in Hdn. apply N.ltb_ge in Hdn. split; [| discriminate]. intros _.
    apply td_prime_crit; auto. intros e He1 He2. apply Hinv; auto.
    assert (e * 2 <= e * e) by (apply N.mul_le_mono_l; lia). lia.
Qed.

Lemma isqrt_specN : forall x, nv x <= E18 ->
  nv (isqrt x) * nv (isqrt x) <= nv x < (nv (isqrt x) + 1) * (nv (isqrt x) + 1).
Proof.
  intros x Hx. pose proof (isqrt_spec x) as S. rewrite <- !nv_Z in S.
  assert (Hx' : (Z.of_N (nv x) < 4611686018427387904)%Z) by (unfold E18 in *; lia).
  specialize (S Hx'). lia.
Qed.

Lemma classify_spec : forall pr np x, sieve_ok pr np -> roughN (nv x) -> 1 < nv x -> nv x <= E18 ->
  (classify pr np x = KPrime -> primeN (nv x)) /\
  (classify pr np x = KSquare -> exists s, nv x = s * s /\ primeN s) /\
  (classify pr np x = KSemi -> exists q r, nv x = q * r /\ primeN q /\ primeN r /\ q <> r).
Proof.
  intros pr np x Hs Hr Hx1 Hx18. unfold classify.
  rewrite nv_leb, nvT12. destruct (N.leb_spec (nv x) E12) as [E1 | E1].
  { split; [intros _; apply rough_prime; auto; unfold E12, B6 in *; lia | split; discriminate]. }
  pose proof (isqrt_specN x Hx18) as [S1 S2].
  set (s := isqrt x) in *.
  assert (Hss : nv (s * s)%uint63 = nv s * nv s) by (apply nv_mul; rewrite wB_val; unfold E18 in *; lia).
  rewrite nv_eqb, Hss. destruct (N.eqb_spec (nv s * nv s) (nv x)) as [E2 | E2].
  { split; [discriminate | split; [| discriminate]]. intros _. exists (nv s). split; [auto|].
    assert (Hs1 : 1 < nv s) by (destruct (N.lt_ge_cases 1 (nv s)) as [L | L]; [auto|];
      assert (nv s * nv s <= 1 * 1) by (apply N.mul_le_mono; lia); lia).
    apply rough_prime; auto.
    - apply (rough_div (nv x)); auto. rewrite <- E2. apply N.divide_factor_l.
    - unfold B6. destruct (N.le_gt_cases (nv s) (1000000 * 1000000)) as [L | L]; auto.
      assert (1000000 * 1000000 * (1000000 * 1000000) < nv s * nv s) by (apply N.mul_lt_mono; lia).
      unfold E18 in *. lia. }
  assert (NS : forall q, nv x <> q * q).
  { intros q Hq. apply E2. rewrite Hq in *. replace q with (nv s); [reflexivity|].
    destruct (N.lt_trichotomy q (nv s)) as [L | [L | L]]; auto; exfalso.
    - assert (q * q < nv s * nv s) by (apply N.mul_lt_mono; lia). lia.
    - assert ((nv s + 1) * (nv s + 1) <= q * q) by (apply N.mul_le_mono; lia). lia. }
  assert (Semi : ~ primeN (nv x) -> exists q r, nv x = q * r /\ primeN q /\ primeN r /\ q <> r).
  { intros Np. destruct (rough_semi (nv x) Hr Hx1 ltac:(unfold E18, B6 in *; lia) Np) as [q [r [Q1 [Q2 Q3]]]].
    exists q, r. split; [auto | split; [auto | split; [auto|]]]. intro E. subst r. apply (NS q Q1). }
  destruct (mr_comp x) eqn:EM.
  { split; [discriminate | split; [discriminate|]]. intros _. apply Semi. intro P.
    rewrite mr_comp_spec in EM; [discriminate | auto | unfold E12 in *; lia]. }
  destruct (certify_spec _ pr np x (Zwf_well_founded 0 _) eq_refl Hs E1 Hx18) as [C1 C2].
  destruct (certify pr np x (Zwf_well_founded 0 (φ x))).
  - split; [intros _; apply C1; reflexivity | split; discriminate].
  - split; [discriminate | split; [discriminate|]]. intros _. apply Semi. apply C2. reflexivity.
  - destruct (td_loop_spec _ x 2%uint63 (Zwf_well_founded 0 _) eq_refl Hx1 Hx18) as [D1 D2];
      change (nv 2%uint63) with 2; [lia | intros e He1 He2; lia | lia |].
    destruct (td_loop x 2 (Zwf_well_founded 0 (gap x 2))).
    + split; [intros _; apply D1; reflexivity | split; discriminate].
    + split; [discriminate | split; [discriminate|]]. intros _. apply Semi. apply D2. reflexivity.
Qed.

End Classify2.

(* ================================================================== *)
(* Part 9. The accumulator                                             *)
(* ================================================================== *)

Section Acc.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Definition MN : N := 1000000007.

Lemma nvMODP : nv MODP = MN.
Proof. reflexivity. Qed.

Lemma Zmod_combo : forall X Y W M, (0 < M)%Z ->
  ((X mod M + 2 * (M - Y mod M) + W mod M) mod M = (X - 2 * Y + W) mod M)%Z.
Proof.
  intros X Y W M HM.
  rewrite (Z.mod_eq X M), (Z.mod_eq Y M), (Z.mod_eq W M) by lia.
  replace (X - M * (X / M) + 2 * (M - (Y - M * (Y / M))) + (W - M * (W / M)))%Z
    with ((X - 2 * Y + W) + (2 - X / M + 2 * (Y / M) - W / M) * M)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Lemma fmod_spec : forall e P, 1 <= nv e -> nv e < 100000 ->
  Z.of_N (nv (fmod e P)) = (fP (nv P) (Z.of_N (nv e)) mod 1000000007)%Z.
Proof.
  intros e P H1 H2. unfold fmod.
  assert (Ee1 : nv (e + 1)%uint63 = nv e + 1) by (apply nv_add; change (nv 1%uint63) with 1; rewrite wB_val; lia).
  assert (Eem : nv (e - 1)%uint63 = nv e - 1) by (apply nv_sub; change (nv 1%uint63) with 1; lia).
  set (a := powmod (e + 1) P MODP). set (b := powmod e P MODP). set (c := powmod (e - 1) P MODP).
  assert (Ha : nv a = (nv (e + 1)%uint63 ^ nv P) mod MN) by (unfold a; rewrite nv_powmod, nvMODP; [reflexivity | reflexivity]).
  assert (Hb : nv b = (nv e ^ nv P) mod MN) by (unfold b; rewrite nv_powmod, nvMODP; [reflexivity | reflexivity]).
  assert (Hc : nv c = (nv (e - 1)%uint63 ^ nv P) mod MN) by (unfold c; rewrite nv_powmod, nvMODP; [reflexivity | reflexivity]).
  assert (Ba : nv a < MN) by (rewrite Ha; apply N.mod_lt; unfold MN; lia).
  assert (Bb : nv b < MN) by (rewrite Hb; apply N.mod_lt; unfold MN; lia).
  assert (Bc : nv c < MN) by (rewrite Hc; apply N.mod_lt; unfold MN; lia).
  assert (E1 : nv (MODP - b)%uint63 = MN - nv b) by (rewrite nv_sub; rewrite nvMODP; lia).
  assert (E2 : nv (2 * (MODP - b))%uint63 = 2 * (MN - nv b))
    by (rewrite nv_mul, E1; [reflexivity | change (nv 2%uint63) with 2; rewrite E1, wB_val; unfold MN in *; lia]).
  assert (E3 : nv (a + 2 * (MODP - b))%uint63 = nv a + 2 * (MN - nv b))
    by (rewrite nv_add, E2; [reflexivity | rewrite E2, wB_val; unfold MN in *; lia]).
  assert (E4 : nv (a + 2 * (MODP - b) + c)%uint63 = nv a + 2 * (MN - nv b) + nv c)
    by (rewrite nv_add, E3; [reflexivity | rewrite E3, wB_val; unfold MN in *; lia]).
  rewrite nv_mod, E4, nvMODP.
  rewrite N2Z.inj_mod, !N2Z.inj_add, N2Z.inj_mul, N2Z.inj_sub by lia.
  rewrite Ha, Hb, Hc, Ee1, Eem, !N2Z.inj_mod, !N2Z.inj_pow, N2Z.inj_add, N2Z.inj_sub by lia.
  unfold fP, MN. simpl Z.of_N. apply Zmod_combo. lia.
Qed.

(* one slot (x^eg, x^el) folded into the accumulator *)
Lemma step_ok : forall P Gd Ld cd acc x (eg el : int) f,
  1 <= P -> 1 < x -> 0 < Gd -> 0 < Ld -> num_sequences P Gd Ld cd -> nv acc = cd mod MN ->
  coprime_vp Gd Ld (x ^ nv eg) (x ^ nv el) ->
  (nv eg < nv el -> exists cs, num_sequences P (x ^ nv eg) (x ^ nv el) cs /\
                               nv (f (el - eg)%uint63) = cs mod MN) ->
  exists cd', num_sequences P (Gd * x ^ nv eg) (Ld * x ^ nv el) cd' /\
              nv (step_acc acc eg el f) = cd' mod MN.
Proof.
  intros P Gd Ld cd acc x eg el f HP Hx HG HL Hc Hacc Hcop Hf. unfold step_acc.
  assert (Px : forall k, 0 < x ^ k) by (intros; apply pow_pos; lia).
  assert (Ne : forall k, x ^ k = x ^ N.of_nat (N.to_nat k)) by (intros; rewrite N2Nat.id; reflexivity).
  rewrite nv_eqb. destruct (N.eqb_spec (nv eg) (nv el)) as [E | E].
  - exists (cd * 1). rewrite E in *. split.
    + apply count_mul; auto. rewrite Ne. apply slot_eq; auto.
    + rewrite N.mul_1_r. exact Hacc.
  - rewrite nv_ltb. destruct (N.ltb_spec (nv el) (nv eg)) as [L | L].
    + exists (cd * 0). split.
      * apply count_mul; auto. rewrite (Ne (nv eg)), (Ne (nv el)). apply slot_zero; auto. lia.
      * rewrite N.mul_0_r. reflexivity.
    + destruct (Hf ltac:(lia)) as [cs [Cs Fs]].
      exists (cd * cs). split; [apply count_mul; auto|].
      rewrite nv_mulmod, Hacc, Fs, nvMODP; unfold MN in *.
      * rewrite <- N.Div0.mul_mod. reflexivity.
      * rewrite nvMODP. unfold MN. lia.
      * rewrite Hacc, nvMODP. apply N.mod_lt. unfold MN. lia.
      * rewrite Fs, nvMODP. apply N.mod_lt. unfold MN. lia.
Qed.

End Acc.

(* ================================================================== *)
(* Part 10. Passes over the cofactor arrays                            *)
(* ================================================================== *)

Section Arr.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Definition cl (a : array int) (k : nat) : N := nv a.[of_Z (Z.of_nat k)].

Fixpoint prodA (a : array int) (n : nat) : N :=
  match n with O => 1 | S n => prodA a n * cl a n end.

Lemma nv_ofnat : forall k, (Z.of_nat k < wB)%Z -> nv (of_Z (Z.of_nat k)) = N.of_nat k.
Proof. intros k H. rewrite nv_lit by lia. lia. Qed.

Lemma idx_eq : forall (i : int) k, (Z.of_nat k < wB)%Z -> nv i = N.of_nat k -> of_Z (Z.of_nat k) = i.
Proof. intros i k H E. apply nv_inj. rewrite nv_ofnat by auto. auto. Qed.

Lemma prodA_set : forall a i v n, (N.of_nat n < 4194304) ->
  (nv i < N.of_nat n -> nv i < nv (PArray.length a) ->
     prodA (a.[i <- v]) n * nv a.[i] = prodA a n * nv v) /\
  (N.of_nat n <= nv i -> prodA (a.[i <- v]) n = prodA a n).
Proof.
  intros a i v n. induction n as [| n IH]; intros Hn; [split; [intros; lia | reflexivity]|].
  destruct IH as [IH1 IH2]; [lia|]. simpl. unfold cl.
  assert (Hw : (Z.of_nat n < wB)%Z) by (rewrite wB_val; lia).
  split.
  - intros Hi Hl. destruct (N.eq_dec (nv i) (N.of_nat n)) as [E | E].
    + rewrite (idx_eq i n Hw E). rewrite iget_set_same by (rewrite nv_ltb; apply N.ltb_lt; auto).
      rewrite IH2 by lia. ring.
    + rewrite iget_set_other by (intro F; subst; rewrite nv_ofnat in E by auto; lia).
      replace (prodA a.[i <- v] n * nv a.[of_Z (Z.of_nat n)] * nv a.[i])
        with (prodA a.[i <- v] n * nv a.[i] * nv a.[of_Z (Z.of_nat n)]) by ring.
      rewrite IH1 by (auto; lia). ring.
  - intros Hi. rewrite IH2 by lia.
    rewrite iget_set_other by (intro F; subst; rewrite nv_ofnat in Hi by auto; lia). reflexivity.
Qed.

Lemma prodA_pos : forall a n, (N.of_nat n < 4194304) ->
  (forall k, nv k < N.of_nat n -> 0 < nv a.[k]) -> 0 < prodA a n.
Proof.
  intros a n. induction n as [| n IH]; intros Hn H; simpl; [lia|].
  assert (0 < cl a n).
  { unfold cl. apply H. rewrite nv_ofnat by (rewrite wB_val; lia). lia. }
  pose proof (IH ltac:(lia) ltac:(intros k Hk; apply H; lia)). nia.
Qed.

Lemma prodA_one : forall a n, (N.of_nat n < 4194304) ->
  (forall k, nv k < N.of_nat n -> nv a.[k] = 1) -> prodA a n = 1.
Proof.
  intros a n. induction n as [| n IH]; intros Hn H; simpl; [reflexivity|].
  rewrite IH; [| lia | intros k Hk; apply H; lia]. unfold cl. rewrite H; [reflexivity|].
  rewrite nv_ofnat by (rewrite wB_val; lia). lia.
Qed.

Lemma prodA_prime : forall a n p, (N.of_nat n < 4194304) -> primeN p -> (p | prodA a n) ->
  exists k, nv k < N.of_nat n /\ (p | nv a.[k]).
Proof.
  intros a n p. induction n as [| n IH]; intros Hn Hp D; simpl in D.
  - exfalso. exact (primeN_not_div1 p Hp D).
  - destruct (primeN_mult p _ _ Hp D) as [D1 | D1].
    + destruct (IH ltac:(lia) Hp D1) as [k [K1 K2]]. exists k. split; [lia | auto].
    + exists (of_Z (Z.of_nat n)). rewrite nv_ofnat by (rewrite wB_val; lia). split; [lia | exact D1].
Qed.

Lemma prodA_ext : forall a b n, (N.of_nat n < 4194304) ->
  (forall k, nv k < N.of_nat n -> a.[k] = b.[k]) -> prodA a n = prodA b n.
Proof.
  intros a b n. induction n as [| n IH]; intros Hn H; simpl; [reflexivity|].
  rewrite IH; [| lia | intros k Hk; apply H; lia]. unfold cl. rewrite H; [reflexivity|].
  rewrite nv_ofnat by (rewrite wB_val; lia). lia.
Qed.

Lemma pow_le_E18 : forall x t, 2 <= x -> x ^ t <= E18 -> t <= 60.
Proof.
  intros x t Hx H. destruct (N.le_gt_cases t 60) as [L | L]; auto. exfalso.
  assert (2 ^ 61 <= x ^ t).
  { apply N.le_trans with (2 ^ t); [apply N.pow_le_mono_r; lia | apply N.pow_le_mono_l; lia]. }
  unfold E18 in H. assert (2 ^ 61 = 2305843009213693952) by reflexivity. lia.
Qed.

Lemma divpass_eq : forall x Hx a n j e (H : Acc (Zwf 0) (gap n j)),
  divpass x Hx a n j e H =
  match bdec (j <? n)%uint63 with
  | left Hj =>
      let c := a.[j] in
      if (c mod x =? 0)%uint63 then
        let ck := divfull x c 0 Hx (Zwf_well_founded 0 _) in
        divpass x Hx a.[j <- fst ck] n (j + 1)%uint63 (e + snd ck)%uint63 (Acc_inv H (dec_step n j Hj))
      else divpass x Hx a n (j + 1)%uint63 e (Acc_inv H (dec_step n j Hj))
  | right _ => (a, e)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma divpass_spec : forall z x Hx a n j e (H : Acc (Zwf 0) (gap n j)), gap n j = z ->
  1 < nv x -> nv n <= nv (PArray.length a) -> nv j <= nv n ->
  (forall k, nv j <= nv k < nv n -> 0 < nv a.[k] <= E18) ->
  nv e + 60 * (nv n - nv j) <= E18 ->
  let r := divpass x Hx a n j e H in
  PArray.length (fst r) = PArray.length a /\
  nv e <= nv (snd r) /\ nv (snd r) <= nv e + 60 * (nv n - nv j) /\
  (forall k, ~ (nv j <= nv k < nv n) -> (fst r).[k] = a.[k]) /\
  (forall k, nv j <= nv k < nv n ->
     (exists t, nv a.[k] = nv x ^ t * nv (fst r).[k]) /\ ~ (nv x | nv (fst r).[k]) /\
     0 < nv (fst r).[k]) /\
  prodA a (N.to_nat (nv n)) = nv x ^ (nv (snd r) - nv e) * prodA (fst r) (N.to_nat (nv n)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x Hx a n j e H Hz Hx1 Hn Hj Hc He. rewrite divpass_eq. cbv zeta.
  pose proof (ilength_bound a) as La.
  destruct (bdec (j <? n)%uint63) as [Hjn | Hjn].
  - pose proof Hjn as Hjn'. rewrite nv_ltb in Hjn'. apply N.ltb_lt in Hjn'.
    assert (Hj1 : nv (j + 1)%uint63 = nv j + 1) by (apply nv_add; change (nv 1%uint63) with 1; rewrite wB_val; lia).
    assert (Hdec : Zwf 0 (gap n (j + 1)%uint63) z) by (rewrite <- Hz; apply dec_step; auto).
    destruct (Hc j ltac:(lia)) as [Hc1 Hc2].
    rewrite nv_eqb, nv_mod. change (nv 0%uint63) with 0.
    destruct (N.eqb_spec (nv a.[j] mod nv x) 0) as [E | E].
    + destruct (divfull_specN x a.[j] 0%uint63 Hx (Zwf_well_founded 0 _)) as [t [T1 [T2 [T3 T4]]]];
        [lia | lia | change (nv 0%uint63) with 0; rewrite N.add_0_l; apply nv_bound |].
      change (nv 0%uint63) with 0 in T4. rewrite N.add_0_l in T4.
      set (c' := fst (divfull x a.[j] 0%uint63 Hx (Zwf_well_founded 0 (to_Z a.[j])))) in *.
      set (t' := snd (divfull x a.[j] 0%uint63 Hx (Zwf_well_founded 0 (to_Z a.[j])))) in *.
      assert (Ht60 : t <= 60).
      { apply (pow_le_E18 (nv x)); [lia|].
        assert (nv x ^ t <= nv a.[j]) by (rewrite T1; apply N.le_mul_r; lia). lia. }
      assert (Het : nv (e + t')%uint63 = nv e + t) by (rewrite <- T4; apply nv_add; rewrite T4; rewrite wB_val; unfold E18 in *; lia).
      assert (Hlen1 : PArray.length a.[j <- c'] = PArray.length a) by apply ilength_set.
      destruct (IH _ Hdec x Hx a.[j <- c'] n (j + 1)%uint63 (e + t')%uint63 (Acc_inv H (dec_step n j Hjn)) eq_refl Hx1)
        as [R1 [R2 [R3 [R4 [R5 R6]]]]].
      * rewrite Hlen1. auto.
      * lia.
      * intros k Hk. rewrite iget_set_other by (intro F; subst; lia). apply Hc. lia.
      * rewrite Het. lia.
      * cbv zeta in *. rewrite Het in R2, R3, R6. rewrite Hj1 in R3, R4, R5.
        set (r := divpass x Hx a.[j <- c'] n (j + 1)%uint63 (e + t')%uint63 (Acc_inv H (dec_step n j Hjn))) in *.
        assert (Rj : (fst r).[j] = c').
        { rewrite R4 by lia. apply iget_set_same. rewrite nv_ltb. apply N.ltb_lt. lia. }
        split; [rewrite R1; auto|]. split; [lia|]. split; [lia|]. split.
        -- intros k Hk. rewrite R4 by lia. apply iget_set_other. intro F; subst; lia.
        -- split.
           ++ intros k Hk. destruct (N.eq_dec (nv k) (nv j)) as [Ek | Ek].
              ** apply nv_inj in Ek. subst k. rewrite Rj. split; [exists t; exact T1 | split; auto].
              ** destruct (R5 k ltac:(lia)) as [[t2 Q1] Q2]. rewrite iget_set_other in Q1 by (intro F; subst; lia).
                 split; [exists t2; exact Q1 | exact Q2].
           ++ destruct (prodA_set a j c' (N.to_nat (nv n)) ltac:(lia)) as [P1 _].
              specialize (P1 ltac:(lia) ltac:(lia)).
              assert (Pa : prodA a (N.to_nat (nv n)) = nv x ^ t * prodA a.[j <- c'] (N.to_nat (nv n))).
              { apply (N.mul_cancel_r _ _ (nv c')); [lia|].
                rewrite <- P1, T1. ring. }
              rewrite Pa, R6, N.mul_assoc, <- N.pow_add_r. f_equal. f_equal. lia.
    + destruct (IH _ Hdec x Hx a n (j + 1)%uint63 e (Acc_inv H (dec_step n j Hjn)) eq_refl Hx1)
        as [R1 [R2 [R3 [R4 [R5 R6]]]]]; [auto | lia | intros k Hk; apply Hc; lia | lia |].
      cbv zeta in *. rewrite Hj1 in R3, R4, R5.
      set (r := divpass x Hx a n (j + 1)%uint63 e (Acc_inv H (dec_step n j Hjn))) in *.
      split; [auto|]. split; [lia|]. split; [lia|]. split.
      * intros k Hk. apply R4. lia.
      * split; [| exact R6].
        intros k Hk. destruct (N.eq_dec (nv k) (nv j)) as [Ek | Ek].
        -- apply nv_inj in Ek. subst k. rewrite R4 by lia.
           split; [exists 0; rewrite N.pow_0_r; ring | split; [| lia]].
           intro D. apply E. apply N.Lcm0.mod_divide. exact D.
        -- apply R5. lia.
  - rewrite nv_ltb in Hjn. apply N.ltb_ge in Hjn. simpl.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + intros k Hk. lia.
    + rewrite N.sub_diag, N.pow_0_r. ring.
Qed.

Lemma gcd_div_1 : forall y x c, (y | x) -> N.gcd x c = 1 -> N.gcd y c = 1.
Proof.
  intros y x c D E. apply N.divide_1_r. rewrite <- E. apply N.gcd_greatest.
  - eapply N.divide_trans; [apply N.gcd_divide_l | exact D].
  - apply N.gcd_divide_r.
Qed.

Lemma refine_spec : forall z a n j x (H : Acc (Zwf 0) (gap n j)), gap n j = z -> 1 < nv x ->
  let x' := refine a n j x H in
  1 < nv x' /\ (nv x' | nv x) /\
  forall k, nv j <= nv k < nv n -> (nv x' | nv a.[k]) \/ N.gcd (nv x') (nv a.[k]) = 1.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a n j x H Hz Hx. destruct H as [H']. simpl.
  destruct (bdec (j <? n)%uint63) as [Hjn | Hjn].
  - pose proof Hjn as Hjn'. rewrite nv_ltb in Hjn'. apply N.ltb_lt in Hjn'.
    assert (Hj1 : nv (j + 1)%uint63 = nv j + 1) by (apply nv_add; change (nv 1%uint63) with 1; pose proof (nv_bound n); lia).
    assert (Hdec : Zwf 0 (gap n (j + 1)%uint63) z) by (rewrite <- Hz; apply dec_step; auto).
    set (d := igcd x a.[j]).
    assert (Hd : nv d = N.gcd (nv x) (nv a.[j])) by apply nv_gcd.
    set (x2 := if (1 <? d)%uint63 && (d <? x)%uint63 then d else x).
    assert (X2 : 1 < nv x2 /\ (nv x2 | nv x) /\ ((nv x2 | nv a.[j]) \/ N.gcd (nv x2) (nv a.[j]) = 1)).
    { unfold x2. rewrite !nv_ltb. change (nv 1%uint63) with 1.
      destruct (N.ltb_spec 1 (nv d)), (N.ltb_spec (nv d) (nv x)); simpl.
      - split; [lia | split; [rewrite Hd; apply N.gcd_divide_l | left; rewrite Hd; apply N.gcd_divide_r]].
      - split; [lia | split; [apply N.divide_refl|]]. left.
        assert (nv d = nv x).
        { apply N.le_antisymm; auto. rewrite Hd. apply N.divide_pos_le; [lia | apply N.gcd_divide_l]. }
        rewrite <- H1, Hd. apply N.gcd_divide_r.
      - split; [lia | split; [apply N.divide_refl|]]. right.
        assert (nv d <> 0) by (rewrite Hd; intro E; apply N.gcd_eq_0 in E; lia). rewrite <- Hd. lia.
      - split; [lia | split; [apply N.divide_refl|]]. right.
        assert (nv d <> 0) by (rewrite Hd; intro E; apply N.gcd_eq_0 in E; lia). rewrite <- Hd. lia. }
    destruct X2 as [X21 [X22 X23]].
    destruct (IH _ Hdec a n (j + 1)%uint63 x2 (H' _ (dec_step n j Hjn)) eq_refl X21) as [R1 [R2 R3]].
    split; [exact R1|]. split; [eapply N.divide_trans; eauto|].
    intros k Hk. destruct (N.eq_dec (nv k) (nv j)) as [Ek | Ek].
    + apply nv_inj in Ek. subst k. destruct X23 as [D | D].
      * left. eapply N.divide_trans; eauto.
      * right. eapply gcd_div_1; eauto.
    + apply R3. lia.
  - split; [auto|]. split; [apply N.divide_refl|]. intros k Hk.
    rewrite nv_ltb in Hjn. apply N.ltb_ge in Hjn. lia.
Qed.

End Arr.

(* ================================================================== *)
(* Part 11. The main invariant and the slot step                       *)
(* ================================================================== *)

Section Main.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Definition cells_ok (a : array int) (n : int) : Prop :=
  forall k, nv k < nv n -> 0 < nv a.[k] <= E18.

Definition no_div (p : N) (aG : array int) (nG : int) (aL : array int) (nL : int) : Prop :=
  (forall k, nv k < nv nG -> ~ (p | nv aG.[k])) /\ (forall k, nv k < nv nL -> ~ (p | nv aL.[k])).

(* the done part (Gd, Ld) times the cells is (G, L); the done part has
   cd sequences, acc = cd mod 10^9+7; no prime of the done part divides a cell *)
Inductive INV (P : N) (gs ls : list N) (aG aL : array int) (nG nL : int) (acc : int) : Prop :=
  mkINV : forall Gd Ld cd,
    PArray.length aG = nG -> PArray.length aL = nL ->
    cells_ok aG nG -> cells_ok aL nL ->
    Gd * prodA aG (N.to_nat (nv nG)) = prod gs ->
    Ld * prodA aL (N.to_nat (nv nL)) = prod ls ->
    (forall p, primeN p -> (p | Gd * Ld) -> no_div p aG nG aL nL) ->
    0 < Gd -> 0 < Ld ->
    num_sequences P Gd Ld cd -> nv acc = cd mod MN ->
    INV P gs ls aG aL nG nL acc.

Lemma prime_div_pow : forall q x k, primeN q -> (q | x ^ k) -> (q | x).
Proof.
  intros q x k Hq. induction k as [| k IH] using N.peano_ind; intros D.
  - rewrite N.pow_0_r in D. exfalso. exact (primeN_not_div1 q Hq D).
  - rewrite N.pow_succ_r' in D. destruct (primeN_mult q _ _ Hq D); auto.
Qed.

(* x is atomic for the cell c: after dividing x out of c, no prime of x is left *)
Definition AT (x c : N) : Prop :=
  forall q t c', primeN q -> (q | x) -> c = x ^ t * c' -> ~ (x | c') -> ~ (q | c').

Lemma slot_step : forall P gs ls aG aL nG nL acc x Hx (f : int -> int),
  1 <= P -> nv nG <= 400 -> nv nL <= 400 -> INV P gs ls aG aL nG nL acc -> 1 < nv x ->
  (forall k, nv k < nv nG -> AT (nv x) (nv aG.[k])) ->
  (forall k, nv k < nv nL -> AT (nv x) (nv aL.[k])) ->
  let rG := divpass x Hx aG nG 0 0 (Zwf_well_founded 0 _) in
  let rL := divpass x Hx aL nL 0 0 (Zwf_well_founded 0 _) in
  (nv (snd rG) < nv (snd rL) -> nv (snd rL) <= 24000 ->
     exists cs, num_sequences P (nv x ^ nv (snd rG)) (nv x ^ nv (snd rL)) cs /\
                nv (f (snd rL - snd rG)%uint63) = cs mod MN) ->
  INV P gs ls (fst rG) (fst rL) nG nL (step_acc acc (snd rG) (snd rL) f) /\
  (forall k, nv k < nv nG -> (nv (fst rG).[k] | nv aG.[k])) /\
  (forall k, nv k < nv nL -> (nv (fst rL).[k] | nv aL.[k])) /\
  (forall k, nv k < nv nG -> ~ (nv x | nv (fst rG).[k])) /\
  (forall k, nv k < nv nL -> ~ (nv x | nv (fst rL).[k])).
Proof.
  intros P gs ls aG aL nG nL acc x Hx f HP HnG HnL Hinv Hx1 ATG ATL rG rL Hf.
  destruct Hinv as [Gd Ld cd LG LL CG CL PG PL Cop G0 L0 Cnt Acc].
  destruct (divpass_spec _ x Hx aG nG 0 0 (Zwf_well_founded 0 _) eq_refl Hx1)
    as [A1 [A2 [A3 [A4 [A5 A6]]]]]; change (nv 0%uint63) with 0;
    [rewrite LG; lia | lia | intros k Hk; apply CG; lia | unfold E18; lia |].
  destruct (divpass_spec _ x Hx aL nL 0 0 (Zwf_well_founded 0 _) eq_refl Hx1)
    as [B1 [B2 [B3 [B4 [B5 B6]]]]]; change (nv 0%uint63) with 0;
    [rewrite LL; lia | lia | intros k Hk; apply CL; lia | unfold E18; lia |].
  cbv zeta in *. fold rG rL in A1, A2, A3, A4, A5, A6, B1, B2, B3, B4, B5, B6.
  change (nv 0%uint63) with 0 in *. rewrite N.sub_0_r in A6, B6.
  set (eg := snd rG) in *. set (el := snd rL) in *.
  assert (PGp : 0 < prodA aG (N.to_nat (nv nG))).
  { apply prodA_pos; [rewrite N2Nat.id; lia | intros k Hk; apply CG; lia]. }
  assert (PLp : 0 < prodA aL (N.to_nat (nv nL))).
  { apply prodA_pos; [rewrite N2Nat.id; lia | intros k Hk; apply CL; lia]. }
  assert (Hcv : coprime_vp Gd Ld (nv x ^ nv eg) (nv x ^ nv el)).
  { intros q Hq. pose proof (primeN_gt1 q Hq) as Hq1.
    destruct (divide_dec q (nv x) ltac:(lia)) as [D | D].
    - destruct (divide_dec q (Gd * Ld) ltac:(lia)) as [D2 | D2].
      + right. destruct (Cop q Hq D2) as [N1 N2].
        assert (Z1 : nv eg = 0).
        { destruct (N.eq_dec (nv eg) 0) as [E | E]; [exact E | exfalso].
          assert (Dp : (q | prodA aG (N.to_nat (nv nG)))).
          { rewrite A6. apply N.divide_mul_l. apply div_pow; auto. }
          destruct (prodA_prime aG (N.to_nat (nv nG)) q ltac:(rewrite N2Nat.id; lia) Hq Dp)
            as [k [K1 K2]]. apply (N1 k); auto. lia. }
        assert (Z2 : nv el = 0).
        { destruct (N.eq_dec (nv el) 0) as [E | E]; [exact E | exfalso].
          assert (Dp : (q | prodA aL (N.to_nat (nv nL)))).
          { rewrite B6. apply N.divide_mul_l. apply div_pow; auto. }
          destruct (prodA_prime aL (N.to_nat (nv nL)) q ltac:(rewrite N2Nat.id; lia) Hq Dp)
            as [k [K1 K2]]. apply (N2 k); auto. lia. }
        rewrite Z1, Z2, N.pow_0_r. split; apply vp_1; auto.
      + left. split; apply vp_zero_iff; auto; intro D3; apply D2;
          [apply N.divide_mul_l | apply N.divide_mul_r]; auto.
    - right. split.
      + apply (proj2 (vp_zero_iff q _ Hq (pow_pos (nv x) (nv eg) ltac:(lia)))). intro D3; apply D.
        eapply prime_div_pow; eauto.
      + apply (proj2 (vp_zero_iff q _ Hq (pow_pos (nv x) (nv el) ltac:(lia)))). intro D3; apply D.
        eapply prime_div_pow; eauto. }
  assert (Hf' : nv eg < nv el -> exists cs, num_sequences P (nv x ^ nv eg) (nv x ^ nv el) cs /\
                                   nv (f (el - eg)%uint63) = cs mod MN).
  { intros L. apply Hf; auto. lia. }
  destruct (step_ok P Gd Ld cd acc (nv x) eg el f HP Hx1 G0 L0 Cnt Acc Hcv Hf') as [cd' [C1 C2]].
  assert (Div : forall (a r : array int) k, (exists t, nv a.[k] = nv x ^ t * nv r.[k]) -> (nv r.[k] | nv a.[k])).
  { intros a r k [t Ht]. rewrite Ht. apply N.divide_factor_r. }
  split; [| split].
  - apply (mkINV _ _ _ _ _ _ _ _ (Gd * nv x ^ nv eg) (Ld * nv x ^ nv el) cd').
    + rewrite A1. auto.
    + rewrite B1. auto.
    + intros k Hk. destruct (A5 k ltac:(lia)) as [[t Ht] [_ Pos]].
      pose proof (CG k Hk) as [_ Le].
      assert (nv (fst rG).[k] <= nv aG.[k]) by (rewrite Ht; apply N.le_mul_l; apply N.pow_nonzero; lia).
      split; lia.
    + intros k Hk. destruct (B5 k ltac:(lia)) as [[t Ht] [_ Pos]].
      pose proof (CL k Hk) as [_ Le].
      assert (nv (fst rL).[k] <= nv aL.[k]) by (rewrite Ht; apply N.le_mul_l; apply N.pow_nonzero; lia).
      split; lia.
    + rewrite <- PG, A6. ring.
    + rewrite <- PL, B6. ring.
    + intros q Hq D.
      assert (Hor : (q | Gd * Ld) \/ (q | nv x)).
      { replace (Gd * nv x ^ nv eg * (Ld * nv x ^ nv el)) with ((Gd * Ld) * (nv x ^ nv eg * nv x ^ nv el)) in D by ring.
        destruct (primeN_mult q _ _ Hq D) as [D1 | D1]; [left; auto | right].
        destruct (primeN_mult q _ _ Hq D1) as [D2 | D2]; eapply prime_div_pow; eauto. }
      destruct Hor as [D1 | D1].
      * destruct (Cop q Hq D1) as [N1 N2]. split.
        -- intros k Hk Dk. apply (N1 k Hk). eapply N.divide_trans; [exact Dk|]. apply (Div aG _). apply A5. lia.
        -- intros k Hk Dk. apply (N2 k Hk). eapply N.divide_trans; [exact Dk|]. apply (Div aL _). apply B5. lia.
      * split.
        -- intros k Hk. destruct (A5 k ltac:(lia)) as [[t Ht] [Nx _]]. exact (ATG k Hk q t _ Hq D1 Ht Nx).
        -- intros k Hk. destruct (B5 k ltac:(lia)) as [[t Ht] [Nx _]]. exact (ATL k Hk q t _ Hq D1 Ht Nx).
    + apply N.mul_pos_pos; [auto | apply pow_pos; lia].
    + apply N.mul_pos_pos; [auto | apply pow_pos; lia].
    + exact C1.
    + exact C2.
  - intros k Hk. apply (Div aG _). apply A5. lia.
  - split; [intros k Hk; apply (Div aL _); apply B5; lia|].
    split; intros k Hk; [apply A5 | apply B5]; lia.
Qed.

End Main.

Section Eqs.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

Lemma ph1_eq : forall pr np k aG aL nG nL P acc (H : Acc (Zwf 0) (gap np k)),
  ph1 pr np k aG aL nG nL P acc H =
  match bdec (k <? np) with
  | left Hk =>
      let p := pr.[k] in
      match bdec (1 <? p) with
      | left Hp =>
          let rG := divpass p Hp aG nG 0 0 (Zwf_well_founded 0 _) in
          let rL := divpass p Hp aL nL 0 0 (Zwf_well_founded 0 _) in
          ph1 pr np (k + 1) (fst rG) (fst rL) nG nL P
            (step_acc acc (snd rG) (snd rL) (fun e => fmod e P))
            (Acc_inv H (dec_step np k Hk))
      | right _ => (aG, aL, acc)
      end
  | right _ => (aG, aL, acc)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma peel_eq : forall pr np aG aL nG nL sel i P acc (H : Acc (Zwf 0) (φ (sel_get sel aG aL i))),
  peel pr np aG aL nG nL sel i P acc H =
  let c := sel_get sel aG aL i in
  match bdec (1 <? c) with
  | left Hc =>
      let x := refine aL nL 0 (refine aG nG 0 c (Zwf_well_founded 0 _)) (Zwf_well_founded 0 _) in
      match bdec (1 <? x) with
      | left Hx =>
          let rG := divpass x Hx aG nG 0 0 (Zwf_well_founded 0 _) in
          let rL := divpass x Hx aL nL 0 0 (Zwf_well_founded 0 _) in
          let acc' := step_acc acc (snd rG) (snd rL) (fun e => contrib pr np x e P) in
          match bdec (sel_get sel (fst rG) (fst rL) i <? c) with
          | left Hd => peel pr np (fst rG) (fst rL) nG nL sel i P acc' (Acc_inv H (dec_lt c _ Hd))
          | right _ => (fst rG, fst rL, acc')
          end
      | right _ => (aG, aL, acc)
      end
  | right _ => (aG, aL, acc)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ph2_eq : forall pr np aG aL nG nL sel n i P acc (H : Acc (Zwf 0) (gap n i)),
  ph2 pr np aG aL nG nL sel n i P acc H =
  match bdec (i <? n) with
  | left Hi =>
      let r := peel pr np aG aL nG nL sel i P acc (Zwf_well_founded 0 _) in
      ph2 pr np (fst (fst r)) (snd (fst r)) nG nL sel n (i + 1) P (snd r)
        (Acc_inv H (dec_step n i Hi))
  | right _ => (aG, aL, acc)
  end.
Proof. intros. destruct H. reflexivity. Qed.

End Eqs.

(* ================================================================== *)
(* Part 12. The two phases                                             *)
(* ================================================================== *)

Section Phases.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Lemma nv_esub : forall eg el, nv eg < nv el -> nv (el - eg)%uint63 = nv el - nv eg.
Proof. intros. apply nv_sub. lia. Qed.

Lemma fmod_slot : forall P Pi X eg el c, nv Pi = P -> nv eg < nv el -> nv el <= 24000 ->
  num_sequences P (X ^ N.of_nat (N.to_nat (nv eg))) (X ^ N.of_nat (N.to_nat (nv el))) c ->
  Z.of_N c = fP P (Z.of_nat (N.to_nat (nv el) - N.to_nat (nv eg))) ->
  exists cs, num_sequences P (X ^ nv eg) (X ^ nv el) cs /\ nv (fmod (el - eg)%uint63 Pi) = cs mod MN.
Proof.
  intros P Pi X eg el c HP H1 H2 C1 C2. exists c. rewrite !N2Nat.id in C1. split; auto.
  apply N2Z.inj. rewrite fmod_spec; rewrite nv_esub by auto; try lia.
  rewrite N2Z.inj_mod, C2, HP. f_equal. f_equal. lia.
Qed.

Lemma contrib_ok : forall pr np x eg el Pi, sieve_ok pr np -> roughN (nv x) -> 1 < nv x -> nv x <= E18 ->
  1 <= nv Pi -> nv eg < nv el -> nv el <= 24000 ->
  exists cs, num_sequences (nv Pi) (nv x ^ nv eg) (nv x ^ nv el) cs /\
             nv (contrib pr np x (el - eg)%uint63 Pi) = cs mod MN.
Proof.
  intros pr np x eg el Pi Hs Hr Hx1 Hx18 HP H1 H2. unfold contrib.
  destruct (classify_spec pr np x Hs Hr Hx1 Hx18) as [K1 [K2 K3]].
  destruct (classify pr np x).
  - destruct (slot_prime (nv Pi) (nv x) (N.to_nat (nv eg)) (N.to_nat (nv el)) HP (K1 eq_refl) ltac:(lia))
      as [c [C1 C2]].
    eapply fmod_slot; eauto.
  - destruct (K2 eq_refl) as [s [Es Ps]].
    destruct (slot_square (nv Pi) (nv x) s (N.to_nat (nv eg)) (N.to_nat (nv el)) HP Es Ps ltac:(lia))
      as [c [C1 C2]].
    exists c. rewrite !N2Nat.id in C1. split; auto.
    assert (Ee : nv ((el - eg) + (el - eg))%uint63 = 2 * (nv el - nv eg)).
    { rewrite nv_add; rewrite nv_esub by auto; [lia | rewrite wB_val; lia]. }
    apply N2Z.inj. rewrite fmod_spec; rewrite Ee; try lia.
    rewrite N2Z.inj_mod, C2. f_equal. f_equal. lia.
  - destruct (K3 eq_refl) as [q [r [Eqr [Pq [Pr Nqr]]]]].
    destruct (slot_semi (nv Pi) (nv x) q r (N.to_nat (nv eg)) (N.to_nat (nv el)) HP Eqr Pq Pr Nqr ltac:(lia))
      as [c [C1 C2]].
    exists c. rewrite !N2Nat.id in C1. split; auto.
    set (fv := fmod (el - eg)%uint63 Pi).
    assert (Fv : Z.of_N (nv fv) = (fP (nv Pi) (Z.of_N (nv el - nv eg)) mod 1000000007)%Z).
    { unfold fv. rewrite fmod_spec; rewrite nv_esub by auto; [reflexivity | lia | lia]. }
    assert (Fb : nv fv < MN).
    { apply N2Z.inj_lt. rewrite Fv. unfold MN. simpl Z.of_N. apply Z.mod_pos_bound. lia. }
    rewrite nv_mulmod, nvMODP; [| rewrite nvMODP; unfold MN; lia | rewrite nvMODP; exact Fb | rewrite nvMODP; exact Fb].
    apply N2Z.inj. rewrite !N2Z.inj_mod, N2Z.inj_mul, Fv, C2. unfold MN. simpl Z.of_N.
    replace (Z.of_N (nv el - nv eg)) with (Z.of_nat (N.to_nat (nv el) - N.to_nat (nv eg))) by lia.
    rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma AT_prime : forall p c, primeN p -> AT p c.
Proof.
  intros p c Hp q t c' Hq D _ Nx Dq. destruct Hp as [_ Hd]. destruct (Hd q D) as [E | E].
  - pose proof (primeN_gt1 q Hq). lia.
  - subst. contradiction.
Qed.

Lemma AT_atomic : forall x c, roughN c -> 0 < c -> c <= E18 ->
  ((x | c) \/ N.gcd x c = 1) -> AT x c.
Proof.
  intros x c Hr Hc H18 [D | G] q t c' Hq Dq Hct Nx Dqc.
  - apply (rough_atomic c x t c' q Hr Hc ltac:(unfold E18, B6 in *; lia) D Hct Nx Hq Dq Dqc).
  - assert (Dc : (q | c)) by (rewrite Hct; apply N.divide_mul_r; exact Dqc).
    assert (Dg : (q | N.gcd x c)) by (apply N.gcd_greatest; auto).
    rewrite G in Dg. exact (primeN_not_div1 q Hq Dg).
Qed.

Lemma ph1_spec : forall z pr np k aG aL nG nL Pi acc gs ls (H : Acc (Zwf 0) (gap np k)), gap np k = z ->
  sieve_ok pr np -> 1 <= nv Pi -> nv nG <= 400 -> nv nL <= 400 ->
  INV (nv Pi) gs ls aG aL nG nL acc -> nv k <= nv np ->
  (forall k', nv k' < nv k -> no_div (nv pr.[k']) aG nG aL nL) ->
  let r := ph1 pr np k aG aL nG nL Pi acc H in
  INV (nv Pi) gs ls (fst (fst r)) (snd (fst r)) nG nL (snd r) /\
  (forall k', nv k' < nv np -> no_div (nv pr.[k']) (fst (fst r)) nG (snd (fst r)) nL).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros pr np k aG aL nG nL Pi acc gs ls H Hz Hs HP HnG HnL Hinv Hk Hnd.
  rewrite ph1_eq. cbv zeta.
  pose proof Hs as [Snp [Slen [Sp Sc]]].
  destruct (bdec (k <? np)%uint63) as [Hkn | Hkn].
  2: { cbn [fst snd]. split; auto. intros k' Hk'. apply Hnd. rewrite nv_ltb in Hkn. apply N.ltb_ge in Hkn. lia. }
  pose proof Hkn as Hkn'. rewrite nv_ltb in Hkn'. apply N.ltb_lt in Hkn'.
  destruct (Sp k Hkn') as [Pp Pp1]. pose proof (primeN_gt1 _ Pp) as Pp2.
  destruct (bdec (1 <? pr.[k])%uint63) as [Hp | Hp].
  2: { exfalso. rewrite nv_ltb in Hp. apply N.ltb_ge in Hp. change (nv 1%uint63) with 1 in Hp. lia. }
  destruct (slot_step (nv Pi) gs ls aG aL nG nL acc pr.[k] Hp (fun e => fmod e Pi) HP HnG HnL Hinv Pp2
              (fun k _ => AT_prime _ _ Pp) (fun k _ => AT_prime _ _ Pp)) as [S1 [S2 [S3 [S4 S5]]]].
  { intros L1 L2.
    match type of L1 with nv ?a < nv ?b =>
      destruct (slot_prime (nv Pi) (nv pr.[k]) (N.to_nat (nv a)) (N.to_nat (nv b)) HP Pp ltac:(lia))
        as [c [C1 C2]] end.
    eapply fmod_slot; eauto. }
  assert (Hk1 : nv (k + 1)%uint63 = nv k + 1) by (apply nv_add; change (nv 1%uint63) with 1; rewrite wB_val; lia).
  apply (IH (gap np (k + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; auto)); auto.
  - rewrite Hk1. lia.
  - intros k' Hk'. rewrite Hk1 in Hk'. destruct (N.eq_dec (nv k') (nv k)) as [E | E].
    + apply nv_inj in E. subst k'. split; [exact S4 | exact S5].
    + destruct (Hnd k' ltac:(lia)) as [N1 N2]. split.
      * intros j Hj Dj. apply (N1 j Hj). eapply N.divide_trans; [exact Dj | apply S2; auto].
      * intros j Hj Dj. apply (N2 j Hj). eapply N.divide_trans; [exact Dj | apply S3; auto].
Qed.

Definition rough_cells (aG : array int) (nG : int) (aL : array int) (nL : int) : Prop :=
  (forall k, nv k < nv nG -> roughN (nv aG.[k])) /\ (forall k, nv k < nv nL -> roughN (nv aL.[k])).

Lemma peel_spec : forall z pr np aG aL nG nL sel i Pi acc gs ls
    (H : Acc (Zwf 0) (φ (sel_get sel aG aL i))), (φ (sel_get sel aG aL i)) = z ->
  sieve_ok pr np -> 1 <= nv Pi -> nv nG <= 400 -> nv nL <= 400 ->
  INV (nv Pi) gs ls aG aL nG nL acc -> rough_cells aG nG aL nL ->
  nv i < nv (if sel then nL else nG) ->
  let r := peel pr np aG aL nG nL sel i Pi acc H in
  INV (nv Pi) gs ls (fst (fst r)) (snd (fst r)) nG nL (snd r) /\
  rough_cells (fst (fst r)) nG (snd (fst r)) nL /\
  nv (sel_get sel (fst (fst r)) (snd (fst r)) i) = 1 /\
  (forall k, nv k < nv nG -> (nv (fst (fst r)).[k] | nv aG.[k])) /\
  (forall k, nv k < nv nL -> (nv (snd (fst r)).[k] | nv aL.[k])).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros pr np aG aL nG nL sel i Pi acc gs ls H Hz Hs HP HnG HnL Hinv [RG RL] Hi.
  rewrite peel_eq. cbv zeta.
  pose proof Hinv as [Gd Ld cd LG LL CG CL _ _ _ _ _ _ _].
  set (c := sel_get sel aG aL i) in *.
  assert (Hcf : roughN (nv c) /\ 0 < nv c <= E18).
  { unfold c, sel_get. destruct sel; split; [apply RL | apply CL | apply RG | apply CG]; auto. }
  destruct Hcf as [Rc Cc].
  destruct (bdec (1 <? c)%uint63) as [Hc | Hc].
  2: { cbn [fst snd]. split; [exact Hinv|]. split; [split; auto|].
       rewrite nv_ltb in Hc. apply N.ltb_ge in Hc. change (nv 1%uint63) with 1 in Hc.
       split; [fold c; lia|]. split; intros; apply N.divide_refl. }
  pose proof Hc as Hc'. rewrite nv_ltb in Hc'. apply N.ltb_lt in Hc'. change (nv 1%uint63) with 1 in Hc'.
  destruct (refine_spec _ aG nG 0%uint63 c (Zwf_well_founded 0 _) eq_refl Hc') as [X01 [X02 X03]].
  set (x0 := refine aG nG 0 c (Zwf_well_founded 0 (gap nG 0))) in *.
  destruct (refine_spec _ aL nL 0%uint63 x0 (Zwf_well_founded 0 _) eq_refl X01) as [X1 [X2 X3]].
  set (x := refine aL nL 0 x0 (Zwf_well_founded 0 (gap nL 0))) in *.
  change (nv 0%uint63) with 0 in *.
  destruct (bdec (1 <? x)%uint63) as [Hx | Hx].
  2: { exfalso. rewrite nv_ltb in Hx. apply N.ltb_ge in Hx. change (nv 1%uint63) with 1 in Hx. lia. }
  assert (Dxc : (nv x | nv c)) by exact (N.divide_trans _ _ _ X2 X02).
  assert (Rx : roughN (nv x)) by exact (rough_div _ _ Rc Dxc).
  assert (Bx : nv x <= E18) by (apply N.divide_pos_le in Dxc; lia).
  destruct (slot_step (nv Pi) gs ls aG aL nG nL acc x Hx (fun e => contrib pr np x e Pi) HP HnG HnL Hinv X1)
    as [S1 [S2 [S3 [S4 S5]]]].
  { intros k Hk. apply AT_atomic; [apply RG; auto | apply CG; auto | apply CG; auto|].
    destruct (X03 k ltac:(lia)) as [D | G]; [left; exact (N.divide_trans _ _ _ X2 D) | right; exact (gcd_div_1 _ _ _ X2 G)]. }
  { intros k Hk. apply AT_atomic; [apply RL; auto | apply CL; auto | apply CL; auto|]. apply X3. lia. }
  { intros L1 L2. apply contrib_ok; auto. }
  set (rG := divpass x Hx aG nG 0 0 (Zwf_well_founded 0 (gap nG 0))) in *.
  set (rL := divpass x Hx aL nL 0 0 (Zwf_well_founded 0 (gap nL 0))) in *.
  set (acc' := step_acc acc (snd rG) (snd rL) (fun e => contrib pr np x e Pi)) in *.
  assert (Hc'1 : (nv (sel_get sel (fst rG) (fst rL) i) | nv c) /\ ~ (nv x | nv (sel_get sel (fst rG) (fst rL) i))).
  { unfold c, sel_get. destruct sel; split; [apply S3 | apply S5 | apply S2 | apply S4]; auto. }
  destruct Hc'1 as [Dc' Nc'].
  assert (Lt : nv (sel_get sel (fst rG) (fst rL) i) < nv c).
  { assert (nv (sel_get sel (fst rG) (fst rL) i) <= nv c) by (apply N.divide_pos_le; [lia | exact Dc']).
    destruct (N.eq_dec (nv (sel_get sel (fst rG) (fst rL) i)) (nv c)) as [E | E]; [| lia].
    exfalso. apply Nc'. rewrite E. exact Dxc. }
  destruct (bdec (sel_get sel (fst rG) (fst rL) i <? c)%uint63) as [Hd | Hd].
  2: { exfalso. rewrite nv_ltb in Hd. apply N.ltb_ge in Hd. lia. }
  assert (Rn : rough_cells (fst rG) nG (fst rL) nL).
  { split; intros k Hk; [apply (rough_div (nv aG.[k])); [apply RG; exact Hk | apply S2; exact Hk]
                       | apply (rough_div (nv aL.[k])); [apply RL; exact Hk | apply S3; exact Hk]]. }
  destruct (IH (φ (sel_get sel (fst rG) (fst rL) i)) ltac:(rewrite <- Hz; apply dec_lt; auto)
              pr np (fst rG) (fst rL) nG nL sel i Pi acc' gs ls (Acc_inv H (dec_lt c _ Hd)) eq_refl
              Hs HP HnG HnL S1 Rn Hi) as [T1 [T2 [T3 [T4 T5]]]].
  split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split.
  - intros k Hk. eapply N.divide_trans; [apply T4; auto | apply S2; auto].
  - intros k Hk. eapply N.divide_trans; [apply T5; auto | apply S3; auto].
Qed.

Lemma ph2_spec : forall z (pr : array int) (np : int) (aG aL : array int) (nG nL : int) (sel : bool) (n i Pi acc : int) (gs ls : list N)
    (H : Acc (Zwf 0) (gap n i)), gap n i = z ->
  sieve_ok pr np -> 1 <= nv Pi -> nv nG <= 400 -> nv nL <= 400 -> n = (if sel then nL else nG) ->
  INV (nv Pi) gs ls aG aL nG nL acc -> rough_cells aG nG aL nL ->
  (forall k, nv k < nv i -> nv (sel_get sel aG aL k) = 1) ->
  (sel = true -> forall k, nv k < nv nG -> nv aG.[k] = 1) -> nv i <= nv n ->
  let r := ph2 pr np aG aL nG nL sel n i Pi acc H in
  INV (nv Pi) gs ls (fst (fst r)) (snd (fst r)) nG nL (snd r) /\
  rough_cells (fst (fst r)) nG (snd (fst r)) nL /\
  (forall k, nv k < nv n -> nv (sel_get sel (fst (fst r)) (snd (fst r)) k) = 1) /\
  (sel = true -> forall k, nv k < nv nG -> nv (fst (fst r)).[k] = 1).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros pr np aG aL nG nL sel n i Pi acc gs ls H Hz Hs HP HnG HnL Hn Hinv Hr Hone HG Hin.
  rewrite ph2_eq. cbv zeta.
  destruct (bdec (i <? n)%uint63) as [Hi | Hi].
  2: { cbn [fst snd]. split; [exact Hinv|]. split; [exact Hr|]. split; [| exact HG].
       intros k Hk. apply Hone. rewrite nv_ltb in Hi. apply N.ltb_ge in Hi. lia. }
  pose proof Hi as Hi'. rewrite nv_ltb in Hi'. apply N.ltb_lt in Hi'.
  destruct (peel_spec _ pr np aG aL nG nL sel i Pi acc gs ls (Zwf_well_founded 0 _) eq_refl Hs HP HnG HnL Hinv Hr
              ltac:(rewrite <- Hn; exact Hi')) as [P1 [P2 [P3 [P4 P5]]]].
  set (r := peel pr np aG aL nG nL sel i Pi acc (Zwf_well_founded 0 (φ (sel_get sel aG aL i)))) in *.
  assert (Hi1 : nv (i + 1)%uint63 = nv i + 1) by (apply nv_add; change (nv 1%uint63) with 1; pose proof (nv_bound n); lia).
  refine (IH (gap n (i + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; auto) pr np (fst (fst r)) (snd (fst r))
            nG nL sel n (i + 1)%uint63 Pi (snd r) gs ls _ eq_refl Hs HP HnG HnL Hn P1 P2 _ _ _).
  - intros k Hk. rewrite Hi1 in Hk. destruct (N.eq_dec (nv k) (nv i)) as [E | E].
    + apply nv_inj in E. subst k. exact P3.
    + apply N.divide_1_r. rewrite <- (Hone k ltac:(lia)). unfold sel_get. destruct sel.
      * apply P5. rewrite <- Hn. lia.
      * apply P4. rewrite <- Hn. lia.
  - intros E k Hk. apply N.divide_1_r. rewrite <- (HG E k Hk). apply P4. auto.
  - rewrite Hi1. lia.
Qed.

End Phases.

(* ================================================================== *)
(* Part 13. The contract                                               *)
(* ================================================================== *)

Section Final.
Local Open Scope uint63_scope.
Local Open Scope N_scope.

Lemma iget_copy : forall (t : array int) i, (PArray.copy t).[i] = t.[i].
Proof. intros t i. exact (get_copy int t i). Qed.

Lemma ilength_copy : forall (t : array int), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros t. exact (length_copy int t). Qed.

Lemma firstn_snoc : forall (l : list N) n v, nth_error l n = Some v -> firstn (S n) l = firstn n l ++ [v].
Proof.
  induction l as [| a l IH]; intros [| n] v H; simpl in *; try discriminate.
  - inversion H; subst. reflexivity.
  - rewrite (IH n v H). reflexivity.
Qed.

Lemma prod_app : forall l1 l2, prod (l1 ++ l2) = prod l1 * prod l2.
Proof.
  induction l1 as [| a l1 IH]; intros l2.
  - change (prod ([] ++ l2)) with (prod l2). change (prod []) with 1. ring.
  - change (prod ((a :: l1) ++ l2)) with (a * prod (l1 ++ l2)). change (prod (a :: l1)) with (a * prod l1).
    rewrite IH. ring.
Qed.

Lemma prodA_list' : forall a l n, (n <= length l)%nat -> N.of_nat n < 4194304 ->
  (forall k, (k < n)%nat -> nth_error l k = Some (cl a k)) -> prodA a n = prod (firstn n l).
Proof.
  intros a l n Hn Hb H. revert Hn Hb H. induction n as [| n IH]; intros Hn Hb H; [reflexivity|].
  simpl prodA. rewrite IH; [| lia | lia | intros k Hk; apply H; lia].
  rewrite (firstn_snoc l n (cl a n)) by (apply H; lia). rewrite prod_app.
  change (prod [cl a n]) with (cl a n * 1). ring.
Qed.

Lemma init_cells : forall (x : array int) l, nv (PArray.length x) = N.of_nat (length l) ->
  (forall k, (k < length l)%nat -> exists m, nth_error l k = Some m /\ nv x.[of_Z (Z.of_nat k)] = m) ->
  Forall (fun g => 1 <= g <= 10 ^ 18) l -> (length l <= 400)%nat ->
  PArray.length (PArray.copy x) = PArray.length x /\
  cells_ok (PArray.copy x) (PArray.length x) /\
  1 * prodA (PArray.copy x) (N.to_nat (nv (PArray.length x))) = prod l.
Proof.
  intros x l Lx Cx Fl Ll. split; [apply ilength_copy|]. split.
  - intros k Hk. rewrite iget_copy. rewrite Lx in Hk.
    destruct (Cx (N.to_nat (nv k)) ltac:(lia)) as [m [M1 M2]].
    assert (Ek : of_Z (Z.of_nat (N.to_nat (nv k))) = k) by (apply idx_eq; [rewrite wB_val; lia | lia]).
    rewrite Ek in M2. rewrite M2. rewrite Forall_forall in Fl.
    pose proof (Fl m (nth_error_In _ _ M1)). unfold E18. lia.
  - rewrite N.mul_1_l, Lx, Nat2N.id.
    rewrite prodA_list' with (l := l); [rewrite firstn_all; reflexivity | lia | lia |].
    intros k Hk. destruct (Cx k Hk) as [m [M1 M2]]. rewrite M1. f_equal. unfold cl.
    rewrite iget_copy. symmetry. exact M2.
Qed.

Lemma atp_impl_correct : forall (P : N) (gs ls : list N) (p : uint) (x y : array uint),
  valid_input P gs ls -> repr p P -> repr x gs -> repr y ls ->
  exists o : N, repr (atp_impl p x y) o /\ atrivialpursuit_spec P gs ls o.
Proof.
  intros P gs ls p x y Hv Hp [Lx0 Cx0] [Ly0 Cy0].
  destruct Hv as [VP VN VM VG VL]. unfold len in VN, VM.
  assert (Hp' : nv p = P) by exact Hp.
  assert (LX : nv (PArray.length x) = N.of_nat (length gs)).
  { assert (E : (φ (PArray.length x)) = Z.of_nat (length gs)) by (symmetry; exact Lx0). unfold nv. rewrite E. lia. }
  assert (LY : nv (PArray.length y) = N.of_nat (length ls)).
  { assert (E : (φ (PArray.length y)) = Z.of_nat (length ls)) by (symmetry; exact Ly0). unfold nv. rewrite E. lia. }
  assert (CX : forall k, (k < length gs)%nat -> exists m, nth_error gs k = Some m /\ nv x.[of_Z (Z.of_nat k)] = m).
  { intros k Hk. destruct (Cx0 k Hk) as [m [M1 M2]]. exists m. split; [exact M1 | exact M2]. }
  assert (CY : forall k, (k < length ls)%nat -> exists m, nth_error ls k = Some m /\ nv y.[of_Z (Z.of_nat k)] = m).
  { intros k Hk. destruct (Cy0 k Hk) as [m [M1 M2]]. exists m. split; [exact M1 | exact M2]. }
  clear Lx0 Cx0 Ly0 Cy0 Hp.
  destruct (init_cells x gs LX CX VG ltac:(lia)) as [IX1 [IX2 IX3]].
  destruct (init_cells y ls LY CY VL ltac:(lia)) as [IY1 [IY2 IY3]].
  unfold atp_impl.
  pose proof sieve_spec as Hs.
  set (pr := fst sieve) in *. set (np := snd sieve) in *.
  set (nG := PArray.length x) in *. set (nL := PArray.length y) in *.
  assert (HP : 1 <= nv p) by lia.
  assert (HnG : nv nG <= 400) by lia. assert (HnL : nv nL <= 400) by lia.
  assert (I0 : INV (nv p) gs ls (PArray.copy x) (PArray.copy y) nG nL 1%uint63).
  { refine (mkINV _ _ _ _ _ _ _ _ 1 1 1 IX1 IY1 IX2 IY2 IX3 IY3 _ ltac:(lia) ltac:(lia) _ _).
    - intros q Hq D. exfalso. rewrite N.mul_1_l in D. exact (primeN_not_div1 q Hq D).
    - apply count_eq; lia.
    - reflexivity. }
  destruct (ph1_spec _ pr np 0%uint63 (PArray.copy x) (PArray.copy y) nG nL p 1%uint63 gs ls
              (Zwf_well_founded 0 _) eq_refl Hs HP HnG HnL I0 ltac:(change (nv 0%uint63) with 0; lia)
              ltac:(intros k' Hk'; change (nv 0%uint63) with 0 in Hk'; lia)) as [J1 J2].
  set (r1 := ph1 pr np 0 (PArray.copy x) (PArray.copy y) nG nL p 1 (Zwf_well_founded 0 (gap np 0))) in *.
  assert (R1 : rough_cells (fst (fst r1)) nG (snd (fst r1)) nL).
  { split; intros k Hk; apply (rough_of_sieve pr np); auto; intros k' Hk'; destruct (J2 k' Hk') as [N1 N2];
      [apply N1 | apply N2]; auto. }
  destruct (ph2_spec _ pr np (fst (fst r1)) (snd (fst r1)) nG nL false nG 0%uint63 p (snd r1) gs ls
              (Zwf_well_founded 0 _) eq_refl Hs HP HnG HnL eq_refl J1 R1
              ltac:(intros k Hk; change (nv 0%uint63) with 0 in Hk; lia) ltac:(discriminate)
              ltac:(change (nv 0%uint63) with 0; lia)) as [K1 [K2 [K3 _]]].
  set (r2 := ph2 pr np (fst (fst r1)) (snd (fst r1)) nG nL false nG 0 p (snd r1) (Zwf_well_founded 0 (gap nG 0))) in *.
  destruct (ph2_spec _ pr np (fst (fst r2)) (snd (fst r2)) nG nL true nL 0%uint63 p (snd r2) gs ls
              (Zwf_well_founded 0 _) eq_refl Hs HP HnG HnL eq_refl K1 K2
              ltac:(intros k Hk; change (nv 0%uint63) with 0 in Hk; lia) ltac:(intros _; exact K3)
              ltac:(change (nv 0%uint63) with 0; lia)) as [M1 [_ [M3 M4]]].
  set (r3 := ph2 pr np (fst (fst r2)) (snd (fst r2)) nG nL true nL 0 p (snd r2) (Zwf_well_founded 0 (gap nL 0))) in *.
  destruct M1 as [Gd Ld cd _ _ _ _ PG PL _ _ _ Cnt Acc].
  rewrite prodA_one in PG; [| rewrite N2Nat.id; lia | rewrite N2Nat.id; intros k Hk; apply (M4 eq_refl); auto].
  rewrite prodA_one in PL; [| rewrite N2Nat.id; lia | rewrite N2Nat.id; intros k Hk; apply M3; auto].
  rewrite N.mul_1_r in PG, PL. subst Gd Ld.
  exists (nv (snd r3)). split; [reflexivity|].
  exists cd. split; [rewrite <- Hp'; exact Cnt|]. rewrite Acc. reflexivity.
Qed.

End Final.

Definition atrivialpursuit_correct :
  forall (P : N) (gs ls : list N) (p : uint) (x y : array uint),
  valid_input P gs ls -> repr p P -> repr x gs -> repr y ls ->
  exists o : N, repr (atrivialpursuit p x y) o /\ atrivialpursuit_spec P gs ls o
  := atp_impl_correct.
