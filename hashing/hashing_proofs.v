(* Correctness proofs for hashing_implem.v. *)
(* Implementation of hashing (hashing.spec): keyed polynomial prefix
   hashing modulo the Mersenne prime p = 2^61 - 1.  See README.md. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Znumtheory Zpow_facts String Ascii.
From Stdlib Require PrimString.
Import ListNotations.

Open Scope Z_scope.

Unset Lia Cache.

Require Export hashing_implem.
Open Scope Z_scope.


(* ================================================================== *)
(* Part 1. Math side: the family, its separation, p prime             *)
(* ================================================================== *)

Definition pZ : Z := 2305843009213693951.

(* Horner evaluation, highest coefficient first, from accumulator acc. *)
Definition G (x acc : Z) (l : list Z) : Z := fold_left (fun t c => t * x + c) l acc.

Lemma G_cons x acc c l : G x acc (c :: l) = G x (acc * x + c) l.
Proof. reflexivity. Qed.

Lemma G_nil x acc : G x acc [] = acc.
Proof. reflexivity. Qed.

Lemma G_app x acc l1 l2 : G x acc (l1 ++ l2) = G x (G x acc l1) l2.
Proof. unfold G. apply fold_left_app. Qed.

Lemma G_snoc x acc l c : G x acc (l ++ [c]) = G x acc l * x + c.
Proof. rewrite G_app. reflexivity. Qed.

Lemma G_shift x : forall l acc,
  G x acc l = acc * x ^ Z.of_nat (List.length l) + G x 0 l.
Proof.
  induction l as [|c l IH]; intros acc.
  - rewrite !G_nil. cbn [List.length]. change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r. ring.
  - rewrite !G_cons, (IH (acc * x + c)), (IH (0 * x + c)).
    cbn [List.length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(* Synthetic division by (x - a), Horner's partial values. *)
Fixpoint qd (a b : Z) (P : list Z) : list Z :=
  match P with [] => [] | c :: P' => b :: qd a (b * a + c) P' end.

Lemma qd_length a : forall P b, List.length (qd a b P) = List.length P.
Proof. induction P as [|c P IH]; intros b; cbn [qd List.length]; auto. Qed.

Lemma qd_eval x a : forall P b,
  G x b P = (x - a) * G x 0 (qd a b P) + G a b P.
Proof.
  induction P as [|c P IH]; intros b.
  - cbn [qd]. rewrite !G_nil. ring.
  - cbn [qd]. rewrite !G_cons.
    pose proof (IH (b * a + c)) as H.
    rewrite (G_shift x P (b * a + c)) in H.
    rewrite (G_shift x P (b * x + c)), (G_shift x (qd a (b * a + c) P) (0 * x + b)),
      qd_length.
    set (k := x ^ Z.of_nat (List.length P)) in *.
    transitivity ((x - a) * ((0 * x + b) * k + G x 0 (qd a (b * a + c) P))
      + ((b * a + c) * k + G x 0 P - (x - a) * G x 0 (qd a (b * a + c) P))).
    + ring.
    + rewrite H. ring.
Qed.

Definition allz (l : list Z) : Prop := Forall (fun c => c mod pZ = 0) l.

Lemma qd_recover a : forall P b,
  allz (qd a b P) -> G a b P mod pZ = 0 -> allz (b :: P).
Proof.
  induction P as [|c P IH]; intros b Hq Hg.
  - constructor; [exact Hg | constructor].
  - cbn [qd] in Hq. apply Forall_cons_iff in Hq as [Hb Hq'].
    rewrite G_cons in Hg.
    pose proof (IH _ Hq' Hg) as H. apply Forall_cons_iff in H as [Hc HP].
    constructor; [exact Hb|]. constructor; [|exact HP].
    replace c with ((b * a + c) - b * a) by ring.
    rewrite Zminus_mod, Hc, Zmult_mod, Hb. reflexivity.
Qed.

Lemma root_dec (f : Z -> Prop) (fdec : forall x, f x \/ ~ f x) :
  forall n : nat, (exists x, 0 <= x < Z.of_nat n /\ f x)
                  \/ (forall x, 0 <= x < Z.of_nat n -> ~ f x).
Proof.
  induction n as [|n IH].
  - right. intros x Hx. lia.
  - destruct IH as [[x [Hx Hf]] | Hn].
    + left. exists x. split; [lia | exact Hf].
    + destruct (fdec (Z.of_nat n)) as [Hf | Hf].
      * left. exists (Z.of_nat n). split; [lia | exact Hf].
      * right. intros x Hx.
        destruct (Z.eq_dec x (Z.of_nat n)) as [->|Hne]; [exact Hf|].
        apply Hn. lia.
Qed.

(* ---- primality of p ---- *)

Fixpoint pm (a : Z) (e : positive) (n : Z) : Z :=
  match e with
  | xH => a mod n
  | xO e' => let t := pm a e' n in (t * t) mod n
  | xI e' => let t := pm a e' n in ((t * t) mod n * (a mod n)) mod n
  end.

Lemma pm_spec a n : 0 < n -> forall e, pm a e n = a ^ Zpos e mod n.
Proof.
  intros Hn. induction e as [e IH|e IH|]; cbn [pm].
  - rewrite IH, Pos2Z.inj_xI.
    replace (2 * Z.pos e + 1) with (Z.pos e + Z.pos e + 1) by lia.
    rewrite !Z.pow_add_r, Z.pow_1_r by lia.
    rewrite (Z.mul_mod (a ^ Z.pos e * a ^ Z.pos e) a), (Z.mul_mod (a ^ Z.pos e) (a ^ Z.pos e))
      by lia. reflexivity.
  - rewrite IH, Pos2Z.inj_xO.
    replace (2 * Z.pos e) with (Z.pos e + Z.pos e) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite <- Z.mul_mod by lia. reflexivity.
  - rewrite Z.pow_1_r. reflexivity.
Qed.

Lemma pow_mod_one_gcd (p a : Z) : 1 < p ->
  forall n, 0 <= n -> forall m, 0 <= m ->
  a ^ m mod p = 1 -> a ^ n mod p = 1 -> a ^ (Z.gcd m n) mod p = 1.
Proof.
  intros Hp n. induction n as [n IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros Hn m Hm Ham Han.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - rewrite Z.gcd_0_r, Z.abs_eq by lia. exact Ham.
  - assert (Hr : 0 <= m mod n < n) by (apply Z.mod_pos_bound; lia).
    assert (E : a ^ m = (a ^ n) ^ (m / n) * a ^ (m mod n)).
    { rewrite <- Z.pow_mul_r, <- Z.pow_add_r; [f_equal; apply Z.div_mod; lia | | | |];
      try lia.
      - apply Z.mul_nonneg_nonneg; [lia|]. apply Z.div_pos; lia.
      - apply Z.div_pos; lia. }
    assert (Hmod : a ^ (m mod n) mod p = 1).
    { rewrite E, Zmult_mod, Zpower_mod, Han, Z.pow_1_l in Ham by (try lia; apply Z.div_pos; lia).
      rewrite Z.mod_1_l, Z.mul_1_l, Z.mod_mod in Ham by lia. exact Ham. }
    rewrite Z.gcd_comm, <- Z.gcd_mod, Z.gcd_comm by lia.
    apply IH; [unfold Zwf; lia | lia | lia | exact Han | exact Hmod].
Qed.

Lemma fin_dec (P : nat -> Prop) (Pdec : forall i, P i \/ ~ P i) :
  forall n, (exists i, (i < n)%nat /\ P i) \/ (forall i, (i < n)%nat -> ~ P i).
Proof.
  induction n as [|n IH].
  - right. intros i Hi. lia.
  - destruct IH as [[i [Hi HP]] | Hno].
    + left. exists i. split; [lia | exact HP].
    + destruct (Pdec n) as [HP | HP].
      * left. exists n. split; [lia | exact HP].
      * right. intros i Hi. destruct (Nat.eq_dec i n) as [->|Hne]; [exact HP|].
        apply Hno. lia.
Qed.

Lemma php : forall n (f : nat -> Z),
  (forall i, (i <= n)%nat -> 1 <= f i <= Z.of_nat n) ->
  exists i j, (i < j <= n)%nat /\ f i = f j.
Proof.
  induction n as [|n IH]; intros f Hf.
  - pose proof (Hf 0%nat ltac:(lia)). lia.
  - destruct (fin_dec (fun i => f i = f (S n))
                (fun i => ltac:(destruct (Z.eq_dec (f i) (f (S n))); auto)) (S n))
      as [[i [Hi E]] | Hno].
    + exists i, (S n). split; [lia | exact E].
    + set (g := fun i => if Z.eq_dec (f i) (Z.of_nat (S n)) then f (S n) else f i).
      assert (Hg : forall i, (i <= n)%nat -> 1 <= g i <= Z.of_nat n).
      { intros i Hi. unfold g. destruct (Z.eq_dec (f i) (Z.of_nat (S n))) as [E|E].
        - pose proof (Hf (S n) ltac:(lia)).
          assert (f (S n) <> Z.of_nat (S n)).
          { intro E'. apply (Hno i); lia. }
          lia.
        - pose proof (Hf i ltac:(lia)). lia. }
      destruct (IH g Hg) as [i [j [Hij E]]].
      unfold g in E.
      destruct (Z.eq_dec (f i) (Z.of_nat (S n))), (Z.eq_dec (f j) (Z.of_nat (S n))).
      * exists i, j. split; lia.
      * exfalso. apply (Hno j); lia.
      * exfalso. apply (Hno i); lia.
      * exists i, j. split; [lia | exact E].
Qed.

Lemma prime_div_pow p a : prime p -> forall k, 0 <= k -> (p | a ^ k) -> (p | a).
Proof.
  intros Hp k Hk. pattern k. apply natlike_ind; [| |exact Hk].
  - rewrite Z.pow_0_r. intros H. apply Z.divide_1_r in H.
    pose proof (prime_ge_2 p Hp). lia.
  - intros k' Hk' IH H. rewrite Z.pow_succ_r in H by lia.
    destruct (prime_mult p Hp _ _ H); auto.
Qed.

Lemma order_exists p a : prime p -> ~ (p | a) ->
  exists e, 1 <= e <= p - 1 /\ a ^ e mod p = 1.
Proof.
  intros Hp Ha. pose proof (prime_ge_2 p Hp) as P2.
  assert (Hnz : forall k, 0 <= k -> a ^ k mod p <> 0).
  { intros k Hk E. apply Zmod_divide in E; [|lia].
    apply Ha. exact (prime_div_pow p a Hp k Hk E). }
  destruct (php (Z.to_nat (p - 1)) (fun i => a ^ Z.of_nat i mod p)) as [i [j [Hij E]]].
  { intros i Hi. pose proof (Hnz (Z.of_nat i) ltac:(lia)).
    pose proof (Z.mod_pos_bound (a ^ Z.of_nat i) p ltac:(lia)). lia. }
  cbv beta in E.
  exists (Z.of_nat j - Z.of_nat i). split; [lia|].
  assert (Ej : a ^ Z.of_nat j = a ^ Z.of_nat i * a ^ (Z.of_nat j - Z.of_nat i)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hd : (p | a ^ Z.of_nat i * (a ^ (Z.of_nat j - Z.of_nat i) - 1))).
  { apply Zmod_divide; [lia|].
    replace (a ^ Z.of_nat i * (a ^ (Z.of_nat j - Z.of_nat i) - 1))
      with (a ^ Z.of_nat j - a ^ Z.of_nat i) by (rewrite Ej; ring).
    rewrite Zminus_mod, E, Z.sub_diag. reflexivity. }
  destruct (prime_mult p Hp _ _ Hd) as [H | [k Hk]].
  - exfalso. apply (Hnz (Z.of_nat i)); [lia|]. apply Zdivide_mod. exact H.
  - replace (a ^ (Z.of_nat j - Z.of_nat i)) with (1 + k * p) by lia.
    rewrite Z.mod_add, Z.mod_1_l by lia. reflexivity.
Qed.

Lemma pock_factor (N a p : Z) (qs : list Z) :
  1 < N -> prime p -> (p | N) ->
  a ^ (N - 1) mod N = 1 ->
  Forall (fun q => prime q /\ (q | N - 1)
                   /\ Z.gcd (a ^ ((N - 1) / q) mod N - 1) N = 1) qs ->
  exists g, 1 <= g <= p - 1 /\ Forall (fun q => (q | g)) qs.
Proof.
  intros HN Hp Hd Ha Hqs. pose proof (prime_ge_2 p Hp) as P2.
  assert (Hap : a ^ (N - 1) mod p = 1).
  { rewrite (Zmod_div_mod p N) by (try lia; exact Hd). rewrite Ha. apply Z.mod_1_l. lia. }
  assert (Hna : ~ (p | a)).
  { intros H. assert (H' : (p | a ^ (N - 1))).
    { replace (N - 1) with (Z.succ (N - 2)) by lia. rewrite Z.pow_succ_r by lia.
      apply Z.divide_mul_l. exact H. }
    apply Zdivide_mod in H'. lia. }
  destruct (order_exists p a Hp Hna) as [e [He Hae]].
  exists (Z.gcd e (N - 1)).
  assert (Hg1 : a ^ Z.gcd e (N - 1) mod p = 1)
    by (apply pow_mod_one_gcd; lia).
  assert (Hgpos : 0 < Z.gcd e (N - 1)).
  { pose proof (Z.gcd_nonneg e (N - 1)).
    destruct (Z.eq_dec (Z.gcd e (N - 1)) 0) as [E|]; [|lia].
    apply Z.gcd_eq_0_l in E. lia. }
  assert (Hge : Z.gcd e (N - 1) <= e) by (apply Z.divide_pos_le; [lia | apply Z.gcd_divide_l]).
  split; [clear - Hgpos Hge He; lia|].
  clear Ha Hap Hae Hge He.
  eapply Forall_impl; [|exact Hqs]. intros q [Hq [HqN Hgcd]]. cbv beta.
  set (g := Z.gcd e (N - 1)) in *.
  destruct (Zdivide_dec q g) as [Y|Hn]; [exact Y|exfalso].
  pose proof (prime_ge_2 q Hq) as Q2.
  assert (Hrel : rel_prime g q) by (apply rel_prime_sym, prime_rel_prime; assumption).
  assert (HgN : (g | q * ((N - 1) / q))).
  { rewrite <- Zdivide_Zdiv_eq by first [exact HqN | lia]. apply Z.gcd_divide_r. }
  pose proof (Gauss _ _ _ HgN Hrel) as [t Ht].
  assert (Hk0 : 0 <= (N - 1) / q) by (apply Z.div_pos; clear - HN Q2; lia).
  assert (Ht0 : 0 <= t) by (clear - Hk0 Ht Hgpos; nia).
  assert (Hk : a ^ ((N - 1) / q) mod p = 1).
  { rewrite Ht, Z.mul_comm, Z.pow_mul_r, Zpower_mod, Hg1, Z.pow_1_l
      by (clear - Ht0 Hgpos P2; lia).
    apply Z.mod_1_l. clear - P2; lia. }
  assert (Hpd : (p | a ^ ((N - 1) / q) mod N - 1)).
  { set (X := a ^ ((N - 1) / q)) in *. clear Hgcd HgN Ht Hk0 Ht0 Hrel Hn.
    apply Zmod_divide; [clear - P2; lia|].
    pose proof Hd as [u Hu].
    rewrite (Z.mod_eq X N) by (clear - HN; lia).
    rewrite Hu.
    replace (X - u * p * (X / (u * p)) - 1) with ((X - 1) + (- (u * (X / (u * p)))) * p) by ring.
    rewrite Z.mod_add by (clear - P2; lia).
    rewrite Zminus_mod, Hk, Z.mod_1_l by (clear - P2; lia). reflexivity. }
  assert (Hp1 : (p | 1)).
  { rewrite <- Hgcd. apply Z.gcd_greatest; [exact Hpd | exact Hd]. }
  apply Z.divide_1_r in Hp1. clear - Hp1 P2. lia.
Qed.

Lemma prime_divisor_exists : forall n, 1 < n -> exists p, prime p /\ (p | n).
Proof.
  intros n. induction n as [n IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros Hn. destruct (prime_dec n) as [Hp|Hp].
  - exists n. split; [exact Hp | apply Z.divide_refl].
  - destruct (not_prime_divide n Hn Hp) as [m [Hm Hd]].
    destruct (IH m ltac:(unfold Zwf; lia) ltac:(lia)) as [p [Hp' Hd']].
    exists p. split; [exact Hp'|]. eapply Z.divide_trans; eassumption.
Qed.

Lemma prime_from_bound (N F : Z) : 1 < N -> N < (F + 1) * (F + 1) -> 0 <= F ->
  (forall p, prime p -> (p | N) -> F < p) -> prime N.
Proof.
  intros HN HF HF0 Hp.
  apply prime_alt. split; [lia|]. intros n Hn [k Hk].
  assert (Hk1 : 1 < k) by nia.
  destruct (prime_divisor_exists n ltac:(lia)) as [p1 [Hp1 Hd1]].
  destruct (prime_divisor_exists k Hk1) as [p2 [Hp2 Hd2]].
  assert (HnN : (n | N)) by (exists k; exact Hk).
  assert (HkN : (k | N)) by (exists n; lia).
  pose proof (Hp p1 Hp1 (Z.divide_trans _ _ _ Hd1 HnN)).
  pose proof (Hp p2 Hp2 (Z.divide_trans _ _ _ Hd2 HkN)).
  pose proof (Z.divide_pos_le p1 n ltac:(lia) Hd1).
  pose proof (Z.divide_pos_le p2 k ltac:(lia) Hd2).
  nia.
Qed.

Lemma prime_check (q : Z) : 1 < q ->
  forallb (fun n => negb (q mod Z.of_nat n =? 0)) (seq 2 (Z.to_nat q - 2)) = true ->
  prime q.
Proof.
  intros Hq H. apply prime_alt. split; [lia|]. intros n Hn Hd.
  rewrite forallb_forall in H. specialize (H (Z.to_nat n)).
  assert (Hin : In (Z.to_nat n) (seq 2 (Z.to_nat q - 2))) by (apply in_seq; lia).
  specialize (H Hin). rewrite Z2Nat.id in H by lia.
  apply Zdivide_mod in Hd. rewrite Hd in H. discriminate.
Qed.

Lemma mul_div_coprime x y g : rel_prime x y -> (x | g) -> (y | g) -> (x * y | g).
Proof.
  intros Hr [k Hk] Hy. subst g.
  assert (Hyk : (y | k)).
  { apply (Gauss y x k); [rewrite Z.mul_comm; exact Hy | apply rel_prime_sym; exact Hr]. }
  destruct Hyk as [l Hl]. subst k. exists l. ring.
Qed.

Lemma pow_check (a N : Z) (e : positive) : 0 < N -> pm a e N = a ^ Zpos e mod N.
Proof. intros HN. apply pm_spec. exact HN. Qed.

Lemma p_prime : prime pZ.
Proof.
  apply (prime_from_bound pZ 4027518961); [unfold pZ; lia | unfold pZ; lia | lia | ].
  intros p Hp Hd.
  assert (HP : forall q, 1 < q -> q < pZ - 1 ->
     forallb (fun n => negb (q mod Z.of_nat n =? 0)) (seq 2 (Z.to_nat q - 2)) = true ->
     (pZ - 1) mod q = 0 ->
     Z.gcd (pm 3 (Z.to_pos ((pZ - 1) / q)) pZ - 1) pZ = 1 ->
     prime q /\ (q | pZ - 1) /\ Z.gcd (3 ^ ((pZ - 1) / q) mod pZ - 1) pZ = 1).
  { intros q Hq1 Hq2 Hc Hm Hg. split; [apply prime_check; assumption|].
    split; [apply Zmod_divide; [lia | exact Hm]|].
    rewrite pm_spec, Z2Pos.id in Hg; [exact Hg | | unfold pZ; lia].
    apply Z.div_str_pos. unfold pZ in *. lia. }
  assert (Hpow : 3 ^ (pZ - 1) mod pZ = 1).
  { replace (pZ - 1) with (Zpos 2305843009213693950) by reflexivity.
    rewrite <- pm_spec by (unfold pZ; lia). vm_compute. reflexivity. }
  assert (Hall : Forall (fun q => prime q /\ (q | pZ - 1)
                   /\ Z.gcd (3 ^ ((pZ - 1) / q) mod pZ - 1) pZ = 1) [61; 151; 331; 1321]).
  { repeat (apply Forall_cons;
      [apply HP; [unfold pZ; lia | unfold pZ; lia | vm_compute; reflexivity
                 | vm_compute; reflexivity | vm_compute; reflexivity] |]).
    apply Forall_nil. }
  destruct (pock_factor pZ 3 p [61; 151; 331; 1321] ltac:(unfold pZ; lia) Hp Hd Hpow Hall)
    as [g [Hg Hq]].
  { apply Forall_cons_iff in Hq as [H1 Hq]. apply Forall_cons_iff in Hq as [H2 Hq].
    apply Forall_cons_iff in Hq as [H3 Hq]. apply Forall_cons_iff in Hq as [H4 _].
    assert (Hr : forall x y, Z.gcd x y = 1 -> rel_prime x y)
      by (intros x y; apply Zgcd_1_rel_prime).
    pose proof (mul_div_coprime 61 151 g (Hr 61 151 eq_refl) H1 H2) as H12.
    pose proof (mul_div_coprime (61 * 151) 331 g (Hr (61 * 151) 331 eq_refl) H12 H3) as H123.
    pose proof (mul_div_coprime (61 * 151 * 331) 1321 g (Hr (61 * 151 * 331) 1321 eq_refl) H123 H4) as H1234.
    apply Z.divide_pos_le in H1234; [|lia]. lia. }
Qed.

(* ---- root counting over F_p ---- *)

Lemma root_count : forall n P b, List.length P = n -> ~ allz (b :: P) ->
  exists l : list Z, (List.length l <= n)%nat /\
    forall x, 0 <= x < pZ -> G x b P mod pZ = 0 -> In x l.
Proof.
  induction n as [|n IH]; intros P b HP Hnz.
  - destruct P; [|discriminate]. exists []. split; [lia|].
    intros x _ Hx. exfalso. apply Hnz. constructor; [exact Hx | constructor].
  - assert (fdec : forall x, G x b P mod pZ = 0 \/ ~ G x b P mod pZ = 0)
      by (intro x; destruct (Z.eq_dec (G x b P mod pZ) 0); auto).
    destruct (root_dec _ fdec (Z.to_nat pZ)) as [[a [Ha Hr]] | Hno].
    + rewrite Z2Nat.id in Ha by (unfold pZ; lia).
      pose proof (qd_length a P b) as L.
      destruct (qd a b P) as [|b' Q'] eqn:EQ; [cbn [List.length] in L; lia|].
      assert (HQ : List.length Q' = n) by (cbn [List.length] in L; lia).
      assert (Hnz' : ~ allz (b' :: Q')).
      { intro Z0. apply Hnz. apply (qd_recover a); [rewrite EQ; exact Z0 | exact Hr]. }
      destruct (IH Q' b' HQ Hnz') as [l [Hl Hin]].
      exists (a :: l). split; [cbn [List.length]; lia|].
      intros x Hx Hgx.
      pose proof (qd_eval x a P b) as Ev. rewrite EQ, G_cons in Ev.
      replace (0 * x + b') with b' in Ev by ring.
      assert (Hm : ((x - a) * G x b' Q') mod pZ = 0).
      { replace ((x - a) * G x b' Q') with (G x b P - G a b P) by lia.
        rewrite Zminus_mod, Hgx, Hr. reflexivity. }
      apply Zmod_divide in Hm; [|unfold pZ; lia].
      destruct (prime_mult _ p_prime _ _ Hm) as [[k Hk] | Hd].
      * left. assert (k = 0) by (unfold pZ in *; nia). subst k. lia.
      * right. apply Hin; [exact Hx|]. apply Zdivide_mod. exact Hd.
    + exists []. split; [cbn [List.length]; lia|]. intros x Hx Hgx. exfalso.
      apply (Hno x); [rewrite Z2Nat.id by (unfold pZ; lia); exact Hx | exact Hgx].
Qed.

(* ---- the difference polynomial ---- *)

Fixpoint psub (A B : list Z) : list Z :=
  match A, B with a :: A', b :: B' => (a - b) :: psub A' B' | _, _ => [] end.

Lemma psub_length : forall A B, List.length A = List.length B ->
  List.length (psub A B) = List.length A.
Proof.
  induction A as [|a A IH]; intros [|b B] HL; cbn [psub List.length] in *;
    try discriminate; auto.
Qed.

Lemma psub_eval x : forall A B, List.length A = List.length B ->
  G x 0 (psub A B) = G x 0 A - G x 0 B.
Proof.
  induction A as [|a A IH]; intros [|b B] HL; cbn [psub List.length] in *;
    try discriminate.
  - reflexivity.
  - injection HL as HL. rewrite !G_cons.
    rewrite (G_shift x (psub A B) (0 * x + (a - b))), (G_shift x A (0 * x + a)),
      (G_shift x B (0 * x + b)), IH, psub_length, HL by exact HL.
    ring.
Qed.

Lemma psub_bound : forall A B,
  Forall (fun c => 0 <= c < 256) A -> Forall (fun c => 0 <= c < 256) B ->
  Forall (fun c => -256 < c < 256) (psub A B).
Proof.
  induction A as [|a A IH]; intros [|b B] HA HB; cbn [psub]; try constructor.
  - apply Forall_cons_iff in HA as [Ha _]. apply Forall_cons_iff in HB as [Hb _]. lia.
  - apply IH; [eapply Forall_inv_tail; exact HA | eapply Forall_inv_tail; exact HB].
Qed.

Lemma allz_small : forall D, Forall (fun c => -256 < c < 256) D -> allz D ->
  Forall (fun c => c = 0) D.
Proof.
  intros D HB HZ. unfold allz in HZ. rewrite Forall_forall in *. intros c Hc.
  specialize (HB c Hc). specialize (HZ c Hc). cbv beta in *.
  apply Zmod_divide in HZ; [|unfold pZ; lia]. destruct HZ as [k Hk].
  unfold pZ in Hk. lia.
Qed.

Lemma G_zero x : forall D acc, Forall (fun c => c = 0) D -> acc = 0 -> G x acc D = 0.
Proof.
  induction D as [|c D IH]; intros acc HD Hacc; [exact Hacc|].
  apply Forall_cons_iff in HD as [Hc HD]. rewrite G_cons. apply IH; [exact HD|].
  subst. ring.
Qed.

Lemma G0_repeat x : forall k l, G x 0 (repeat 0 k ++ l) = G x 0 l.
Proof.
  induction k as [|k IH]; intros l; cbn [repeat app]; [reflexivity|].
  rewrite G_cons. replace (0 * x + 0) with 0 by ring. apply IH.
Qed.

Lemma G_pos x : 1 <= x -> forall l acc, 1 <= acc ->
  Forall (fun c => 0 <= c) l -> 1 <= G x acc l.
Proof.
  intros Hx. induction l as [|c l IH]; intros acc Hacc Hl; [exact Hacc|].
  rewrite G_cons. apply Forall_cons_iff in Hl as [Hc Hl]. apply IH; [nia | exact Hl].
Qed.

Lemma G256_inj : forall l l',
  Forall (fun c => 0 <= c < 256) l -> Forall (fun c => 0 <= c < 256) l' ->
  G 256 1 l = G 256 1 l' -> l = l'.
Proof.
  intros l. induction l as [|c l IH] using rev_ind; intros l' Hl Hl' E;
    destruct l' as [|c' l'] using rev_ind.
  - reflexivity.
  - exfalso. rewrite G_snoc, G_nil in E. apply Forall_app in Hl' as [Hl1 Hl2].
    apply Forall_cons_iff in Hl2 as [Hc' _].
    pose proof (G_pos 256 ltac:(lia) l' 1 ltac:(lia)
                  (Forall_impl _ (fun c H => proj1 H) Hl1)). lia.
  - exfalso. rewrite G_snoc, G_nil in E. apply Forall_app in Hl as [Hl1 Hl2].
    apply Forall_cons_iff in Hl2 as [Hc _].
    pose proof (G_pos 256 ltac:(lia) l 1 ltac:(lia)
                  (Forall_impl _ (fun c H => proj1 H) Hl1)). lia.
  - rewrite !G_snoc in E. apply Forall_app in Hl as [Hl1 Hl2].
    apply Forall_app in Hl' as [Hl1' Hl2'].
    apply Forall_cons_iff in Hl2 as [Hc _]. apply Forall_cons_iff in Hl2' as [Hc' _].
    assert (c = c') by lia. subst c'.
    rewrite (IH l' Hl1 Hl1' ltac:(lia)). reflexivity.
Qed.

(* ---- the family ---- *)

(* The codes of the characters of w, as integers. *)
Definition codes (w : string) : list Z :=
  map (fun c => Z.of_N (N_of_ascii c)) (list_ascii_of_string w).

Lemma codes_bound w : Forall (fun c => 0 <= c < 256) (codes w).
Proof.
  unfold codes. apply Forall_map. apply Forall_forall. intros c _.
  pose proof (N_ascii_bounded c). lia.
Qed.

Lemma codes_length w : List.length (codes w) = String.length w.
Proof. induction w as [|c w IH]; cbn; [reflexivity|]. unfold codes in IH. lia. Qed.

Lemma codes_back w :
  map (fun z => ascii_of_N (Z.to_N z)) (codes w) = list_ascii_of_string w.
Proof.
  unfold codes. rewrite map_map. erewrite map_ext; [apply map_id|].
  intros c. cbv beta. rewrite N2Z.id. apply ascii_N_embedding.
Qed.

Lemma codes_inj w w' : codes w = codes w' -> w = w'.
Proof.
  intros E. rewrite <- (string_of_list_ascii_of_string w),
    <- (string_of_list_ascii_of_string w'), <- codes_back, <- (codes_back w'), E.
  reflexivity.
Qed.

(* The polynomial hash r^|w| + w_0 r^(|w|-1) + ... + w_(|w|-1) modulo p. *)
Definition Hz (r : Z) (w : string) : Z := G r 0 (1 :: codes w) mod pZ.

Definition Hf (r : N) (w : string) : N := Z.to_N (Hz (Z.of_N r) w).

Lemma Hf_separating : separating Hf.
Proof.
  intros w w' Hne.
  set (n := Nat.max (String.length w) (String.length w')).
  set (A := repeat 0 (n - String.length w) ++ 1 :: codes w).
  set (B := repeat 0 (n - String.length w') ++ 1 :: codes w').
  assert (LA : List.length A = S n).
  { unfold A. rewrite length_app, repeat_length. cbn [List.length].
    rewrite codes_length. lia. }
  assert (LB : List.length B = S n).
  { unfold B. rewrite length_app, repeat_length. cbn [List.length].
    rewrite codes_length. lia. }
  assert (BA : Forall (fun c => 0 <= c < 256) A).
  { unfold A. apply Forall_app. split.
    - apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia.
    - constructor; [lia | apply codes_bound]. }
  assert (BB : Forall (fun c => 0 <= c < 256) B).
  { unfold B. apply Forall_app. split.
    - apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia.
    - constructor; [lia | apply codes_bound]. }
  assert (Ev : forall x, G x 0 (psub A B) = G x 0 (1 :: codes w) - G x 0 (1 :: codes w')).
  { intros x. rewrite psub_eval by lia. unfold A, B. rewrite !G0_repeat. reflexivity. }
  pose proof (psub_length A B ltac:(lia)) as LD.
  pose proof (psub_bound A B BA BB) as BD.
  destruct (psub A B) as [|d D'] eqn:ED; [cbn [List.length] in LD; lia|].
  assert (Hnz : ~ allz (d :: D')).
  { intro Hz0. apply Hne. apply codes_inj.
    pose proof (allz_small _ BD Hz0) as H0.
    pose proof (Ev 256) as E. rewrite (G_zero 256 _ 0 H0 eq_refl), !G_cons in E.
    change (0 * 256 + 1) with 1 in E.
    apply G256_inj; [apply codes_bound | apply codes_bound | lia]. }
  destruct (root_count n D' d ltac:(cbn [List.length] in LD; lia) Hnz) as [l [Hl Hin]].
  exists (map Z.to_N l). split.
  - unfold len, slen. rewrite length_map. lia.
  - intros r Hkey Heq. unfold key, key_count in Hkey.
    apply in_map_iff. exists (Z.of_N r). split; [apply N2Z.id|].
    apply Hin; [unfold pZ; lia|].
    unfold Hf, Hz in Heq.
    apply Z2N.inj in Heq; try (apply Z.mod_pos_bound; unfold pZ; lia).
    pose proof (Ev (Z.of_N r)) as E. rewrite G_cons in E.
    replace (0 * Z.of_N r + d) with d in E by ring.
    rewrite E, Zminus_mod, Heq, Z.sub_diag. reflexivity.
Qed.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope Z_scope.

Lemma pre_loop_eq : forall r s n i t acc H,
  pre_loop r s n i t acc H =
  match bdec (i <? n)%uint63 with
  | left Hi =>
      let acc' := addmod (mulmod acc r) (PrimString.get s i) in
      pre_loop r s n (i + 1)%uint63 t.[(i + 1)%uint63 <- acc'] acc' (Acc_inv H (dec_step n i Hi))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma pow_loop_eq : forall r n i t acc H,
  pow_loop r n i t acc H =
  match bdec (i <? n)%uint63 with
  | left Hi =>
      let acc' := mulmod acc r in
      pow_loop r n (i + 1)%uint63 t.[(i + 1)%uint63 <- acc'] acc' (Acc_inv H (dec_step n i Hi))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma q_loop_eq : forall pre pw xl xr q j out H,
  q_loop pre pw xl xr q j out H =
  match bdec (j <? q)%uint63 with
  | left Hj =>
      q_loop pre pw xl xr q (j + 1)%uint63 out.[j <- hash pre pw xl.[j] xr.[j]]
        (Acc_inv H (dec_step q j Hj))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ---- modular arithmetic ---- *)

Lemma P61_val : (φ P61) = 2305843009213693951.
Proof. reflexivity. Qed.

Lemma wB_val : wB = 9223372036854775808.
Proof. reflexivity. Qed.

Lemma addmod_spec a b : (φ a) < pZ -> (φ b) < pZ -> (φ (addmod a b)) = ((φ a) + (φ b)) mod pZ.
Proof.
  unfold addmod, pZ. intros Ha Hb. pose proof P61_val.
  destruct (P61 <=? a + b)%uint63 eqn:E;
    [rewrite leb_spec in E | rewrite <- Bool.not_true_iff_false, leb_spec in E]; sia.
Qed.

Lemma submod_spec a b : (φ a) < pZ -> (φ b) < pZ -> (φ (submod a b)) = ((φ a) - (φ b)) mod pZ.
Proof.
  unfold submod, pZ. intros Ha Hb. pose proof P61_val.
  destruct (b <=? a)%uint63 eqn:E;
    [rewrite leb_spec in E | rewrite <- Bool.not_true_iff_false, leb_spec in E]; sia.
Qed.

Lemma fold61 x y : (x * 2305843009213693952 + y) mod pZ = (x + y) mod pZ.
Proof.
  replace (x * 2305843009213693952 + y) with ((x + y) + x * pZ) by (unfold pZ; ring).
  apply Z.mod_add. unfold pZ; lia.
Qed.

Lemma land_P61 x : (φ (x land P61))%uint63 = (φ x) mod 2305843009213693952.
Proof.
  rewrite land_spec'. change (φ P61) with (Z.ones 61).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma mulmod_spec a b : (φ a) < pZ -> (φ b) < pZ -> (φ (mulmod a b)) = ((φ a) * (φ b)) mod pZ.
Proof.
  intros Ha Hb. unfold mulmod.
  pose proof (mulc_spec a b) as Hm.
  destruct (mulc a b) as [h l]. cbn [fst snd] in Hm. cbv beta iota zeta.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  pose proof (to_Z_bounded h). pose proof (to_Z_bounded l).
  rewrite wB_val in *.
  assert (Hh : (φ h) < 576460752303423488) by (unfold pZ in *; nia).
  assert (HD : 0 <= (φ l) / 2305843009213693952 < 4)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (HM : 0 <= (φ l) mod 2305843009213693952 < 2305843009213693952)
    by (apply Z.mod_pos_bound; lia).
  assert (Es : (φ ((h << 2) + (l >> 61) + (l land P61)))%uint63
               = 4 * (φ h) + (φ l) / 2305843009213693952 + (φ l) mod 2305843009213693952).
  { rewrite !add_spec, lsl_spec, lsr_spec, land_P61.
    change (2 ^ (φ 2)) with 4. change (2 ^ (φ 61)) with 2305843009213693952.
    rewrite wB_val.
    rewrite (Z.mod_small ((φ h) * 4)) by lia.
    rewrite (Z.mod_small ((φ h) * 4 + (φ l) / 2305843009213693952)) by lia.
    rewrite Z.mod_small by lia. ring. }
  set (S := 4 * (φ h) + (φ l) / 2305843009213693952 + (φ l) mod 2305843009213693952) in *.
  assert (CS : S mod pZ = ((φ a) * (φ b)) mod pZ).
  { rewrite Hm.
    replace ((φ h) * 9223372036854775808 + (φ l))
      with ((4 * (φ h) + (φ l) / 2305843009213693952) * 2305843009213693952
            + (φ l) mod 2305843009213693952).
    - rewrite fold61. reflexivity.
    - pose proof (Z.div_mod (φ l) 2305843009213693952 ltac:(lia)). lia. }
  assert (HS : 0 <= S <= 4611686018427387902) by (unfold S; lia).
  set (s := ((h << 2) + (l >> 61) + (l land P61))%uint63) in *.
  assert (Et : (φ ((s >> 61) + (s land P61)))%uint63
               = S / 2305843009213693952 + S mod 2305843009213693952).
  { rewrite add_spec, lsr_spec, land_P61, Es.
    change (2 ^ (φ 61)) with 2305843009213693952. rewrite wB_val.
    apply Z.mod_small. Z.to_euclidean_division_equations; lia. }
  set (T := S / 2305843009213693952 + S mod 2305843009213693952) in *.
  assert (CT : T mod pZ = S mod pZ).
  { unfold T. rewrite <- fold61. f_equal.
    pose proof (Z.div_mod S 2305843009213693952 ltac:(lia)). lia. }
  assert (HT : 0 <= T <= pZ + 1)
    by (unfold T, pZ; Z.to_euclidean_division_equations; lia).
  set (t := ((s >> 61) + (s land P61))%uint63) in *.
  rewrite <- CS, <- CT.
  destruct (P61 <=? t)%uint63 eqn:E;
    [rewrite leb_spec in E | rewrite <- Bool.not_true_iff_false, leb_spec in E];
    rewrite ?sub_spec, Et, ?P61_val in *; rewrite ?wB_val; unfold pZ in *;
    Z.to_euclidean_division_equations; lia.
Qed.

(* ---- PArray plumbing (at int, as in the template) ---- *)

Lemma max_length_val : (φ PArray.max_length) = 4194303.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if (n <=? PArray.max_length)%uint63 then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_make_small (n b : int) : (φ n) <= 4194303 -> PArray.length (PArray.make n b) = n.
Proof.
  intros Hn. rewrite alength_make.
  replace ((n <=? PArray.max_length)%uint63) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact Hn.
Qed.

(* ---- lists ---- *)

Lemma firstn_snoc : forall (l : list Z) i, (i < List.length l)%nat ->
  firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  induction l as [|a l IH]; intros [|i] Hi; cbn [List.length] in Hi; try lia.
  - reflexivity.
  - rewrite !firstn_cons. cbn [nth app]. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_split (l : list Z) L R : (L <= R)%nat -> (L <= List.length l)%nat ->
  firstn R l = firstn L l ++ firstn (R - L) (skipn L l).
Proof.
  intros H1 H2. rewrite <- (firstn_skipn L l) at 1.
  rewrite firstn_app, firstn_firstn, length_firstn.
  replace (Nat.min R L) with L by lia.
  replace (Nat.min L (List.length l)) with L by lia. reflexivity.
Qed.

Lemma codes_cons c w : codes (String c w) = Z.of_N (N_of_ascii c) :: codes w.
Proof. reflexivity. Qed.

Lemma codes_substring : forall w a b,
  codes (substring a b w) = firstn b (skipn a (codes w)).
Proof.
  induction w as [|c w IH]; intros [|a] [|b]; cbn [substring]; try reflexivity;
    rewrite ?codes_cons, IH; reflexivity.
Qed.

Lemma codes_get : forall w k c, String.get k w = Some c ->
  nth k (codes w) 0 = Z.of_N (N_of_ascii c).
Proof.
  induction w as [|a w IH]; intros [|k] c E; cbn in E; try discriminate.
  - injection E as <-. reflexivity.
  - rewrite codes_cons. cbn [nth]. apply IH. exact E.
Qed.

(* ---- the loops ---- *)

Lemma pre_loop_spec (rz : Z) (cs : list Z) (r : int) (xs : PrimString.string) (n : int) :
  (φ r) = rz -> 0 <= rz < pZ ->
  (φ n) = Z.of_nat (List.length cs) ->
  (forall i : int, (φ i) < (φ n) -> (φ (PrimString.get xs i)) = nth (Z.to_nat (φ i)) cs 0) ->
  Forall (fun c => 0 <= c < 256) cs ->
  forall z i (t : array int) acc H, gap n i = z -> (φ i) <= (φ n) ->
  (φ (PArray.length t)) = (φ n) + 1 ->
  (φ acc) = G rz 0 (firstn (Z.to_nat (φ i)) cs) mod pZ ->
  (forall j : int, (φ j) <= (φ i) -> (φ (t.[j])) = G rz 0 (firstn (Z.to_nat (φ j)) cs) mod pZ) ->
  (φ (PArray.length (pre_loop r xs n i t acc H))) = (φ n) + 1 /\
  forall j : int, (φ j) <= (φ n) ->
    (φ ((pre_loop r xs n i t acc H).[j])) = G rz 0 (firstn (Z.to_nat (φ j)) cs) mod pZ.
Proof.
  intros Hr Hrz Hn Hget Hcs z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i t acc H Hz Hi Hlen Hacc Hinv.
  rewrite pre_loop_eq.
  destruct (bdec (i <? n)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    cbv zeta.
    assert (Hc : (φ (PrimString.get xs i)) = nth (Z.to_nat (φ i)) cs 0) by (apply Hget; lia).
    assert (Hcb : 0 <= (φ (PrimString.get xs i)) < 256).
    { rewrite Hc. rewrite Forall_forall in Hcs. apply Hcs. apply nth_In. lia. }
    assert (Hab : 0 <= (φ acc) < pZ)
      by (rewrite Hacc; apply Z.mod_pos_bound; unfold pZ; lia).
    assert (Hm : (φ (mulmod acc r)) = ((φ acc) * rz) mod pZ)
      by (rewrite mulmod_spec; [rewrite Hr; reflexivity | lia | lia]).
    assert (Hmb : 0 <= (φ (mulmod acc r)) < pZ)
      by (rewrite Hm; apply Z.mod_pos_bound; unfold pZ; lia).
    assert (Hacc' : (φ (addmod (mulmod acc r) (PrimString.get xs i)))
                    = G rz 0 (firstn (Z.to_nat ((φ (i + 1))%uint63)) cs) mod pZ).
    { rewrite addmod_spec by (unfold pZ in *; lia). rewrite Hm, Hacc, Hi1.
      rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite firstn_snoc by lia.
      rewrite G_snoc, <- Hc. rewrite Zmult_mod_idemp_l, Zplus_mod_idemp_l. reflexivity. }
    eapply IH; [ | reflexivity | lia | | exact Hacc' | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite alength_set. exact Hlen.
    + intros j Hj. rewrite Hi1 in Hj.
      destruct (Z.eq_dec (φ j) ((φ i) + 1)) as [E | E].
      * assert (Ej : j = (i + 1)%uint63) by (apply to_Z_inj; lia). subst j.
        rewrite aget_set_same by (rewrite ltb_spec; lia). exact Hacc'.
      * rewrite aget_set_other by (intro F; apply E; rewrite <- F; exact Hi1).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Hlen|]. intros j Hj. apply Hinv. lia.
Qed.

Lemma pow_loop_spec (rz : Z) (r n : int) :
  (φ r) = rz -> 0 <= rz < pZ ->
  forall z i (t : array int) acc H, gap n i = z -> (φ i) <= (φ n) ->
  (φ (PArray.length t)) = (φ n) + 1 ->
  (φ acc) = rz ^ (φ i) mod pZ ->
  (forall j : int, (φ j) <= (φ i) -> (φ (t.[j])) = rz ^ (φ j) mod pZ) ->
  (φ (PArray.length (pow_loop r n i t acc H))) = (φ n) + 1 /\
  forall j : int, (φ j) <= (φ n) -> (φ ((pow_loop r n i t acc H).[j])) = rz ^ (φ j) mod pZ.
Proof.
  intros Hr Hrz z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i t acc H Hz Hi Hlen Hacc Hinv.
  rewrite pow_loop_eq.
  destruct (bdec (i <? n)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    cbv zeta.
    assert (Hab : 0 <= (φ acc) < pZ)
      by (rewrite Hacc; apply Z.mod_pos_bound; unfold pZ; lia).
    assert (Hacc' : (φ (mulmod acc r)) = rz ^ (φ (i + 1))%uint63 mod pZ).
    { rewrite mulmod_spec by lia. rewrite Hacc, Hr, Hi1.
      rewrite Z.pow_add_r, Z.pow_1_r by lia. rewrite Zmult_mod_idemp_l. reflexivity. }
    eapply IH; [ | reflexivity | lia | | exact Hacc' | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite alength_set. exact Hlen.
    + intros j Hj. rewrite Hi1 in Hj.
      destruct (Z.eq_dec (φ j) ((φ i) + 1)) as [E | E].
      * assert (Ej : j = (i + 1)%uint63) by (apply to_Z_inj; lia). subst j.
        rewrite aget_set_same by (rewrite ltb_spec; lia). exact Hacc'.
      * rewrite aget_set_other by (intro F; apply E; rewrite <- F; exact Hi1).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Hlen|]. intros j Hj. apply Hinv. lia.
Qed.

Lemma prefix_spec (rz : Z) (cs : list Z) (r : int) (xs : PrimString.string) (n : int) :
  (φ r) = rz -> 0 <= rz < pZ -> (φ n) = Z.of_nat (List.length cs) -> (φ n) <= 300000 ->
  (forall i : int, (φ i) < (φ n) -> (φ (PrimString.get xs i)) = nth (Z.to_nat (φ i)) cs 0) ->
  Forall (fun c => 0 <= c < 256) cs ->
  forall j : int, (φ j) <= (φ n) ->
    (φ ((prefix_hashes r xs n).[j])) = G rz 0 (firstn (Z.to_nat (φ j)) cs) mod pZ.
Proof.
  intros Hr Hrz Hn Hnb Hget Hcs j Hj.
  assert (Hn1 : (φ (n + 1))%uint63 = (φ n) + 1) by sia.
  unfold prefix_hashes.
  refine (proj2 (pre_loop_spec rz cs r xs n Hr Hrz Hn Hget Hcs _ 0%uint63 _ 0%uint63 _
                   eq_refl ltac:(change ((φ 0)%uint63) with 0; pose proof (to_Z_bounded n); lia)
                   _ _ _) j Hj).
  - rewrite alength_make_small by lia. exact Hn1.
  - reflexivity.
  - intros j' Hj'. change ((φ 0)%uint63) with 0 in Hj'.
    pose proof (to_Z_bounded j').
    assert (E : (φ j') = 0) by lia. rewrite aget_make, E. reflexivity.
Qed.

Lemma powers_spec (rz : Z) (r n : int) :
  (φ r) = rz -> 0 <= rz < pZ -> (φ n) <= 300000 ->
  forall j : int, (φ j) <= (φ n) -> (φ ((powers r n).[j])) = rz ^ (φ j) mod pZ.
Proof.
  intros Hr Hrz Hnb j Hj.
  assert (Hn1 : (φ (n + 1))%uint63 = (φ n) + 1) by sia.
  unfold powers.
  refine (proj2 (pow_loop_spec rz r n Hr Hrz _ 0%uint63 _ 1%uint63 _
                   eq_refl ltac:(change ((φ 0)%uint63) with 0; pose proof (to_Z_bounded n); lia)
                   _ _ _) j Hj).
  - rewrite alength_make_small by lia. exact Hn1.
  - change ((φ 0)%uint63) with 0. rewrite Z.pow_0_r. reflexivity.
  - intros j' Hj'. change ((φ 0)%uint63) with 0 in Hj'.
    pose proof (to_Z_bounded j').
    assert (E : (φ j') = 0) by lia. rewrite aget_make, E, Z.pow_0_r. reflexivity.
Qed.

Lemma q_loop_spec (pre pw xl xr : array int) (q : int) (F : Z -> Z) :
  (forall j : int, (φ j) < (φ q) -> (φ (hash pre pw xl.[j] xr.[j])) = F (φ j)) ->
  forall z j (out : array int) H, gap q j = z -> (φ j) <= (φ q) -> PArray.length out = q ->
  (forall j' : int, (φ j') < (φ j) -> (φ (out.[j'])) = F (φ j')) ->
  PArray.length (q_loop pre pw xl xr q j out H) = q /\
  forall j' : int, (φ j') < (φ q) -> (φ ((q_loop pre pw xl xr q j out H).[j'])) = F (φ j').
Proof.
  intros Hh z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j out H Hz Hj Hlen Hinv.
  rewrite q_loop_eq.
  destruct (bdec (j <? q)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite alength_set. exact Hlen.
    + intros j' Hj'. rewrite Hj1 in Hj'.
      destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
      * assert (Ej : j' = j) by (apply to_Z_inj; exact E). subst j'.
        rewrite aget_set_same by (rewrite Hlen; exact Hlt). apply Hh. exact Hlt'.
      * rewrite aget_set_other by (intro F'; apply E; rewrite F'; reflexivity).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Hlen|]. intros j' Hj'. apply Hinv. lia.
Qed.

(* ---- one query ---- *)

Lemma combine A B C :
  (((A * C + B) mod pZ - (A mod pZ * (C mod pZ)) mod pZ) mod pZ + C mod pZ) mod pZ
  = (C + B) mod pZ.
Proof.
  rewrite <- Z.mul_mod by (unfold pZ; lia).
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  f_equal. ring.
Qed.

Lemma window_value rz w (L R : Z) : 0 <= L < R -> R <= Z.of_nat (String.length w) ->
  G rz 0 (firstn (Z.to_nat R) (codes w))
    = G rz 0 (firstn (Z.to_nat L) (codes w)) * rz ^ (R - L)
      + G rz 0 (codes (window w (Z.to_N L) (Z.to_N R))) /\
  G rz 0 (1 :: codes (window w (Z.to_N L) (Z.to_N R)))
    = rz ^ (R - L) + G rz 0 (codes (window w (Z.to_N L) (Z.to_N R))).
Proof.
  intros HLR HRn. unfold window. rewrite codes_substring.
  replace (N.to_nat (Z.to_N L)) with (Z.to_nat L) by lia.
  replace (N.to_nat (Z.to_N R - Z.to_N L)) with (Z.to_nat (R - L)) by lia.
  pose proof (codes_length w) as Lc.
  assert (LW : List.length (firstn (Z.to_nat (R - L)) (skipn (Z.to_nat L) (codes w)))
               = Z.to_nat (R - L)).
  { rewrite length_firstn, length_skipn. lia. }
  rewrite (firstn_split (codes w) (Z.to_nat L) (Z.to_nat R)) by lia.
  replace (Z.to_nat R - Z.to_nat L)%nat with (Z.to_nat (R - L)) by lia.
  set (W := firstn (Z.to_nat (R - L)) (skipn (Z.to_nat L) (codes w))) in *.
  rewrite G_app, G_cons, (G_shift rz W (G rz 0 (firstn (Z.to_nat L) (codes w)))),
    (G_shift rz W (0 * rz + 1)), LW.
  replace (Z.of_nat (Z.to_nat (R - L))) with (R - L) by lia.
  split; ring.
Qed.

Lemma hash_spec (rz : Z) (w : string) (pre pw : array int) (L R : int) :
  0 <= rz < pZ ->
  (forall j : int, (φ j) <= Z.of_nat (String.length w) ->
     (φ (pre.[j])) = G rz 0 (firstn (Z.to_nat (φ j)) (codes w)) mod pZ) ->
  (forall j : int, (φ j) <= Z.of_nat (String.length w) -> (φ (pw.[j])) = rz ^ (φ j) mod pZ) ->
  (φ L) < (φ R) -> (φ R) <= Z.of_nat (String.length w) ->
  (φ (hash pre pw L R)) = Hz rz (window w (Z.to_N (φ L)) (Z.to_N (φ R))).
Proof.
  intros Hrz Hpre Hpw HLR HRn.
  pose proof (to_Z_bounded L) as BL.
  assert (Hk : (φ (R - L))%uint63 = (φ R) - (φ L)) by sia.
  unfold hash. cbv zeta.
  pose proof (Hpre R ltac:(lia)) as ER.
  pose proof (Hpre L ltac:(lia)) as EL.
  pose proof (Hpw (R - L)%uint63 ltac:(lia)) as EK. rewrite Hk in EK.
  assert (BR : 0 <= (φ (pre.[R])) < pZ) by (rewrite ER; apply Z.mod_pos_bound; unfold pZ; lia).
  assert (BL' : 0 <= (φ (pre.[L])) < pZ) by (rewrite EL; apply Z.mod_pos_bound; unfold pZ; lia).
  assert (BK : 0 <= (φ (pw.[(R - L)%uint63])) < pZ)
    by (rewrite EK; apply Z.mod_pos_bound; unfold pZ; lia).
  assert (Hm : (φ (mulmod (pre.[L]) (pw.[(R - L)%uint63])))
               = ((φ (pre.[L])) * (φ (pw.[(R - L)%uint63]))) mod pZ) by (apply mulmod_spec; lia).
  assert (Bm : 0 <= (φ (mulmod (pre.[L]) (pw.[(R - L)%uint63]))) < pZ)
    by (rewrite Hm; apply Z.mod_pos_bound; unfold pZ; lia).
  assert (Hs : (φ (submod (pre.[R]) (mulmod (pre.[L]) (pw.[(R - L)%uint63]))))
               = ((φ (pre.[R])) - (φ (mulmod (pre.[L]) (pw.[(R - L)%uint63])))) mod pZ)
    by (apply submod_spec; lia).
  assert (Bs : 0 <= (φ (submod (pre.[R]) (mulmod (pre.[L]) (pw.[(R - L)%uint63])))) < pZ)
    by (rewrite Hs; apply Z.mod_pos_bound; unfold pZ; lia).
  rewrite addmod_spec by lia. rewrite Hs, Hm, ER, EL, EK.
  destruct (window_value rz w (φ L) (φ R) ltac:(lia) HRn) as [E1 E2].
  unfold Hz. rewrite E1, E2. apply combine.
Qed.

(* ---- reading the inputs through repr ---- *)

Lemma repr_get_u (x : array uint) (a : list N) : repr x a ->
  forall i : int, (φ i) < Z.of_nat (List.length a) ->
  (φ (x.[i])) = Z.of_N (get_list_N a (Z.to_N (φ i))).
Proof.
  intros [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  unfold get_list_N. rewrite Z_N_nat. rewrite (nth_error_nth _ _ _ Hm).
  rewrite <- Hr. rewrite Z2N.id; [reflexivity | apply to_Z_bounded].
Qed.

Lemma repr_length_u (x : array uint) (a : list N) : repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_str (xs : PrimString.string) (w : string) : repr xs w ->
  (φ (PrimString.length xs)) = Z.of_nat (String.length w) /\
  forall i : int, (φ i) < Z.of_nat (String.length w) ->
    (φ (PrimString.get xs i)) = nth (Z.to_nat (φ i)) (codes w) 0.
Proof.
  intros [Hl Hc]. split; [symmetry; exact Hl|].
  intros i Hi. destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (c & Hg & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia). rewrite of_to_Z in Hr.
  rewrite (codes_get _ _ _ Hg). rewrite <- Hr.
  rewrite Z2N.id; [reflexivity | apply to_Z_bounded].
Qed.

(* ---- the output ---- *)

Definition out_list (r : N) (s : string) (ls rs : list N) : list N :=
  map (fun k => Hf r (window s (get_list_N ls (N.of_nat k)) (get_list_N rs (N.of_nat k))))
      (seq 0 (List.length ls)).

Lemma out_correct (r : N) (s : string) (ls rs : list N) (o : array@{Set} uint) (q : int) :
  PArray.length@{Set} o = q -> (φ q) = Z.of_nat (List.length ls) ->
  (forall j : int, (φ j) < (φ q) ->
     (φ (PArray.get@{Set} o j))
     = Hz (Z.of_N r) (window s (get_list_N ls (Z.to_N (φ j))) (get_list_N rs (Z.to_N (φ j))))) ->
  repr o (out_list r s ls rs) /\ hashes_spec Hf r s ls rs (out_list r s ls rs).
Proof.
  intros Hol0 Hq Hoc0.
  assert (Hol : PArray.length@{repr_array.u0} o = q) by exact Hol0.
  assert (Hoc : forall j : int, (φ j) < (φ q) ->
     (φ (PArray.get@{repr_array.u0} o j))
     = Hz (Z.of_N r) (window s (get_list_N ls (Z.to_N (φ j))) (get_list_N rs (Z.to_N (φ j)))))
    by exact Hoc0.
  clear Hol0 Hoc0.
  assert (Hlen : List.length (out_list r s ls rs) = List.length ls).
  { unfold out_list. rewrite length_map, length_seq. reflexivity. }
  assert (Hnth : forall k, (k < List.length ls)%nat ->
    nth_error (out_list r s ls rs) k
    = Some (Hf r (window s (get_list_N ls (N.of_nat k)) (get_list_N rs (N.of_nat k))))).
  { intros k Hk. unfold out_list. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec k (List.length ls)); [reflexivity | lia]. }
  split.
  - split.
    + rewrite Hlen, Hol, Hq. reflexivity.
    + intros k Hk. rewrite Hlen in Hk.
      eexists. split; [apply Hnth; exact Hk|].
      unfold repr, repr_uint.
      assert (Hk' : (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. pose proof (to_Z_bounded q). lia. }
      rewrite Hoc by (rewrite Hk', Hq; lia). rewrite Hk'.
      unfold Hf. replace (Z.to_N (Z.of_nat k)) with (N.of_nat k) by lia. reflexivity.
  - split; [exact Hf_separating|]. split.
    + unfold len. rewrite Hlen. reflexivity.
    + intros i Hi. unfold len in Hi. unfold get_list_N at 1.
      rewrite (nth_error_nth _ _ _ (Hnth (N.to_nat i) ltac:(lia))).
      rewrite N2Nat.id. reflexivity.
Qed.

Lemma hashes_impl_correct :
  forall (r : N) (s : string) (ls rs : list N)
         (xr : uint) (xs : PrimString.string) (xl xr' : array uint),
  valid_input r s ls rs ->
  repr xr r -> repr xs s -> repr xl ls -> repr xr' rs ->
  exists h : list N, repr (hashes_impl xr xs xl xr') h /\ hashes_spec Hf r s ls rs h.
Proof.
  intros r s ls rs xr xs xl xr' Hv Hr Hs Hl Hrr.
  destruct Hv as [Hkey [Hs1 Hs2] _ Hq Hrl Hwin].
  unfold key, key_count in Hkey. unfold slen in Hs1, Hs2. unfold len in Hq, Hrl, Hwin.
  assert (Hrz : (φ xr) = Z.of_N r).
  { unfold repr, repr_uint in Hr. rewrite <- Hr. rewrite Z2N.id; [reflexivity | apply to_Z_bounded]. }
  assert (Hrzp : 0 <= (φ xr) < pZ) by (rewrite Hrz; unfold pZ; lia).
  destruct (repr_str xs s Hs) as [Hn Hget].
  pose proof (codes_length s) as Lc.
  assert (Hnb : (φ (PrimString.length xs)) <= 300000) by lia.
  assert (Hpre : forall j : int, (φ j) <= Z.of_nat (String.length s) ->
     (φ ((prefix_hashes xr xs (PrimString.length xs)).[j]))
     = G (φ xr) 0 (firstn (Z.to_nat (φ j)) (codes s)) mod pZ).
  { intros j Hj. apply prefix_spec; try lia; [| apply codes_bound].
    intros i Hi. apply Hget. lia. }
  assert (Hpw : forall j : int, (φ j) <= Z.of_nat (String.length s) ->
     (φ ((powers xr (PrimString.length xs)).[j])) = (φ xr) ^ (φ j) mod pZ).
  { intros j Hj. apply powers_spec; lia. }
  pose proof (repr_length_u xl ls Hl) as Hq'.
  assert (Hh : forall j : int, (φ j) < (φ (PArray.length xl)) ->
     (φ (hash (prefix_hashes xr xs (PrimString.length xs)) (powers xr (PrimString.length xs))
             (xl.[j]) (xr'.[j])))
     = Hz (Z.of_N r) (window s (get_list_N ls (Z.to_N (φ j))) (get_list_N rs (Z.to_N (φ j))))).
  { intros j Hj.
    pose proof (to_Z_bounded j) as Bj.
    pose proof (Hwin (Z.to_N (φ j)) ltac:(lia)) as [W1 W2].
    unfold slen in W2.
    pose proof (repr_get_u xl ls Hl j ltac:(lia)) as GL.
    pose proof (repr_get_u xr' rs Hrr j ltac:(lia)) as GR.
    rewrite <- Hrz.
    rewrite hash_spec with (rz := (φ xr)) (w := s); [ | lia | exact Hpre | exact Hpw | | ].
    - rewrite GL, GR, !N2Z.id. reflexivity.
    - rewrite GL, GR. lia.
    - rewrite GR. lia. }
  unfold hashes_impl. cbv zeta.
  assert (Hmk : PArray.length (PArray.make (PArray.length xl) 0%uint63) = PArray.length xl)
    by (apply alength_make_small; lia).
  destruct (q_loop_spec _ _ xl xr' (PArray.length xl)
              (fun jz => Hz (Z.of_N r) (window s (get_list_N ls (Z.to_N jz))
                                                 (get_list_N rs (Z.to_N jz))))
              Hh _ 0%uint63
              (PArray.make (PArray.length xl) 0%uint63)
              (Zwf_well_founded 0 (gap (PArray.length xl) 0%uint63)) eq_refl
              ltac:(change ((φ 0)%uint63) with 0; pose proof (to_Z_bounded (PArray.length xl)); lia)
              Hmk
              ltac:(intros j' Hj'; change ((φ 0)%uint63) with 0 in Hj';
                    pose proof (to_Z_bounded j'); lia))
    as [Hol Hoc].
  exists (out_list r s ls rs).
  exact (out_correct r s ls rs _ _ Hol Hq' Hoc).
Qed.

Lemma hashes_correct :
  exists H : N -> string -> N,
  forall (r : N) (s : string) (ls rs : list N)
         (xr : uint) (xs : PrimString.string) (xl xr' : array uint),
  valid_input r s ls rs ->
  repr xr r -> repr xs s -> repr xl ls -> repr xr' rs ->
  exists h : list N, repr (hashes xr xs xl xr') h /\ hashes_spec H r s ls rs h.
Proof. exists Hf. exact hashes_impl_correct. Qed.
