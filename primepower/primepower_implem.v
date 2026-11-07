From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Znumtheory.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

(* ------------------------------------------------------------------ *)
(* The termination devices                                             *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

(* Distance to the top of the word: decreases on every strict increase. *)
Definition up (j : int) : Z := (wB - (φ j))%Z.

Lemma dec_up : forall a b : int, (a <? b) = true -> Zwf 0 (up b) (up a).
Proof.
  intros a b H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded b). unfold Zwf, up. lia.
Qed.

Lemma dec_down : forall a p : int, (a <? p) = true -> Zwf 0 (φ (p - 1)) (φ p).
Proof. intros a p H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

Lemma dec_half : forall e : int, (0 <? e) = true -> Zwf 0 (φ (e >> 1)) (φ e).
Proof. intros e H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition M : int := 1000000007.

(* acc * b^e mod M, by repeated squaring. *)
Fixpoint pow_loop (b e acc : int) (H : Acc (Zwf 0) (φ e)) {struct H} : int :=
  match bdec (0 <? e) with
  | left He =>
      pow_loop ((b * b) mod M) (e >> 1)
        (if is_even e then acc else (acc * b) mod M)
        (Acc_inv H (dec_half e He))
  | right _ => acc
  end.

Lemma pow_loop_eq : forall b e acc H,
  pow_loop b e acc H =
  match bdec (0 <? e) with
  | left He =>
      pow_loop ((b * b) mod M) (e >> 1)
        (if is_even e then acc else (acc * b) mod M)
        (Acc_inv H (dec_half e He))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition powmod (b e : int) : int :=
  pow_loop (b mod M) e 1 (Zwf_well_founded 0 (φ e)).

(* Cross out j, j + i, j + 2i, ... up to R. *)
Fixpoint cross_loop (i R j : int) (s : array int)
    (H : Acc (Zwf 0) (up j)) {struct H} : array int :=
  match bdec (j <=? R) with
  | left _ =>
      let j' := j + i in
      match bdec (j <? j') with
      | left Hj => cross_loop i R j' s.[j <- 0] (Acc_inv H (dec_up j j' Hj))
      | right _ => s.[j <- 0]
      end
  | right _ => s
  end.

Lemma cross_loop_eq : forall i R j s H,
  cross_loop i R j s H =
  match bdec (j <=? R) with
  | left _ =>
      let j' := j + i in
      match bdec (j <? j') with
      | left Hj => cross_loop i R j' s.[j <- 0] (Acc_inv H (dec_up j j' Hj))
      | right _ => s.[j <- 0]
      end
  | right _ => s
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The sieve of Eratosthenes, for i = 2, 3, ... while i * i <= R. *)
Fixpoint sieve_loop (R i : int) (s : array int)
    (H : Acc (Zwf 0) (up i)) {struct H} : array int :=
  match bdec (i * i <=? R) with
  | left _ =>
      let s' := if s.[i] =? 0 then s
                else cross_loop i R (i * i) s
                       (Zwf_well_founded 0 (up (i * i))) in
      match bdec (i <? i + 1) with
      | left Hi => sieve_loop R (i + 1) s' (Acc_inv H (dec_up i (i + 1) Hi))
      | right _ => s'
      end
  | right _ => s
  end.

Lemma sieve_loop_eq : forall R i s H,
  sieve_loop R i s H =
  match bdec (i * i <=? R) with
  | left _ =>
      let s' := if s.[i] =? 0 then s
                else cross_loop i R (i * i) s
                       (Zwf_well_founded 0 (up (i * i))) in
      match bdec (i <? i + 1) with
      | left Hi => sieve_loop R (i + 1) s' (Acc_inv H (dec_up i (i + 1) Hi))
      | right _ => s'
      end
  | right _ => s
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* s.[p] <> 0 iff p is prime, for p <= R. *)
Definition sieve (R : int) : array int :=
  sieve_loop R 2 (PArray.make (R + 1) 1).[0 <- 0].[1 <- 0]
    (Zwf_well_founded 0 (up 2)).

(* p = R, R - 1, ..., L: acc becomes the product of p^E over the primes
   p seen, modulo M. *)
Fixpoint prod_loop (s : array int) (E L p acc : int)
    (H : Acc (Zwf 0) (φ p)) {struct H} : int :=
  let acc' := if s.[p] =? 0 then acc else (powmod p E * acc) mod M in
  match bdec (L <? p) with
  | left Hp => prod_loop s E L (p - 1) acc' (Acc_inv H (dec_down L p Hp))
  | right _ => acc'
  end.

Lemma prod_loop_eq : forall s E L p acc H,
  prod_loop s E L p acc H =
  let acc' := if s.[p] =? 0 then acc else (powmod p E * acc) mod M in
  match bdec (L <? p) with
  | left Hp => prod_loop s E L (p - 1) acc' (Acc_inv H (dec_down L p Hp))
  | right _ => acc'
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition primepower_impl (E L R : uint) : uint :=
  if R <? L then 1
  else prod_loop (sieve R) E L R 1 (Zwf_well_founded 0 (φ R)).

(* ------------------------------------------------------------------ *)
(* Prop side: modular exponentiation                                   *)
(* ------------------------------------------------------------------ *)

Definition Mz : Z := 1000000007.

Lemma M_val : (φ M) = Mz.
Proof. reflexivity. Qed.

(* The product of two residues fits in the word. *)
Lemma mulmod_spec : forall a b : int, ((φ a) < Mz)%Z -> ((φ b) < Mz)%Z ->
  (φ ((a * b) mod M)) = (((φ a) * (φ b)) mod Mz)%Z.
Proof.
  intros a b Ha Hb. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite mod_spec, mul_spec, M_val. f_equal.
  apply Z.mod_small. rewrite wB_val. unfold Mz in *. nia.
Qed.

Lemma pow_step : forall a x q : Z, (0 <= q)%Z ->
  ((a * ((x * x) mod Mz) ^ q) mod Mz = (a * x ^ (q + q)) mod Mz)%Z.
Proof.
  intros a x q Hq.
  rewrite <- Z.mul_mod_idemp_r by (unfold Mz; lia).
  rewrite Z.mod_pow_l, Z.mul_mod_idemp_r by (unfold Mz; lia).
  rewrite Z.pow_mul_l, Z.pow_add_r by lia. reflexivity.
Qed.

Lemma pow_loop_spec : forall (z : Z) (e b acc : int) (H : Acc (Zwf 0) (φ e)),
  (φ e) = z -> ((φ b) < Mz)%Z -> ((φ acc) < Mz)%Z ->
  (φ (pow_loop b e acc H)) = (((φ acc) * (φ b) ^ (φ e)) mod Mz)%Z.
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros e b acc H Hz Hb Hacc.
  pose proof (to_Z_bounded b) as Bb. pose proof (to_Z_bounded acc) as Bacc.
  pose proof (to_Z_bounded e) as Be.
  rewrite pow_loop_eq.
  destruct (bdec (0 <? e)) as [He | He].
  - assert (Hb' : (φ ((b * b) mod M)) = (((φ b) * (φ b)) mod Mz)%Z)
      by (apply mulmod_spec; assumption).
    assert (He' : (φ (e >> 1)) = ((φ e) / 2)%Z) by sia.
    assert (Hdm : (φ e) = (2 * ((φ e) / 2) + (φ e) mod 2)%Z)
      by (apply Z.div_mod; lia).
    assert (Hq : (0 <= (φ e) / 2)%Z) by (apply Z.div_pos; lia).
    assert (HMz : (0 < Mz)%Z) by (unfold Mz; lia).
    rewrite (IH (φ (e >> 1))); [ | rewrite <- Hz; apply dec_half; exact He
                                 | reflexivity
                                 | rewrite Hb'; apply Z.mod_pos_bound; exact HMz
                                 | ].
    + rewrite Hb', He', pow_step by exact Hq.
      pose proof (is_even_spec e) as Hev.
      destruct (is_even e).
      * rewrite Hev in Hdm. rewrite Hdm at 2. f_equal. f_equal. f_equal. lia.
      * rewrite Hev in Hdm. rewrite mulmod_spec by assumption.
        rewrite Z.mul_mod_idemp_l by lia.
        rewrite Hdm at 2. rewrite <- Z.mul_assoc, <- Z.pow_succ_r by lia.
        f_equal. f_equal. f_equal. lia.
    + destruct (is_even e); [exact Hacc|].
      rewrite mulmod_spec by assumption. apply Z.mod_pos_bound. exact HMz.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in He.
    change (φ 0) with 0%Z in He.
    replace (φ e) with 0%Z by lia. rewrite Z.pow_0_r, Z.mul_1_r.
    symmetry. apply Z.mod_small. lia.
Qed.

Lemma powmod_spec : forall b e : int,
  (φ (powmod b e)) = (((φ b) ^ (φ e)) mod Mz)%Z.
Proof.
  intros b e. unfold powmod.
  rewrite (pow_loop_spec (φ e)); [ | reflexivity | | ].
  - change (φ 1) with 1%Z. rewrite Z.mul_1_l.
    rewrite mod_spec, M_val. apply Z.mod_pow_l.
  - rewrite mod_spec, M_val. apply Z.mod_pos_bound. unfold Mz; lia.
  - change (φ 1) with 1%Z. unfold Mz; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the sieve                                                *)
(* ------------------------------------------------------------------ *)

(* k is crossed out once the divisors below i have been processed: it is
   below 2, or it has a divisor d in [2, i) with d * d <= k. *)
Definition crossed (i k : Z) : Prop :=
  (k < 2 \/ exists d, 2 <= d < i /\ (d | k) /\ d * d <= k)%Z.

Lemma crossed_succ : forall i k : Z, (2 <= i)%Z ->
  crossed (i + 1) k <-> crossed i k \/ ((i | k) /\ i * i <= k)%Z.
Proof.
  intros i k Hi. unfold crossed. split.
  - intros [Hk | (d & Hd & Hdk & Hdd)]; [left; left; exact Hk|].
    destruct (Z.eq_dec d i) as [E | E].
    + subst d. right. split; assumption.
    + left. right. exists d. repeat split; try assumption; lia.
  - intros [[Hk | (d & Hd & Hdk & Hdd)] | [Hik Hii]].
    + left. exact Hk.
    + right. exists d. repeat split; try assumption; lia.
    + right. exists i. repeat split; try assumption; lia.
Qed.

Lemma crossed_skip : forall i k : Z, (2 <= i)%Z -> crossed i i ->
  crossed (i + 1) k <-> crossed i k.
Proof.
  intros i k Hi Hc. rewrite crossed_succ by exact Hi. split; [|tauto].
  intros [H | [Hik Hii]]; [exact H|].
  destruct Hc as [Hc | (d & Hd & Hdi & Hdd)]; [lia|].
  right. exists d. split; [lia|]. split.
  - apply (Z.divide_trans d i k); assumption.
  - nia.
Qed.

Lemma crossed_final : forall i k : Z, (0 <= k)%Z -> (0 <= i)%Z -> (k < i * i)%Z ->
  crossed i k <-> ~ prime k.
Proof.
  intros i k Hk Hi Hki. split.
  - intros [Hk2 | (d & Hd & Hdk & Hdd)] Hp.
    + apply prime_alt in Hp. destruct Hp as [Hp _]. lia.
    + apply prime_alt in Hp. destruct Hp as [_ Hp].
      apply (Hp d); [nia | exact Hdk].
  - intros Hnp. destruct (Z_lt_le_dec k 2) as [Hk2 | Hk2]; [left; exact Hk2|].
    right. destruct (not_prime_divide k ltac:(lia) Hnp) as (n & Hn & [c Hc]).
    destruct (Z_le_gt_dec (n * n) k) as [Hnn | Hnn].
    + exists n. split; [split; [lia | nia]|]. split; [exists c; exact Hc | exact Hnn].
    + assert (Hc1 : (1 < c)%Z) by nia.
      assert (Hcn : (c < n)%Z) by nia.
      exists c. split; [split; [lia | nia]|]. split.
      * exists n. lia.
      * nia.
Qed.

Lemma no_mult_between : forall i t c : Z, (0 < i)%Z ->
  (t * i < c * i)%Z -> (c * i < t * i + i)%Z -> False.
Proof. intros i t c Hi H1 H2. assert (t < c)%Z by nia. nia. Qed.

Section Sieve.

Variable R : int.
Hypothesis HR1 : (1 <= (φ R))%Z.
Hypothesis HR2 : ((φ R) <= 1000000)%Z.

Definition sieve_inv (i : Z) (s : array int) : Prop :=
  (φ (PArray.length s)) = ((φ R) + 1)%Z /\
  forall k : int, ((φ k) <= (φ R))%Z -> (s.[k] = 0 <-> crossed i (φ k)).

Lemma cross_loop_spec : forall i : int, (2 <= (φ i))%Z -> ((φ i) <= (φ R))%Z ->
  forall (z : Z) (j : int) (s : array int) (H : Acc (Zwf 0) (up j)),
  up j = z ->
  (φ (PArray.length s)) = ((φ R) + 1)%Z ->
  ((φ i) * (φ i) <= (φ j))%Z -> ((φ i) | (φ j))%Z ->
  (forall k : int, ((φ k) <= (φ R))%Z ->
     (s.[k] = 0 <-> crossed (φ i) (φ k) \/
                    (((φ i) | (φ k)) /\ (φ i) * (φ i) <= (φ k) < (φ j))%Z)) ->
  (φ (PArray.length (cross_loop i R j s H))) = ((φ R) + 1)%Z /\
  forall k : int, ((φ k) <= (φ R))%Z ->
    ((cross_loop i R j s H).[k] = 0 <->
       crossed (φ i) (φ k) \/ (((φ i) | (φ k)) /\ (φ i) * (φ i) <= (φ k))%Z).
Proof.
  intros i Hi2 HiR z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j s H Hz Hlen Hjii Hij Hinv.
  pose proof (to_Z_bounded j) as Bj.
  rewrite cross_loop_eq.
  destruct (bdec (j <=? R)) as [HjR | HjR].
  - rewrite leb_spec in HjR.
    assert (Hj' : (φ (j + i)) = ((φ j) + (φ i))%Z) by sia.
    assert (Hlen' : (φ (PArray.length s.[j <- 0])) = ((φ R) + 1)%Z)
      by (rewrite alength_set; exact Hlen).
    assert (Hinv' : forall k : int, ((φ k) <= (φ R))%Z ->
       (s.[j <- 0].[k] = 0 <-> crossed (φ i) (φ k) \/
          (((φ i) | (φ k)) /\ (φ i) * (φ i) <= (φ k) < (φ j) + (φ i))%Z)).
    { intros k Hk. destruct (Uint63.eqs j k) as [E | E].
      - subst k. rewrite aget_set_same by (rewrite ltb_spec; lia).
        split; [intros _; right; repeat split; try assumption; lia | reflexivity].
      - rewrite aget_set_other by exact E. rewrite (Hinv k Hk).
        assert (Ez : (φ j) <> (φ k)) by (intro F; apply E; apply to_Z_inj; exact F).
        split; intros [C | (Hd & Hl & Hh)]; [left; exact C | | left; exact C |].
        + right. repeat split; try assumption; lia.
        + right. repeat split; try assumption.
          destruct (Z_lt_le_dec (φ k) (φ j)) as [Hkj | Hkj]; [exact Hkj|].
          exfalso. destruct Hij as [t Ht]. destruct Hd as [c Hc].
          apply (no_mult_between (φ i) t c); lia. }
    cbv zeta. destruct (bdec (j <? j + i)) as [Hjj | Hjj].
    + apply (IH (up (j + i))); [ rewrite <- Hz; apply dec_up; exact Hjj
                               | reflexivity | exact Hlen' | lia | | ].
      * rewrite Hj'. apply Z.divide_add_r; [exact Hij | apply Z.divide_refl].
      * intros k Hk. rewrite Hj'. apply Hinv'. exact Hk.
    + exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hjj. lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec in HjR.
    split; [exact Hlen|].
    intros k Hk. rewrite (Hinv k Hk).
    split; [intros [C | (Hd & Hl & Hh)] | intros [C | (Hd & Hl)]];
      [left; exact C | | left; exact C |]; right; repeat split; try assumption; lia.
Qed.

Lemma sieve_loop_spec : forall (z : Z) (i : int) (s : array int)
  (H : Acc (Zwf 0) (up i)),
  up i = z -> (2 <= (φ i))%Z -> (((φ i) - 1) * ((φ i) - 1) <= (φ R))%Z ->
  sieve_inv (φ i) s ->
  (φ (PArray.length (sieve_loop R i s H))) = ((φ R) + 1)%Z /\
  forall k : int, ((φ k) <= (φ R))%Z ->
    ((sieve_loop R i s H).[k] = 0 <-> ~ prime (φ k)).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i s H Hz Hi2 Hi1 Hinv.
  assert (Bi : ((φ i) <= 1001)%Z) by nia.
  assert (Hii : (φ (i * i)) = ((φ i) * (φ i))%Z)
    by (rewrite mul_spec; apply Z.mod_small; rewrite wB_val; nia).
  rewrite sieve_loop_eq.
  destruct (bdec (i * i <=? R)) as [Hc | Hc].
  - rewrite leb_spec, Hii in Hc. cbv zeta.
    assert (HiR : ((φ i) <= (φ R))%Z) by nia.
    assert (Hs' : sieve_inv ((φ i) + 1)
        (if s.[i] =? 0 then s
         else cross_loop i R (i * i) s (Zwf_well_founded 0 (up (i * i))))).
    { destruct Hinv as [Hlen Hinv].
      destruct (s.[i] =? 0) eqn:E.
      - rewrite eqb_spec in E. split; [exact Hlen|].
        intros k Hk. rewrite (Hinv k Hk). symmetry.
        apply crossed_skip; [lia|]. apply (Hinv i HiR). exact E.
      - assert (Hinv0 : forall k : int, ((φ k) <= (φ R))%Z ->
           (s.[k] = 0 <-> crossed (φ i) (φ k) \/
              (((φ i) | (φ k)) /\ (φ i) * (φ i) <= (φ k) < (φ (i * i)))%Z)).
        { intros k Hk. rewrite (Hinv k Hk). rewrite Hii. split; [tauto|].
          intros [C | (_ & Hl & Hh)]; [exact C | lia]. }
        destruct (cross_loop_spec i ltac:(lia) HiR (up (i * i)) (i * i) s
                    (Zwf_well_founded 0 (up (i * i))) eq_refl Hlen
                    ltac:(rewrite Hii; lia)
                    ltac:(rewrite Hii; exists (φ i); reflexivity) Hinv0)
          as [L1 L2].
        split; [exact L1|].
        intros k Hk. rewrite (L2 k Hk). symmetry. apply crossed_succ. lia. }
    destruct (bdec (i <? i + 1)) as [Hi | Hi].
    + assert (Hi' : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      apply (IH (up (i + 1))); [ rewrite <- Hz; apply dec_up; exact Hi
                               | reflexivity | lia | | rewrite Hi'; exact Hs' ].
      rewrite Hi'. replace ((φ i) + 1 - 1)%Z with (φ i) by lia. lia.
    + exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. sia.
  - rewrite <- Bool.not_true_iff_false, leb_spec, Hii in Hc.
    destruct Hinv as [Hlen Hinv]. split; [exact Hlen|].
    intros k Hk. rewrite (Hinv k Hk).
    pose proof (to_Z_bounded k). apply crossed_final; lia.
Qed.

Lemma int_1_0 : (1 : int) <> 0.
Proof. intro F. apply (f_equal to_Z) in F. discriminate F. Qed.

Lemma sieve_spec :
  (φ (PArray.length (sieve R))) = ((φ R) + 1)%Z /\
  forall k : int, ((φ k) <= (φ R))%Z -> ((sieve R).[k] = 0 <-> ~ prime (φ k)).
Proof.
  unfold sieve. apply (sieve_loop_spec (up 2)); [reflexivity | | | ];
    change (φ 2) with 2%Z; [lia | lia | ].
  assert (HR' : (φ (R + 1)) = ((φ R) + 1)%Z) by sia.
  assert (Hlen : (φ (PArray.length (PArray.make (R + 1) 1))) = ((φ R) + 1)%Z).
  { rewrite alength_make.
    replace (R + 1 <=? PArray.max_length) with true; [exact HR'|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  split; [rewrite !alength_set; exact Hlen|].
  intros k Hk.
  destruct (Uint63.eqs 1 k) as [E1 | E1].
  - subst k. rewrite aget_set_same
      by (rewrite !alength_set, ltb_spec, Hlen; change (φ 1) with 1%Z; lia).
    split; [intros _; left; change (φ 1) with 1%Z; lia | reflexivity].
  - rewrite aget_set_other by exact E1.
    destruct (Uint63.eqs 0 k) as [E0 | E0].
    + subst k. rewrite aget_set_same
        by (rewrite ltb_spec, Hlen; change (φ 0) with 0%Z; lia).
      split; [intros _; left; change (φ 0) with 0%Z; lia | reflexivity].
    + rewrite aget_set_other by exact E0. rewrite aget_make.
      assert (Hk2 : (2 <= (φ k))%Z).
      { assert ((φ k) <> 1%Z) by (intro F; apply E1; apply to_Z_inj; exact (eq_sym F)).
        assert ((φ k) <> 0%Z) by (intro F; apply E0; apply to_Z_inj; exact (eq_sym F)).
        pose proof (to_Z_bounded k). lia. }
      split; [intro F; exfalso; exact (int_1_0 F)|].
      intros [C | (d & Hd & _)]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the product                                              *)
(* ------------------------------------------------------------------ *)

Lemma ppf_step : forall (e : N) (p : Z) (k : nat), (0 <= p)%Z ->
  Z.of_N (prime_power_product_from e (Z.to_N p) (S k))
  = ((if prime_dec p then p ^ Z.of_N e else 1)
     * Z.of_N (prime_power_product_from e (Z.to_N p + 1) k))%Z.
Proof.
  intros e p k Hp. cbn [prime_power_product_from].
  rewrite Z2N.id by exact Hp.
  destruct (prime_dec p); rewrite N2Z.inj_mul; [rewrite N2Z.inj_pow, Z2N.id by exact Hp|];
    reflexivity.
Qed.

Lemma prod_loop_spec : forall (s : array int) (E L : int),
  (forall k : int, ((φ k) <= (φ R))%Z -> (s.[k] = 0 <-> ~ prime (φ k))) ->
  (1 <= (φ L))%Z ->
  forall (z : Z) (p acc : int) (H : Acc (Zwf 0) (φ p)),
  (φ p) = z -> ((φ L) <= (φ p) <= (φ R))%Z ->
  (φ acc) = (Z.of_N (prime_power_product_from (Z.to_N (φ E)) (Z.to_N (φ p) + 1)
                     (Z.to_nat ((φ R) - (φ p)))) mod Mz)%Z ->
  (φ (prod_loop s E L p acc H))
  = (Z.of_N (prime_power_product_from (Z.to_N (φ E)) (Z.to_N (φ L))
               (Z.to_nat ((φ R) + 1 - (φ L)))) mod Mz)%Z.
Proof.
  intros s E L Hs HL z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p acc H Hz Hp Hacc.
  pose proof (to_Z_bounded E) as BE.
  assert (HMz : (0 < Mz)%Z) by (unfold Mz; lia).
  rewrite prod_loop_eq. cbv zeta.
  assert (Hacc' : (φ (if s.[p] =? 0 then acc else (powmod p E * acc) mod M))
     = (Z.of_N (prime_power_product_from (Z.to_N (φ E)) (Z.to_N (φ p))
                  (Z.to_nat ((φ R) + 1 - (φ p)))) mod Mz)%Z).
  { replace (Z.to_nat ((φ R) + 1 - (φ p))) with (S (Z.to_nat ((φ R) - (φ p)))) by lia.
    rewrite ppf_step by lia. rewrite Z2N.id by lia.
    destruct (s.[p] =? 0) eqn:E0.
    - rewrite eqb_spec in E0. apply (Hs p ltac:(lia)) in E0.
      destruct (prime_dec (φ p)) as [Hp' | Hp']; [contradiction|].
      rewrite Z.mul_1_l. exact Hacc.
    - rewrite eqb_false_spec in E0.
      destruct (prime_dec (φ p)) as [Hp' | Hp'];
        [| exfalso; apply E0; apply (Hs p ltac:(lia)); exact Hp'].
      rewrite mulmod_spec;
        [ | rewrite powmod_spec; apply Z.mod_pos_bound; exact HMz
          | rewrite Hacc; apply Z.mod_pos_bound; exact HMz].
      rewrite powmod_spec, Hacc. symmetry. apply Z.mul_mod. lia. }
  destruct (bdec (L <? p)) as [Hlp | Hlp].
  - pose proof Hlp as Hlp0. rewrite ltb_spec in Hlp0.
    assert (Hp1 : (φ (p - 1)) = ((φ p) - 1)%Z) by sia.
    apply (IH (φ (p - 1))); [ rewrite <- Hz, Hp1; unfold Zwf; lia
                            | reflexivity | lia | ].
    rewrite Hp1.
    replace (Z.to_N ((φ p) - 1) + 1)%N with (Z.to_N (φ p)) by lia.
    replace ((φ R) - ((φ p) - 1))%Z with ((φ R) + 1 - (φ p))%Z by lia.
    exact Hacc'.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlp.
    replace (φ L) with (φ p) by lia. exact Hacc'.
Qed.

End Sieve.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma primepower_impl_correct :
  forall (e l r : N) (x y z : uint),
  valid_input e l r -> repr x e -> repr y l -> repr z r ->
  exists o : N, repr (primepower_impl x y z) o /\ primepower_spec e l r o.
Proof.
  intros e l r x y z Hv Hx Hy Hz.
  unfold repr, repr_uint in Hx, Hy, Hz. subst e l r.
  destruct Hv as [Ve Vl Vlr Vr].
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
  pose proof (to_Z_bounded z).
  assert (Hl1 : (1 <= (φ y))%Z) by lia.
  assert (Hlr : ((φ y) <= (φ z))%Z) by lia.
  assert (Hr : ((φ z) <= 1000000)%Z) by lia.
  exists (Z.to_N (φ (primepower_impl x y z))). split; [reflexivity|].
  unfold primepower_spec, prime_power_product, modulus, primepower_impl.
  destruct (z <? y) eqn:C; [rewrite ltb_spec in C; lia|].
  destruct (sieve_spec z ltac:(lia) Hr) as [_ Hs].
  rewrite (prod_loop_spec z Hr (sieve z) x y Hs Hl1 (φ z) z 1
             (Zwf_well_founded 0 (φ z)) eq_refl ltac:(lia)).
  - replace (N.to_nat (Z.to_N (φ z) + 1 - Z.to_N (φ y)))
      with (Z.to_nat ((φ z) + 1 - (φ y))) by lia.
    change Mz with (Z.of_N 1000000007).
    rewrite <- N2Z.inj_mod, N2Z.id. reflexivity.
  - replace ((φ z) - (φ z))%Z with 0%Z by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition primepower : uint -> uint -> uint -> uint := primepower_impl.

Definition primepower_correct :
  forall (e l r : N) (x y z : uint),
  valid_input e l r -> repr x e -> repr y l -> repr z r ->
  exists o : N, repr (primepower x y z) o /\ primepower_spec e l r o
  := primepower_impl_correct.
