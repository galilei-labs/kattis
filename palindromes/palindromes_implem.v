(* Implementation of palindromes (palindromes.spec).

   Code.  Manacher over the 2n doubled centres q = a + b (cnt.[q] = number
   of palindromic candidates [q/2 - k, (q+1)/2 + k]); every query [l, r] is
   split by centre parity and at its middle into four clipped sums
   sum_{i < T} min(d_i, i - A + 1)^+, answered offline: queries bucketed by
   T (head/next lists), a sweep over T inserting one centre at a time into
   two Fenwick trees (constant and slope of a piecewise linear function of
   A).  Wrapping 63-bit arithmetic, exact since every answer is < 2^63.
   Termination: erased Acc (Zwf 0) on Z measures, as in the template.  No
   nat, no lists, flat arrays only. *)

From Palindromes.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63 String Ascii PrimString.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Sums over integer ranges (Prop side)                                *)
(* ------------------------------------------------------------------ *)

Ltac zb :=
  repeat match goal with
  | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _)%Z = false |- _ => apply Z.leb_gt in H
  | H : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _)%Z = false |- _ => apply Z.ltb_ge in H
  | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H
  end.

Section Sums.
Local Open Scope Z_scope.

(* f a + f (a+1) + ... + f (a+k-1) *)
Fixpoint sumz (f : Z -> Z) (a : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => sumz f a k' + f (a + Z.of_nat k')
  end.

Lemma sumz_ext : forall f g a k,
  (forall x, a <= x < a + Z.of_nat k -> f x = g x) -> sumz f a k = sumz g a k.
Proof.
  intros f g a k. induction k as [|k IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros x Hx; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumz_split : forall f a k1 k2,
  sumz f a (k1 + k2) = sumz f a k1 + sumz f (a + Z.of_nat k1) k2.
Proof.
  intros f a k1 k2. induction k2 as [|k2 IH]; simpl.
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. simpl. rewrite IH.
    replace (a + Z.of_nat (k1 + k2)) with (a + Z.of_nat k1 + Z.of_nat k2) by lia. lia.
Qed.

Lemma sumz_zero : forall f a k,
  (forall x, a <= x < a + Z.of_nat k -> f x = 0) -> sumz f a k = 0.
Proof.
  intros f a k. induction k as [|k IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros x Hx; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumz_add : forall f g a k,
  sumz (fun x => f x + g x) a k = sumz f a k + sumz g a k.
Proof. intros f g a k. induction k as [|k IH]; simpl; lia. Qed.

Lemma sumz_scale : forall c f a k,
  sumz (fun x => c * f x) a k = c * sumz f a k.
Proof. intros c f a k. induction k as [|k IH]; simpl; lia. Qed.

Lemma sumz_const0 : forall a k, sumz (fun _ => 0) a k = 0.
Proof. intros a k. apply sumz_zero. reflexivity. Qed.

Lemma sumz_point : forall p d a k,
  sumz (fun x => if x =? p then d else 0) a k
  = if andb (a <=? p) (p <? a + Z.of_nat k) then d else 0.
Proof.
  intros p d a k. induction k as [|k IH]; cbn [sumz].
  - replace (a + Z.of_nat 0) with a by lia.
    destruct (a <=? p) eqn:E1, (p <? a) eqn:E2; simpl; auto; zb; lia.
  - rewrite IH.
    destruct (a <=? p) eqn:E1, (p <? a + Z.of_nat k) eqn:E2,
             (p <? a + Z.of_nat (S k)) eqn:E3, (a + Z.of_nat k =? p) eqn:E4; simpl;
      repeat match goal with
      | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
      | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
      | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
      | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
      | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
      | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
      end; lia.
Qed.

Lemma sumz_front : forall f a k,
  sumz f a (S k) = f a + sumz f (a + 1) k.
Proof.
  intros f a k. replace (S k) with (1 + k)%nat by lia.
  rewrite sumz_split. simpl. f_equal. f_equal. lia.
Qed.

Lemma sumz_shift : forall f a c k,
  sumz f a k = sumz (fun x => f (x - c)) (a + c) k.
Proof.
  intros f a c k. induction k as [|k IH]; simpl; [reflexivity|].
  rewrite IH. f_equal. f_equal. lia.
Qed.

(* reading the range backwards *)
Lemma sumz_rev : forall f a k,
  sumz f a k = sumz (fun x => f (2 * a + Z.of_nat k - 1 - x)) a k.
Proof.
  intros f a k. revert a. induction k as [|k IH]; intros a; [reflexivity|].
  transitivity (sumz f a k + f (a + Z.of_nat k)); [reflexivity|].
  rewrite sumz_front. rewrite IH. rewrite (sumz_shift _ a 1 k).
  match goal with |- ?A + ?B = ?C + ?D => assert (E1 : A = D); [| assert (E2 : B = C); [|lia]] end.
  - apply sumz_ext. intros x Hx. f_equal. lia.
  - f_equal. lia.
Qed.

(* pairs: x = 2i and x = 2i+1 *)
Lemma sumz_pairs : forall f k,
  sumz f 0 (2 * k) = sumz (fun i => f (2 * i) + f (2 * i + 1)) 0 k.
Proof.
  intros f k. induction k as [|k IH]; [reflexivity|].
  replace (2 * S k)%nat with (S (S (2 * k))) by lia.
  transitivity (sumz f 0 (2 * k) + f (0 + Z.of_nat (2 * k)) + f (0 + Z.of_nat (S (2 * k))));
    [reflexivity|].
  transitivity (sumz (fun i => f (2 * i) + f (2 * i + 1)) 0 k
     + (f (2 * (0 + Z.of_nat k)) + f (2 * (0 + Z.of_nat k) + 1))); [|reflexivity].
  rewrite IH.
  replace (0 + Z.of_nat (S (2 * k))) with (2 * (0 + Z.of_nat k) + 1) by lia.
  replace (0 + Z.of_nat (2 * k)) with (2 * (0 + Z.of_nat k)) by lia. lia.
Qed.

(* a sum over a sub-range of [a, a+K) whose function vanishes outside *)
Lemma sumz_sub : forall f a K b k,
  a <= b -> b + Z.of_nat k <= a + Z.of_nat K ->
  (forall x, a <= x < a + Z.of_nat K -> (x < b \/ b + Z.of_nat k <= x) -> f x = 0) ->
  sumz f a K = sumz f b k.
Proof.
  intros f a K b k H1 H2 H3.
  replace K with (Z.to_nat (b - a) + (k + Z.to_nat (a + Z.of_nat K - b - Z.of_nat k)))%nat by lia.
  rewrite !sumz_split.
  rewrite (sumz_zero f a) by (intros x Hx; apply H3; lia).
  rewrite (sumz_zero f (a + Z.of_nat (Z.to_nat (b - a)) + Z.of_nat k)) by (intros x Hx; apply H3; lia).
  replace (a + Z.of_nat (Z.to_nat (b - a))) with b by lia. lia.
Qed.

Lemma sumz_nonneg : forall f a k,
  (forall x, 0 <= f x) -> 0 <= sumz f a k.
Proof. intros f a k H. induction k; simpl; [lia|]. specialize (H (a + Z.of_nat k)). lia. Qed.

Lemma sumz_le : forall f a k c,
  (forall x, f x <= c) -> sumz f a k <= Z.of_nat k * c.
Proof.
  intros f a k c H. induction k; [simpl; lia|].
  change (sumz f a (S k)) with (sumz f a k + f (a + Z.of_nat k)).
  specialize (H (a + Z.of_nat k)). rewrite Nat2Z.inj_succ. lia.
Qed.

(* Fenwick ranges: D (a+1) + ... + D b *)
Definition rs (D : Z -> Z) (a b : Z) : Z := sumz D (a + 1) (Z.to_nat (b - a)).

Lemma rs_split : forall D a b c, a <= b <= c -> rs D a c = rs D a b + rs D b c.
Proof.
  intros D a b c H. unfold rs.
  replace (Z.to_nat (c - a)) with (Z.to_nat (b - a) + Z.to_nat (c - b))%nat by lia.
  rewrite sumz_split. f_equal. f_equal. lia.
Qed.

Definition upd (D : Z -> Z) (p d : Z) : Z -> Z :=
  fun x => if x =? p then D x + d else D x.

Lemma rs_upd : forall D p d a b, a <= b ->
  rs (upd D p d) a b = rs D a b + (if andb (a <? p) (p <=? b) then d else 0).
Proof.
  intros D p d a b H. unfold rs, upd.
  rewrite (sumz_ext _ (fun x => D x + (if x =? p then d else 0))).
  - rewrite sumz_add, sumz_point. f_equal.
    destruct (a + 1 <=? p) eqn:E1, (p <? a + 1 + Z.of_nat (Z.to_nat (b - a))) eqn:E2,
             (a <? p) eqn:E3, (p <=? b) eqn:E4; simpl;
      repeat match goal with
      | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
      | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
      | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
      | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
      end; lia.
  - intros x Hx. destruct (x =? p); lia.
Qed.

End Sums.

(* ------------------------------------------------------------------ *)
(* The low bit                                                         *)
(* ------------------------------------------------------------------ *)

Section LowBit.
Local Open Scope Z_scope.

Lemma land2 : forall a b e f, (e = 0 \/ e = 1) -> (f = 0 \/ f = 1) ->
  Z.land (2 * a + e) (2 * b + f) = 2 * Z.land a b + e * f.
Proof.
  intros a b e f He Hf. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  destruct (Z.eq_dec k 0) as [-> | Hk0].
  - destruct He as [-> | ->], Hf as [-> | ->]; rewrite ?Z.add_0_r, ?Z.mul_0_r, ?Z.mul_1_r;
      rewrite ?Z.testbit_even_0, ?Z.testbit_odd_0; reflexivity.
  - replace k with (Z.succ (k - 1)) by lia.
    destruct He as [-> | ->], Hf as [-> | ->]; rewrite ?Z.add_0_r, ?Z.mul_0_r, ?Z.mul_1_r,
      ?Z.add_0_r;
      rewrite ?Z.testbit_even_succ, ?Z.testbit_odd_succ, ?Z.land_spec by lia; reflexivity.
Qed.

Definition lowZ (j : Z) : Z := j - Z.land j (j - 1).

Lemma land_pow : forall c w, 0 <= c -> 0 <= w ->
  Z.land (2 ^ c * (2 * w + 1)) (2 ^ c * (2 * w + 1) - 1) = 2 ^ c * (2 * w + 1) - 2 ^ c.
Proof.
  intros c w Hc Hw. pattern c. apply natlike_ind; [| | exact Hc].
  - change (2 ^ 0) with 1. rewrite !Z.mul_1_l.
    replace (2 * w + 1 - 1) with (2 * w + 0) by lia.
    rewrite land2 by lia. rewrite Z.land_diag. lia.
  - intros x Hx IH. rewrite Z.pow_succ_r by lia.
    set (X := 2 ^ x * (2 * w + 1)) in *.
    replace (2 * 2 ^ x * (2 * w + 1)) with (2 * X + 0) by (unfold X; lia).
    replace (2 * X + 0 - 1) with (2 * (X - 1) + 1) by lia.
    rewrite land2 by lia. rewrite IH. lia.
Qed.

Lemma lowZ_pow : forall c w, 0 <= c -> 0 <= w -> lowZ (2 ^ c * (2 * w + 1)) = 2 ^ c.
Proof. intros c w Hc Hw. unfold lowZ. rewrite land_pow by lia. lia. Qed.

Lemma decomp : forall j, 1 <= j -> exists c w, 0 <= c /\ 0 <= w /\ j = 2 ^ c * (2 * w + 1).
Proof.
  assert (H : forall k : nat, forall j, 1 <= j <= Z.of_nat k ->
            exists c w, 0 <= c /\ 0 <= w /\ j = 2 ^ c * (2 * w + 1)).
  { induction k as [|k IH]; intros j Hj; [lia|].
    destruct (Z.eq_dec (j mod 2) 1) as [E | E].
    - exists 0, (j / 2). change (2 ^ 0) with 1. split; [lia|]. split; [|].
      + apply Z.div_pos; lia.
      + pose proof (Z.div_mod j 2 ltac:(lia)). lia.
    - assert (Hm : j mod 2 = 0) by (pose proof (Z.mod_pos_bound j 2); lia).
      pose proof (Z.div_mod j 2 ltac:(lia)) as Hd.
      destruct (IH (j / 2) ltac:(lia)) as (c & w & Hc & Hw & Hj').
      exists (c + 1), w. split; [lia|]. split; [lia|].
      rewrite Z.pow_add_r by lia. lia. }
  intros j Hj. apply (H (Z.to_nat j)). lia.
Qed.

Lemma low_pos : forall j, 1 <= j -> 1 <= lowZ j <= j.
Proof.
  intros j Hj. destruct (decomp j Hj) as (c & w & Hc & Hw & ->).
  rewrite lowZ_pow by lia. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) Hc). nia.
Qed.

Lemma low_up : forall j, 1 <= j -> j + lowZ j - lowZ (j + lowZ j) <= j - lowZ j.
Proof.
  intros j Hj. destruct (decomp j Hj) as (c & w & Hc & Hw & ->).
  rewrite lowZ_pow by lia.
  destruct (decomp (w + 1) ltac:(lia)) as (b & v & Hb & Hv & Hwv).
  assert (E : 2 ^ c * (2 * w + 1) + 2 ^ c = 2 ^ (c + 1 + b) * (2 * v + 1)).
  { rewrite !Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite <- Z.mul_assoc, <- Hwv. lia. }
  rewrite E. rewrite lowZ_pow by lia.
  assert (2 ^ (c + 1) <= 2 ^ (c + 1 + b)) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.pow_add_r in H by lia. change (2 ^ 1) with 2 in H. lia.
Qed.

Lemma low_mid : forall j r, 1 <= j -> 0 < r < lowZ j -> j <= (j + r) - lowZ (j + r).
Proof.
  intros j r Hj Hr. destruct (decomp j Hj) as (c & w & Hc & Hw & ->).
  rewrite lowZ_pow in Hr by lia.
  destruct (decomp r ltac:(lia)) as (b & v & Hb & Hv & ->).
  assert (Hbc : b < c).
  { destruct (Z.lt_ge_cases b c) as [|H]; [lia|].
    assert (2 ^ c <= 2 ^ b) by (apply Z.pow_le_mono_r; lia). nia. }
  assert (Ec : 2 ^ c = 2 ^ b * 2 * 2 ^ (c - b - 1)).
  { replace c with (b + 1 + (c - b - 1)) at 1 by lia.
    rewrite !Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
  assert (E : 2 ^ c * (2 * w + 1) + 2 ^ b * (2 * v + 1)
              = 2 ^ b * (2 * (2 ^ (c - b - 1) * (2 * w + 1) + v) + 1))
    by (rewrite Ec; ring).
  rewrite E. rewrite lowZ_pow; [| lia |].
  - rewrite <- E. nia.
  - pose proof (Z.pow_pos_nonneg 2 (c - b - 1) ltac:(lia) ltac:(lia)). nia.
Qed.

End LowBit.

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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make_small : forall (n : int) (b : int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma int_eq_dec_Z : forall i j : int, (φ i) <> (φ j) -> i <> j.
Proof. intros i j H E. apply H. rewrite E. reflexivity. Qed.

Lemma to_Z_eq : forall i j : int, (φ i) = (φ j) -> i = j.
Proof. intros i j H. apply to_Z_inj. exact H. Qed.

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
Elpi complexity andb.
Elpi complexity fst.
Elpi complexity snd.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* distance to the top of the word: decreases along any increasing walk *)
Definition mtop (j : int) : Z := (wB - (φ j))%Z.

Lemma top_dec : forall j nj : int, (j <? nj) = true -> Zwf 0 (mtop nj) (mtop j).
Proof.
  intros j nj H. rewrite ltb_spec in H. pose proof (to_Z_bounded nj).
  unfold Zwf, mtop. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Fenwick trees                                                       *)
(* ------------------------------------------------------------------ *)

(* the lowest set bit of j > 0 *)
Definition lowb (j : int) : int := j - (j land (j - 1)).
Elpi complexity lowb.
Arguments lowb_cost : simpl never.

Lemma land_low : forall j : int, (0 < (φ j))%Z ->
  (φ (j land (j - 1))) = ((φ j) - lowZ (φ j))%Z.
Proof.
  intros j Hj. rewrite land_spec'.
  assert (E : (φ (j - 1)) = ((φ j) - 1)%Z) by sia. rewrite E. unfold lowZ. lia.
Qed.

Lemma lowb_spec : forall j : int, (0 < (φ j))%Z -> (φ (lowb j)) = lowZ (φ j).
Proof.
  intros j Hj. unfold lowb. rewrite sub_spec, land_low by exact Hj.
  pose proof (low_pos (φ j) ltac:(lia)). pose proof (to_Z_bounded j).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sum_dec : forall j : int, (0 <? j) = true -> Zwf 0 (φ (j land (j - 1))) (φ j).
Proof.
  intros j H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  pose proof (land_low j H). pose proof (low_pos (φ j) ltac:(lia)).
  unfold Zwf. lia.
Qed.

(* t.[j] += delta for every j = p, p + low p, ... up to N *)
Fixpoint fen_add (t : array int) (N j delta : int)
    (H : Acc (Zwf 0) (mtop j)) {struct H} : array int :=
  match bdec ((0 <? j) && (j <=? N)) with
  | left _ =>
      let t' := t.[j <- t.[j] + delta] in
      let nj := j + lowb j in
      match bdec (j <? nj) with
      | left Hlt => fen_add t' N nj delta (Acc_inv H (top_dec j nj Hlt))
      | right _ => t'
      end
  | right _ => t
  end.
Elpi complexity fen_add.
Arguments fen_add_cost : simpl never.

Lemma fen_add_eq : forall t N j delta H,
  fen_add t N j delta H =
  match bdec ((0 <? j) && (j <=? N)) with
  | left _ =>
      let t' := t.[j <- t.[j] + delta] in
      let nj := j + lowb j in
      match bdec (j <? nj) with
      | left Hlt => fen_add t' N nj delta (Acc_inv H (top_dec j nj Hlt))
      | right _ => t'
      end
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* acc + t.[j] + t.[j - low j] + ... *)
Fixpoint fen_sum (t : array int) (j acc : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : int :=
  match bdec (0 <? j) with
  | left Hj => fen_sum t (j land (j - 1)) (acc + t.[j]) (Acc_inv H (sum_dec j Hj))
  | right _ => acc
  end.
Elpi complexity fen_sum.
Arguments fen_sum_cost : simpl never.

Lemma fen_sum_eq : forall t j acc H,
  fen_sum t j acc H =
  match bdec (0 <? j) with
  | left Hj => fen_sum t (j land (j - 1)) (acc + t.[j]) (Acc_inv H (sum_dec j Hj))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* t is the Fenwick tree, indices 1..N, of the point values D *)
Definition Fen (N : Z) (t : array int) (D : Z -> Z) : Prop :=
  (φ (PArray.length t)) = (N + 1)%Z /\
  forall j : int, (1 <= (φ j) <= N)%Z ->
    (φ (t.[j])) = (rs D ((φ j) - lowZ (φ j)) (φ j) mod wB)%Z.

Lemma fen_sum_spec : forall N t D, Fen N t D ->
  forall z (j acc : int) H, (φ j) = z -> ((φ j) <= N)%Z ->
  (φ (fen_sum t j acc H)) = (((φ acc) + rs D 0 (φ j)) mod wB)%Z.
Proof.
  intros N t D [Hlen Hc] z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j acc H Hz HjN. rewrite fen_sum_eq.
  destruct (bdec (0 <? j)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'. change (φ 0) with 0%Z in Hj'.
    pose proof (land_low j Hj') as El. pose proof (low_pos (φ j) ltac:(lia)) as Bl.
    rewrite (IH (φ (j land (j - 1)))); [ | rewrite <- Hz; apply sum_dec; exact Hj
                                         | reflexivity | lia].
    rewrite add_spec, Hc by lia. rewrite El.
    rewrite (rs_split D 0 ((φ j) - lowZ (φ j)) (φ j)) by lia.
    rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l. f_equal. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj. change (φ 0) with 0%Z in Hj.
    pose proof (to_Z_bounded j). replace (φ j) with 0%Z by lia.
    unfold rs. simpl. rewrite Z.add_0_r. pose proof (to_Z_bounded acc).
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Definition fprop (p i : Z) : bool := andb (i - lowZ i <? p)%Z (p <=? i)%Z.

Lemma fen_add_loop : forall (Nm : int) (D : Z -> Z) (p : Z) (delta : int),
  (1 <= p <= (φ Nm))%Z -> ((φ Nm) < 2305843009213693952)%Z ->
  forall z (j : int) (t : array int) H, mtop j = z ->
  (φ (PArray.length t)) = ((φ Nm) + 1)%Z ->
  (p <= (φ j))%Z -> ((φ j) - lowZ (φ j) < p)%Z ->
  (forall i : int, (1 <= (φ i) <= (φ Nm))%Z ->
     (φ (t.[i])) = ((rs D ((φ i) - lowZ (φ i)) (φ i)
                 + if andb ((φ i) <? (φ j))%Z (fprop p (φ i)) then (φ delta) else 0) mod wB)%Z) ->
  Fen (φ Nm) (fen_add t Nm j delta H) (upd D p (φ delta)).
Proof.
  intros Nm D p delta Hp HN z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j t H Hz Hlen Hpj Hlj Hc. rewrite fen_add_eq.
  destruct (bdec ((0 <? j) && (j <=? Nm))) as [Hj | Hj].
  - assert (Hj' : (0 < (φ j))%Z /\ ((φ j) <= (φ Nm))%Z).
    { apply andb_prop in Hj. destruct Hj as [H1 H2].
      rewrite ltb_spec in H1. rewrite leb_spec in H2. change (φ 0) with 0%Z in H1. lia. }
    destruct Hj' as [Hj0 HjN].
    pose proof (lowb_spec j Hj0) as Elb. pose proof (low_pos (φ j) ltac:(lia)) as Bl.
    assert (Enj : (φ (j + lowb j)) = ((φ j) + lowZ (φ j))%Z).
    { rewrite add_spec, Elb. apply Z.mod_small. rewrite wB_val. lia. }
    cbv zeta.
    destruct (bdec (j <? j + lowb j)) as [Hlt | Hlt].
    + eapply IH; [ rewrite <- Hz; apply top_dec; exact Hlt | reflexivity | | | | ].
      * rewrite alength_set. exact Hlen.
      * lia.
      * rewrite Enj. pose proof (low_up (φ j) ltac:(lia)). lia.
      * intros i Hi. rewrite Enj.
        destruct (Z.eq_dec (φ i) (φ j)) as [E | E].
        -- apply to_Z_eq in E. subst i.
           rewrite aget_set_same by (rewrite ltb_spec, Hlen; lia).
           rewrite add_spec, Hc by lia.
           assert (Fj : fprop p (φ j) = true)
             by (unfold fprop; apply andb_true_intro; split; [apply Z.ltb_lt | apply Z.leb_le]; lia).
           assert (Lt1 : ((φ j) <? (φ j) + lowZ (φ j))%Z = true) by (apply Z.ltb_lt; lia).
           rewrite Z.ltb_irrefl, Lt1, Fj, Bool.andb_false_l. cbv iota.
           rewrite Z.add_0_r, Zplus_mod_idemp_l. reflexivity.
        -- rewrite aget_set_other by (apply int_eq_dec_Z; lia).
           rewrite Hc by lia. f_equal. f_equal.
           destruct (Z.ltb_spec (φ i) (φ j)); destruct (Z.ltb_spec (φ i) ((φ j) + lowZ (φ j)));
             try lia; try reflexivity.
           simpl andb. unfold fprop.
           pose proof (low_mid (φ j) ((φ i) - (φ j)) ltac:(lia) ltac:(lia)) as M.
           replace ((φ j) + ((φ i) - (φ j)))%Z with (φ i) in M by lia.
           destruct (Z.ltb_spec ((φ i) - lowZ (φ i)) p); [lia|]. reflexivity.
    + exfalso. rewrite <- Bool.not_true_iff_false in Hlt. apply Hlt. rewrite ltb_spec, Enj. lia.
  - assert (HjN : ((φ Nm) < (φ j))%Z).
    { rewrite <- Bool.not_true_iff_false in Hj.
      destruct (Z.ltb_spec (φ Nm) (φ j)) as [|Hle]; [lia|]. exfalso. apply Hj.
      apply andb_true_intro. split; [rewrite ltb_spec; change (φ 0) with 0%Z; lia
                                   | rewrite leb_spec; lia]. }
    split; [exact Hlen|]. intros i Hi. rewrite Hc by lia.
    pose proof (low_pos (φ i) ltac:(lia)).
    rewrite rs_upd by lia. replace ((φ i) <? (φ j))%Z with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
Qed.

Lemma fen_add_spec : forall (Nm : int) D t (p delta : int) H,
  Fen (φ Nm) t D -> (1 <= (φ p) <= (φ Nm))%Z -> ((φ Nm) < 2305843009213693952)%Z ->
  Fen (φ Nm) (fen_add t Nm p delta H) (upd D (φ p) (φ delta)).
Proof.
  intros Nm D t p delta H [Hlen Hc] Hp HN.
  eapply fen_add_loop; [lia | exact HN | reflexivity | exact Hlen | lia | | ].
  - pose proof (low_pos (φ p) ltac:(lia)). lia.
  - intros i Hi. destruct (Z.ltb_spec (φ i) (φ p)) as [Hl | Hl].
    + unfold fprop. replace ((φ p) <=? (φ i))%Z with false by (symmetry; apply Z.leb_gt; lia).
      rewrite Bool.andb_false_r. simpl andb. cbv iota. rewrite Z.add_0_r. apply Hc. exact Hi.
    + simpl andb. cbv iota. rewrite Z.add_0_r. apply Hc. exact Hi.
Qed.

Lemma fen_init : forall Nm : int, ((φ Nm) + 1 <= 4194303)%Z ->
  Fen (φ Nm) (PArray.make (Nm + 1) 0) (fun _ => 0%Z).
Proof.
  intros Nm HN. assert (E : (φ (Nm + 1)) = ((φ Nm) + 1)%Z) by sia.
  split.
  - rewrite alength_make_small by lia. exact E.
  - intros j Hj. rewrite aget_make. unfold rs. rewrite sumz_const0. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Manacher, on the doubled centres q = a + b of the factors s_a..s_b  *)
(* ------------------------------------------------------------------ *)

(* Centre q (0 <= q < 2n) has the candidates [q/2 - k, (q+1)/2 + k],
   k = 0, 1, ...; cnt.[q] is the number of them that are palindromes. *)

Definition imin (a b : int) : int := if a <? b then a else b.
Elpi complexity imin.
Arguments imin_cost : simpl never.

Definition hcond (x : PrimString.string) (n q k : int) : bool :=
  (k <=? (q >> 1)) && (((q + 1) >> 1) + k <? n)
  && (PrimString.get x ((q >> 1) - k) =? PrimString.get x (((q + 1) >> 1) + k)).
Elpi complexity hcond.
Arguments hcond_cost : simpl never.

Fixpoint expand (x : PrimString.string) (n q k : int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : int :=
  match bdec (k <? n) with
  | left Hk => if hcond x n q k then expand x n q (k + 1) (Acc_inv H (dec_step n k Hk)) else k
  | right _ => k
  end.
Elpi complexity expand.
Arguments expand_cost : simpl never.

Lemma expand_eq : forall x n q k H,
  expand x n q k H =
  match bdec (k <? n) with
  | left Hk => if hcond x n q k then expand x n q (k + 1) (Acc_inv H (dec_step n k Hk)) else k
  | right _ => k
  end.
Proof. intros. destruct H. reflexivity. Qed.

Fixpoint man (x : PrimString.string) (n n2 : int) (cnt : array int) (q Q rb : int)
    (H : Acc (Zwf 0) (gap n2 q)) {struct H} : array int :=
  match bdec (q <? n2) with
  | left Hq =>
      let bq := (q + 1) >> 1 in
      let k0 := if bq <? rb then imin cnt.[Q + Q - q] (rb - bq) else 0 in
      let c := expand x n q k0 (Zwf_well_founded 0 (gap n k0)) in
      if rb <? bq + c
      then man x n n2 cnt.[q <- c] (q + 1) q (bq + c) (Acc_inv H (dec_step n2 q Hq))
      else man x n n2 cnt.[q <- c] (q + 1) Q rb (Acc_inv H (dec_step n2 q Hq))
  | right _ => cnt
  end.
Elpi complexity man.
Arguments man_cost : simpl never.

Lemma man_eq : forall x n n2 cnt q Q rb H,
  man x n n2 cnt q Q rb H =
  match bdec (q <? n2) with
  | left Hq =>
      let bq := (q + 1) >> 1 in
      let k0 := if bq <? rb then imin cnt.[Q + Q - q] (rb - bq) else 0 in
      let c := expand x n q k0 (Zwf_well_founded 0 (gap n k0)) in
      if rb <? bq + c
      then man x n n2 cnt.[q <- c] (q + 1) q (bq + c) (Acc_inv H (dec_step n2 q Hq))
      else man x n n2 cnt.[q <- c] (q + 1) Q rb (Acc_inv H (dec_step n2 q Hq))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition manacher (x : PrimString.string) : array int :=
  let n := PrimString.length x in
  man x n (n + n) (PArray.make (n + n) 0) 0 0 0 (Zwf_well_founded 0 (gap (n + n) 0)).
Elpi complexity manacher.
Arguments manacher_cost : simpl never.

(* Prop side *)

Definition ch (x : PrimString.string) (z : Z) : Z := (φ (PrimString.get x (of_Z z))).

Section ManacherProof.
Local Open Scope Z_scope.
Variable x : PrimString.string.
Variable n : Z.

(* candidate k of centre q is a palindrome inside [0, n) *)
Definition Pk (q k : Z) : Prop :=
  0 <= k /\ k <= q / 2 /\ (q + 1) / 2 + k < n /\
  forall j, 0 <= j <= k -> ch x (q / 2 - j) = ch x ((q + 1) / 2 + j).

Lemma Pk_down : forall q k j, Pk q k -> 0 <= j <= k -> Pk q j.
Proof.
  intros q k j (H0 & H1 & H2 & H3) Hj.
  refine (conj _ (conj _ (conj _ _))); [lia | lia | lia |].
  intros i Hi. apply H3. lia.
Qed.

(* s is symmetric about Q on [Q + 1 - rb, rb - 1] *)
Definition Sym (Q rb : Z) : Prop :=
  forall t, Q + 1 - rb <= t <= rb - 1 -> ch x t = ch x (Q - t).

Lemma mirror : forall Q rb q j,
  Sym Q rb -> rb <= Q + 1 -> rb <= n -> Q < q -> 0 <= j -> (q + 1) / 2 + j < rb ->
  Pk (2 * Q - q) j -> Pk q j.
Proof.
  intros Q rb q j HS Hrb Hrn HQq Hj Hjr (_ & Hb1 & Hb2 & Heq).
  assert (E1 : (2 * Q - q) / 2 = Q - (q + 1) / 2) by (Z.to_euclidean_division_equations; lia).
  assert (E2 : (2 * Q - q + 1) / 2 = Q - q / 2) by (Z.to_euclidean_division_equations; lia).
  assert (E3 : q / 2 + (q + 1) / 2 = q) by (Z.to_euclidean_division_equations; lia).
  rewrite E1, E2 in *.
  refine (conj _ (conj _ (conj _ _))); [lia | lia | lia |].
  intros i Hi.
  rewrite (HS (q / 2 - i)) by lia.
  rewrite (HS ((q + 1) / 2 + i)) by lia.
  replace (Q - (q / 2 - i)) with (Q - q / 2 + i) by lia.
  replace (Q - ((q + 1) / 2 + i)) with (Q - (q + 1) / 2 - i) by lia.
  symmetry. apply Heq. lia.
Qed.

Lemma cnt_bound : forall q c, 0 <= q < 2 * n -> 0 <= c ->
  (forall j, 0 <= j -> (Pk q j <-> j < c)) ->
  c <= q / 2 + 1 /\ (q + 1) / 2 + c <= n.
Proof.
  intros q c Hq Hc H.
  destruct (Z.eq_dec c 0) as [-> | Hc0].
  - split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia.
  - destruct (proj2 (H (c - 1) ltac:(lia)) ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Lemma sym_new : forall q c, 0 <= c ->
  (forall j, 0 <= j -> (Pk q j <-> j < c)) -> Sym q ((q + 1) / 2 + c).
Proof.
  intros q c Hc H t Ht.
  assert (E3 : q / 2 + (q + 1) / 2 = q) by (Z.to_euclidean_division_equations; lia).
  assert (E4 : (q + 1) / 2 <= q / 2 + 1) by (Z.to_euclidean_division_equations; lia).
  assert (E5 : q / 2 <= (q + 1) / 2) by (Z.to_euclidean_division_equations; lia).
  destruct (proj2 (H (c - 1) ltac:(lia)) ltac:(lia)) as (_ & _ & _ & Heq).
  destruct (Z.le_gt_cases t (q / 2)) as [Ht1 | Ht1].
  - pose proof (Heq (q / 2 - t) ltac:(lia)) as E.
    replace (q / 2 - (q / 2 - t)) with t in E by lia.
    rewrite E. f_equal. lia.
  - pose proof (Heq (t - (q + 1) / 2) ltac:(lia)) as E.
    replace ((q + 1) / 2 + (t - (q + 1) / 2)) with t in E by lia.
    rewrite <- E. f_equal. lia.
Qed.

End ManacherProof.

Lemma ch_phi : forall x (i : int), ch x (φ i) = (φ (PrimString.get x i)).
Proof. intros x i. unfold ch. rewrite of_to_Z. reflexivity. Qed.

Lemma lsr1 : forall q : int, (φ (q >> 1)) = ((φ q) / 2)%Z.
Proof. intros q. rewrite lsr_spec. change (φ 1) with 1%Z. rewrite Z.pow_1_r. reflexivity. Qed.

Lemma half_facts : forall q : Z, (0 <= q)%Z ->
  (0 <= q / 2 /\ 2 * (q / 2) <= q <= 2 * (q / 2) + 1 /\ (q + 1) / 2 = q - q / 2)%Z.
Proof. intros q Hq. Z.to_euclidean_division_equations; lia. Qed.

Lemma Pk_step : forall x n q k, (0 <= k)%Z ->
  (forall j, (0 <= j < k)%Z -> Pk x n q j) ->
  (Pk x n q k <-> (k <= q / 2 /\ (q + 1) / 2 + k < n
                   /\ ch x (q / 2 - k) = ch x ((q + 1) / 2 + k))%Z).
Proof.
  intros x n q k Hk Hpre. split.
  - intros (H0 & H1 & H2 & H3). refine (conj H1 (conj H2 _)). apply H3. lia.
  - intros (H1 & H2 & H3). refine (conj Hk (conj H1 (conj H2 _))).
    intros j Hj. destruct (Z.eq_dec j k) as [-> | Hjk]; [exact H3|].
    destruct (Hpre j ltac:(lia)) as (_ & _ & _ & H4). apply H4. lia.
Qed.

Lemma hcond_iff : forall x (n q k : int),
  ((φ n) <= 1152921504606846976)%Z -> ((φ q) <= 2305843009213693952)%Z ->
  (hcond x n q k = true <->
   ((φ k) <= (φ q) / 2 /\ ((φ q) + 1) / 2 + (φ k) < (φ n)
    /\ ch x ((φ q) / 2 - (φ k)) = ch x (((φ q) + 1) / 2 + (φ k)))%Z).
Proof.
  intros x n q k Hn Hq. pose proof (to_Z_bounded k). pose proof (to_Z_bounded q).
  pose proof (half_facts (φ q) ltac:(lia)) as Hh.
  assert (Eb : (φ ((q + 1) >> 1)) = (((φ q) + 1) / 2)%Z).
  { rewrite lsr1. f_equal. rewrite add_spec. apply Z.mod_small. change (φ 1) with 1%Z.
    rewrite wB_val. lia. }
  unfold hcond. rewrite !Bool.andb_true_iff, leb_spec, ltb_spec, eqb_spec, lsr1.
  split.
  - intros [[H1 H2] H3].
    assert (Ea : (φ ((q >> 1) - k)) = ((φ q) / 2 - (φ k))%Z).
    { rewrite sub_spec, lsr1. apply Z.mod_small. lia. }
    assert (Ec : (φ (((q + 1) >> 1) + k)) = (((φ q) + 1) / 2 + (φ k))%Z).
    { rewrite add_spec, Eb. apply Z.mod_small. rewrite wB_val. lia. }
    rewrite Ec in H2. refine (conj H1 (conj H2 _)).
    rewrite <- Ea, <- Ec, !ch_phi, H3. reflexivity.
  - intros (H1 & H2 & H3).
    assert (Ea : (φ ((q >> 1) - k)) = ((φ q) / 2 - (φ k))%Z).
    { rewrite sub_spec, lsr1. apply Z.mod_small. lia. }
    assert (Ec : (φ (((q + 1) >> 1) + k)) = (((φ q) + 1) / 2 + (φ k))%Z).
    { rewrite add_spec, Eb. apply Z.mod_small. rewrite wB_val. lia. }
    split; [split; [exact H1 | rewrite Ec; exact H2] |].
    apply to_Z_inj. rewrite <- Ea, <- Ec, !ch_phi in H3. exact H3.
Qed.

Lemma expand_spec : forall x (n q : int),
  ((φ n) <= 1152921504606846976)%Z -> ((φ q) <= 2305843009213693952)%Z ->
  forall z (k : int) H, gap n k = z ->
  (forall j, (0 <= j < (φ k))%Z -> Pk x (φ n) (φ q) j) ->
  forall j, (0 <= j)%Z -> (Pk x (φ n) (φ q) j <-> (j < (φ (expand x n q k H)))%Z).
Proof.
  intros x n q Hn Hq z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k H Hz Hpre. rewrite expand_eq.
  pose proof (to_Z_bounded k) as Bk.
  destruct (bdec (k <? n)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Ek : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    destruct (hcond x n q k) eqn:Hc.
    + apply (IH (gap n (k + 1))); [rewrite <- Hz; apply dec_step; exact Hk | reflexivity |].
      intros j Hj. rewrite Ek in Hj. destruct (Z.eq_dec j (φ k)) as [-> | Hjk].
      * apply (Pk_step x (φ n) (φ q) (φ k) ltac:(lia) (fun j Hj => Hpre j Hj)).
        apply hcond_iff; assumption.
      * apply Hpre. lia.
    + intros j Hj. split.
      * intros HP. destruct (Z.lt_ge_cases j (φ k)) as [|Hge]; [assumption|].
        exfalso. assert (HPk : Pk x (φ n) (φ q) (φ k)) by (apply (Pk_down x (φ n) (φ q) j); [exact HP | lia]).
        rewrite (Pk_step x (φ n) (φ q) (φ k) ltac:(lia) (fun j Hj => Hpre j Hj)) in HPk.
        rewrite <- hcond_iff in HPk by assumption. congruence.
      * intros Hj'. apply Hpre. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    intros j Hj. split.
    + intros (_ & _ & H2 & _). pose proof (half_facts (φ q) ltac:(pose proof (to_Z_bounded q); lia)). lia.
    + intros Hj'. apply Hpre. lia.
Qed.

Lemma imin_spec : forall a b : int, (φ (imin a b)) = Z.min (φ a) (φ b).
Proof.
  intros a b. unfold imin. destruct (a <? b) eqn:E;
    [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E]; lia.
Qed.

Lemma man_loop : forall x (nm n2 : int),
  ((φ nm) <= 33554432)%Z -> (φ n2) = (2 * (φ nm))%Z ->
  forall z (q : int) cnt Q rb H, gap n2 q = z -> ((φ q) <= (φ n2))%Z ->
  (φ (PArray.length cnt)) = (2 * (φ nm))%Z ->
  (forall q' : int, ((φ q') < (φ q))%Z -> forall j, (0 <= j)%Z ->
     (Pk x (φ nm) (φ q') j <-> (j < (φ (cnt.[q'])))%Z)) ->
  Sym x (φ Q) (φ rb) -> ((φ rb) <= (φ Q) + 1)%Z -> ((φ rb) <= (φ nm))%Z -> ((φ Q) <= (φ n2))%Z ->
  ((φ rb) <= ((φ q) + 1) / 2 \/ (φ Q) < (φ q))%Z ->
  (φ (PArray.length (man x nm n2 cnt q Q rb H))) = (2 * (φ nm))%Z /\
  (forall q' : int, ((φ q') < (φ n2))%Z -> forall j, (0 <= j)%Z ->
     (Pk x (φ nm) (φ q') j <-> (j < (φ ((man x nm n2 cnt q Q rb H).[q'])))%Z)).
Proof.
  intros x nm n2 Hnm Hn2 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q cnt Q rb H Hz Hqn Hlen Hinv HS Hrb1 Hrb2 HQ Hdisj.
  rewrite man_eq.
  pose proof (to_Z_bounded q) as Bq. pose proof (to_Z_bounded Q) as BQ.
  pose proof (to_Z_bounded rb) as Brb.
  destruct (bdec (q <? n2)) as [Hq | Hq].
  - pose proof Hq as Hq'. rewrite ltb_spec in Hq'.
    pose proof (half_facts (φ q) ltac:(lia)) as Hh.
    assert (Eq1 : (φ (q + 1)) = ((φ q) + 1)%Z) by sia.
    assert (Eb : (φ ((q + 1) >> 1)) = (((φ q) + 1) / 2)%Z) by (rewrite lsr1, Eq1; reflexivity).
    cbv zeta.
    set (k0 := if (q + 1) >> 1 <? rb then imin cnt.[Q + Q - q] (rb - ((q + 1) >> 1)) else 0).
    assert (Hk0 : forall j, (0 <= j < (φ k0))%Z -> Pk x (φ nm) (φ q) j).
    { unfold k0. destruct ((q + 1) >> 1 <? rb) eqn:Ebr.
      - rewrite ltb_spec, Eb in Ebr.
        assert (HQq : ((φ Q) < (φ q))%Z) by lia.
        assert (Eq' : (φ (Q + Q - q)) = (2 * (φ Q) - (φ q))%Z) by sia.
        intros j Hj. rewrite imin_spec in Hj.
        assert (Er : (φ (rb - ((q + 1) >> 1))) = ((φ rb) - ((φ q) + 1) / 2)%Z)
          by (rewrite sub_spec, Eb; apply Z.mod_small; lia).
        rewrite Er in Hj.
        apply (mirror x (φ nm) (φ Q) (φ rb)); try assumption; try lia.
        rewrite <- Eq'. apply (Hinv (Q + Q - q)); [rewrite Eq'; lia | lia |]. lia.
      - intros j Hj. change (φ 0) with 0%Z in Hj. lia. }
    set (c := expand x nm q k0 (Zwf_well_founded 0 (gap nm k0))).
    assert (Hc : forall j, (0 <= j)%Z -> (Pk x (φ nm) (φ q) j <-> (j < (φ c))%Z)).
    { exact (expand_spec x nm q ltac:(lia) ltac:(lia) (gap nm k0) k0 _ eq_refl Hk0). }
    pose proof (to_Z_bounded c) as Bc.
    destruct (cnt_bound x (φ nm) (φ q) (φ c) ltac:(lia) ltac:(lia) Hc) as [Bc1 Bc2].
    assert (Ee : (φ ((q + 1) >> 1 + c)) = (((φ q) + 1) / 2 + (φ c))%Z)
      by (rewrite add_spec, Eb; apply Z.mod_small; rewrite wB_val; lia).
    assert (Hinv' : forall q' : int, ((φ q') < (φ (q + 1)))%Z -> forall j, (0 <= j)%Z ->
              (Pk x (φ nm) (φ q') j <-> (j < (φ (cnt.[q <- c].[q'])))%Z)).
    { intros q' Hq'' j Hj. rewrite Eq1 in Hq''.
      destruct (Z.eq_dec (φ q') (φ q)) as [E | E].
      - apply to_Z_eq in E. subst q'.
        rewrite aget_set_same by (rewrite ltb_spec, Hlen; lia). apply Hc. exact Hj.
      - rewrite aget_set_other by (apply int_eq_dec_Z; lia). apply Hinv; [lia | exact Hj]. }
    assert (Hlen' : (φ (PArray.length cnt.[q <- c])) = (2 * (φ nm))%Z) by (rewrite alength_set; exact Hlen).
    destruct (rb <? (q + 1) >> 1 + c) eqn:Erb.
    + rewrite ltb_spec, Ee in Erb.
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hq | reflexivity | lia | exact Hlen'
                 | exact Hinv' | | | | | ].
      * rewrite Ee. apply (sym_new x (φ nm)); [lia | exact Hc].
      * rewrite Ee. lia.
      * rewrite Ee. lia.
      * lia.
      * right. rewrite Eq1. lia.
    + eapply IH; [rewrite <- Hz; apply dec_step; exact Hq | reflexivity | lia | exact Hlen'
                 | exact Hinv' | exact HS | exact Hrb1 | exact Hrb2 | exact HQ | ].
      rewrite Eq1. pose proof (half_facts ((φ q) + 1) ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hq.
    split; [exact Hlen|]. intros q' Hq' j Hj. apply Hinv; [lia | exact Hj].
Qed.

Lemma manacher_spec : forall x,
  (2 * (φ (PrimString.length x)) <= 4194303)%Z ->
  (φ (PArray.length (manacher x))) = (2 * (φ (PrimString.length x)))%Z /\
  (forall q' : int, ((φ q') < 2 * (φ (PrimString.length x)))%Z -> forall j, (0 <= j)%Z ->
     (Pk x (φ (PrimString.length x)) (φ q') j <-> (j < (φ ((manacher x).[q'])))%Z)).
Proof.
  intros x Hn. unfold manacher.
  set (nm := PrimString.length x).
  assert (Hn' : (2 * (φ nm) <= 4194303)%Z) by exact Hn.
  pose proof (to_Z_bounded nm).
  assert (E2 : (φ (nm + nm)) = (2 * (φ nm))%Z) by sia.
  assert (P1 : (φ (PArray.length (PArray.make (nm + nm) 0))) = (2 * (φ nm))%Z)
    by (rewrite alength_make_small by lia; exact E2).
  assert (P2 : forall q' : int, ((φ q') < (φ 0))%Z -> forall j, (0 <= j)%Z ->
     (Pk x (φ nm) (φ q') j <-> (j < (φ ((PArray.make (nm + nm) 0%uint63).[q'])))%Z)).
  { intros q' Hq'. change (φ 0) with 0%Z in Hq'. pose proof (to_Z_bounded q'). lia. }
  assert (P3 : Sym x (φ 0) (φ 0)).
  { intros t Ht. change (φ 0) with 0%Z in Ht. lia. }
  assert (P0 : ((φ nm) <= 33554432)%Z) by lia.
  destruct (man_loop x nm (nm + nm) P0 E2 _ 0 (PArray.make (nm + nm) 0) 0 0
              (Zwf_well_founded 0 (gap (nm + nm) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) P1 P2 P3
              ltac:(change (φ 0) with 0%Z; lia) ltac:(change (φ 0) with 0%Z; lia)
              ltac:(change (φ 0) with 0%Z; lia) ltac:(left; change (φ 0) with 0%Z; lia))
    as [A B].
  split; [exact A|]. intros q' Hq'. apply B. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Tabulation                                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint tab_loop (f : int -> int) (n i : int) (a : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => tab_loop f n (i + 1) a.[i <- f i] (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.
Elpi complexity tab_loop.
Arguments tab_loop_cost : simpl never.

Lemma tab_loop_eq : forall f n i a H,
  tab_loop f n i a H =
  match bdec (i <? n) with
  | left Hi => tab_loop f n (i + 1) a.[i <- f i] (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition tab (n : int) (f : int -> int) : array int :=
  tab_loop f n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)).
Elpi complexity tab.
Arguments tab_cost : simpl never.

Lemma tab_loop_spec : forall f n z i a H, gap n i = z ->
  PArray.length a = n -> ((φ i) <= (φ n))%Z ->
  (forall j : int, ((φ j) < (φ i))%Z -> a.[j] = f j) ->
  PArray.length (tab_loop f n i a H) = n /\
  forall j : int, ((φ j) < (φ n))%Z -> (tab_loop f n i a H).[j] = f j.
Proof.
  intros f n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i a H Hz Hl Hi Ha. rewrite tab_loop_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (E : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hin | reflexivity | | | ].
    + rewrite alength_set. exact Hl.
    + lia.
    + intros j Hj. destruct (Z.eq_dec (φ j) (φ i)) as [Ej | Ej].
      * apply to_Z_eq in Ej. subst j. apply aget_set_same. rewrite Hl. exact Hin.
      * rewrite aget_set_other by (apply int_eq_dec_Z; lia). apply Ha. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact Hl|]. intros j Hj. apply Ha. lia.
Qed.

Lemma tab_spec : forall n f, ((φ n) <= 4194303)%Z ->
  PArray.length (tab n f) = n /\ forall j : int, ((φ j) < (φ n))%Z -> (tab n f).[j] = f j.
Proof.
  intros n f Hn. unfold tab. eapply tab_loop_spec; [reflexivity | | |].
  - apply alength_make_small. exact Hn.
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The offline sweep: buckets of queries, Fenwick trees over the       *)
(* left border                                                         *)
(* ------------------------------------------------------------------ *)

(* Event k (k < m) asks, at slot ts.[k], for the point value at as.[k].
   head.[t] = 1 + the last event of slot t (0: none), next.[k] = 1 + the
   previous event of the slot of k (0: none). *)
Fixpoint build (ts : array int) (m k : int) (head next : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int * array int :=
  match bdec (k <? m) with
  | left Hk =>
      let t := ts.[k] in
      let h := head.[t] in
      build ts m (k + 1) head.[t <- k + 1] next.[k <- h] (Acc_inv H (dec_step m k Hk))
  | right _ => (head, next)
  end.
Elpi complexity build.
Arguments build_cost : simpl never.

Lemma build_eq : forall ts m k head next H,
  build ts m k head next H =
  match bdec (k <? m) with
  | left Hk =>
      let t := ts.[k] in
      let h := head.[t] in
      build ts m (k + 1) head.[t <- k + 1] next.[k <- h] (Acc_inv H (dec_step m k Hk))
  | right _ => (head, next)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition fadd (t : array int) (N j delta : int) : array int :=
  fen_add t N j delta (Zwf_well_founded 0 (mtop j)).
Elpi complexity fadd.
Arguments fadd_cost : simpl never.

Definition fsum (t : array int) (j : int) : int :=
  fen_sum t j 0 (Zwf_well_founded 0 (φ j)).
Elpi complexity fsum.
Arguments fsum_cost : simpl never.

(* the point value at a of the function the two trees hold *)
Definition fval (t : array int * array int) (a : int) : int :=
  fsum (fst t) (a + 1) + a * fsum (snd t) (a + 1).
Elpi complexity fval.
Arguments fval_cost : simpl never.

Lemma lt_dec : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. pose proof (to_Z_bounded a). unfold Zwf. lia.
Qed.

Fixpoint walk (as_ next : array int) (t : array int * array int) (v : array int)
    (ptr : int) (H : Acc (Zwf 0) (φ ptr)) {struct H} : array int :=
  match bdec (0 <? ptr) with
  | left _ =>
      let k := ptr - 1 in
      let nx := next.[k] in
      let v' := v.[k <- fval t as_.[k]] in
      match bdec (nx <? ptr) with
      | left Hlt => walk as_ next t v' nx (Acc_inv H (lt_dec nx ptr Hlt))
      | right _ => v'
      end
  | right _ => v
  end.
Elpi complexity walk.
Arguments walk_cost : simpl never.

Lemma walk_eq : forall as_ next t v ptr H,
  walk as_ next t v ptr H =
  match bdec (0 <? ptr) with
  | left _ =>
      let k := ptr - 1 in
      let nx := next.[k] in
      let v' := v.[k <- fval t as_.[k]] in
      match bdec (nx <? ptr) with
      | left Hlt => walk as_ next t v' nx (Acc_inv H (lt_dec nx ptr Hlt))
      | right _ => v'
      end
  | right _ => v
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* centre i with radius di: add min(di, i+1, i-A+1)^+ at every A *)
Definition insert (NN : int) (t : array int * array int) (i di : int) : array int * array int :=
  let dd := imin di (i + 1) in
  let lft := i + 1 - dd in
  let t0 := fadd (fst t) NN 1 dd in
  let t0 := fadd t0 NN (lft + 2) lft in
  let t0 := fadd t0 NN (i + 2) (0 - (i + 1)) in
  let t1 := fadd (snd t) NN (lft + 2) (0 - 1) in
  let t1 := fadd t1 NN (i + 2) 1 in
  (t0, t1).
Elpi complexity insert.
Arguments insert_cost : simpl never.

Fixpoint sweep (d as_ head next : array int) (n n1 NN : int) (t : array int * array int)
    (v : array int) (tau : int) (H : Acc (Zwf 0) (gap n1 tau)) {struct H} : array int :=
  match bdec (tau <? n1) with
  | left Ht =>
      let v' := walk as_ next t v head.[tau] (Zwf_well_founded 0 (φ (head.[tau]))) in
      let t' := if tau <? n then insert NN t tau d.[tau] else t in
      sweep d as_ head next n n1 NN t' v' (tau + 1) (Acc_inv H (dec_step n1 tau Ht))
  | right _ => v
  end.
Elpi complexity sweep.
Arguments sweep_cost : simpl never.

Lemma sweep_eq : forall d as_ head next n n1 NN t v tau H,
  sweep d as_ head next n n1 NN t v tau H =
  match bdec (tau <? n1) with
  | left Ht =>
      let v' := walk as_ next t v head.[tau] (Zwf_well_founded 0 (φ (head.[tau]))) in
      let t' := if tau <? n then insert NN t tau d.[tau] else t in
      sweep d as_ head next n n1 NN t' v' (tau + 1) (Acc_inv H (dec_step n1 tau Ht))
  | right _ => v
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* v.[k] = sum_{i < ts.[k]} min(d.[i], i - as.[k] + 1)^+ (mod 2^63), k < m *)
Definition lsum_all (n m : int) (d as_ ts : array int) : array int :=
  let hn := build ts m 0 (PArray.make (n + 1) 0) (PArray.make m 0)
                  (Zwf_well_founded 0 (gap m 0)) in
  let NN := n + 2 in
  sweep d as_ (fst hn) (snd hn) n (n + 1) NN
        (PArray.make (NN + 1) 0, PArray.make (NN + 1) 0) (PArray.make m 0) 0
        (Zwf_well_founded 0 (gap (n + 1) 0)).
Elpi complexity lsum_all.
Arguments lsum_all_cost : simpl never.

(* Prop side of the sweep *)

Section SweepProof.
Local Open Scope Z_scope.

(* 1 + the last event e < p of slot t, 0 if none *)
Fixpoint lastbn (ts : array int) (t : Z) (p : nat) : Z :=
  match p with
  | O => 0
  | S p' => if (φ (ts.[of_Z (Z.of_nat p')])) =? t then Z.of_nat p' + 1 else lastbn ts t p'
  end.

Definition lastb (ts : array int) (t p : Z) : Z := lastbn ts t (Z.to_nat p).

Lemma lastb_step : forall ts t p, 0 <= p ->
  lastb ts t (p + 1) = if (φ (ts.[of_Z p])) =? t then p + 1 else lastb ts t p.
Proof.
  intros ts t p Hp. unfold lastb.
  replace (Z.to_nat (p + 1)) with (S (Z.to_nat p)) by lia. simpl lastbn.
  rewrite Z2Nat.id by exact Hp. reflexivity.
Qed.

Lemma lastbn_bound : forall ts t k, 0 <= lastbn ts t k <= Z.of_nat k.
Proof.
  intros ts t k. induction k as [|k IH]; simpl lastbn; [lia|].
  destruct (_ =? t); lia.
Qed.

Lemma lastb_bound : forall ts t p, 0 <= p -> 0 <= lastb ts t p <= p.
Proof. intros ts t p Hp. unfold lastb. pose proof (lastbn_bound ts t (Z.to_nat p)). lia. Qed.

Lemma lastbn_zero : forall ts t k, lastbn ts t k = 0 ->
  forall e, 0 <= e < Z.of_nat k -> (φ (ts.[of_Z e])) <> t.
Proof.
  intros ts t k. induction k as [|k IH]; simpl lastbn; intros H e He; [lia|].
  destruct ((φ (ts.[of_Z (Z.of_nat k)])) =? t) eqn:E; [lia|].
  apply Z.eqb_neq in E.
  destruct (Z.eq_dec e (Z.of_nat k)) as [-> | Hne]; [exact E|].
  apply IH; [exact H | lia].
Qed.

Lemma lastbn_pos : forall ts t k e, lastbn ts t k = e + 1 -> 0 <= e ->
  e < Z.of_nat k /\ (φ (ts.[of_Z e])) = t /\
  forall e', e < e' < Z.of_nat k -> (φ (ts.[of_Z e'])) <> t.
Proof.
  intros ts t k. induction k as [|k IH]; simpl lastbn; intros e H He; [lia|].
  destruct ((φ (ts.[of_Z (Z.of_nat k)])) =? t) eqn:E.
  - apply Z.eqb_eq in E. assert (e = Z.of_nat k) by lia. subst e.
    split; [lia|]. split; [exact E|]. intros e' He'. lia.
  - apply Z.eqb_neq in E. destruct (IH e H He) as (H1 & H2 & H3).
    split; [lia|]. split; [exact H2|]. intros e' He'.
    destruct (Z.eq_dec e' (Z.of_nat k)) as [-> | Hne]; [exact E|]. apply H3. lia.
Qed.

Lemma get_of_to_Z : forall (a : array int) (i : int), a.[of_Z (φ i)] = a.[i].
Proof. intros a i. rewrite of_to_Z. reflexivity. Qed.

Lemma build_loop : forall ts (m nn : int),
  (forall k : int, (φ k) < (φ m) -> (φ (ts.[k])) < (φ nn)) ->
  forall z (k : int) head next H, gap m k = z -> (φ k) <= (φ m) ->
  PArray.length head = nn -> PArray.length next = m ->
  (forall t : int, (φ t) < (φ nn) -> (φ (head.[t])) = lastb ts (φ t) (φ k)) ->
  (forall e : int, (φ e) < (φ k) -> (φ (next.[e])) = lastb ts (φ (ts.[e])) (φ e)) ->
  PArray.length (fst (build ts m k head next H)) = nn /\
  PArray.length (snd (build ts m k head next H)) = m /\
  (forall t : int, (φ t) < (φ nn) -> (φ ((fst (build ts m k head next H)).[t])) = lastb ts (φ t) (φ m)) /\
  (forall e : int, (φ e) < (φ m) -> (φ ((snd (build ts m k head next H)).[e])) = lastb ts (φ (ts.[e])) (φ e)).
Proof.
  intros ts m nn Hts z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k head next H Hz Hk Hlh Hln Hh Hn. rewrite build_eq.
  pose proof (to_Z_bounded k) as Bk.
  destruct (bdec (k <? m)%uint63) as [Hkm | Hkm].
  - pose proof Hkm as Hkm'. rewrite ltb_spec in Hkm'.
    assert (Ek : (φ ((k + 1)%uint63)) = (φ k) + 1) by sia.
    cbv zeta.
    pose proof (Hts k Hkm') as Htk.
    apply IH with (y := gap m (k + 1)%uint63); [rewrite <- Hz; apply dec_step; exact Hkm | reflexivity
      | lia | rewrite alength_set; exact Hlh | rewrite alength_set; exact Hln | | ].
    + intros t Ht. rewrite Ek, lastb_step by lia. rewrite get_of_to_Z.
      destruct (Z.eq_dec (φ t) (φ (ts.[k]))) as [E | E].
      * apply to_Z_eq in E. subst t.
        rewrite aget_set_same by (rewrite ltb_spec, Hlh; exact Ht).
        rewrite Z.eqb_refl. exact Ek.
      * rewrite aget_set_other by (apply int_eq_dec_Z; lia).
        replace ((φ (ts.[k])) =? (φ t)) with false by (symmetry; apply Z.eqb_neq; lia).
        apply Hh. exact Ht.
    + intros e He. rewrite Ek in He.
      destruct (Z.eq_dec (φ e) (φ k)) as [E | E].
      * apply to_Z_eq in E. subst e.
        rewrite aget_set_same by (rewrite ltb_spec, Hln; exact Hkm').
        apply Hh. exact Htk.
      * rewrite aget_set_other by (apply int_eq_dec_Z; lia). apply Hn. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkm.
    assert (Ekm : k = m) by (apply to_Z_eq; lia). subst k.
    simpl fst. simpl snd. auto.
Qed.

Lemma walk_spec : forall ts as_ next t (m : Z) (tau : Z),
  (forall e : int, (φ e) < m -> (φ (next.[e])) = lastb ts (φ (ts.[e])) (φ e)) ->
  forall p', 0 <= p' <= m -> forall v ptr H, (φ ptr) = lastb ts tau p' ->
  (φ (PArray.length v)) = m ->
  (φ (PArray.length (walk as_ next t v ptr H))) = m /\
  forall e : int, (φ e) < m ->
    (walk as_ next t v ptr H).[e]
    = if andb ((φ e) <? p') ((φ (ts.[e])) =? tau) then fval t (as_.[e]) else v.[e].
Proof.
  intros ts as_ next t m tau Hn p'.
  induction p' as [p' IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros Hp v ptr H Hptr Hlv. rewrite walk_eq.
  destruct (bdec (0 <? ptr)%uint63) as [Hp0 | Hp0].
  - rewrite ltb_spec in Hp0. change (φ 0) with 0 in Hp0.
    destruct (lastbn_pos ts tau (Z.to_nat p') ((φ ptr) - 1) ltac:(unfold lastb in Hptr; lia) ltac:(lia))
      as (P1 & P2 & P3).
    rewrite Z2Nat.id in P1, P3 by lia.
    assert (Ek : (φ ((ptr - 1)%uint63)) = (φ ptr) - 1) by sia.
    cbv zeta.
    assert (Enx : (φ (next.[(ptr - 1)%uint63])) = lastb ts tau ((φ ptr) - 1)).
    { rewrite Hn by lia. rewrite Ek. f_equal.
      rewrite <- (get_of_to_Z ts (ptr - 1)%uint63), Ek. exact P2. }
    pose proof (lastb_bound ts tau ((φ ptr) - 1) ltac:(lia)) as Bnx.
    destruct (bdec (next.[(ptr - 1)%uint63] <? ptr)%uint63) as [Hlt | Hlt].
    + destruct (IH ((φ ptr) - 1) ltac:(unfold Zwf; lia) ltac:(lia)
                  (v.[(ptr - 1)%uint63 <- fval t (as_.[(ptr - 1)%uint63])]) (next.[(ptr - 1)%uint63])
                  (Acc_inv H (lt_dec (next.[(ptr - 1)%uint63]) ptr Hlt)) Enx
                  ltac:(rewrite alength_set; exact Hlv)) as [W1 W2].
      split; [exact W1|]. intros e He. rewrite W2 by exact He.
      destruct (Z.eq_dec (φ e) ((φ ptr) - 1)) as [E | E].
      * assert (e = (ptr - 1)%uint63) by (apply to_Z_eq; lia). subst e.
        rewrite Ek, Z.ltb_irrefl. simpl andb. cbv iota.
        rewrite aget_set_same by (rewrite ltb_spec; lia).
        replace ((φ ptr) - 1 <? p') with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite <- (get_of_to_Z ts (ptr - 1)%uint63), Ek, P2, Z.eqb_refl. reflexivity.
      * rewrite aget_set_other by (apply int_eq_dec_Z; lia).
        destruct (Z.ltb_spec (φ e) ((φ ptr) - 1)); destruct (Z.ltb_spec (φ e) p'); try lia;
          simpl andb; try reflexivity.
        replace ((φ (ts.[e])) =? tau) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. rewrite <- get_of_to_Z. apply P3. lia.
    + exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hp0. change (φ 0) with 0 in Hp0.
    pose proof (to_Z_bounded ptr).
    split; [exact Hlv|]. intros e He.
    destruct (Z.ltb_spec (φ e) p'); simpl andb; [|reflexivity].
    replace ((φ (ts.[e])) =? tau) with false; [reflexivity|].
    symmetry. apply Z.eqb_neq. rewrite <- get_of_to_Z.
    apply (lastbn_zero ts tau (Z.to_nat p')); [unfold lastb in Hptr; lia | ].
    pose proof (to_Z_bounded e). lia.
Qed.

(* the value one centre adds at the left border A *)
Definition fterm (d : array int) (i A : Z) : Z :=
  Z.max 0 (Z.min (Z.min (φ (d.[of_Z i])) (i + 1)) (i - A + 1)).

Definition Vsum (d : array int) (tau A : Z) : Z :=
  sumz (fun i => fterm d i A) 0 (Z.to_nat tau).

Definition St (d : array int) (n NN tau : Z) (t : array int * array int) : Prop :=
  exists D0 D1, Fen NN (fst t) D0 /\ Fen NN (snd t) D1 /\
  forall A, 0 <= A <= n ->
    (rs D0 0 (A + 1) + A * rs D1 0 (A + 1)) mod wB = Vsum d tau A mod wB.

Lemma fval_spec : forall d n NN tau t (a : int), St d n NN tau t -> n + 1 <= NN -> n <= 1000000 ->
  (φ a) <= n -> (φ (fval t a)) = Vsum d tau (φ a) mod wB.
Proof.
  intros d n NN tau t a (D0 & D1 & F0 & F1 & HV) HN Hn Ha.
  pose proof (to_Z_bounded a) as Ba.
  assert (Ea : (φ ((a + 1)%uint63)) = (φ a) + 1) by (rewrite add_spec; apply Z.mod_small; change (φ 1) with 1; lia).
  unfold fval, fsum. rewrite add_spec, mul_spec.
  rewrite (fen_sum_spec NN (fst t) D0 F0 _ (a + 1)%uint63 0%uint63 _ eq_refl) by lia.
  rewrite (fen_sum_spec NN (snd t) D1 F1 _ (a + 1)%uint63 0%uint63 _ eq_refl) by lia.
  change (φ 0) with 0. rewrite !Z.add_0_l, Ea.
  rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  apply HV. lia.
Qed.

Lemma mod_shift : forall X Y V F w,
  X mod wB = V mod wB -> Y = X + F + wB * w -> Y mod wB = (V + F) mod wB.
Proof.
  intros X Y V F w H1 H2. subst Y.
  rewrite (Z.mul_comm wB w), Z_mod_plus_full.
  rewrite Zplus_mod, H1, <- Zplus_mod. reflexivity.
Qed.

Lemma contrib : forall dd i A lft,
  0 <= dd <= i + 1 -> lft = i + 1 - dd -> 0 <= A -> 0 <= i ->
  (if andb (0 <? 1) (1 <=? A + 1) then dd else 0)
  + (if andb (0 <? lft + 2) (lft + 2 <=? A + 1) then lft else 0)
  + (if andb (0 <? i + 2) (i + 2 <=? A + 1) then wB - (i + 1) else 0)
  + A * ((if andb (0 <? lft + 2) (lft + 2 <=? A + 1) then wB - 1 else 0)
         + (if andb (0 <? i + 2) (i + 2 <=? A + 1) then 1 else 0))
  = Z.max 0 (Z.min dd (i - A + 1))
    + wB * ((if lft + 2 <=? A + 1 then A else 0) + (if i + 2 <=? A + 1 then 1 else 0)).
Proof.
  intros dd i A lft Hd Hl HA Hi. rewrite wB_val.
  replace (0 <? 1) with true by reflexivity.
  replace (1 <=? A + 1) with true by (symmetry; apply Z.leb_le; lia).
  replace (0 <? lft + 2) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <? i + 2) with true by (symmetry; apply Z.ltb_lt; lia).
  simpl andb.
  destruct (Z.leb_spec (lft + 2) (A + 1)); destruct (Z.leb_spec (i + 2) (A + 1)); lia.
Qed.

Lemma insert_spec : forall d (n : Z) (NN : int) tau t (i : int),
  St d n (φ NN) tau t -> (φ NN) = n + 2 -> n <= 1000000 -> 0 <= (φ i) < n -> tau = (φ i) ->
  St d n (φ NN) (tau + 1) (insert NN t i (d.[i])).
Proof.
  intros d n NN tau t i (D0 & D1 & F0 & F1 & HV) HNN Hn Hi ->.
  unfold insert. cbv zeta. simpl fst. simpl snd.
  set (dd := imin (d.[i]) (i + 1)%uint63).
  assert (Ei1 : (φ ((i + 1)%uint63)) = (φ i) + 1) by sia.
  assert (Edd : (φ dd) = Z.min (φ (d.[i])) ((φ i) + 1)) by (unfold dd; rewrite imin_spec, Ei1; reflexivity).
  pose proof (to_Z_bounded (d.[i])).
  assert (Elft : (φ ((i + 1 - dd)%uint63)) = (φ i) + 1 - (φ dd)) by (rewrite sub_spec, Ei1; apply Z.mod_small; lia).
  set (lft := (i + 1 - dd)%uint63) in *.
  assert (El2 : (φ ((lft + 2)%uint63)) = (φ lft) + 2) by sia.
  assert (Ei2 : (φ ((i + 2)%uint63)) = (φ i) + 2) by sia.
  assert (Em1 : (φ ((0 - (i + 1))%uint63)) = wB - ((φ i) + 1)).
  { rewrite sub_spec, Ei1. change (φ 0) with 0.
    rewrite <- (Z_mod_plus_full _ 1 wB). rewrite Z.mod_small; rewrite wB_val; lia. }
  assert (Em2 : (φ ((0 - 1)%uint63)) = wB - 1) by reflexivity.
  assert (HN61 : (φ NN) < 2305843009213693952) by lia.
  pose proof (fen_add_spec NN D0 (fst t) 1%uint63 dd (Zwf_well_founded 0 _) F0 ltac:(change (φ 1) with 1; lia) HN61) as G1.
  pose proof (fen_add_spec NN _ _ (lft + 2)%uint63 lft (Zwf_well_founded 0 _) G1 ltac:(lia) HN61) as G2.
  pose proof (fen_add_spec NN _ _ (i + 2)%uint63 (0 - (i + 1))%uint63 (Zwf_well_founded 0 _) G2 ltac:(lia) HN61) as G3.
  pose proof (fen_add_spec NN D1 (snd t) (lft + 2)%uint63 (0 - 1)%uint63 (Zwf_well_founded 0 _) F1 ltac:(lia) HN61) as G4.
  pose proof (fen_add_spec NN _ _ (i + 2)%uint63 1%uint63 (Zwf_well_founded 0 _) G4 ltac:(lia) HN61) as G5.
  eexists. eexists. split; [exact G3|]. split; [exact G5|].
  intros A HA.
  rewrite !rs_upd by lia.
  rewrite El2, Ei2, Em1, Em2, Elft in *. change (φ 1) with 1.
  unfold Vsum. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  change (sumz (fun i0 => fterm d i0 A) 0 (S (Z.to_nat (φ i))))
    with (sumz (fun i0 => fterm d i0 A) 0 (Z.to_nat (φ i)) + fterm d (0 + Z.of_nat (Z.to_nat (φ i))) A).
  rewrite Z2Nat.id by lia. rewrite Z.add_0_l.
  apply (mod_shift (rs D0 0 (A + 1) + A * rs D1 0 (A + 1)) _ _ _
           ((if (φ i) + 1 - (φ dd) + 2 <=? A + 1 then A else 0) + (if (φ i) + 2 <=? A + 1 then 1 else 0))).
  - apply HV. exact HA.
  - unfold fterm. rewrite of_to_Z. rewrite <- Edd.
    pose proof (contrib (φ dd) (φ i) A ((φ i) + 1 - (φ dd)) ltac:(lia) eq_refl ltac:(lia) ltac:(lia)) as C.
    lia.
Qed.

End SweepProof.

Lemma sweep_loop : forall d as_ ts head next (n m : int),
  ((φ n) <= 1000000)%Z -> ((φ m) <= 4194303)%Z ->
  (forall k : int, ((φ k) < (φ m))%Z -> ((φ (ts.[k])) <= (φ n))%Z /\ ((φ (as_.[k])) <= (φ n))%Z) ->
  (forall t : int, ((φ t) <= (φ n))%Z -> (φ (head.[t])) = lastb ts (φ t) (φ m)) ->
  (forall e : int, ((φ e) < (φ m))%Z -> (φ (next.[e])) = lastb ts (φ (ts.[e])) (φ e)) ->
  forall z (tau : int) t v H, gap (n + 1) tau = z -> ((φ tau) <= (φ n) + 1)%Z ->
  (((φ tau) <= (φ n))%Z -> St d (φ n) ((φ n) + 2) (φ tau) t) ->
  (φ (PArray.length v)) = (φ m) ->
  (forall e : int, ((φ e) < (φ m))%Z -> ((φ (ts.[e])) < (φ tau))%Z ->
     (φ (v.[e])) = (Vsum d (φ (ts.[e])) (φ (as_.[e])) mod wB)%Z) ->
  (φ (PArray.length (sweep d as_ head next n (n + 1) (n + 2) t v tau H))) = (φ m) /\
  forall e : int, ((φ e) < (φ m))%Z ->
     (φ ((sweep d as_ head next n (n + 1) (n + 2) t v tau H).[e]))
     = (Vsum d (φ (ts.[e])) (φ (as_.[e])) mod wB)%Z.
Proof.
  intros d as_ ts head next n m Hn Hm Hts Hhead Hnext z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros tau t v H Hz Htau HSt Hlv Hv. rewrite sweep_eq.
  assert (E1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  assert (E2 : (φ (n + 2)) = ((φ n) + 2)%Z) by sia.
  pose proof (to_Z_bounded tau) as Bt.
  destruct (bdec (tau <? n + 1)) as [Ht | Ht].
  - pose proof Ht as Ht'. rewrite ltb_spec, E1 in Ht'.
    cbv zeta.
    pose proof (to_Z_bounded m) as Bm.
    destruct (walk_spec ts as_ next t (φ m) (φ tau) Hnext (φ m) ltac:(lia) v (head.[tau])
                (Zwf_well_founded 0 _) (Hhead tau ltac:(lia)) Hlv) as [W1 W2].
    assert (Ett : (φ (tau + 1)) = ((φ tau) + 1)%Z) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Ht | reflexivity | lia | | exact W1 | ].
    + intros Hle. rewrite Ett in Hle |- *.
      destruct (tau <? n) eqn:E.
      * rewrite ltb_spec in E.
        pose proof (insert_spec d (φ n) (n + 2) (φ tau) t tau
                      ltac:(rewrite E2; apply HSt; lia) E2 Hn ltac:(lia) eq_refl) as I.
        rewrite E2 in I. exact I.
      * rewrite <- Bool.not_true_iff_false, ltb_spec in E. lia.
    + intros e He Hte. rewrite Ett in Hte. rewrite W2 by exact He.
      replace ((φ e) <? (φ m))%Z with true by (symmetry; apply Z.ltb_lt; exact He).
      simpl andb.
      destruct (Z.eqb_spec (φ (ts.[e])) (φ tau)) as [E | E].
      * rewrite E. apply (fval_spec d (φ n) ((φ n) + 2)); [apply HSt; lia | lia | lia |].
        apply Hts. exact He.
      * apply Hv; [exact He | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec, E1 in Ht.
    split; [exact Hlv|]. intros e He. apply Hv; [exact He|].
    destruct (Hts e He). lia.
Qed.

Lemma lsum_all_spec : forall (n m : int) d as_ ts,
  ((φ n) <= 1000000)%Z -> ((φ m) <= 4194303)%Z ->
  (forall k : int, ((φ k) < (φ m))%Z -> ((φ (ts.[k])) <= (φ n))%Z /\ ((φ (as_.[k])) <= (φ n))%Z) ->
  (φ (PArray.length (lsum_all n m d as_ ts))) = (φ m) /\
  forall e : int, ((φ e) < (φ m))%Z ->
    (φ ((lsum_all n m d as_ ts).[e])) = (Vsum d (φ (ts.[e])) (φ (as_.[e])) mod wB)%Z.
Proof.
  intros n m d as_ ts Hn Hm Hts. unfold lsum_all. cbv zeta.
  assert (E1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  assert (E2 : (φ (n + 2)) = ((φ n) + 2)%Z) by sia.
  destruct (build_loop ts m (n + 1)
              ltac:(intros k Hk; destruct (Hts k Hk); lia)
              _ 0 (PArray.make (n + 1) 0) (PArray.make m 0)
              (Zwf_well_founded 0 (gap m 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded m); lia)
              ltac:(apply alength_make_small; lia)
              ltac:(apply alength_make_small; lia)
              ltac:(intros t Ht; rewrite aget_make; reflexivity)
              ltac:(intros e He; change (φ 0) with 0%Z in He; pose proof (to_Z_bounded e); lia))
    as (B1 & B2 & B3 & B4).
  apply (sweep_loop d as_ ts _ _ n m Hn Hm Hts) with (z := gap (n + 1) 0).
  - intros t Ht. apply B3. lia.
  - exact B4.
  - reflexivity.
  - change (φ 0) with 0%Z. lia.
  - intros _. exists (fun _ => 0%Z), (fun _ => 0%Z).
    pose proof (fen_init (n + 2) ltac:(lia)) as F. rewrite E2 in F.
    split; [exact F|]. split; [exact F|].
    intros A HA. unfold rs. rewrite !sumz_const0. change (φ 0) with 0%Z.
    unfold Vsum. simpl. rewrite Z.mul_0_r. reflexivity.
  - rewrite alength_make_small by lia. reflexivity.
  - intros e He Hte. change (φ 0) with 0%Z in Hte. pose proof (to_Z_bounded (ts.[e])). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Palindromes of the math string                                      *)
(* ------------------------------------------------------------------ *)

Lemma get_sola : forall l t,
  String.get t (String.string_of_list_ascii l) = nth_error l t.
Proof.
  intros l. induction l as [|c l IH]; intros t; destruct t; simpl; auto.
Qed.

Lemma length_sola : forall l,
  String.length (String.string_of_list_ascii l) = List.length l.
Proof. intros l. induction l; simpl; auto. Qed.

Lemma nth_lsoa : forall w t,
  nth_error (String.list_ascii_of_string w) t = String.get t w.
Proof.
  intros w. induction w as [|c w IH]; intros t; destruct t; simpl; auto.
Qed.

Lemma length_lsoa : forall w,
  List.length (String.list_ascii_of_string w) = String.length w.
Proof. intros w. induction w; simpl; auto. Qed.

Lemma length_substring : forall s a len, (a + len <= String.length s)%nat ->
  String.length (String.substring a len s) = len.
Proof.
  intros s. induction s as [|c s IH]; intros a len H.
  - simpl in H. destruct a, len; simpl; auto; lia.
  - destruct a as [|a].
    + destruct len as [|len]; simpl; auto. simpl in H. rewrite IH; [reflexivity | lia].
    + simpl. simpl in H. apply IH. lia.
Qed.

Lemma get_reverse : forall w t,
  String.get t (reverse w)
  = if (t <? String.length w)%nat then String.get (String.length w - S t) w else None.
Proof.
  intros w t. unfold reverse. rewrite get_sola, nth_error_rev, length_lsoa, nth_lsoa.
  reflexivity.
Qed.

Lemma pal_substring : forall s a len, (a + len <= String.length s)%nat ->
  (String.eqb (String.substring a len s) (reverse (String.substring a len s)) = true <->
   forall t, (t < len)%nat -> String.get (a + t) s = String.get (a + len - 1 - t) s).
Proof.
  intros s a len H.
  set (w := String.substring a len s).
  assert (Hw : String.length w = len) by (apply length_substring; exact H).
  assert (Gw : forall t, String.get t w = if (t <? len)%nat then String.get (t + a) s else None).
  { intros t. unfold w. destruct (Nat.ltb_spec t len).
    - apply String.substring_correct1. exact H0.
    - apply String.substring_correct2. exact H0. }
  rewrite String.eqb_eq, <- String.get_correct. split.
  - intros E t Ht. specialize (E t). rewrite get_reverse, Hw, !Gw in E.
    destruct (Nat.ltb_spec t len); [|lia].
    destruct (Nat.ltb_spec (len - S t) len); [|lia].
    replace (a + t)%nat with (t + a)%nat by lia. rewrite E. f_equal. lia.
  - intros E t. rewrite get_reverse, Hw, !Gw.
    destruct (Nat.ltb_spec t len); [|reflexivity].
    destruct (Nat.ltb_spec (len - S t) len); [|lia].
    rewrite Nat.add_comm, E by exact H0. f_equal. lia.
Qed.

Section PalProof.
Local Open Scope Z_scope.
Variable s : String.string.
Variable x : PrimString.string.
Hypothesis Hx : repr x s.

Definition nlen : Z := Z.of_nat (String.length s).

Lemma ch_get : forall z, 0 <= z < nlen ->
  exists c, String.get (Z.to_nat z) s = Some c /\ ch x z = Z.of_N (Ascii.N_of_ascii c).
Proof.
  intros z Hz. destruct Hx as [_ Hc]. unfold nlen in Hz.
  destruct (Hc (Z.to_nat z) ltac:(lia)) as (c & Hg & Hr).
  exists c. split; [exact Hg|].
  unfold repr, repr_uint in Hr. unfold ch. rewrite Z2Nat.id in Hr by lia.
  rewrite <- Hr. pose proof (to_Z_bounded (PrimString.get x (of_Z z))). lia.
Qed.

Lemma ch_eq_iff : forall a b, 0 <= a < nlen -> 0 <= b < nlen ->
  (ch x a = ch x b <-> String.get (Z.to_nat a) s = String.get (Z.to_nat b) s).
Proof.
  intros a b Ha Hb.
  destruct (ch_get a Ha) as (ca & Ga & Ca). destruct (ch_get b Hb) as (cb & Gb & Cb).
  rewrite Ga, Gb, Ca, Cb. split.
  - intros E. f_equal. rewrite <- (Ascii.ascii_N_embedding ca), <- (Ascii.ascii_N_embedding cb).
    f_equal. lia.
  - intros E. injection E as ->. reflexivity.
Qed.

Definition PalZ (a b : Z) : Prop := forall t, 0 <= t <= b - a -> ch x (a + t) = ch x (b - t).

Lemma palZ_iff : forall a b, 0 <= a <= b -> b < nlen ->
  (palindrome (Prelude.sub s (Z.to_N (a + 1)) (Z.to_N (b + 1))) = true <-> PalZ a b).
Proof.
  intros a b Hab Hb. unfold palindrome, Prelude.sub.
  replace (N.to_nat (Z.to_N (a + 1) - 1)) with (Z.to_nat a) by lia.
  replace (N.to_nat (Z.to_N (b + 1) - Z.to_N (a + 1) + 1)) with (Z.to_nat (b - a + 1)) by lia.
  rewrite pal_substring by (unfold nlen in Hb; lia).
  split.
  - intros H t Ht. apply ch_eq_iff; [lia | lia |].
    replace (Z.to_nat (a + t)) with (Z.to_nat a + Z.to_nat t)%nat by lia.
    rewrite (H (Z.to_nat t) ltac:(lia)). f_equal. lia.
  - intros H t Ht.
    pose proof (proj1 (ch_eq_iff (a + Z.of_nat t) (b - Z.of_nat t) ltac:(lia) ltac:(lia))
                  (H (Z.of_nat t) ltac:(lia))) as E.
    replace (Z.to_nat (a + Z.of_nat t)) with (Z.to_nat a + t)%nat in E by lia.
    rewrite E. f_equal. lia.
Qed.

Lemma Pk_pal : forall q k, 0 <= q -> 0 <= k ->
  (Pk x nlen q k <-> (0 <= q / 2 - k /\ (q + 1) / 2 + k < nlen /\ PalZ (q / 2 - k) ((q + 1) / 2 + k))).
Proof.
  intros q k Hq Hk. pose proof (half_facts q Hq) as (H1 & H2 & H3).
  set (h := q / 2) in *. set (h' := (q + 1) / 2) in *.
  split.
  - intros (_ & P1 & P2 & P3). change ((q + 1) / 2) with h' in P1, P2, P3. change (q / 2) with h in P1, P2, P3. split; [lia|]. split; [exact P2|].
    intros t Ht. destruct (Z.le_gt_cases t k) as [Htk | Htk].
    + specialize (P3 (k - t) ltac:(lia)).
      replace (h - (k - t)) with (h - k + t) in P3 by lia.
      replace (h' + (k - t)) with (h' + k - t) in P3 by lia. exact P3.
    + specialize (P3 (t + h - h' - k) ltac:(lia)).
      replace (h - (t + h - h' - k)) with (h' + k - t) in P3 by lia.
      replace (h' + (t + h - h' - k)) with (h - k + t) in P3 by lia.
      symmetry. exact P3.
  - intros (P1 & P2 & P3). unfold Pk. change ((q + 1) / 2) with h'. change (q / 2) with h. split; [exact Hk|]. split; [lia|]. split; [exact P2|].
    intros j Hj. specialize (P3 (k - j) ltac:(lia)).
    replace (h - k + (k - j)) with (h - j) in P3 by lia.
    replace (h' + k - (k - j)) with (h' + j) in P3 by lia. exact P3.
Qed.

End PalProof.

(* ------------------------------------------------------------------ *)
(* palindromic_count as a sum over the doubled centres                 *)
(* ------------------------------------------------------------------ *)

Definition natsum {A} (h : A -> nat) (xs : list A) : nat :=
  fold_right (fun a acc => (h a + acc)%nat) 0%nat xs.

Lemma natsum_app : forall A (h : A -> nat) xs ys,
  natsum h (xs ++ ys) = (natsum h xs + natsum h ys)%nat.
Proof. intros A h xs ys. induction xs as [|a xs IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma natsum_ext : forall A (h g : A -> nat) xs,
  (forall a, In a xs -> h a = g a) -> natsum h xs = natsum g xs.
Proof.
  intros A h g xs. induction xs as [|a xs IH]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros b Hb; apply H; right; exact Hb).
  reflexivity.
Qed.

Lemma natsum_add : forall A (h g : A -> nat) xs,
  natsum (fun a => h a + g a)%nat xs = (natsum h xs + natsum g xs)%nat.
Proof. intros A h g xs. induction xs as [|a xs IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma length_filter_flat_map : forall A B (f : B -> bool) (g : A -> list B) xs,
  List.length (filter f (flat_map g xs)) = natsum (fun a => List.length (filter f (g a))) xs.
Proof.
  intros A B f g xs. induction xs as [|a xs IH]; simpl; [reflexivity|].
  rewrite filter_app, length_app, IH. reflexivity.
Qed.

Lemma range_S : forall a b, (a <= b + 1)%N -> range a (b + 1) = range a b ++ [(b + 1)%N].
Proof.
  intros a b H. unfold range.
  replace (N.to_nat (b + 1 + 1 - a)) with (S (N.to_nat (b + 1 - a))) by lia.
  rewrite seq_S, map_app. simpl. f_equal. f_equal. f_equal. lia.
Qed.

Lemma range_empty : forall b, range (b + 1) b = [].
Proof.
  intros b. unfold range. replace (N.to_nat (b + 1 - (b + 1))) with 0%nat by lia. reflexivity.
Qed.

Lemma in_range : forall i a b, In i (range a b) -> (a <= i <= b)%N.
Proof.
  intros i a b H. unfold range in H. apply in_map_iff in H.
  destruct H as (k & <- & Hk). apply in_seq in Hk. lia.
Qed.

Lemma natsum_seq : forall (h : N -> nat) st k,
  Z.of_nat (natsum h (map N.of_nat (seq st k)))
  = sumz (fun z => Z.of_nat (h (Z.to_N z))) (Z.of_nat st) k.
Proof.
  intros h st k. induction k as [|k IH]; [reflexivity|].
  rewrite seq_S, map_app, natsum_app, Nat2Z.inj_add, IH. simpl.
  f_equal. rewrite Nat.add_0_r. f_equal. f_equal. lia.
Qed.

Section Count.
Local Open Scope Z_scope.
Variable s : String.string.
Variable x : PrimString.string.
Hypothesis Hx : repr x s.
Variable cntf : Z -> Z.
Hypothesis Hcnt : forall q, 0 <= q < 2 * nlen s ->
  0 <= cntf q /\ forall j, 0 <= j -> (Pk x (nlen s) q j <-> j < cntf q).

(* palindromes of centre q inside [L, R] (0-based) *)
Definition C (q L R : Z) : Z :=
  Z.max 0 (Z.min (Z.min (cntf q) (q / 2 - L + 1)) (R - (q + 1) / 2 + 1)).

Definition Pb (a b : Z) : bool :=
  palindrome (Prelude.sub s (Z.to_N (a + 1)) (Z.to_N (b + 1))).

Lemma C_step : forall q L R, 0 <= q < 2 * nlen s -> 0 <= L <= R -> R < nlen s ->
  C q L R = C q L (R - 1)
            + (if andb (andb (L <=? q - R) (q - R <=? R)) (Pb (q - R) R) then 1 else 0).
Proof.
  intros q L R Hq HL HR.
  pose proof (half_facts q ltac:(lia)) as (H1 & H2 & H3).
  destruct (Hcnt q Hq) as [Hc0 Hc].
  unfold C.
  destruct (Z.lt_ge_cases (R - (q + 1) / 2) 0) as [Hk | Hk].
  - destruct (Z.leb_spec (q - R) R); [lia|].
    rewrite Bool.andb_false_r, Bool.andb_false_l. lia.
  - destruct (Z.leb_spec (q - R) R); [|lia].
    destruct (Z.leb_spec L (q - R)) as [HLq | HLq].
    + simpl andb.
      pose proof (Pk_pal s x q (R - (q + 1) / 2) ltac:(lia) Hk) as P.
      replace (q / 2 - (R - (q + 1) / 2)) with (q - R) in P by lia.
      replace ((q + 1) / 2 + (R - (q + 1) / 2)) with R in P by lia.
      pose proof (palZ_iff s x Hx (q - R) R ltac:(lia) HR) as P'.
      pose proof (Hc (R - (q + 1) / 2) Hk) as P''.
      unfold Pb. destruct (palindrome (Prelude.sub s (Z.to_N (q - R + 1)) (Z.to_N (R + 1)))).
      * assert (R - (q + 1) / 2 < cntf q) by (apply P''; apply P; split; [lia|]; split; [lia|]; apply P'; reflexivity).
        lia.
      * assert (cntf q <= R - (q + 1) / 2).
        { destruct (Z.lt_ge_cases (R - (q + 1) / 2) (cntf q)) as [Hlt|]; [|lia].
          exfalso. apply P'' in Hlt. apply P in Hlt. destruct Hlt as (_ & _ & Hp).
          apply P' in Hp. discriminate. }
        lia.
    + simpl andb. lia.
Qed.

Lemma sum_step : forall L R, 0 <= L <= R -> R < nlen s ->
  sumz (fun q => C q L R) 0 (Z.to_nat (2 * nlen s))
  = sumz (fun q => C q L (R - 1)) 0 (Z.to_nat (2 * nlen s))
    + sumz (fun a => if Pb a R then 1 else 0) L (Z.to_nat (R - L + 1)).
Proof.
  intros L R HL HR.
  rewrite (sumz_ext (fun q => C q L R)
             (fun q => C q L (R - 1)
                + (if andb (andb (L <=? q - R) (q - R <=? R)) (Pb (q - R) R) then 1 else 0)))
    by (intros q Hq; apply C_step; lia).
  rewrite sumz_add. f_equal.
  rewrite (sumz_sub _ 0 _ (L + R) (Z.to_nat (R - L + 1))) by
    (try lia; intros q Hq Hout; destruct (Z.leb_spec L (q - R)); destruct (Z.leb_spec (q - R) R);
     simpl andb; try reflexivity; lia).
  rewrite (sumz_shift (fun a => if Pb a R then 1 else 0) L R).
  apply sumz_ext. intros q Hq.
  replace (L <=? q - R) with true by (symmetry; apply Z.leb_le; lia).
  replace (q - R <=? R) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Definition cnt_i (i r : N) : nat :=
  List.length (filter (fun p => palindrome (Prelude.sub s (fst p) (snd p)))
                      (map (fun j => (i, j)) (range i r))).

Lemma cnt_i_S : forall i r, (i <= r + 1)%N ->
  cnt_i i (r + 1) = (cnt_i i r + if palindrome (Prelude.sub s i (r + 1)) then 1 else 0)%nat.
Proof.
  intros i r H. unfold cnt_i. rewrite range_S by exact H.
  rewrite map_app, filter_app, length_app. simpl.
  destruct (palindrome _); simpl; lia.
Qed.

Lemma pc_natsum : forall l r,
  List.length (filter (fun p => palindrome (Prelude.sub s (fst p) (snd p))) (index_pairs l r))
  = natsum (fun i => cnt_i i r) (range l r).
Proof. intros l r. unfold index_pairs. apply length_filter_flat_map. Qed.

Definition ind (r : N) (i : N) : nat :=
  if palindrome (Prelude.sub s i (r + 1)) then 1%nat else 0%nat.

Lemma pc_step : forall l r, (1 <= l <= r + 1)%N ->
  Z.of_N (palindromic_count s l (r + 1))
  = Z.of_N (palindromic_count s l r)
    + sumz (fun a => if Pb a (Z.of_N r) then 1 else 0) (Z.of_N l - 1)
           (Z.to_nat (Z.of_N r - (Z.of_N l - 1) + 1)).
Proof.
  intros l r Hlr. unfold palindromic_count, len. rewrite !nat_N_Z, !pc_natsum.
  assert (E1 : natsum (fun i => cnt_i i (r + 1)) (range l (r + 1))
               = (natsum (fun i => cnt_i i r) (range l r) + natsum (ind r) (range l (r + 1)))%nat).
  { rewrite !range_S by lia. rewrite !natsum_app. simpl natsum.
    rewrite (natsum_ext _ (fun i => cnt_i i (r + 1)) (fun i => cnt_i i r + ind r i)%nat)
      by (intros i Hi; apply in_range in Hi; apply cnt_i_S; lia).
    rewrite natsum_add. rewrite cnt_i_S by lia.
    assert (E0 : cnt_i (r + 1) r = 0%nat) by (unfold cnt_i; rewrite range_empty; reflexivity).
    rewrite E0. unfold ind. lia. }
  rewrite E1, Nat2Z.inj_add. f_equal.
  unfold range at 1. rewrite natsum_seq.
  replace (Z.of_nat (N.to_nat l)) with (Z.of_N l) by lia.
  replace (N.to_nat (r + 1 + 1 - l)) with (Z.to_nat (Z.of_N r - (Z.of_N l - 1) + 1)) by lia.
  rewrite (sumz_shift _ (Z.of_N l) (-1)). replace (Z.of_N l + -1) with (Z.of_N l - 1) by lia.
  apply sumz_ext. intros a Ha. unfold ind, Pb.
  replace (Z.to_N (a - -1)) with (Z.to_N (a + 1)) by (f_equal; lia).
  replace (Z.to_N (Z.of_N r + 1)) with (r + 1)%N by lia.
  destruct (palindrome _); reflexivity.
Qed.

Lemma C_empty : forall q L, 0 <= q -> C q L (L - 1) = 0.
Proof.
  intros q L Hq. pose proof (half_facts q Hq). unfold C. lia.
Qed.

Lemma pc_sum : forall (t : nat) (l : N), (1 <= l)%N ->
  Z.of_N l - 1 + Z.of_nat t <= nlen s ->
  Z.of_N (palindromic_count s l (l - 1 + N.of_nat t))
  = sumz (fun q => C q (Z.of_N l - 1) (Z.of_N (l - 1 + N.of_nat t) - 1)) 0 (Z.to_nat (2 * nlen s)).
Proof.
  intros t. induction t as [|t IH]; intros l Hl Hn.
  - replace (l - 1 + N.of_nat 0)%N with (l - 1)%N by lia.
    unfold palindromic_count, index_pairs.
    replace (range l (l - 1)) with (@nil N)
      by (unfold range; replace (N.to_nat (l - 1 + 1 - l)) with 0%nat by lia; reflexivity).
    simpl. symmetry. apply sumz_zero. intros q Hq.
    replace (Z.of_N (l - 1) - 1) with ((Z.of_N l - 1) - 1) by lia. apply C_empty. lia.
  - replace (l - 1 + N.of_nat (S t))%N with ((l - 1 + N.of_nat t) + 1)%N by lia.
    rewrite pc_step by lia. rewrite IH by lia.
    rewrite (sum_step (Z.of_N l - 1) (Z.of_N (l - 1 + N.of_nat t + 1) - 1)) by lia.
    f_equal.
    + apply sumz_ext. intros q Hq. f_equal; try lia.
    + replace (Z.of_N (l - 1 + N.of_nat t + 1) - 1) with (Z.of_N (l - 1 + N.of_nat t)) by lia.
      f_equal; try lia.
Qed.

End Count.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* One of the four families of clipped sums: the odd (par = 0) or even
   (par = 1) centres, the left half of every query (rev = false) or its
   right half read backwards (rev = true). *)
Definition fam (n m : int) (cnt xl xr : array int) (par : int) (rev : bool) : array int :=
  let d := tab n (fun i => cnt.[2 * (if rev then n - 1 - i else i) + par]) in
  let as_ := tab m (fun k => if rev then n - (xr.[k] - par) else xl.[k] - 1) in
  let ts := tab m (fun k => let h := (xl.[k] + xr.[k] - par) >> 1 in
                            if rev then n - h else h) in
  lsum_all n m d as_ ts.
Elpi complexity fam.
Arguments fam_cost : simpl never.

Definition palindromes_impl (x : PrimString.string) (xl xr : array uint) : array uint :=
  let n := PrimString.length x in
  let m := PArray.length xl in
  let cnt := manacher x in
  let v0 := fam n m cnt xl xr 0 false in
  let v1 := fam n m cnt xl xr 0 true in
  let v2 := fam n m cnt xl xr 1 false in
  let v3 := fam n m cnt xl xr 1 true in
  tab m (fun k => v0.[k] + v1.[k] + v2.[k] + v3.[k]).
Elpi complexity palindromes_impl.
Arguments palindromes_impl_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Prop side of the assembly                                           *)
(* ------------------------------------------------------------------ *)

Lemma of_Z_phi : forall z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma fam_spec : forall (n m : int) cnt xl xr (par : int) (rev : bool),
  ((φ n) <= 1000000)%Z -> ((φ m) <= 4194303)%Z -> ((φ par) <= 1)%Z ->
  (forall k : int, ((φ k) < (φ m))%Z ->
     (1 <= (φ (xl.[k])) <= (φ (xr.[k])))%Z /\ ((φ (xr.[k])) <= (φ n))%Z) ->
  exists d,
  (forall i, (0 <= i < (φ n))%Z ->
     (φ (d.[of_Z i])) = (φ (cnt.[of_Z (2 * (if rev then (φ n) - 1 - i else i) + (φ par))]))) /\
  (φ (PArray.length (fam n m cnt xl xr par rev))) = (φ m) /\
  forall k : int, ((φ k) < (φ m))%Z ->
    (φ ((fam n m cnt xl xr par rev).[k]))
    = (Vsum d (if rev then (φ n) - ((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) / 2
               else ((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) / 2)
              (if rev then (φ n) - ((φ (xr.[k])) - (φ par)) else (φ (xl.[k])) - 1) mod wB)%Z.
Proof.
  intros n m cnt xl xr par rev Hn Hm Hpar Hq.
  pose proof (to_Z_bounded par) as Bp.
  unfold fam. cbv zeta.
  set (d := tab n (fun i => cnt.[2 * (if rev then n - 1 - i else i) + par])).
  set (as_ := tab m (fun k => if rev then n - (xr.[k] - par) else xl.[k] - 1)).
  set (ts := tab m (fun k => if rev then n - ((xl.[k] + xr.[k] - par) >> 1)
                             else (xl.[k] + xr.[k] - par) >> 1)).
  destruct (tab_spec n (fun i => cnt.[2 * (if rev then n - 1 - i else i) + par]) ltac:(lia)) as [Dl Dc].
  destruct (tab_spec m (fun k => if rev then n - (xr.[k] - par) else xl.[k] - 1) Hm) as [Al Ac].
  destruct (tab_spec m (fun k => if rev then n - ((xl.[k] + xr.[k] - par) >> 1)
                                 else (xl.[k] + xr.[k] - par) >> 1) Hm) as [Tl Tc].
  fold d in Dl, Dc. fold as_ in Al, Ac. fold ts in Tl, Tc.
  assert (EH : forall k : int, ((φ k) < (φ m))%Z ->
     (φ ((xl.[k] + xr.[k] - par) >> 1)) = (((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) / 2)%Z).
  { intros k Hk. destruct (Hq k Hk). rewrite lsr1. f_equal. sia. }
  assert (EA : forall k : int, ((φ k) < (φ m))%Z ->
     (φ (as_.[k])) = (if rev then (φ n) - ((φ (xr.[k])) - (φ par)) else (φ (xl.[k])) - 1)%Z).
  { intros k Hk. rewrite Ac by exact Hk. destruct (Hq k Hk). destruct rev; sia. }
  assert (ET : forall k : int, ((φ k) < (φ m))%Z ->
     (φ (ts.[k])) = (if rev then (φ n) - ((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) / 2
                   else ((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) / 2)%Z).
  { intros k Hk. rewrite Tc by exact Hk. pose proof (EH k Hk) as E. destruct (Hq k Hk).
    pose proof (half_facts ((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) ltac:(lia)).
    destruct rev; [|exact E]. rewrite sub_spec, E. apply Z.mod_small. lia. }
  exists d. split.
  - intros i Hi. rewrite Dc by (rewrite of_Z_phi; lia).
    f_equal. f_equal. apply to_Z_inj. rewrite of_Z_phi by (destruct rev; lia).
    destruct rev; rewrite ?of_Z_phi by lia; sia.
  - destruct (lsum_all_spec n m d as_ ts Hn Hm) as [L1 L2].
    + intros k Hk. rewrite EA, ET by exact Hk. destruct (Hq k Hk).
      pose proof (half_facts ((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) ltac:(lia)).
      destruct rev; lia.
    + split; [exact L1|]. intros k Hk. rewrite L2 by exact Hk. rewrite EA, ET by exact Hk.
      reflexivity.
Qed.

Section Split.
Local Open Scope Z_scope.

Lemma split_FF : forall (g : Z -> Z) (d dr : array int) (n A Bx : Z),
  0 <= A <= Bx -> Bx <= n ->
  (forall i, 0 <= i < n -> (φ (d.[of_Z i])) = g i) ->
  (forall j, 0 <= j < n -> (φ (dr.[of_Z j])) = g (n - 1 - j)) ->
  sumz (fun i => Z.max 0 (Z.min (Z.min (g i) (i - A + 1)) (Bx - i))) 0 (Z.to_nat n)
  = Vsum d ((A + Bx + 1) / 2) A + Vsum dr (n - (A + Bx + 1) / 2) (n - Bx).
Proof.
  intros g d dr n A Bx HA HB Hd Hdr.
  assert (HM : A <= (A + Bx + 1) / 2 <= Bx /\ A + Bx <= 2 * ((A + Bx + 1) / 2) <= A + Bx + 1)
    by (Z.to_euclidean_division_equations; lia).
  set (Mx := (A + Bx + 1) / 2) in *.
  replace (Z.to_nat n) with (Z.to_nat Mx + Z.to_nat (n - Mx))%nat by lia.
  rewrite sumz_split. f_equal.
  - unfold Vsum. apply sumz_ext. intros i Hi. unfold fterm. rewrite (Hd i) by lia. lia.
  - rewrite (sumz_rev _ (0 + Z.of_nat (Z.to_nat Mx))).
    rewrite (sumz_shift _ (0 + Z.of_nat (Z.to_nat Mx)) (- (0 + Z.of_nat (Z.to_nat Mx)))).
    replace (0 + Z.of_nat (Z.to_nat Mx) + - (0 + Z.of_nat (Z.to_nat Mx))) with 0 by lia.
    unfold Vsum. apply sumz_ext. intros j Hj. unfold fterm. rewrite (Hdr j) by lia.
    match goal with |- context [g ?E] => replace E with (n - 1 - j) by lia end.
    lia.
Qed.

End Split.

Lemma Forall2_nth_error : forall A B (P : A -> B -> Prop) l1 l2 k a b,
  Forall2 P l1 l2 -> nth_error l1 k = Some a -> nth_error l2 k = Some b -> P a b.
Proof.
  intros A B P l1 l2 k a b H. revert k. induction H as [|a' b' l1 l2 Hab H IH]; intros k H1 H2.
  - destruct k; discriminate.
  - destruct k; simpl in H1, H2.
    + injection H1 as <-. injection H2 as <-. exact Hab.
    + apply (IH k H1 H2).
Qed.

Lemma repr_cell : forall (xa : array uint) (l : list N), repr xa l ->
  forall k : nat, (k < List.length l)%nat ->
  (φ (xa.[of_Z (Z.of_nat k)])) = Z.of_N (nth k l 0%N).
Proof.
  intros xa l [Hl Hc] k Hk.
  destruct (Hc k Hk) as (v & Hv & Hr).
  assert (E : Z.to_N (φ (xa.[of_Z (Z.of_nat k)])) = v) by exact Hr.
  rewrite (nth_error_nth l k 0%N Hv). rewrite <- E.
  pose proof (to_Z_bounded (xa.[of_Z (Z.of_nat k)])). lia.
Qed.

Lemma repr_len : forall (xa : array uint) (l : list N), repr xa l ->
  (φ (PArray.length xa)) = Z.of_nat (List.length l).
Proof. intros xa l [Hl _]. symmetry. exact Hl. Qed.

Lemma add4_spec : forall a b c d : int,
  (φ (a + b + c + d)) = (((φ a) + (φ b) + (φ c) + (φ d)) mod wB)%Z.
Proof.
  intros a b c d. rewrite !add_spec.
  rewrite Zplus_mod_idemp_l.
  rewrite <- (Z.add_assoc (((φ a) + (φ b)) mod wB)), Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma mod4 : forall A B C D : Z,
  ((A mod wB + B mod wB + C mod wB + D mod wB) mod wB = (A + B + C + D) mod wB)%Z.
Proof.
  intros A B C D. assert (Hw : wB <> 0%Z) by (rewrite wB_val; lia).
  rewrite (Z.mod_eq A wB Hw), (Z.mod_eq B wB Hw), (Z.mod_eq C wB Hw), (Z.mod_eq D wB Hw).
  replace (A - wB * (A / wB) + (B - wB * (B / wB)) + (C - wB * (C / wB)) + (D - wB * (D / wB)))%Z
    with (A + B + C + D + (- (A / wB + B / wB + C / wB + D / wB)) * wB)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Section Query.
Local Open Scope Z_scope.

Lemma query_ok : forall s x (cnt : array int) (n : Z) d0 d1 d2 d3 (l r : Z),
  repr x s -> n = nlen s -> n <= 100000 ->
  (forall q, (0 <= q < 2 * nlen s)%Z ->
     (0 <= (φ (cnt.[of_Z q])))%Z /\
     forall j, (0 <= j)%Z -> (Pk x (nlen s) q j <-> (j < (φ (cnt.[of_Z q])))%Z)) ->
  (forall i, (0 <= i < n)%Z -> (φ (d0.[of_Z i])) = (φ (cnt.[of_Z (2 * i + 0)]))) ->
  (forall i, (0 <= i < n)%Z -> (φ (d1.[of_Z i])) = (φ (cnt.[of_Z (2 * (n - 1 - i) + 0)]))) ->
  (forall i, (0 <= i < n)%Z -> (φ (d2.[of_Z i])) = (φ (cnt.[of_Z (2 * i + 1)]))) ->
  (forall i, (0 <= i < n)%Z -> (φ (d3.[of_Z i])) = (φ (cnt.[of_Z (2 * (n - 1 - i) + 1)]))) ->
  (1 <= l <= r)%Z -> (r <= n)%Z ->
  (Vsum d0 ((l + r - 0) / 2) (l - 1) + Vsum d1 (n - (l + r - 0) / 2) (n - (r - 0))
   + Vsum d2 ((l + r - 1) / 2) (l - 1) + Vsum d3 (n - (l + r - 1) / 2) (n - (r - 1)))%Z
  = Z.of_N (palindromic_count s (Z.to_N l) (Z.to_N r))
  /\ (Z.of_N (palindromic_count s (Z.to_N l) (Z.to_N r)) <= 2 * n * n)%Z.
Proof.
  intros s x cnt n d0 d1 d2 d3 l r Hx -> Hn Hcnt D0 D1 D2 D3 Hlr Hrn.
  set (cntf := fun q => (φ (cnt.[of_Z q]))).
  assert (Hc : forall q, (0 <= q < 2 * nlen s)%Z ->
     (0 <= cntf q)%Z /\ forall j, (0 <= j)%Z -> (Pk x (nlen s) q j <-> (j < cntf q)%Z))
    by exact Hcnt.
  replace (Z.to_N r) with (Z.to_N l - 1 + N.of_nat (Z.to_nat (r - l + 1)))%N by lia.
  rewrite (pc_sum s x Hx cntf Hc) by lia.
  rewrite (sumz_ext _ (fun q => C cntf q (l - 1) (r - 1))) by (intros q Hq; f_equal; lia).
  replace (Z.to_nat (2 * nlen s)) with (2 * Z.to_nat (nlen s))%nat by lia.
  split.
  - rewrite sumz_pairs.
    rewrite (sumz_ext _
      (fun i => Z.max 0 (Z.min (Z.min (cntf (2 * i)) (i - (l - 1) + 1)) (r - i))
              + Z.max 0 (Z.min (Z.min (cntf (2 * i + 1)) (i - (l - 1) + 1)) ((r - 1) - i)))).
    2:{ intros i Hi. unfold C.
        assert (E1 : (2 * i / 2 = i)%Z) by (Z.to_euclidean_division_equations; lia).
        assert (E2 : ((2 * i + 1) / 2 = i)%Z) by (Z.to_euclidean_division_equations; lia).
        assert (E3 : ((2 * i + 1 + 1) / 2 = i + 1)%Z) by (Z.to_euclidean_division_equations; lia).
        rewrite E1, E2, E3. lia. }
    rewrite sumz_add.
    rewrite (split_FF (fun i => cntf (2 * i)) d0 d1 (nlen s) (l - 1) r) by
      first [ lia
            | intros i Hi; unfold cntf; rewrite D0 by lia; do 3 f_equal; lia
            | intros i Hi; unfold cntf; rewrite D1 by lia; do 3 f_equal; lia ].
    rewrite (split_FF (fun i => cntf (2 * i + 1)) d2 d3 (nlen s) (l - 1) (r - 1)) by
      first [ lia
            | intros i Hi; unfold cntf; rewrite D2 by lia; reflexivity
            | intros i Hi; unfold cntf; rewrite D3 by lia; reflexivity ].
    replace ((l - 1 + r + 1) / 2)%Z with ((l + r - 0) / 2)%Z by (f_equal; lia).
    replace ((l - 1 + (r - 1) + 1) / 2)%Z with ((l + r - 1) / 2)%Z by (f_equal; lia).
    replace (nlen s - r)%Z with (nlen s - (r - 0))%Z by lia.
    lia.
  - assert (Hle : sumz (fun q => C cntf q (l - 1) (r - 1)) 0 (2 * Z.to_nat (nlen s))
                  <= Z.of_nat (2 * Z.to_nat (nlen s)) * nlen s).
    { apply sumz_le. intros q. unfold C.
      assert (q / 2 <= (q + 1) / 2)%Z by (apply Z.div_le_mono; lia). lia. }
    lia.
Qed.

End Query.

Lemma palindromes_impl_correct : forall (s : String.string) (ls rs : list N)
    (x : PrimString.string) (xl xr : array uint),
  valid_input s ls rs -> repr x s -> repr xl ls -> repr xr rs ->
  exists o : list N, repr (palindromes_impl x xl xr) o /\ palindromes_spec s ls rs o.
Proof.
  intros s ls rs x xl xr Hv Hx Hl Hr.
  pose proof Hv as Hv'. destruct Hv' as [_ Hvn Hvm Hvlr].
  unfold slen in Hvn. unfold len in Hvm.
  pose proof (Forall2_length Hvlr) as Hlr.
  assert (Hn : (φ (PrimString.length x)) = nlen s)
    by (destruct Hx as [H _]; unfold nlen; symmetry; exact H).
  pose proof (repr_len xl ls Hl) as Hml. pose proof (repr_len xr rs Hr) as Hmr.
  assert (Hcells : forall k : nat, (k < List.length ls)%nat ->
     (φ (xl.[of_Z (Z.of_nat k)])) = Z.of_N (nth k ls 0%N) /\
     (φ (xr.[of_Z (Z.of_nat k)])) = Z.of_N (nth k rs 0%N) /\
     (1 <= nth k ls 0%N <= nth k rs 0%N)%N /\ (nth k rs 0%N <= slen s)%N).
  { intros k Hk. split; [apply (repr_cell xl ls Hl k Hk)|].
    split; [apply (repr_cell xr rs Hr k ltac:(lia))|].
    assert (Hk2 : (k < List.length rs)%nat) by lia.
    pose proof (Forall2_nth_error _ _ _ _ _ k _ _ Hvlr (nth_error_nth' ls 0%N Hk)
                  (nth_error_nth' rs 0%N Hk2)) as [H1 H2].
    unfold slen. split; [exact H1 | exact H2]. }
  set (n := PrimString.length x) in *. set (m := PArray.length xl) in *.
  assert (Hnb : ((φ n) <= 100000)%Z) by (pose proof Hn as H; unfold nlen in H; lia).
  assert (Hnb' : (nlen s <= 100000)%Z) by lia.
  assert (Hn2 : (2 * (φ n) <= 4194303)%Z) by lia.
  assert (Hint : forall k : int, ((φ k) < (φ m))%Z -> k = of_Z (Z.of_nat (Z.to_nat (φ k)))).
  { intros k Hk. rewrite Z2Nat.id by (pose proof (to_Z_bounded k); lia). symmetry. apply of_to_Z. }
  assert (Hq : forall k : int, ((φ k) < (φ m))%Z ->
     (1 <= (φ (xl.[k])) <= (φ (xr.[k])))%Z /\ ((φ (xr.[k])) <= (φ n))%Z).
  { intros k Hk. rewrite (Hint k Hk).
    destruct (Hcells (Z.to_nat (φ k)) ltac:(lia)) as (H1 & H2 & H3 & H4).
    rewrite H1, H2. unfold slen in H4. pose proof Hn as Hn'. unfold nlen in Hn'. lia. }
  destruct (manacher_spec x Hn2) as [Cl Cc].
  set (cnt := manacher x) in *.
  assert (Hcnt : forall q, (0 <= q < 2 * nlen s)%Z ->
     (0 <= (φ (cnt.[of_Z q])))%Z /\
     forall j, (0 <= j)%Z -> (Pk x (nlen s) q j <-> (j < (φ (cnt.[of_Z q])))%Z)).
  { intros q Hq'. split; [apply to_Z_bounded|]. intros j Hj.
    pose proof (Cc (of_Z q) ltac:(rewrite of_Z_phi; rewrite ?wB_val; lia) j Hj) as P.
    rewrite of_Z_phi in P by (rewrite wB_val; lia). rewrite <- Hn. exact P. }
  assert (Bm : ((φ m) <= 4194303)%Z) by lia.
  destruct (fam_spec n m cnt xl xr 0 false ltac:(lia) Bm ltac:(change (φ 0) with 0%Z; lia) Hq)
    as (d0 & D0 & L0 & V0).
  destruct (fam_spec n m cnt xl xr 0 true ltac:(lia) Bm ltac:(change (φ 0) with 0%Z; lia) Hq)
    as (d1 & D1 & L1 & V1).
  destruct (fam_spec n m cnt xl xr 1 false ltac:(lia) Bm ltac:(change (φ 1) with 1%Z; lia) Hq)
    as (d2 & D2 & L2 & V2).
  destruct (fam_spec n m cnt xl xr 1 true ltac:(lia) Bm ltac:(change (φ 1) with 1%Z; lia) Hq)
    as (d3 & D3 & L3 & V3).
  set (v0 := fam n m cnt xl xr 0 false) in *. set (v1 := fam n m cnt xl xr 0 true) in *.
  set (v2 := fam n m cnt xl xr 1 false) in *. set (v3 := fam n m cnt xl xr 1 true) in *.
  change (palindromes_impl x xl xr) with
    (tab m (fun k => v0.[k] + v1.[k] + v2.[k] + v3.[k])).
  destruct (tab_spec m (fun k => v0.[k] + v1.[k] + v2.[k] + v3.[k]) Bm) as [TL TC].
  set (out := tab m (fun k => v0.[k] + v1.[k] + v2.[k] + v3.[k])) in *.
  assert (Key : forall k : nat, (k < List.length ls)%nat ->
     (φ (out.[of_Z (Z.of_nat k)])) = Z.of_N (palindromic_count s (nth k ls 0%N) (nth k rs 0%N))).
  { intros k Hk.
    assert (Hk' : ((φ (of_Z (Z.of_nat k))) < (φ m))%Z) by (rewrite of_Z_phi; rewrite ?wB_val; lia).
    rewrite TC by exact Hk'. rewrite add4_spec.
    rewrite V0, V1, V2, V3 by exact Hk'. rewrite mod4.
    destruct (Hcells k Hk) as (H1 & H2 & H3 & H4).
    assert (H1' : (φ (@PArray.get@{Set} int xl (of_Z (Z.of_nat k)))) = Z.of_N (nth k ls 0%N)) by exact H1.
    assert (H2' : (φ (@PArray.get@{Set} int xr (of_Z (Z.of_nat k)))) = Z.of_N (nth k rs 0%N)) by exact H2.
    rewrite H1', H2'.
    change (φ 0) with 0%Z. change (φ 1) with 1%Z. cbv iota. rewrite Hn.
    destruct (query_ok s x cnt (nlen s) d0 d1 d2 d3 (Z.of_N (nth k ls 0%N)) (Z.of_N (nth k rs 0%N))
                Hx eq_refl ltac:(lia) Hcnt) as [Q1 Q2].
    - intros i Hi. rewrite D0 by (rewrite Hn; exact Hi). reflexivity.
    - intros i Hi. rewrite D1 by (rewrite Hn; exact Hi). rewrite Hn. reflexivity.
    - intros i Hi. rewrite D2 by (rewrite Hn; exact Hi). reflexivity.
    - intros i Hi. rewrite D3 by (rewrite Hn; exact Hi). rewrite Hn. reflexivity.
    - lia.
    - unfold slen in H4. unfold nlen. lia.
    - rewrite Q1. rewrite !N2Z.id. apply Z.mod_small. rewrite !N2Z.id in Q2.
      rewrite wB_val. unfold nlen in Q2.
      assert (Hs : (Z.of_nat (String.length s) <= 100000)%Z) by lia.
      assert (Hss : (Z.of_nat (String.length s) * Z.of_nat (String.length s) <= 100000 * 100000)%Z)
        by (apply Z.mul_le_mono_nonneg; lia).
      lia. }
  exists (map (fun k => palindromic_count s (nth k ls 0%N) (nth k rs 0%N)) (seq 0 (List.length ls))).
  assert (Hnth : forall k, (k < List.length ls)%nat ->
     nth_error (map (fun k => palindromic_count s (nth k ls 0%N) (nth k rs 0%N)) (seq 0 (List.length ls))) k
     = Some (palindromic_count s (nth k ls 0%N) (nth k rs 0%N))).
  { intros k Hk. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec k (List.length ls)); [reflexivity | lia]. }
  split.
  - split.
    + rewrite length_map, length_seq.
      assert (E : (φ (PArray.length out)) = Z.of_nat (List.length ls)) by (rewrite TL; exact Hml).
      symmetry. exact E.
    + intros k Hk. rewrite length_map, length_seq in Hk.
      exists (palindromic_count s (nth k ls 0%N) (nth k rs 0%N)). split; [apply Hnth; exact Hk|].
      assert (E : Z.to_N (φ (out.[of_Z (Z.of_nat k)]))
                  = palindromic_count s (nth k ls 0%N) (nth k rs 0%N))
        by (rewrite Key by exact Hk; apply N2Z.id).
      exact E.
  - split.
    + unfold len. rewrite length_map, length_seq. reflexivity.
    + intros k Hk. unfold len in Hk. rewrite length_map, length_seq in Hk.
      unfold at_ at 1. rewrite (nth_error_nth _ _ 0%N (Hnth (N.to_nat k) ltac:(lia))).
      reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition palindromes : PrimString.string -> array uint -> array uint -> array uint :=
  palindromes_impl.
Elpi complexity palindromes.

Definition palindromes_correct :
  forall (s : String.string) (ls rs : list N)
         (x : PrimString.string) (xl xr : array uint),
  valid_input s ls rs -> repr x s -> repr xl ls -> repr xr rs ->
  exists o : list N, repr (palindromes x xl xr) o /\ palindromes_spec s ls rs o
  := palindromes_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* Every loop is bounded on its cost twin by induction on a nat bound of
   its measure (the Acc proof destructed, cost_simpl, cost_destruct on the
   tests), the callees' bounds generalized in their callers' goals (the
   callees' twins are kept folded by `Arguments ... : simpl never`, and
   so are the program's own functions and φ, so that cbn never unfolds φ
   of a variable in an Acc index).
   - Fenwick loops: log2 N + 1 iterations, the potential being
     log2 N - log2 (lowbit j) (the lowest bit at least doubles per step).
   - expand: cost + 100 * k <= 100 * result + 100.
   - man (Manacher): amortised with the potential n - rb, rb the right
     border; an expansion beyond the initial radius k0 moves rb by at
     least as much (man_step, through the mirror lemma and its converse
     mirror_back: a radius strictly inside the window is never extended).
   - walk visits exactly the queries of its bucket (cnteq), sweep carries
     cntge (the queries of the buckets still to come) as a potential, so
     the walks total m.
   The final bound: c1 = 14000, c2 = 3000. *)

Arguments Uint63.to_Z : simpl never.
Arguments gap : simpl never.
Arguments mtop : simpl never.

Definition zn (x : int) : nat := Z.to_nat (φ x).
Arguments zn : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Ltac zero_partials :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch T with forall _, _ => change (@cost T X) with 0%nat end end.
Ltac zero_pairs := repeat match goal with |- context [@cost ?T (?z, ?x)] => change (@cost T (z, x)) with 0%nat end.

Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  end.
Ltac get_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (get_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (get_cost a b c) d e) f g)) with 1%nat
  end.

Lemma gap_S (i n : int) : (i <? n) = true -> Z.to_nat (gap n i) = S (Z.to_nat (gap n (i + 1))).
Proof.
  intros Hx. apply ltb_spec in Hx. unfold gap.
  assert (E1 : (φ (i + 1) = φ i + 1)%Z) by sia. rewrite E1. lia.
Qed.

Lemma tab_loop_time f fC n nC i iC a aC H HC K :
  (forall j jC, (cost (fC j jC) <= K)%nat) ->
  (cost (extract (extract (extract (extract (tab_loop_cost stepsCM f fC) n nC) i iC) a aC) H HC)
    <= Z.to_nat (gap n i) * (K + 40) + 20)%nat.
Proof.
  intros HK. unfold tab_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G f fC n nC i iC a aC H HC)] =>
    assert (HG : forall N i iC a aC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G f fC n nC i iC a aC H HC) <= Z.to_nat (gap n i) * (K + 40) + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' a' aC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials. set_simpl.
      pose proof (HK i' iC').
      assert (E : Z.to_nat (gap n i') = S (Z.to_nat (gap n (i' + 1))))
        by (match goal with Hx : (i' <? n) = true |- _ => exact (gap_S _ _ Hx) end).
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?i2 ?iC2 ?P2 ?PC2 ?a ?e)] =>
        pose proof (IH _ HN2 i2 iC2 P2 PC2 a e (le_n _)
          : (@cost T (G' a1 a2 a3 a4 i2 iC2 P2 PC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 i2 iC2 P2 PC2 a e)); intros ? HI
      end.
      lia.
    - zero_pairs. lia. }
  match goal with |- context [@cost ?T (?G f fC n nC i iC a aC H HC)] =>
    exact (HG _ i iC a aC H HC (le_n _) : (@cost T (G f fC n nC i iC a aC H HC) <= _)%nat) end.
Qed.

(* ---- low bits ---- *)
Lemma lowZ_mul_pow : forall e y, (0 <= e)%Z -> (1 <= y)%Z -> (2 ^ e <= lowZ (2 ^ e * y))%Z.
Proof.
  intros e y He Hy. destruct (decomp y Hy) as (d & u & Hd & Hu & Ey).
  rewrite Ey, Z.mul_assoc, <- Z.pow_add_r by lia.
  rewrite lowZ_pow by lia. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lowZ_up2 : forall j, (1 <= j)%Z -> (2 * lowZ j <= lowZ (j + lowZ j))%Z.
Proof.
  intros j Hj. destruct (decomp j Hj) as (c & w & Hc & Hw & Ej).
  rewrite Ej, lowZ_pow by lia.
  replace (2 ^ c * (2 * w + 1) + 2 ^ c)%Z with (2 ^ (c + 1) * (w + 1))%Z
    by (rewrite Z.pow_add_r by lia; ring).
  replace (2 * 2 ^ c)%Z with (2 ^ (c + 1))%Z by (rewrite Z.pow_add_r by lia; ring).
  apply lowZ_mul_pow; lia.
Qed.

Lemma lowZ_down2 : forall j, (1 <= j)%Z -> (1 <= j - lowZ j)%Z -> (2 * lowZ j <= lowZ (j - lowZ j))%Z.
Proof.
  intros j Hj1 Hj.
  destruct (decomp j Hj1) as (c & w & Hc & Hw & Ej).
  rewrite Ej, lowZ_pow in * by lia.
  replace (2 ^ c * (2 * w + 1) - 2 ^ c)%Z with (2 ^ (c + 1) * w)%Z
    by (rewrite Z.pow_add_r by lia; ring).
  replace (2 * 2 ^ c)%Z with (2 ^ (c + 1))%Z by (rewrite Z.pow_add_r by lia; ring).
  apply lowZ_mul_pow; [lia|].
  destruct (Z.le_gt_cases 1 w); [lia|].
  assert (w = 0)%Z by lia. subst w. lia.
Qed.

Lemma log2_double_le : forall a b, (1 <= a)%Z -> (2 * a <= b)%Z -> (Z.log2 a + 1 <= Z.log2 b)%Z.
Proof.
  intros a b Ha Hab. pose proof (Z.log2_double a ltac:(lia)) as E.
  pose proof (Z.log2_le_mono (2 * a) b Hab). lia.
Qed.

Lemma andb_time a b (aC : bool_cost stepsCM a) bC :
  (cost (extract (andb_cost stepsCM a aC) b bC) <= 3)%nat.
Proof. destruct aC; cbn; lia. Qed.

Arguments andb_cost : simpl never.
Lemma lowb_time j jC : (cost (lowb_cost stepsCM j jC) <= 10)%nat.
Proof. unfold lowb_cost. cost_simpl. lia. Qed.

Ltac gen_known :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (andb_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hc" in
        pose proof (andb_time a b aC bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | lowb_cost stepsCM ?a ?aC =>
        let Hc := fresh "Hc" in
        pose proof (lowb_time a aC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Definition inr_ (N j : int) : Prop := (0 < φ j <= φ N)%Z.
Definition mu (N j : int) : nat := Z.to_nat (Z.log2 (φ N) - Z.log2 (lowZ (φ j))).
Arguments mu : simpl never.

Lemma mu_up (N j : int) : (j <? j + lowb j) = true -> (0 < φ j)%Z -> (φ j <= φ N)%Z ->
  (0 < φ (j + lowb j) <= φ N)%Z -> (mu N (j + lowb j) < mu N j)%nat.
Proof.
  intros Hlt Hj HjN Hn. rewrite ltb_spec in Hlt.
  pose proof (lowb_spec j Hj) as El. pose proof (low_pos (φ j) ltac:(lia)) as Lp.
  pose proof (to_Z_bounded j). pose proof (to_Z_bounded (lowb j)).
  assert (E : φ (j + lowb j) = (φ j + lowZ (φ j))%Z).
  { rewrite add_spec, El. rewrite add_spec, El in Hlt.
    destruct (Z.lt_ge_cases (φ j + lowZ (φ j)) wB) as [W|W].
    - apply Z.mod_small. lia.
    - exfalso. rewrite (Z.mod_eq _ wB) in Hlt by lia.
      assert (Hq : ((φ j + lowZ (φ j)) / wB = 1)%Z).
      { assert (1 <= (φ j + lowZ (φ j)) / wB)%Z by (apply Z.div_le_lower_bound; lia).
        assert ((φ j + lowZ (φ j)) / wB < 2)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
      rewrite Hq in Hlt. lia. }
  rewrite E in Hn.
  pose proof (lowZ_up2 (φ j) ltac:(lia)) as D.
  pose proof (low_pos (φ j + lowZ (φ j)) ltac:(lia)) as Lp2.
  pose proof (log2_double_le (lowZ (φ j)) _ ltac:(lia) D) as G.
  pose proof (Z.log2_le_mono _ _ (proj2 Lp2)) as G2.
  pose proof (Z.log2_le_mono _ _ (proj2 Hn)) as G3.
  unfold mu. rewrite E. lia.
Qed.

Lemma fen_add_time t tC N NC j jC d dC H HC :
  (cost (extract (extract (extract (extract (fen_add_cost stepsCM t tC) N NC) j jC) d dC) H HC)
    <= (Z.to_nat (Z.log2 (φ N)) + 1) * 100 + 20)%nat.
Proof.
  unfold fen_add_cost. cbn.
  match goal with |- context [@cost ?T (?G t tC N NC j jC d dC H HC)] =>
    assert (HG : forall k t tC j jC H HC, (inr_ N j -> mu N j < k)%nat ->
       (cost (G t tC N NC j jC d dC H HC) <= k * 100 + 20)%nat) end.
  { induction k as [|k IH]; intros t' tC' j' jC' [g] HC' Hk;
      cost_simpl; gen_known;
      match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB end;
      cost_destruct (bdec ((0 <? j') && (j' <=? N))); cost_simpl; zero_partials; set_simpl.
    - exfalso. destruct (proj1 (Bool.andb_true_iff _ _) e) as [e1 e2].
      apply ltb_spec in e1. apply leb_spec in e2. change (φ 0) with 0%Z in e1.
      assert (Hin : inr_ N j') by (unfold inr_; lia). specialize (Hk Hin). lia.
    - lia.
    - destruct (proj1 (Bool.andb_true_iff _ _) e) as [e1 e2].
      apply ltb_spec in e1. apply leb_spec in e2. change (φ 0) with 0%Z in e1.
      match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB2 end.
      cost_destruct (bdec (j' <? j' + (j' - j' land (j' - 1)))); cost_simpl; zero_partials; set_simpl.
      + assert (Hin : inr_ N j') by (unfold inr_; lia). specialize (Hk Hin).
        assert (Hk2 : inr_ N (j' + lowb j') -> (mu N (j' + lowb j') < k)%nat).
        { intros [A1 A2]. match goal with Hl : (j' <? _) = true |- _ => pose proof (mu_up N j' Hl e1 e2 (conj A1 A2)) end. lia. }
        match goal with |- context [@cost ?T (?G' ?t2 ?tC2 ?a3 ?a4 ?j2 ?jC2 ?a7 ?a8 ?a ?ee)] =>
          pose proof (IH t2 tC2 j2 jC2 a ee Hk2 : (@cost T (G' t2 tC2 a3 a4 j2 jC2 a7 a8 a ee) <= _)%nat) as HI;
          revert HI; generalize (@cost T (G' t2 tC2 a3 a4 j2 jC2 a7 a8 a ee)); intros ? HI
        end.
        lia.
      + lia.
    - lia. }
  match goal with |- context [@cost ?T (?G t tC N NC j jC d dC H HC)] =>
    pose proof (HG (S (Z.to_nat (Z.log2 (φ N)))) t tC j jC H HC) as HH end.
  refine (Nat.le_trans _ _ _ (HH _) _); [ | lia].
  intros _. unfold mu. pose proof (Z.log2_nonneg (φ N)). pose proof (Z.log2_nonneg (lowZ (φ j))). lia.
Qed.

Definition muS (J : Z) (j : int) : nat := Z.to_nat (Z.log2 J - Z.log2 (lowZ (φ j))).
Arguments muS : simpl never.

Lemma land_val (j : int) : (0 < φ j)%Z -> φ (j land (j - 1)) = (φ j - lowZ (φ j))%Z.
Proof. intros Hj. exact (land_low j Hj). Qed.

Lemma mu_down (J : Z) (j : int) : (0 < φ j)%Z -> (φ j <= J)%Z ->
  (0 < φ (j land (j - 1)))%Z -> (φ (j land (j - 1)) <= J)%Z /\ (muS J (j land (j - 1)) < muS J j)%nat.
Proof.
  intros Hj HjJ Hn. rewrite land_val in * by exact Hj.
  pose proof (low_pos (φ j) ltac:(lia)) as Lp.
  split; [lia|].
  pose proof (lowZ_down2 (φ j) ltac:(lia) ltac:(lia)) as D.
  pose proof (low_pos (φ j - lowZ (φ j)) ltac:(lia)) as Lp2.
  pose proof (log2_double_le (lowZ (φ j)) _ ltac:(lia) D) as G.
  pose proof (Z.log2_le_mono _ _ (proj2 Lp2)) as G2.
  pose proof (Z.log2_le_mono (φ j - lowZ (φ j)) J ltac:(lia)) as G3.
  unfold muS. rewrite land_val by exact Hj. lia.
Qed.

Lemma fen_sum_time t tC j jC acc accC H HC :
  (cost (extract (extract (extract (fen_sum_cost stepsCM t tC) j jC) acc accC) H HC)
    <= (Z.to_nat (Z.log2 (φ j)) + 1) * 100 + 20)%nat.
Proof.
  unfold fen_sum_cost. cbn.
  match goal with |- context [@cost ?T (?G t tC j jC acc accC H HC)] =>
    assert (HG : forall J k j jC acc accC H HC, (φ j <= J)%Z -> ((0 < φ j)%Z -> muS J j < k)%nat ->
       (cost (G t tC j jC acc accC H HC) <= k * 100 + 20)%nat) end.
  { intros J. induction k as [|k IH]; intros j' jC' acc' accC' [g] HC' HjJ Hk;
      cost_simpl; gen_known;
      match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB end;
      cost_destruct (bdec (0 <? j')); cost_simpl; zero_partials; set_simpl; get_simpl.
    - exfalso. pose proof (proj1 (ltb_spec _ _) e) as e'. change (φ 0) with 0%Z in e'. specialize (Hk e'). lia.
    - lia.
    - pose proof (proj1 (ltb_spec _ _) e) as e'. change (φ 0) with 0%Z in e'.
      specialize (Hk e').
      assert (Hk2 : (φ (j' land (j' - 1)) <= J)%Z /\ ((0 < φ (j' land (j' - 1)))%Z -> (muS J (j' land (j' - 1)) < k)%nat)).
      { pose proof (to_Z_bounded (j' land (j' - 1))).
        rewrite land_val by exact e'. pose proof (low_pos (φ j') ltac:(lia)).
        split; [lia|]. intros Hp.
        pose proof (mu_down J j' e' HjJ ltac:(rewrite land_val by exact e'; lia)). lia. }
      destruct Hk2 as [Hk2a Hk2b].
      match goal with |- context [@cost ?T (?G' ?t2 ?tC2 ?j2 ?jC2 ?c2 ?cC2 ?a ?ee)] =>
        pose proof (IH j2 jC2 c2 cC2 a ee Hk2a Hk2b : (@cost T (G' t2 tC2 j2 jC2 c2 cC2 a ee) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' t2 tC2 j2 jC2 c2 cC2 a ee)); intros ? HI
      end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G t tC j jC acc accC H HC)] =>
    pose proof (HG (φ j) (S (Z.to_nat (Z.log2 (φ j)))) j jC acc accC H HC ltac:(lia)) as HH end.
  refine (Nat.le_trans _ _ _ (HH _) _); [ | lia].
  intros _. unfold muS. pose proof (Z.log2_nonneg (φ j)). pose proof (Z.log2_nonneg (lowZ (φ j))). lia.
Qed.

Ltac gen_fen :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (fen_add_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
        let Hc := fresh "Hc" in
        pose proof (fen_add_time a aC b bC c cC d dC e eC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (fen_sum_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
        let Hc := fresh "Hc" in
        pose proof (fen_sum_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma fadd_time t tC N NC j jC d dC :
  (cost (extract (extract (extract (fadd_cost stepsCM t tC) N NC) j jC) d dC)
    <= (Z.to_nat (Z.log2 (φ N)) + 1) * 100 + 40)%nat.
Proof. unfold fadd_cost. cost_simpl. zero_partials. gen_fen. lia. Qed.

Lemma fsum_time t tC j jC :
  (cost (extract (fsum_cost stepsCM t tC) j jC) <= (Z.to_nat (Z.log2 (φ j)) + 1) * 100 + 40)%nat.
Proof. unfold fsum_cost. cost_simpl. zero_partials. gen_fen. lia. Qed.

Ltac gen_f2 :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (fadd_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
        let Hc := fresh "Hc" in
        pose proof (fadd_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (fsum_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hc" in
        pose proof (fsum_time a aC b bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma fval_time t tC a aC (X : Z) : (φ (a + 1) <= X)%Z ->
  (cost (extract (fval_cost stepsCM t tC) a aC) <= (Z.to_nat (Z.log2 X) + 1) * 200 + 150)%nat.
Proof.
  intros HX. unfold fval_cost. cost_simpl. zero_partials. gen_f2.
  assert (L : (Z.to_nat (Z.log2 (φ (a + 1))) <= Z.to_nat (Z.log2 X))%nat).
  { pose proof (to_Z_bounded (a + 1)). destruct (Z.eq_dec (φ (a + 1)) 0) as [E|E].
    - rewrite E. cbn. lia.
    - pose proof (Z.log2_le_mono (φ (a + 1)) X HX). lia. }
  destruct t; cbn. lia.
Qed.

Lemma imin_time a aC b bC : (cost (extract (imin_cost stepsCM a aC) b bC) <= 10)%nat.
Proof. unfold imin_cost. cost_simpl. cost_destruct (a <? b); cost_simpl; lia. Qed.

Ltac gen_imin :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (imin_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hc" in
        pose proof (imin_time a aC b bC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma insert_time NN NNC t tC i iC d dC :
  (cost (extract (extract (extract (insert_cost stepsCM NN NNC) t tC) i iC) d dC)
    <= (Z.to_nat (Z.log2 (φ NN)) + 1) * 500 + 400)%nat.
Proof.
  unfold insert_cost. cost_simpl. zero_partials. gen_imin. gen_f2.
  destruct t; cbn. lia.
Qed.

Fixpoint cnteqn (ts : array int) (t : Z) (p : nat) : nat :=
  match p with
  | O => O
  | S p' => ((if (φ (ts.[of_Z (Z.of_nat p')]) =? t)%Z then 1 else 0) + cnteqn ts t p')%nat
  end.

Lemma cnteq_pos : forall ts t k e, lastbn ts t k = (e + 1)%Z -> (0 <= e)%Z ->
  cnteqn ts t k = S (cnteqn ts t (Z.to_nat e)).
Proof.
  intros ts t k. induction k as [|k IH]; simpl lastbn; intros e H He; [lia|].
  simpl cnteqn. destruct ((φ (ts.[of_Z (Z.of_nat k)])) =? t)%Z eqn:E.
  - assert (e = Z.of_nat k) by lia. subst e. rewrite Nat2Z.id. lia.
  - rewrite (IH e H He). lia.
Qed.

Lemma cnteq_zero : forall ts t k, lastbn ts t k = 0%Z -> cnteqn ts t k = O.
Proof.
  intros ts t k. induction k as [|k IH]; simpl lastbn; intros H; [reflexivity|].
  simpl cnteqn. destruct ((φ (ts.[of_Z (Z.of_nat k)])) =? t)%Z eqn:E; [lia|].
  rewrite (IH H). reflexivity.
Qed.

Definition cnteq (ts : array int) (t p : Z) : nat := cnteqn ts t (Z.to_nat p).

Ltac gen_fval X HX :=
  repeat match goal with |- context [@cost ?T ?Y] =>
    lazymatch Y with
    | extract (fval_cost stepsCM ?a ?aC) ?b ?bC =>
        let Hc := fresh "Hc" in
        pose proof (fval_time a aC b bC X HX : (@cost T Y <= _)%nat) as Hc;
        revert Hc; generalize (@cost T Y); intros ? Hc
    end end.

Lemma walk_time ts as_ as_C next nextC t tC (m tau X : Z) :
  (forall e : int, (φ e < m)%Z -> φ (next.[e]) = lastb ts (φ (ts.[e])) (φ e)) ->
  (forall e : int, (φ e < m)%Z -> (φ (as_.[e] + 1) <= X)%Z) ->
  forall p' v vC ptr ptrC H HC, (0 <= p' <= m)%Z -> φ ptr = lastb ts tau p' ->
  (cost (extract (extract (extract (extract (extract (walk_cost stepsCM as_ as_C) next nextC) t tC) v vC) ptr ptrC) H HC)
    <= cnteq ts tau p' * ((Z.to_nat (Z.log2 X) + 1) * 200 + 300) + 20)%nat.
Proof.
  intros Hn Has p' v vC ptr ptrC H HC. unfold walk_cost. cbn.
  match goal with |- context [@cost ?T (?G as_ as_C next nextC t tC v vC ptr ptrC H HC)] =>
    assert (HG : forall N p' v vC ptr ptrC H HC, (Z.to_nat p' <= N)%nat -> (0 <= p' <= m)%Z -> φ ptr = lastb ts tau p' ->
       (cost (G as_ as_C next nextC t tC v vC ptr ptrC H HC)
         <= cnteq ts tau p' * ((Z.to_nat (Z.log2 X) + 1) * 200 + 300) + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros p2 v' vC' ptr' ptrC' [g] HC' HN Hp Hptr.
    cost_simpl.
    match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB end.
    cost_destruct (bdec (0 <? ptr')); cost_simpl; zero_partials; set_simpl; get_simpl.
    - pose proof (proj1 (ltb_spec _ _) e) as Hp0. change (φ 0) with 0%Z in Hp0.
      destruct (lastbn_pos ts tau (Z.to_nat p2) (φ ptr' - 1) ltac:(unfold lastb in Hptr; lia) ltac:(lia))
        as (P1 & P2 & P3).
      rewrite Z2Nat.id in P1, P3 by lia.
      assert (Ek : φ (ptr' - 1) = (φ ptr' - 1)%Z) by sia.
      assert (Hcnt : cnteq ts tau p2 = S (cnteq ts tau (φ ptr' - 1))).
      { unfold cnteq. apply cnteq_pos; [unfold lastb in Hptr; lia | lia]. }
      pose proof (Has (ptr' - 1) ltac:(lia)) as HX.
      gen_fval X HX.
      match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB2 end.
      cost_destruct (bdec (next.[ptr' - 1] <? ptr')); cost_simpl; zero_partials; set_simpl; get_simpl.
      + assert (Enx : φ (next.[ptr' - 1]) = lastb ts tau (φ ptr' - 1)).
        { rewrite Hn by lia. rewrite Ek. f_equal. rewrite <- (get_of_to_Z ts (ptr' - 1)), Ek. exact P2. }
        assert (HN2 : (Z.to_nat (φ ptr' - 1) < N)%nat) by lia.
        match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?v2 ?vC2 ?p3 ?pC3 ?a ?ee)] =>
          pose proof (IH _ HN2 (φ ptr' - 1)%Z v2 vC2 p3 pC3 a ee (le_n _) ltac:(lia) Enx
            : (@cost T (G' a1 a2 a3 a4 a5 a6 v2 vC2 p3 pC3 a ee) <= _)%nat) as HI;
          revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 v2 vC2 p3 pC3 a ee)); intros ? HI
        end.
        rewrite Hcnt. set (W := ((Z.to_nat (Z.log2 X) + 1) * 200 + 300)%nat) in *.
        rewrite Nat.mul_succ_l. lia.
      + rewrite Hcnt. set (W := ((Z.to_nat (Z.log2 X) + 1) * 200 + 300)%nat) in *.
        rewrite Nat.mul_succ_l. lia.
    - zero_pairs. lia. }
  intros Hp Hptr.
  match goal with |- context [@cost ?T (?G as_ as_C next nextC t tC v vC ptr ptrC H HC)] =>
    exact (HG _ p' v vC ptr ptrC H HC (le_n _) Hp Hptr : (@cost T (G as_ as_C next nextC t tC v vC ptr ptrC H HC) <= _)%nat) end.
Qed.

Arguments insert : simpl never.
Arguments walk : simpl never.
Arguments fval : simpl never.
Arguments fsum : simpl never.
Arguments fadd : simpl never.
Arguments sweep : simpl never.
Arguments build : simpl never.
Arguments tab : simpl never.
Arguments tab_loop : simpl never.
Arguments lsum_all : simpl never.
Arguments fam : simpl never.
Arguments manacher : simpl never.
Arguments man : simpl never.
Arguments expand : simpl never.
Arguments imin : simpl never.
Arguments hcond : simpl never.

Fixpoint cntgen (ts : array int) (t : Z) (p : nat) : nat :=
  match p with
  | O => O
  | S p' => ((if (t <=? φ (ts.[of_Z (Z.of_nat p')]))%Z then 1 else 0) + cntgen ts t p')%nat
  end.

Lemma cntge_split : forall ts t p, cntgen ts t p = (cnteqn ts t p + cntgen ts (t + 1) p)%nat.
Proof.
  intros ts t p. induction p as [|p IH]; [reflexivity|]. simpl.
  rewrite IH.
  destruct (Z.leb_spec t (φ (ts.[of_Z (Z.of_nat p)])));
  destruct (Z.eqb_spec (φ (ts.[of_Z (Z.of_nat p)])) t);
  destruct (Z.leb_spec (t + 1) (φ (ts.[of_Z (Z.of_nat p)]))); lia.
Qed.

Definition cntge (ts : array int) (t p : Z) : nat := cntgen ts t (Z.to_nat p).

Lemma sweep_arith ts (m : Z) (n1 tau : int) : (tau <? n1) = true ->
  Z.to_nat (gap n1 tau) = S (Z.to_nat (gap n1 (tau + 1))) /\
  cntge ts (φ tau) m = (cnteq ts (φ tau) m + cntge ts (φ (tau + 1)) m)%nat.
Proof.
  intros H. split; [exact (gap_S _ _ H)|].
  apply ltb_spec in H. assert (E : φ (tau + 1) = (φ tau + 1)%Z) by sia.
  rewrite E. unfold cntge, cnteq. apply cntge_split.
Qed.

Ltac gen_insert :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (insert_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
        let Hc := fresh "Hc" in
        pose proof (insert_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma sweep_time d dC as_ as_C head headC next nextC n nC n1 n1C NN NNC t tC v vC tau tauC H HC
    ts (m X : Z) :
  (0 <= m)%Z ->
  (forall e : int, (φ e < m)%Z -> φ (next.[e]) = lastb ts (φ (ts.[e])) (φ e)) ->
  (forall e : int, (φ e < m)%Z -> (φ (as_.[e] + 1) <= X)%Z) ->
  (forall t : int, (φ t < φ n1)%Z -> φ (head.[t]) = lastb ts (φ t) m) ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (sweep_cost stepsCM d dC) as_ as_C) head headC) next nextC) n nC) n1 n1C) NN NNC) t tC) v vC) tau tauC) H HC)
    <= Z.to_nat (gap n1 tau) * ((Z.to_nat (Z.log2 (φ NN)) + 1) * 500 + 600)
       + cntge ts (φ tau) m * ((Z.to_nat (Z.log2 X) + 1) * 200 + 300) + 20)%nat.
Proof.
  intros Hm Hn Has Hhead. unfold sweep_cost. cbn.
  set (W := ((Z.to_nat (Z.log2 X) + 1) * 200 + 300)%nat).
  set (S1 := ((Z.to_nat (Z.log2 (φ NN)) + 1) * 500 + 600)%nat).
  match goal with |- context [@cost ?T (?G d dC as_ as_C head headC next nextC n nC n1 n1C NN NNC t tC v vC tau tauC H HC)] =>
    assert (HG : forall N t tC v vC tau tauC H HC, (Z.to_nat (gap n1 tau) <= N)%nat ->
       (cost (G d dC as_ as_C head headC next nextC n nC n1 n1C NN NNC t tC v vC tau tauC H HC)
         <= Z.to_nat (gap n1 tau) * S1 + cntge ts (φ tau) m * W + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros t' tC' v' vC' tau' tauC' [g] HC' HN.
    cost_simpl.
    match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB end.
    cost_destruct (bdec (tau' <? n1)). cost_simpl. zero_partials. set_simpl. get_simpl.
    - pose proof (proj1 (ltb_spec _ _) e) as Ht.
      match goal with |- context [@cost ?T ?Y] =>
        lazymatch Y with
        | extract (extract (extract (extract (extract (walk_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?f ?fC) ?h ?hC =>
            let Hc := fresh "Hw" in
            pose proof (walk_time ts a aC b bC c cC m (φ tau') X Hn Has m d dC f fC h hC ltac:(lia) (Hhead tau' Ht)
              : (@cost T Y <= _)%nat) as Hc;
            revert Hc; generalize (@cost T Y); intros ? Hc
        end end.
      destruct (sweep_arith ts m n1 tau' e) as [A1 A2].
      assert (HN2 : (Z.to_nat (gap n1 (tau' + 1)) < N)%nat) by lia.
      cost_destruct (tau' <? n); cost_simpl; zero_partials; zero_pairs; gen_insert;
      match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?t2 ?tC2 ?v2 ?vC2 ?tau2 ?tauC2 ?a ?ee)] =>
        pose proof (IH _ HN2 t2 tC2 v2 vC2 tau2 tauC2 a ee (le_n _)
          : (@cost T (G' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 t2 tC2 v2 vC2 tau2 tauC2 a ee) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 t2 tC2 v2 vC2 tau2 tauC2 a ee)); intros ? HI
      end;
      rewrite A1, A2, Nat.mul_succ_l, Nat.mul_add_distr_r; unfold S1 in *; lia.
    - zero_pairs. lia. }
  match goal with |- context [@cost ?T (?G d dC as_ as_C head headC next nextC n nC n1 n1C NN NNC t tC v vC tau tauC H HC)] =>
    exact (HG _ t tC v vC tau tauC H HC (le_n _) : (@cost T (G d dC as_ as_C head headC next nextC n nC n1 n1C NN NNC t tC v vC tau tauC H HC) <= _)%nat) end.
Qed.

Lemma build_time ts tsC m mC k kC head headC next nextC H HC :
  (cost (extract (extract (extract (extract (extract (build_cost stepsCM ts tsC) m mC) k kC) head headC) next nextC) H HC)
    <= Z.to_nat (gap m k) * 50 + 20)%nat.
Proof.
  unfold build_cost. cbn.
  match goal with |- context [@cost ?T (?G ts tsC m mC k kC head headC next nextC H HC)] =>
    assert (HG : forall N k kC head headC next nextC H HC, (Z.to_nat (gap m k) <= N)%nat ->
       (cost (G ts tsC m mC k kC head headC next nextC H HC) <= Z.to_nat (gap m k) * 50 + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros k' kC' h' hC' n' nC' [g] HC' HN.
    cost_simpl.
    match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB end.
    cost_destruct (bdec (k' <? m)); cost_simpl; zero_partials; set_simpl; get_simpl.
    - assert (E : Z.to_nat (gap m k') = S (Z.to_nat (gap m (k' + 1)))) by exact (gap_S _ _ e).
      assert (HN2 : (Z.to_nat (gap m (k' + 1)) < N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?k2 ?kC2 ?h2 ?hC2 ?n2 ?nC2 ?a ?ee)] =>
        pose proof (IH _ HN2 k2 kC2 h2 hC2 n2 nC2 a ee (le_n _)
          : (@cost T (G' a1 a2 a3 a4 k2 kC2 h2 hC2 n2 nC2 a ee) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 k2 kC2 h2 hC2 n2 nC2 a ee)); intros ? HI
      end.
      lia.
    - zero_pairs. lia. }
  match goal with |- context [@cost ?T (?G ts tsC m mC k kC head headC next nextC H HC)] =>
    exact (HG _ k kC head headC next nextC H HC (le_n _) : (@cost T (G ts tsC m mC k kC head headC next nextC H HC) <= _)%nat) end.
Qed.

Ltac make_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.

Lemma tab_time n nC f fC K :
  (forall j jC, (cost (fC j jC) <= K)%nat) ->
  (cost (extract (tab_cost stepsCM n nC) f fC) <= zn n * (K + 40) + 40)%nat.
Proof.
  intros HK. unfold tab_cost. cost_simpl. zero_partials. make_simpl.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (tab_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
        pose proof (tab_loop_time a aC b bC c cC d dC e eC K HK : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.
  assert (E : Z.to_nat (gap n 0) = zn n) by (unfold gap, zn; change (φ 0) with 0%Z; f_equal; lia).
  rewrite E in Hc. lia.
Qed.

Lemma cntgen_le : forall ts t p, (cntgen ts t p <= p)%nat.
Proof. intros ts t p. induction p as [|p IH]; [simpl; lia|]. simpl. destruct (_ <=? _)%Z; lia. Qed.

Arguments fst_cost : simpl never.
Arguments snd_cost : simpl never.
Lemma fst_cost0 A AC B BC p w :
  cost (extract (extract (fst_cost stepsCM A AC) B BC) p w) = 1%nat.
Proof. destruct p; reflexivity. Qed.
Lemma snd_cost0 A AC B BC p w :
  cost (extract (extract (snd_cost stepsCM A AC) B BC) p w) = 1%nat.
Proof. destruct p; reflexivity. Qed.
Ltac gen_fstsnd :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (fst_cost stepsCM ?A ?AC) ?B ?BC) ?p ?w =>
        let Hc := fresh "Hf" in
        pose proof (fst_cost0 A AC B BC p w : (@cost T X = _)) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (snd_cost stepsCM ?A ?AC) ?B ?BC) ?p ?w =>
        let Hc := fresh "Hf" in
        pose proof (snd_cost0 A AC B BC p w : (@cost T X = _)) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma arith_lsum : forall a b c L L2 S, (c <= b)%nat -> (L2 <= L)%nat ->
  (S <= (a + 1) * ((L + 1) * 500 + 600) + c * ((L2 + 1) * 200 + 300) + 20)%nat ->
  (S + 50 * b + 200 <= (a + b + 1) * ((L + 1) * 1200) + 300)%nat.
Proof. intros. nia. Qed.

Definition LL (n : int) : nat := Z.to_nat (Z.log2 (φ n + 2)).
Arguments LL : simpl never.

Lemma lsum_all_time n nC m mC d dC as_ as_C ts tsC :
  ((φ n) <= 1000000)%Z -> ((φ m) <= 4194303)%Z ->
  (forall k : int, ((φ k) < (φ m))%Z -> ((φ (ts.[k])) <= (φ n))%Z /\ ((φ (as_.[k])) <= (φ n))%Z) ->
  (cost (extract (extract (extract (extract (lsum_all_cost stepsCM n nC) m mC) d dC) as_ as_C) ts tsC)
    <= (zn n + zn m + 1) * ((LL n + 1) * 1200) + 300)%nat.
Proof.
  intros Hn Hm Hts.
  assert (E1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  assert (E2 : (φ (n + 2)) = ((φ n) + 2)%Z) by sia.
  destruct (build_loop ts m (n + 1)
              ltac:(intros k Hk; destruct (Hts k Hk) as [A _]; eapply Z.le_lt_trans; [exact A | lia])
              _ 0 (PArray.make (n + 1) 0) (PArray.make m 0)
              (Zwf_well_founded 0 (gap m 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded m); lia)
              ltac:(apply alength_make_small; lia)
              ltac:(apply alength_make_small; lia)
              ltac:(intros t Ht; rewrite aget_make; reflexivity)
              ltac:(intros e He; change (φ 0) with 0%Z in He; pose proof (to_Z_bounded e); lia))
    as (B1 & B2 & B3 & B4).
  unfold lsum_all_cost. cost_simpl. zero_partials. make_simpl.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (extract (build_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
        pose proof (build_time a aC b bC c cC d dC e eC f fC : (@cost T X <= _)%nat) as Hb;
        revert Hb; generalize (@cost T X); intros ? Hb
    end end.
  zero_partials. gen_fstsnd.
  assert (Has : forall e : int, (φ e < φ m)%Z -> (φ (as_.[e] + 1) <= φ n + 1)%Z).
  { intros e He. destruct (Hts e He) as [_ A].
    assert (A' : (φ (as_.[e]) <= φ n)%Z) by exact A.
    pose proof (to_Z_bounded (as_.[e])). rewrite add_spec. change (φ 1) with 1%Z.
    rewrite Z.mod_small; [lia|]. rewrite wB_val. lia. }
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (sweep_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC) ?i ?iC) ?j ?jC) ?k ?kC =>
        pose proof (sweep_time a aC b bC c cC d dC e eC f fC g gC h hC i iC j jC k kC ts (φ m) (φ n + 1)
           ltac:(pose proof (to_Z_bounded m); lia) B4 Has B3 : (@cost T X <= _)%nat) as Hs;
        revert Hs; generalize (@cost T X); intros ? Hs
    end end.
  assert (G1 : Z.to_nat (gap (n + 1) 0) = (zn n + 1)%nat) by (unfold gap, zn; rewrite E1; change (φ 0) with 0%Z; pose proof (to_Z_bounded n); lia).
  assert (G2 : Z.to_nat (gap m 0) = zn m) by (unfold gap, zn; change (φ 0) with 0%Z; f_equal; lia).
  assert (G3 : (cntge ts (φ 0) (φ m) <= zn m)%nat) by (unfold cntge, zn; apply cntgen_le).
  assert (G4 : Z.to_nat (Z.log2 (φ (n + 2))) = LL n) by (unfold LL; rewrite E2; reflexivity).
  assert (G5 : (Z.to_nat (Z.log2 (φ n + 1)) <= LL n)%nat).
  { unfold LL. pose proof (to_Z_bounded n). pose proof (Z.log2_le_mono (φ n + 1) (φ n + 2) ltac:(lia)). lia. }
  rewrite G1, G4 in Hs. rewrite G2 in Hb.
  pose proof (arith_lsum (zn n) (zn m) _ (LL n) _ n3 G3 G5 Hs). subst n1 n2. lia.
Qed.

Lemma fam_time n nC m mC cnt cntC xl xlC xr xrC par parC rev revC :
  ((φ n) <= 1000000)%Z -> ((φ m) <= 4194303)%Z -> ((φ par) <= 1)%Z ->
  (forall k : int, ((φ k) < (φ m))%Z ->
     (1 <= (φ (xl.[k])) <= (φ (xr.[k])))%Z /\ ((φ (xr.[k])) <= (φ n))%Z) ->
  (cost (extract (extract (extract (extract (extract (extract (fam_cost stepsCM n nC) m mC) cnt cntC) xl xlC) xr xrC) par parC) rev revC)
    <= (zn n + zn m + 1) * ((LL n + 1) * 1200) + (zn n + zn m + zn m) * 80 + 500)%nat.
Proof.
  intros Hn Hm Hpar Hq.
  pose proof (to_Z_bounded par) as Bp.
  set (ts := tab m (fun k => if rev then n - ((xl.[k] + xr.[k] - par) >> 1)
                             else (xl.[k] + xr.[k] - par) >> 1)).
  set (as_ := tab m (fun k => if rev then n - (xr.[k] - par) else xl.[k] - 1)).
  destruct (tab_spec m (fun k => if rev then n - (xr.[k] - par) else xl.[k] - 1) Hm) as [Al Ac].
  destruct (tab_spec m (fun k => if rev then n - ((xl.[k] + xr.[k] - par) >> 1)
                                 else (xl.[k] + xr.[k] - par) >> 1) Hm) as [Tl Tc].
  fold as_ in Al, Ac. fold ts in Tl, Tc.
  assert (EH : forall k : int, ((φ k) < (φ m))%Z ->
     (φ ((xl.[k] + xr.[k] - par) >> 1)) = (((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) / 2)%Z).
  { intros k Hk. destruct (Hq k Hk). rewrite lsr1. f_equal. sia. }
  assert (Hts : forall k : int, ((φ k) < (φ m))%Z -> ((φ (ts.[k])) <= (φ n))%Z /\ ((φ (as_.[k])) <= (φ n))%Z).
  { intros k Hk. rewrite Tc, Ac by exact Hk. pose proof (EH k Hk) as E. destruct (Hq k Hk).
    pose proof (half_facts ((φ (xl.[k])) + (φ (xr.[k])) - (φ par)) ltac:(lia)).
    destruct rev.
    - split; [rewrite sub_spec, E; rewrite Z.mod_small; lia|]. sia.
    - split; [rewrite E; lia | sia]. }
  unfold fam_cost. cost_simpl. zero_partials.
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (tab_cost stepsCM ?a ?aC) ?f ?fC =>
        let Hc := fresh "Ht" in
        pose proof (tab_time a aC f fC 40 ltac:(intros j jC; destruct revC; cbn; lia) : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.
  fold ts as_.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (lsum_all_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
        pose proof (lsum_all_time a aC b bC c cC d dC e eC Hn Hm Hts : (@cost T X <= _)%nat) as Hl;
        revert Hl; generalize (@cost T X); intros ? Hl
    end end.
  lia.
Qed.

Lemma hcond_time x xC n nC q qC k kC :
  (cost (extract (extract (extract (hcond_cost stepsCM x xC) n nC) q qC) k kC) <= 60)%nat.
Proof.
  unfold hcond_cost. cost_simpl. zero_partials. gen_known.
  lia.
Qed.

Ltac gen_hcond :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (hcond_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
        let Hc := fresh "Hc" in
        pose proof (hcond_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Lemma zn_succ' (k n : int) : (k <? n) = true -> zn (k + 1) = S (zn k).
Proof. intros H. apply ltb_spec in H. unfold zn. assert (φ (k + 1) = φ k + 1)%Z by sia. lia. Qed.

Lemma expand_time x xC n nC q qC k kC H HC :
  (cost (extract (extract (extract (extract (expand_cost stepsCM x xC) n nC) q qC) k kC) H HC)
    + zn k * 100 <= zn (expand x n q k H) * 100 + 100)%nat.
Proof.
  unfold expand_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC q qC k kC H HC)] =>
    assert (HG : forall N k kC H HC, (Z.to_nat (gap n k) <= N)%nat ->
       (cost (G x xC n nC q qC k kC H HC) + zn k * 100 <= zn (expand x n q k H) * 100 + 100)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros k' kC' [g] HC' HN.
    cost_simpl.
    match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB end.
    rewrite expand_eq.
    cost_destruct (bdec (k' <? n)); cost_simpl; zero_partials; gen_hcond.
    - pose proof (zn_succ' _ _ e) as Ez.
      assert (HN2 : (Z.to_nat (gap n (k' + 1)) < N)%nat) by (pose proof (gap_S _ _ e); lia).
      cost_destruct (hcond x n q k'); cost_simpl.
      + match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?k2 ?kC2 ?a ?ee)] =>
          pose proof (IH _ HN2 k2 kC2 a ee (le_n _) : (@cost T (G' a1 a2 a3 a4 a5 a6 k2 kC2 a ee) + _ <= _)%nat) as HI;
          revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 k2 kC2 a ee)); intros ? HI
        end.
        lia.
      + lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC q qC k kC H HC)] =>
    exact (HG _ k kC H HC (le_n _) : (@cost T (G x xC n nC q qC k kC H HC) + _ <= _)%nat) end.
Qed.


Lemma expand_ge : forall x n q (z : Z) k (H : Acc (Zwf 0) (gap n k)),
  gap n k = z -> (φ k <= φ (expand x n q k H))%Z.
Proof.
  intros x n q z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k H Hz. rewrite expand_eq.
  destruct (bdec (k <? n)) as [Hk | Hk]; [|lia].
  pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
  assert (Ek : (φ (k + 1) = φ k + 1)%Z) by sia.
  destruct (hcond x n q k); [|lia].
  pose proof (IH (gap n (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hk)
                (k + 1) (Acc_inv H (dec_step n k Hk)) eq_refl). lia.
Qed.

Lemma mirror_back : forall x n Q rb q j,
  Sym x Q rb -> (rb <= Q + 1)%Z -> (rb <= n)%Z -> (Q < q)%Z -> (0 <= j)%Z -> ((q + 1) / 2 + j < rb)%Z ->
  Pk x n q j -> Pk x n (2 * Q - q) j.
Proof.
  intros x n Q rb q j HS Hrb Hrn HQq Hj Hjr (H0 & H1 & H2 & H3).
  assert (E1 : ((2 * Q - q) / 2 = Q - (q + 1) / 2)%Z) by (Z.to_euclidean_division_equations; lia).
  assert (E2 : ((2 * Q - q + 1) / 2 = Q - q / 2)%Z) by (Z.to_euclidean_division_equations; lia).
  assert (E3 : (q / 2 + (q + 1) / 2 = q)%Z) by (Z.to_euclidean_division_equations; lia).
  unfold Pk. rewrite E1, E2.
  refine (conj _ (conj _ (conj _ _))); [lia | lia | lia |].
  intros i Hi.
  pose proof (HS ((q + 1) / 2 + i)%Z ltac:(lia)) as A.
  pose proof (HS (q / 2 - i)%Z ltac:(lia)) as B.
  pose proof (H3 i Hi) as C.
  replace (Q - (q + 1) / 2 - i)%Z with (Q - ((q + 1) / 2 + i))%Z by lia.
  replace (Q - q / 2 + i)%Z with (Q - (q / 2 - i))%Z by lia.
  rewrite <- A, <- B. symmetry. exact C.
Qed.

Definition Inv x (nm n2 q : int) (cnt : array int) (Q rb : int) : Prop :=
  (φ q <= φ n2)%Z /\ φ (PArray.length cnt) = (2 * φ nm)%Z /\
  (forall q' : int, (φ q' < φ q)%Z -> forall j, (0 <= j)%Z ->
     (Pk x (φ nm) (φ q') j <-> (j < φ (cnt.[q']))%Z)) /\
  Sym x (φ Q) (φ rb) /\ (φ rb <= φ Q + 1)%Z /\ (φ rb <= φ nm)%Z /\ (φ Q <= φ n2)%Z /\
  (φ rb <= (φ q + 1) / 2 \/ φ Q < φ q)%Z.

Lemma man_step x (nm n2 q : int) cnt (Q rb : int) (k0 : int) (Hk : Acc (Zwf 0) (gap nm k0)) :
  (φ nm <= 33554432)%Z -> φ n2 = (2 * φ nm)%Z -> Inv x nm n2 q cnt Q rb -> (q <? n2) = true ->
  (((q + 1) >> 1 <? rb) = true /\ k0 = imin cnt.[Q + Q - q] (rb - ((q + 1) >> 1))
   \/ ((q + 1) >> 1 <? rb) = false /\ k0 = 0) ->
  let c := expand x nm q k0 Hk in
  (φ k0 <= φ c)%Z /\
  ((rb <? (q + 1) >> 1 + c) = true -> Inv x nm n2 (q + 1) cnt.[q <- c] q ((q + 1) >> 1 + c)
       /\ (φ c - φ k0 <= φ ((q + 1) >> 1 + c) - φ rb)%Z) /\
  ((rb <? (q + 1) >> 1 + c) = false -> Inv x nm n2 (q + 1) cnt.[q <- c] Q rb /\ (φ c <= φ k0)%Z).
Proof.
  intros Hnm Hn2 (Hqn & Hlen & Hinv & HS & Hrb1 & Hrb2 & HQ & Hdisj) Hq Hk0 c.
  pose proof (to_Z_bounded q) as Bq. pose proof (to_Z_bounded Q) as BQ.
  pose proof (to_Z_bounded rb) as Brb. pose proof (to_Z_bounded k0) as Bk0.
  pose proof Hq as Hq'. rewrite ltb_spec in Hq'.
  pose proof (half_facts (φ q) ltac:(lia)) as Hh.
  assert (Eq1 : (φ (q + 1)) = ((φ q) + 1)%Z) by sia.
  assert (Eb : (φ ((q + 1) >> 1)) = (((φ q) + 1) / 2)%Z) by (rewrite lsr1, Eq1; reflexivity).
  (* the mirror facts when bq < rb *)
  assert (Mir : ((q + 1) >> 1 <? rb) = true ->
     (φ Q < φ q)%Z /\ φ (Q + Q - q) = (2 * φ Q - φ q)%Z /\
     φ (rb - ((q + 1) >> 1)) = (φ rb - (φ q + 1) / 2)%Z).
  { intros Ebr. rewrite ltb_spec, Eb in Ebr.
    assert (HQq : ((φ Q) < (φ q))%Z) by lia.
    split; [exact HQq|]. split; [sia|].
    rewrite sub_spec, Eb; apply Z.mod_small; lia. }
  assert (Hk0' : forall j, (0 <= j < (φ k0))%Z -> Pk x (φ nm) (φ q) j).
  { destruct Hk0 as [[Ebr Ek] | [Ebr Ek]].
    - destruct (Mir Ebr) as (HQq & Eq' & Er). rewrite ltb_spec, Eb in Ebr.
      intros j Hj. rewrite Ek, imin_spec, Er in Hj.
      apply (mirror x (φ nm) (φ Q) (φ rb)); try assumption; try lia.
      rewrite <- Eq'. apply (Hinv (Q + Q - q)); [rewrite Eq'; lia | lia |]. lia.
    - intros j Hj. subst k0. change (φ 0) with 0%Z in Hj. lia. }
  assert (Hc : forall j, (0 <= j)%Z -> (Pk x (φ nm) (φ q) j <-> (j < (φ c))%Z)).
  { exact (expand_spec x nm q ltac:(lia) ltac:(lia) (gap nm k0) k0 Hk eq_refl Hk0'). }
  pose proof (to_Z_bounded c) as Bc.
  destruct (cnt_bound x (φ nm) (φ q) (φ c) ltac:(lia) ltac:(lia) Hc) as [Bc1 Bc2].
  assert (Ee : (φ ((q + 1) >> 1 + c)) = (((φ q) + 1) / 2 + (φ c))%Z)
    by (rewrite add_spec, Eb; apply Z.mod_small; rewrite wB_val; lia).
  assert (Hinv' : forall q' : int, ((φ q') < (φ (q + 1)))%Z -> forall j, (0 <= j)%Z ->
            (Pk x (φ nm) (φ q') j <-> (j < (φ (cnt.[q <- c].[q'])))%Z)).
  { intros q' Hq'' j Hj. rewrite Eq1 in Hq''.
    destruct (Z.eq_dec (φ q') (φ q)) as [E | E].
    - apply to_Z_eq in E. subst q'.
      rewrite aget_set_same by (rewrite ltb_spec, Hlen; lia). apply Hc. exact Hj.
    - rewrite aget_set_other by (apply int_eq_dec_Z; lia). apply Hinv; [lia | exact Hj]. }
  assert (Hlen' : (φ (PArray.length cnt.[q <- c])) = (2 * (φ nm))%Z) by (rewrite alength_set; exact Hlen).
  assert (Hge : (φ k0 <= φ c)%Z) by exact (expand_ge x nm q _ k0 Hk eq_refl).
  (* no extension past a mirror radius strictly inside the window *)
  assert (NoExt : ((q + 1) >> 1 <? rb) = true -> k0 = imin cnt.[Q + Q - q] (rb - ((q + 1) >> 1)) ->
                  (φ k0 < φ rb - (φ q + 1) / 2)%Z -> (φ c <= φ k0)%Z).
  { intros Ebr Ek Hlt. destruct (Mir Ebr) as (HQq & Eq' & Er).
    rewrite Ek, imin_spec, Er in Hlt |- *.
    destruct (Z.le_gt_cases (φ c) (Z.min (φ (cnt.[Q + Q - q])) (φ rb - (φ q + 1) / 2))) as [L|L]; [exact L|].
    exfalso. set (a := φ (cnt.[Q + Q - q])) in *.
    assert (Ea : Z.min a (φ rb - (φ q + 1) / 2) = a) by lia. rewrite Ea in L, Hlt.
    pose proof (to_Z_bounded (cnt.[Q + Q - q])) as Ba. fold a in Ba.
    assert (P1 : Pk x (φ nm) (φ q) a) by (apply Hc; lia).
    pose proof (mirror_back x (φ nm) (φ Q) (φ rb) (φ q) a HS Hrb1 Hrb2 HQq ltac:(lia) ltac:(lia) P1) as P2.
    rewrite <- Eq' in P2. apply (Hinv (Q + Q - q)) in P2; [lia | rewrite Eq'; lia | lia]. }
  split; [exact Hge|]. split.
  - intros Erb. rewrite ltb_spec, Ee in Erb.
    split.
    + refine (conj _ (conj Hlen' (conj Hinv' (conj _ (conj _ (conj _ (conj _ _))))))).
      * lia.
      * rewrite Ee. apply (sym_new x (φ nm)); [lia | exact Hc].
      * rewrite Ee. lia.
      * rewrite Ee. lia.
      * lia.
      * right. rewrite Eq1. lia.
    + rewrite Ee. destruct Hk0 as [[Ebr Ek] | [Ebr Ek]].
      * destruct (Mir Ebr) as (HQq & Eq' & Er).
        destruct (Z.lt_ge_cases (φ k0) (φ rb - (φ q + 1) / 2)) as [Lt|Ge].
        -- pose proof (NoExt Ebr Ek Lt). lia.
        -- lia.
      * rewrite <- Bool.not_true_iff_false, ltb_spec, Eb in Ebr. lia.
  - intros Erb. rewrite <- Bool.not_true_iff_false, ltb_spec, Ee in Erb.
    split.
    + refine (conj _ (conj Hlen' (conj Hinv' (conj HS (conj Hrb1 (conj Hrb2 (conj HQ _))))))).
      * lia.
      * rewrite Eq1. pose proof (half_facts ((φ q) + 1) ltac:(lia)). lia.
    + destruct Hk0 as [[Ebr Ek] | [Ebr Ek]].
      * destruct (Mir Ebr) as (HQq & Eq' & Er).
        destruct (Z.lt_ge_cases (φ k0) (φ rb - (φ q + 1) / 2)) as [Lt|Ge].
        -- exact (NoExt Ebr Ek Lt).
        -- lia.
      * rewrite <- Bool.not_true_iff_false, ltb_spec, Eb in Ebr. subst k0. change (φ 0) with 0%Z in *. lia.
Qed.

Lemma zn_amort (a b c d e : int) : (φ c - φ a <= φ d - φ b)%Z -> (φ a <= φ c)%Z -> (φ d <= φ e)%Z -> (φ b <= φ e)%Z ->
  (zn c + zn b <= zn a + zn d /\ zn d <= zn e /\ zn b <= zn e /\ zn a <= zn c)%nat.
Proof.
  intros. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded c).
  pose proof (to_Z_bounded d). unfold zn. lia.
Qed.

Lemma zn_noext (a b c e : int) : (φ c <= φ a)%Z -> (φ a <= φ c)%Z -> (φ b <= φ e)%Z ->
  (zn c = zn a /\ zn b <= zn e)%nat.
Proof. intros. unfold zn. split; [f_equal; lia | lia]. Qed.

Lemma man_time x xC nm nmC n2 n2C cnt cntC q qC Q QC rb rbC H HC :
  (φ nm <= 33554432)%Z -> φ n2 = (2 * φ nm)%Z -> Inv x nm n2 q cnt Q rb ->
  (cost (extract (extract (extract (extract (extract (extract (extract (man_cost stepsCM x xC) nm nmC) n2 n2C) cnt cntC) q qC) Q QC) rb rbC) H HC)
    <= Z.to_nat (gap n2 q) * 300 + (zn nm - zn rb) * 100 + 50)%nat.
Proof.
  intros Hnm Hn2. unfold man_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC nm nmC n2 n2C cnt cntC q qC Q QC rb rbC H HC)] =>
    assert (HG : forall N cnt cntC q qC Q QC rb rbC H HC, (Z.to_nat (gap n2 q) <= N)%nat ->
       Inv x nm n2 q cnt Q rb ->
       (cost (G x xC nm nmC n2 n2C cnt cntC q qC Q QC rb rbC H HC)
         <= Z.to_nat (gap n2 q) * 300 + (zn nm - zn rb) * 100 + 50)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros c' cC' q' qC' Q' QC' rb' rbC' [g] HC' HN HI.
    cost_simpl.
    match goal with |- context [bdec_cost stepsCM ?b ?w] => pose proof (bdec_time b w) as HB end.
    cost_destruct (bdec (q' <? n2)); cost_simpl; zero_partials; set_simpl; get_simpl.
    - gen_imin.
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with
        | extract (extract (extract (extract (expand_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?f ?fC =>
            pose proof (expand_time a aC b bC c cC d dC f fC : (@cost T X + _ <= _)%nat) as Hex;
            revert Hex; generalize (@cost T X); intros ? Hex
        end end.
      revert Hex.
      cost_destruct_eqn ((q' + 1) >> 1 <? rb') Ebr; intros Hex; cost_simpl; zero_partials; gen_imin;
      match goal with |- context [expand x nm q' ?d ?f] =>
        pose proof (man_step x nm n2 q' c' Q' rb' d f Hnm Hn2 HI e
                      ltac:(first [left; split; [exact Ebr | reflexivity] | right; split; [exact Ebr | reflexivity]])) as MS
      end;
      (match goal with |- context [expand ?xx ?nn q' ?d ?f] => set (cc := expand xx nn q' d f) in * end;
      destruct MS as (Mge & Mt & Mf);
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HI)))))) as Hrbn;
      pose proof (gap_S _ _ e) as Eg;
      (assert (HN2 : (Z.to_nat (gap n2 (q' + 1)) < N)%nat) by lia);
      cost_destruct_eqn (rb' <? (q' + 1) >> 1 + cc) Erb; cost_simpl; zero_partials; set_simpl;
      [ destruct (Mt eq_refl) as [HI2 Ham];
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HI2)))))) as Hrbn2;
        pose proof (zn_amort _ _ _ _ _ Ham Mge Hrbn2 Hrbn) as ZA
      | destruct (Mf eq_refl) as [HI2 Ham];
        pose proof (zn_noext _ _ _ _ Ham Mge Hrbn) as ZA ];
      (match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?c2 ?cC2 ?q2 ?qC2 ?Q2 ?QC2 ?r2 ?rC2 ?a ?ee)] =>
        pose proof (IH _ HN2 c2 cC2 q2 qC2 Q2 QC2 r2 rC2 a ee (le_n _) HI2
          : (@cost T (G' a1 a2 a3 a4 a5 a6 c2 cC2 q2 qC2 Q2 QC2 r2 rC2 a ee) <= _)%nat) as HIH;
        revert HIH; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 c2 cC2 q2 qC2 Q2 QC2 r2 rC2 a ee)); intros ? HIH
      end);
      lia).
    - zero_pairs. lia. }
  intros HI.
  match goal with |- context [@cost ?T (?G x xC nm nmC n2 n2C cnt cntC q qC Q QC rb rbC H HC)] =>
    exact (HG _ cnt cntC q qC Q QC rb rbC H HC (le_n _) HI : (@cost T (G x xC nm nmC n2 n2C cnt cntC q qC Q QC rb rbC H HC) <= _)%nat) end.
Qed.

Lemma manacher_time x xC :
  (2 * (φ (PrimString.length x)) <= 4194303)%Z ->
  (cost (manacher_cost stepsCM x xC) <= zn (PrimString.length x) * 700 + 100)%nat.
Proof.
  intros Hn.
  set (nm := PrimString.length x).
  assert (Hn' : (2 * (φ nm) <= 4194303)%Z) by exact Hn.
  pose proof (to_Z_bounded nm).
  assert (E2 : (φ (nm + nm)) = (2 * (φ nm))%Z) by sia.
  assert (HI : Inv x nm (nm + nm) 0 (PArray.make (nm + nm) 0) 0 0).
  { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); change (φ 0) with 0%Z; try lia.
    all: try (rewrite alength_make_small by lia; exact E2).
    all: intros a b; try (pose proof (to_Z_bounded a)); exfalso; lia. }
  unfold manacher_cost. cost_simpl. zero_partials. make_simpl.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (extract (extract (extract (man_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC =>
        pose proof (man_time a aC b bC c cC d dC e eC f fC g gC h hC ltac:(lia) E2 HI : (@cost T X <= _)%nat) as Hm;
        revert Hm; generalize (@cost T X); intros ? Hm
    end end.
  assert (G1 : Z.to_nat (gap (nm + nm) 0) = (zn nm * 2)%nat) by (unfold gap, zn; rewrite E2; change (φ 0) with 0%Z; lia).
  assert (G2 : zn 0 = 0%nat) by reflexivity.
  fold nm in Hm |- *. rewrite G1, G2 in Hm. lia.
Qed.

Lemma palindromes_impl_time x xC xl xlC xr xrC :
  (φ (PrimString.length x) <= 100000)%Z -> (φ (PArray.length xl) <= 4194303)%Z ->
  (forall k : int, ((φ k) < (φ (PArray.length xl)))%Z ->
     (1 <= (φ (xl.[k])) <= (φ (xr.[k])))%Z /\ ((φ (xr.[k])) <= (φ (PrimString.length x)))%Z) ->
  (cost (extract (extract (palindromes_impl_cost stepsCM x xC) xl xlC) xr xrC)
    <= (zn (PrimString.length x) + zn (PArray.length xl) + 1) * ((LL (PrimString.length x) + 1) * 1000 * 7) + 3000)%nat.
Proof.
  intros Hn Hm Hq.
  unfold palindromes_impl_cost. cost_simpl. zero_partials.
  match goal with |- context [@cost ?T (manacher_cost stepsCM x xC)] =>
    pose proof (manacher_time x xC ltac:(lia) : (@cost T (manacher_cost stepsCM x xC) <= _)%nat) as Hma;
    revert Hma; generalize (@cost T (manacher_cost stepsCM x xC)); intros ? Hma end.
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (extract (extract (fam_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
        let Hc := fresh "Hf" in
        pose proof (fam_time a aC b bC c cC d dC e eC f fC g gC ltac:(lia) Hm
                      ltac:(first [change (φ 0) with 0%Z; lia | change (φ 1) with 1%Z; lia]) Hq : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (tab_cost stepsCM ?a ?aC) ?f ?fC =>
        let Hc := fresh "Ht" in
        pose proof (tab_time a aC f fC 30 ltac:(intros j jC; cbn; lia) : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.
  repeat match goal with |- context [zn ?b] => match goal with H : context [zn ?a] |- _ =>
    tryif constr_eq a b then fail else (unify a b; change (zn a) with (zn b) in H) end end.
  lia.
Qed.

Lemma zlog2_nat k : (1 <= k)%nat -> (Z.log2 (Z.of_nat k) <= Z.of_nat (Nat.log2 k))%Z.
Proof.
  intros Hk. destruct (Nat.log2_spec k ltac:(lia)) as [_ H2].
  assert (H : (Z.of_nat k < 2 ^ Z.of_nat (S (Nat.log2 k)))%Z).
  { rewrite <- (Nat2Z.inj_pow 2). lia. }
  apply Z.log2_lt_pow2 in H; lia.
Qed.

Lemma LL_le (n : int) (b : nat) : (1 <= φ n)%Z -> (1 <= b)%nat ->
  (LL n <= Nat.log2 (zn n + b) + 1)%nat.
Proof.
  intros Hn Hb. unfold LL, zn.
  pose proof (zlog2_nat (Z.to_nat (φ n) + b) ltac:(lia)) as A.
  rewrite Nat2Z.inj_add, Z2Nat.id in A by lia.
  assert (B : (Z.log2 (φ n + 2) <= Z.log2 (φ n + Z.of_nat b) + 1)%Z).
  { pose proof (Z.log2_double (φ n + Z.of_nat b) ltac:(lia)) as D.
    pose proof (Z.log2_le_mono (φ n + 2) (2 * (φ n + Z.of_nat b)) ltac:(lia)). lia. }
  pose proof (Z.log2_nonneg (φ n + 2)). lia.
Qed.

Theorem palindromes_time : exists c1 c2 : nat,
  forall (name : String.string) (left_ends right_ends : list
  N)
  (name_str : PrimString.string)
  (left_ends_arr right_ends_arr : array uint),
  valid_input name left_ends right_ends ->
  repr name_str name ->
  repr left_ends_arr left_ends ->
  repr right_ends_arr right_ends ->
  (cost3 palindromes_cost name_str left_ends_arr right_ends_arr <= c1 * ((size name_str + size left_ends_arr + 1) * (Nat.log2 (size name_str + size left_ends_arr) + 1)) + c2)%nat.
Proof.
  exists (1000 * 14)%nat, 3000%nat.
  intros s ls rs x xl xr Hv Hx Hl Hr.
  match goal with |- (_ <= ?R)%nat => remember R as RHS eqn:ER end.
  pose proof Hv as Hv'. destruct Hv' as [_ Hvn Hvm Hvlr].
  unfold slen in Hvn. unfold len in Hvm.
  pose proof (Forall2_length Hvlr) as Hlr.
  assert (Hn : (φ (PrimString.length x)) = nlen s)
    by (destruct Hx as [H _]; unfold nlen; symmetry; exact H).
  pose proof (repr_len xl ls Hl) as Hml. pose proof (repr_len xr rs Hr) as Hmr.
  assert (Hcells : forall k : nat, (k < List.length ls)%nat ->
     (φ (xl.[of_Z (Z.of_nat k)])) = Z.of_N (nth k ls 0%N) /\
     (φ (xr.[of_Z (Z.of_nat k)])) = Z.of_N (nth k rs 0%N) /\
     (1 <= nth k ls 0%N <= nth k rs 0%N)%N /\ (nth k rs 0%N <= slen s)%N).
  { intros k Hk. split; [apply (repr_cell xl ls Hl k Hk)|].
    split; [apply (repr_cell xr rs Hr k ltac:(lia))|].
    assert (Hk2 : (k < List.length rs)%nat) by lia.
    pose proof (Forall2_nth_error _ _ _ _ _ k _ _ Hvlr (nth_error_nth' ls 0%N Hk)
                  (nth_error_nth' rs 0%N Hk2)) as [H1 H2].
    unfold slen. split; [exact H1 | exact H2]. }
  assert (Hnb : ((φ (PrimString.length x)) <= 100000)%Z) by (pose proof Hn as H; unfold nlen in H; lia).
  assert (Hn1 : (1 <= φ (PrimString.length x))%Z) by (pose proof Hn as H; unfold nlen in H; lia).
  assert (Hint : forall k : int, ((φ k) < (φ (PArray.length xl)))%Z -> k = of_Z (Z.of_nat (Z.to_nat (φ k)))).
  { intros k Hk. rewrite Z2Nat.id by (pose proof (to_Z_bounded k); lia). symmetry. apply of_to_Z. }
  assert (Hq : forall k : int, ((φ k) < (φ (PArray.length xl)))%Z ->
     (1 <= (φ (xl.[k])) <= (φ (xr.[k])))%Z /\ ((φ (xr.[k])) <= (φ (PrimString.length x)))%Z).
  { intros k Hk. rewrite (Hint k Hk).
    destruct (Hcells (Z.to_nat (φ k)) ltac:(lia)) as (H1 & H2 & H3 & H4).
    rewrite H1, H2. unfold slen in H4. pose proof Hn as Hn'. unfold nlen in Hn'. lia. }
  assert (Bm : ((φ (PArray.length xl)) <= 4194303)%Z) by lia.
  assert (Bm1 : (1 <= zn (PArray.length xl))%nat) by (unfold zn; lia).
  pose proof (palindromes_impl_time x (witness x) xl (witness xl) xr (witness xr) Hnb Bm Hq) as HT.
  pose proof (LL_le (PrimString.length x) (zn (PArray.length xl)) Hn1 Bm1) as HL.
  change (size x) with (zn (PrimString.length x)) in ER.
  change (size xl) with (zn (PArray.length xl)) in ER.
  unfold cost3. rewrite call_cost3_eq. unfold palindromes_cost.
  rewrite call_cost2_eq. zero_partials.
  match goal with |- (?A <= _)%nat => assert (EA : A = cost (extract (extract (palindromes_impl_cost stepsCM x (witness x)) xl (witness xl)) xr (witness xr))) by reflexivity end.
  rewrite EA. refine (Nat.le_trans _ _ _ HT _). subst RHS.
  do 5 try match goal with H : context [zn ?b] |- _ => match goal with |- context [zn ?a] =>
    tryif constr_eq a b then fail else (unify a b; change (zn a) with (zn b)) end end.
  set (a := zn (PrimString.length x)) in *. set (b := zn (PArray.length xl)) in *.
  set (L := LL (PrimString.length x)) in *. set (G := Nat.log2 (a + b)) in *.
  clearbody a b L G. nia.
Qed.

Print Assumptions palindromes_time.
