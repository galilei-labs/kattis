(* Correctness proofs for plot_implem.v. *)
(* Implementation of plot (plot.spec): the constants C_0, ..., C_n are the
   forward differences of p at 0, Delta^k p (0).

   Code.  [plot n y] (y = a_n, ..., a_0, length L = n+1) allocates one flat
   table d = [PArray.make L 0], fills d.[x] = p(x) for x = 0 .. L-1 by
   Horner's rule over y, then builds the difference table in place: stage
   s = 0 .. L-1 runs i from L-1 down to s+1 with d.[i] <- d.[i] - d.[i-1].
   After stage s, cell i holds Delta^(min i (s+1)) p (i - min i (s+1)), so at
   the end d.[k] = Delta^k p (0).  Everything is wrapping 63-bit [int]
   arithmetic; every value is exact modulo 2^63 and the final constants are
   bounded by 2^6 * 50 * 7 * 6^7 < 2^62, so the signed reading is exact.
   The degree argument n is not read: L is the length of y (= n+1).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap ...)] proof, as in template/polymul1.  The table is
   threaded linearly (each [set] on the latest version, its reads before
   it); y is only read.

   Proof.  Math side: [dk k f m] is Delta^k f (m); [polydeg d f] says
   Delta^(d+1) f = 0, closed under constants, sums, shifts and x * f; a
   polynomial with n+1 coefficients has [polydeg n].  The vector
   [Delta^0 f m; ...; Delta^n f m] is mapped by [step] to the same vector
   at m+1, so i iterations give f(i) at the head. *)

From Plot.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Plot Require Export plot_implem.
Open Scope uint63_scope.
Open Scope array_scope.


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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma horner_loop_eq : forall y len x j h H,
  horner_loop y len x j h H =
  match bdec (j <? len)%uint63 with
  | left Hj =>
      horner_loop y len x (j + 1) (h * x + y.[j])
        (Acc_inv H (dec_step len j Hj))
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma eval_loop_eq : forall y len x d H,
  eval_loop y len x d H =
  match bdec (x <? len) with
  | left Hx =>
      eval_loop y len (x + 1)
        d.[x <- horner_loop y len x 0 0 (Zwf_well_founded 0 (gap len 0))]
        (Acc_inv H (dec_step len x Hx))
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma diff_inner_eq : forall lo i d H,
  diff_inner lo i d H =
  match bdec (lo <? i) with
  | left Hi =>
      let v := d.[i] - d.[i - 1] in
      diff_inner lo (i - 1) d.[i <- v] (Acc_inv H (dec_down lo i Hi))
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma diff_outer_eq : forall len s d H,
  diff_outer len s d H =
  match bdec (s <? len)%uint63 with
  | left Hs =>
      diff_outer len (s + 1)
        (diff_inner s (len - 1) d (Zwf_well_founded 0 (gap (len - 1) s)))
        (Acc_inv H (dec_step len s Hs))
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Math side: finite differences                                       *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* Delta^k f (m). *)
Fixpoint dk (k : nat) (f : Z -> Z) (m : Z) : Z :=
  match k with
  | O => f m
  | S k' => dk k' f (m + 1) - dk k' f m
  end.

Lemma dk_comm : forall k f m,
  dk k (fun x => f (x + 1) - f x) m = dk (S k) f m.
Proof.
  induction k as [| k IH]; intros f m; [reflexivity|].
  cbn [dk]. rewrite !IH. reflexivity.
Qed.

(* Delta^(d+1) f = 0. *)
Fixpoint polydeg (d : nat) (f : Z -> Z) : Prop :=
  match d with
  | O => forall x, f x = f 0
  | S d' => polydeg d' (fun x => f (x + 1) - f x)
  end.

Lemma polydeg_ext : forall d f g,
  (forall x, f x = g x) -> polydeg d f -> polydeg d g.
Proof.
  induction d as [| d IH]; intros f g E H; cbn in *.
  - intros x. rewrite <- !E. apply H.
  - eapply IH; [| exact H]. intros x. cbv beta. rewrite !E. reflexivity.
Qed.

Lemma polydeg_const : forall d c, polydeg d (fun _ => c).
Proof.
  induction d as [| d IH]; intros c; cbn.
  - reflexivity.
  - eapply polydeg_ext; [| exact (IH 0)]. intros x. cbv beta. ring.
Qed.

Lemma polydeg_add : forall d f g,
  polydeg d f -> polydeg d g -> polydeg d (fun x => f x + g x).
Proof.
  induction d as [| d IH]; intros f g Hf Hg; cbn in *.
  - intros x. rewrite (Hf x), (Hg x). reflexivity.
  - eapply polydeg_ext; [| exact (IH _ _ Hf Hg)]. intros x. cbv beta. ring.
Qed.

Lemma polydeg_S : forall d f, polydeg d f -> polydeg (S d) f.
Proof.
  induction d as [| d IH]; intros f H.
  - cbn [polydeg] in *. intros x. rewrite (H (x + 1)), (H x), (H (0 + 1)). ring.
  - exact (IH _ H).
Qed.

Lemma polydeg_shift : forall d f, polydeg d f -> polydeg d (fun x => f (x + 1)).
Proof.
  induction d as [| d IH]; intros f H.
  - cbn [polydeg] in *. intros x. rewrite (H (x + 1)), (H (0 + 1)). reflexivity.
  - cbn in *. eapply polydeg_ext; [| exact (IH _ H)]. intros x. reflexivity.
Qed.

Lemma polydeg_mulx : forall d f, polydeg d f -> polydeg (S d) (fun x => x * f x).
Proof.
  induction d as [| d IH]; intros f H.
  - cbn [polydeg] in *. intros x. rewrite (H (x + 1)), (H x), (H (0 + 1)). ring.
  - change (polydeg (S d) (fun x => (x + 1) * f (x + 1) - x * f x)).
    eapply polydeg_ext with
      (f := fun x => x * (f (x + 1) - f x) + f (x + 1)).
    + intros x. ring.
    + apply polydeg_add.
      * apply (IH (fun x => f (x + 1) - f x)). exact H.
      * apply polydeg_shift. exact H.
Qed.

Lemma polydeg_dk : forall d f, polydeg d f -> forall m, dk (S d) f m = 0.
Proof.
  induction d as [| d IH]; intros f H m.
  - cbn in *. rewrite (H (m + 1)), (H m). ring.
  - rewrite <- dk_comm. apply IH. exact H.
Qed.

(* Polynomials. *)
Lemma pval_snoc : forall l c x, pval (l ++ [c]) x = x * pval l x + c.
Proof.
  induction l as [| d l IH]; intros c x; cbn [app pval].
  - cbn [List.length]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring.
  - rewrite IH, length_app. cbn [List.length].
    rewrite Nat.add_1_r, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma polydeg_pval : forall l c, polydeg (List.length l) (fun x => pval (l ++ [c]) x).
Proof.
  induction l as [| c0 l IH] using rev_ind; intros c.
  - cbn. intros x. ring.
  - rewrite length_app. cbn [List.length]. rewrite Nat.add_1_r.
    eapply polydeg_ext with (f := fun x => x * pval (l ++ [c0]) x + c).
    + intros x. rewrite (pval_snoc (l ++ [c0]) c x). reflexivity.
    + apply polydeg_add.
      * apply polydeg_mulx. apply IH.
      * apply polydeg_const.
Qed.

(* The vector [Delta^j f m; ...; Delta^(j+L-1) f m]. *)
Fixpoint vec (f : Z -> Z) (m : Z) (j : nat) (L : nat) : list Z :=
  match L with
  | O => []
  | S L' => dk j f m :: vec f m (S j) L'
  end.

Lemma vec_length : forall f m L j, List.length (vec f m j L) = L.
Proof. intros f m L. induction L as [| L IH]; intros j; cbn; [reflexivity | now rewrite IH]. Qed.

Lemma vec_nth : forall f m L j t, (t < L)%nat ->
  nth_error (vec f m j L) t = Some (dk (j + t) f m).
Proof.
  intros f m L. induction L as [| L IH]; intros j t Ht; [lia|].
  destruct t as [| t]; cbn.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma step_vec : forall f L j m,
  (forall m', dk (S (j + L)) f m' = 0) ->
  step (vec f m j (S L)) = vec f (m + 1) j (S L).
Proof.
  intros f L. induction L as [| L IH]; intros j m H.
  - cbn [vec step]. f_equal. specialize (H m). rewrite Nat.add_0_r in H.
    cbn [dk] in H. lia.
  - change (vec f m j (S (S L))) with (dk j f m :: vec f m (S j) (S L)).
    change (vec f (m + 1) j (S (S L)))
      with (dk j f (m + 1) :: vec f (m + 1) (S j) (S L)).
    change (vec f m (S j) (S L)) with (dk (S j) f m :: vec f m (S (S j)) L).
    cbn [step]. rewrite <- IH.
    + f_equal. cbn [dk]. ring.
    + intros m'. replace (S j + L)%nat with (j + S L)%nat by lia. apply H.
Qed.

Lemma iter_vec : forall f n,
  (forall m', dk (S n) f m' = 0) ->
  forall i : N, N.iter i step (vec f 0 0 (S n)) = vec f (Z.of_N i) 0 (S n).
Proof.
  intros f n H i. induction i as [| i IH] using N.peano_ind.
  - reflexivity.
  - rewrite N.iter_succ, IH, N2Z.inj_succ, <- Z.add_1_r.
    apply step_vec. exact H.
Qed.

(* Bounds. *)
Lemma dk_bound : forall k f m B,
  (forall t, m <= t <= m + Z.of_nat k -> Z.abs (f t) <= B) ->
  Z.abs (dk k f m) <= 2 ^ Z.of_nat k * B.
Proof.
  induction k as [| k IH]; intros f m B H.
  - cbn [dk]. change (2 ^ Z.of_nat 0) with 1. specialize (H m ltac:(lia)). lia.
  - cbn [dk]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (IH f (m + 1) B ltac:(intros t Ht; apply H; lia)) as H1.
    pose proof (IH f m B ltac:(intros t Ht; apply H; lia)) as H2.
    lia.
Qed.

Lemma pval_bound : forall a x,
  Forall (fun c => Z.abs c <= 50) a -> 0 <= x <= 6 ->
  Z.abs (pval a x) <= 50 * Z.of_nat (List.length a) * 6 ^ Z.of_nat (List.length a).
Proof.
  induction a as [| c r IH]; intros x Hf Hx; [cbn; lia|].
  inversion Hf as [| ? ? Hc Hr]; subst.
  cbn [pval List.length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  specialize (IH x Hr Hx).
  set (k := Z.of_nat (List.length r)) in *.
  assert (Hq0 : 0 <= x ^ k) by (apply Z.pow_nonneg; lia).
  assert (Hqp : x ^ k <= 6 ^ k) by (apply Z.pow_le_mono_l; lia).
  assert (Hk : 0 <= k) by lia.
  pose proof (Z.abs_triangle (c * x ^ k) (pval r x)).
  rewrite Z.abs_mul, (Z.abs_eq (x ^ k)) in H by lia.
  nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the input                                                   *)
(* ------------------------------------------------------------------ *)

Lemma repr_get : forall (x : array sint) (a : list Z), repr x a ->
  forall i : int, (φ i) < Z.of_nat (List.length a) ->
  Sint63.to_Z x.[i] = nth (Z.to_nat (φ i)) a 0.
Proof.
  intros x a [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hr.
  symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array sint) (a : list Z), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma sint_mod : forall v : int, Sint63.to_Z v mod wB = (φ v).
Proof. intros v. apply Sint63.to_Z_mod_Uint63to_Z. Qed.

Lemma firstn_S_nth : forall (a : list Z) j, (j < List.length a)%nat ->
  firstn (S j) a = firstn j a ++ [nth j a 0].
Proof.
  induction a as [| c a IH]; intros j Hj; cbn in Hj; [lia|].
  destruct j as [| j]; [reflexivity|].
  change (firstn (S (S j)) (c :: a)) with (c :: firstn (S j) a).
  rewrite (IH j) by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Horner and the evaluation loop                                      *)
(* ------------------------------------------------------------------ *)

Lemma horner_arith : forall P X c H C,
  H = P mod wB -> C mod wB = c mod wB ->
  ((H * X) mod wB + C) mod wB = (X * P + c) mod wB.
Proof.
  intros P X c H C EH EC. subst H.
  rewrite Zplus_mod_idemp_l.
  rewrite Zplus_mod, EC, <- Zplus_mod.
  rewrite Zplus_mod, Zmult_mod_idemp_l, <- Zplus_mod.
  rewrite (Z.mul_comm P X). reflexivity.
Qed.

Lemma horner_spec : forall (a : list Z) (y : array sint), repr y a ->
  forall len x : int, (φ len) = Z.of_nat (List.length a) ->
  forall (z : Z) (j h : int) (H : Acc (Zwf 0) (gap len j)),
  gap len j = z -> (φ j) <= (φ len) ->
  (φ h) = pval (firstn (Z.to_nat (φ j)) a) (φ x) mod wB ->
  (φ (horner_loop y len x j h H)) = pval a (φ x) mod wB.
Proof.
  intros a y Ha len x Hlen z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j h H Hz Hj Hh.
  rewrite horner_loop_eq.
  destruct (bdec (j <? len)%uint63) as [Hjl | Hjl].
  - pose proof Hjl as Hjl'. rewrite ltb_spec in Hjl'.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    pose proof (to_Z_bounded j) as Bj.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hjl.
    + rewrite Hj1, Z2Nat.inj_add, Nat.add_1_r by lia.
      rewrite firstn_S_nth by lia. rewrite pval_snoc.
      rewrite add_spec, mul_spec.
      apply horner_arith; [exact Hh|].
      rewrite <- sint_mod. rewrite Zmod_mod. f_equal.
      exact (repr_get y a Ha j ltac:(lia)).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hjl.
    replace (Z.to_nat (φ j)) with (List.length a) in Hh by lia.
    rewrite firstn_all in Hh. exact Hh.
Qed.

Lemma horner_full : forall (a : list Z) (y : array sint), repr y a ->
  forall x : int,
  (φ (horner_loop y (PArray.length y) x 0 0
       (Zwf_well_founded 0 (gap (PArray.length y) 0))))
  = pval a (φ x) mod wB.
Proof.
  intros a y Ha x.
  eapply horner_spec; [exact Ha | exact (repr_length y a Ha) | reflexivity | |].
  - change (φ 0) with 0. pose proof (to_Z_bounded (PArray.length y)). lia.
  - reflexivity.
Qed.

Lemma eval_spec : forall (a : list Z) (y : array sint), repr y a ->
  forall (z : Z) (x : int) (d : array int)
         (H : Acc (Zwf 0) (gap (PArray.length y) x)),
  gap (PArray.length y) x = z ->
  (φ x) <= (φ (PArray.length y)) ->
  PArray.length d = PArray.length y ->
  (forall t : int, (φ t) < (φ x) -> (φ (d.[t])) = pval a (φ t) mod wB) ->
  PArray.length (eval_loop y (PArray.length y) x d H) = PArray.length y
  /\ forall t : int, (φ t) < (φ (PArray.length y)) ->
     (φ ((eval_loop y (PArray.length y) x d H).[t])) = pval a (φ t) mod wB.
Proof.
  intros a y Ha z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x d H Hz Hx Hd Hinv.
  rewrite eval_loop_eq.
  destruct (bdec (x <? PArray.length y)%uint63) as [Hxl | Hxl].
  - pose proof Hxl as Hxl'. rewrite ltb_spec in Hxl'.
    assert (Hx1 : (φ (x + 1))%uint63 = (φ x) + 1) by sia.
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hxl.
    + rewrite alength_set. exact Hd.
    + intros t Ht. rewrite Hx1 in Ht.
      destruct (Z.eq_dec (φ t) (φ x)) as [E | E].
      * assert (t = x) by (apply to_Z_inj; exact E). subst t.
        rewrite aget_set_same by (rewrite Hd; exact Hxl).
        apply horner_full. exact Ha.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hxl.
    split; [exact Hd|]. intros t Ht. apply Hinv. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The difference table                                                *)
(* ------------------------------------------------------------------ *)

Section Table.

Variable P : Z -> Z.

(* The content of cell i after s stages. *)
Definition V (s i : Z) : Z :=
  if i <=? s then dk (Z.to_nat i) P 0 else dk (Z.to_nat s) P (i - s).

Lemma V_gen : forall s i, 0 <= s <= i -> V s i = dk (Z.to_nat s) P (i - s).
Proof.
  intros s i H. unfold V. destruct (Z.leb_spec i s); [|reflexivity].
  replace i with s by lia. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma V_0 : forall i, 0 <= i -> V 0 i = P i.
Proof. intros i H. rewrite V_gen by lia. cbn. f_equal. lia. Qed.

Lemma V_step : forall s i, 0 <= s < i -> V (s + 1) i = V s i - V s (i - 1).
Proof.
  intros s i H. rewrite !V_gen by lia.
  rewrite Z2Nat.inj_add, Nat.add_1_r by lia. cbn [dk].
  replace (i - (s + 1) + 1) with (i - s) by lia.
  replace (i - 1 - s) with (i - (s + 1)) by lia. reflexivity.
Qed.

Lemma V_low : forall s t, t <= s -> V s t = V (s + 1) t.
Proof.
  intros s t H. unfold V.
  destruct (Z.leb_spec t s), (Z.leb_spec t (s + 1)); lia || reflexivity.
Qed.

Lemma V_full : forall s t, 0 <= t <= s -> V s t = dk (Z.to_nat t) P 0.
Proof. intros s t H. unfold V. destruct (Z.leb_spec t s); [reflexivity | lia]. Qed.

Lemma inner_spec : forall (len s : int),
  forall (z : Z) (i : int) (d : array int) (H : Acc (Zwf 0) (gap i s)),
  gap i s = z ->
  (φ s) <= (φ i) -> (φ i) < (φ len) ->
  PArray.length d = len ->
  (forall t : int, (φ t) < (φ len) ->
     (φ (d.[t])) = (if (φ i) <? (φ t) then V ((φ s) + 1) (φ t) else V (φ s) (φ t)) mod wB) ->
  PArray.length (diff_inner s i d H) = len
  /\ forall t : int, (φ t) < (φ len) ->
     (φ ((diff_inner s i d H).[t])) = V ((φ s) + 1) (φ t) mod wB.
Proof.
  intros len s z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i d H Hz Hsi Hil Hd Hinv.
  rewrite diff_inner_eq.
  destruct (bdec (s <? i)%uint63) as [Hs | Hs].
  - pose proof Hs as Hs'. rewrite ltb_spec in Hs'.
    pose proof (to_Z_bounded s) as Bs.
    assert (Hi1 : (φ (i - 1))%uint63 = (φ i) - 1) by sia.
    cbv zeta.
    eapply IH; [ | reflexivity | lia | lia | | ].
    + rewrite <- Hz. apply dec_down. exact Hs.
    + rewrite alength_set. exact Hd.
    + intros t Ht. rewrite Hi1.
      destruct (Z.eq_dec (φ t) (φ i)) as [E | E].
      * assert (t = i) by (apply to_Z_inj; exact E). subst t.
        rewrite aget_set_same by (rewrite Hd, ltb_spec; exact Hil).
        replace ((φ i) - 1 <? (φ i)) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite sub_spec, (Hinv i Hil), (Hinv (i - 1)%uint63 ltac:(lia)).
        rewrite Hi1, Z.ltb_irrefl.
        replace ((φ i) <? (φ i) - 1) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite V_step by lia.
        rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        rewrite (Hinv t Ht).
        destruct (Z.ltb_spec (φ i) (φ t)), (Z.ltb_spec ((φ i) - 1) (φ t));
          try reflexivity; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hs.
    split; [exact Hd|]. intros t Ht. rewrite (Hinv t Ht).
    destruct (Z.ltb_spec (φ i) (φ t)); [reflexivity|].
    rewrite V_low by lia. reflexivity.
Qed.

Lemma outer_spec : forall (len : int),
  forall (z : Z) (s : int) (d : array int) (H : Acc (Zwf 0) (gap len s)),
  gap len s = z ->
  (φ s) <= (φ len) ->
  PArray.length d = len ->
  (forall t : int, (φ t) < (φ len) -> (φ (d.[t])) = V (φ s) (φ t) mod wB) ->
  PArray.length (diff_outer len s d H) = len
  /\ forall t : int, (φ t) < (φ len) ->
     (φ ((diff_outer len s d H).[t])) = V (φ len) (φ t) mod wB.
Proof.
  intros len z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros s d H Hz Hsl Hd Hinv.
  rewrite diff_outer_eq.
  destruct (bdec (s <? len)%uint63) as [Hs | Hs].
  - pose proof Hs as Hs'. rewrite ltb_spec in Hs'.
    pose proof (to_Z_bounded s) as Bs.
    assert (Hs1 : (φ (s + 1))%uint63 = (φ s) + 1) by sia.
    assert (Hl1 : (φ (len - 1))%uint63 = (φ len) - 1) by sia.
    destruct (inner_spec len s _ (len - 1)%uint63 d
                (Zwf_well_founded 0 (gap (len - 1)%uint63 s)) eq_refl
                ltac:(lia) ltac:(lia) Hd
                ltac:(intros t Ht; rewrite Hinv by exact Ht;
                      replace ((φ (len - 1))%uint63 <? (φ t)) with false
                        by (symmetry; apply Z.ltb_ge; lia);
                      reflexivity))
      as [Hd' Hinv'].
    eapply IH; [ | reflexivity | lia | exact Hd' | ].
    + rewrite <- Hz. apply dec_step. exact Hs.
    + intros t Ht. rewrite Hs1. apply Hinv'. exact Ht.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hs.
    split; [exact Hd|]. intros t Ht. rewrite Hinv by exact Ht.
    replace (φ s) with (φ len) by lia. reflexivity.
Qed.

End Table.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma dk_small : forall (n : N) (a : list Z), valid_input n a ->
  forall k : nat, (k < List.length a)%nat ->
  Z.abs (dk k (pval a) 0) < 4611686018427387904.
Proof.
  intros n a [Hn Hl Hc _] k Hk. unfold len in Hl.
  assert (Hla : (List.length a <= 7)%nat) by lia.
  pose proof (dk_bound k (pval a) 0
                (50 * Z.of_nat (List.length a) * 6 ^ Z.of_nat (List.length a))
                ltac:(intros t Ht; apply pval_bound; [exact Hc | lia])) as B.
  assert (H6 : 6 ^ Z.of_nat (List.length a) <= 6 ^ 7)
    by (apply Z.pow_le_mono_r; lia).
  assert (H2 : 2 ^ Z.of_nat k <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia).
  assert (H60 : 0 <= 6 ^ Z.of_nat (List.length a)) by (apply Z.pow_nonneg; lia).
  assert (H20 : 0 <= 2 ^ Z.of_nat k) by (apply Z.pow_nonneg; lia).
  change (2 ^ 6) with 64 in H2. change (6 ^ 7) with 279936 in H6.
  assert (HB : 50 * Z.of_nat (List.length a) * 6 ^ Z.of_nat (List.length a)
               <= 97977600) by nia.
  assert (HB0 : 0 <= 50 * Z.of_nat (List.length a) * 6 ^ Z.of_nat (List.length a))
    by nia.
  assert (HP : 2 ^ Z.of_nat k *
     (50 * Z.of_nat (List.length a) * 6 ^ Z.of_nat (List.length a))
     <= 64 * 97977600) by (apply Z.mul_le_mono_nonneg; lia).
  lia.
Qed.

Lemma out_correct : forall (n : N) (a : list Z) (r : array@{Set} sint) (L : int),
  valid_input n a ->
  PArray.length@{Set} r = L ->
  (φ L) = Z.of_nat (List.length a) ->
  (forall t : int, (φ t) < (φ L) ->
     (φ (PArray.get@{Set} r t)) = dk (Z.to_nat (φ t)) (pval a) 0 mod wB) ->
  repr r (vec (pval a) 0 0 (List.length a))
  /\ plot_spec n a (vec (pval a) 0 0 (List.length a)).
Proof.
  intros n a r L Hv Hrl0 HL Hrc0.
  assert (Hrl : PArray.length@{repr_array.u0} r = L) by exact Hrl0.
  assert (Hrc : forall t : int, (φ t) < (φ L) ->
     (φ (PArray.get@{repr_array.u0} r t)) = dk (Z.to_nat (φ t)) (pval a) 0 mod wB)
    by exact Hrc0.
  clear Hrl0 Hrc0.
  pose proof Hv as [Hn Hla _ Hlead]. unfold len in Hla.
  split.
  - split.
    + rewrite vec_length, Hrl, HL. reflexivity.
    + intros k Hk. rewrite vec_length in Hk.
      exists (dk k (pval a) 0). split; [apply vec_nth; exact Hk|].
      unfold repr, repr_sint.
      assert (Hk' : (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
      rewrite Sint63.to_Z_cmodwB, Hrc by (rewrite Hk', HL; lia).
      rewrite Sint63.cmod_mod, Hk', Nat2Z.id.
      apply Sint63.cmod_small.
      pose proof (dk_small n a Hv k Hk) as B.
      rewrite wB_val. change (9223372036854775808 / 2) with 4611686018427387904.
      lia.
  - split.
    + unfold len. rewrite vec_length. lia.
    + intros i. unfold plotted.
      destruct (exists_last (l := a)) as (l & c & El).
      { intro E. subst a. cbn in Hla. lia. }
      assert (Hdeg : forall m', dk (S (List.length l)) (pval a) m' = 0).
      { intros m'. apply polydeg_dk.
        eapply polydeg_ext; [| exact (polydeg_pval l c)].
        intros x. rewrite El. reflexivity. }
      assert (Ela : List.length a = S (List.length l))
        by (rewrite El, length_app; cbn; lia).
      rewrite Ela, iter_vec by exact Hdeg. reflexivity.
Qed.

Lemma plot_impl_correct : forall (n : N) (a : list Z) (x : uint) (y : array sint),
  valid_input n a -> repr x n -> repr y a ->
  exists c : list Z, repr (plot_impl x y) c /\ plot_spec n a c.
Proof.
  intros n a x y Hv Hx Ha.
  pose proof Hv as [Hn Hla _ _]. unfold len in Hla.
  pose proof (repr_length y a Ha) as Ly.
  pose proof (alength_bound y) as By.
  exists (vec (pval a) 0 0 (List.length a)).
  unfold plot_impl.
  set (len := PArray.length y) in *.
  assert (Hm : PArray.length (PArray.make len 0%uint63) = len).
  { rewrite alength_make.
    replace (len <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (eval_spec a y Ha _ 0 (PArray.make len 0%uint63)
              (Zwf_well_founded 0 (gap len 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) Hm
              ltac:(intros t Ht; change (φ 0) with 0%Z in Ht;
                    pose proof (to_Z_bounded t); lia))
    as [Hd1 Hc1].
  destruct (outer_spec (pval a) len _ 0 _ (Zwf_well_founded 0 (gap len 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded len); lia)
              Hd1
              ltac:(intros t Ht; change (φ 0) with 0%Z;
                    rewrite V_0 by (pose proof (to_Z_bounded t); lia);
                    apply Hc1; exact Ht))
    as [Hd2 Hc2].
  apply (out_correct n a _ len Hv Hd2 Ly).
  intros t Ht. rewrite Hc2 by exact Ht.
  rewrite V_full by (pose proof (to_Z_bounded t); lia). reflexivity.
Qed.

Definition plot_correct : forall (n : N) (a : list Z) (x : uint) (y : array sint),
  valid_input n a -> repr x n -> repr y a ->
  exists c : list Z, repr (plot x y) c /\ plot_spec n a c
  := plot_impl_correct.
