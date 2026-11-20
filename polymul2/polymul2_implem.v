(* Implementation of polymul2 (polymul2.spec): exact polynomial product by
   a binary64 complex FFT on split coefficients.

   Code.  Every coefficient c (a signed 32-bit integer) is split into SIX
   balanced 6-bit limbs, c = sum_{i<6} (d_i - 32) 64^i with d_i the base-64
   digits of c + KOFF (Uint63 shifts and masks).  N = 2^lg is the smallest
   power of two >= |a| + |b| - 1.  The 12 limb polynomials are transformed
   by a radix-2 Stockham FFT (natural order in and out, two pairs of flat
   float buffers used in ping-pong, all threaded linearly); the twiddles of
   stage s, w^k = exp(2 i pi k / 2^(s+1)), are built once per call from the
   stage s-1 table (even k: copy, odd k: one complex product by the base
   exp(2 i pi / 2^(s+1))), the bases by the sqrt half-angle recursion
   c' = sqrt((1 + c)/2), s' = s / (2 c').  For each g < 6 the pointwise sum
   P = sum_{i+j=2g} A_i B_j + I sum_{i+j=2g+1} A_i B_j is inverse-transformed
   (one complex inverse transform for two weights), scaled by 1/N, rounded
   to the nearest integer with the 1.5 * 2^52 trick and read back through
   frshiftexp / normfr_mantissa; the result cell accumulates
   D_2g 64^2g + D_(2g+1) 64^(2g+1) in wrapping Uint63 arithmetic.  No nat,
   no Z, no list in the code; loops terminate by an erased Acc on a Z gap.

   Proof.  Exact side (Parts A-C): complex numbers as pairs of reals, the
   stage map, its isometry (|.|^2 doubles), the composition of the lg stages
   is the DFT, orthogonality of the roots of unity, the Cauchy product.
   Rounded side (Parts D-E): the code is mirrored by functions over R built
   from rnd (ReprFloat); a butterfly errs by (5.43 eps + delta)(|u| + |v|),
   a stage by 2 alpha ||x|| in the 2-norm, the whole transform by
   sqrt(2)^lg (||x|| + 1) 0.78 sum_s alpha_s; the half-angle bases err by
   at most 4 eps (cos) and 7 eps (sin), the stage-s twiddles by 15.1 s eps.
   The final bound (FinalErr) is 0.2465 per output before scaling, with
   forward errors bounded through Cauchy-Schwarz in l1; the scaling and the
   rounding step keep it below 1/2.  Part G relates every loop to its
   mirror (repr on every cell), Part IntId reassembles the limbs into
   prod_coeff, the convolution formula, and the 63-bit word read as a
   signed integer is the exact coefficient by vi_product.  The spec states
   the product by evaluation (p(x) = a(x) * b(x) at every integer x, with
   the length); Part 0 states the convolution formula (the former spec's
   model) and proves that the list it defines is that product. *)

From Polymul2.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Sint63.
From StdGalilei Require Import repr repr_float.
From KattisLib Require Import Cost.
From Flocq Require Core.Core IEEE754.BinarySingleNaN IEEE754.PrimFloat.
Import ListNotations.

Unset Lia Cache.

Ltac zc := repeat (first [rewrite Nat2Z.inj_add | rewrite Nat2Z.inj_mul
                         | rewrite Nat2Z.inj_sub by lia]); simpl Z.of_nat.

(* ====================================================================== *)
(* Part 0.  The convolution formula, and that it defines the product      *)
(* ====================================================================== *)

(* The spec states the product by evaluation ([polymul_spec]: the length,
   and p(x) = a(x) * b(x) at every integer x).  The code and its proof
   produce the coefficients by the convolution formula
   ([coeff], [sum_below], [prod_coeff]); [pzconv] is
   the same convolution written structurally on the lists, [eval_pzconv]
   says it evaluates to the product, [nth_pzconv] that its cells are the
   [prod_coeff]. *)

Section Conv.
Open Scope Z_scope.

(* The coefficient of x^i in a ; zero beyond the degree. *)
Definition coeff (a : list Z) (i : N) : Z := nth (N.to_nat i) a 0.

(* f 0 + f 1 + ... + f (n - 1). *)
Fixpoint sum_below (f : N -> Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S m => sum_below f m + f (N.of_nat m)
  end.

(* The coefficient of x^k in the product : the sum of a_i * b_(k - i) for
   0 <= i <= k. *)
Definition prod_coeff (a b : list Z) (k : N) : Z :=
  sum_below (fun i => coeff a i * coeff b (k - i)%N) (N.to_nat (k + 1)%N).

(* Coefficient-wise sum, and the convolution, structurally on the lists. *)
Fixpoint pzadd (u v : list Z) : list Z :=
  match u, v with
  | [], _ => v
  | _, [] => u
  | c :: u', d :: v' => (c + d) :: pzadd u' v'
  end.

Fixpoint pzconv (a b : list Z) : list Z :=
  match a with
  | [] => []
  | c :: a' => pzadd (map (Z.mul c) b) (0 :: pzconv a' b)
  end.

Lemma eval_pzadd : forall u v x, eval (pzadd u v) x = eval u x + eval v x.
Proof.
  induction u as [|c u IH]; intros [|d v] x; simpl; try ring. rewrite IH. ring.
Qed.

Lemma eval_scale : forall c b x, eval (map (Z.mul c) b) x = c * eval b x.
Proof. intros c b x. induction b as [|d b IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma eval_pzconv : forall a b x, eval (pzconv a b) x = eval a x * eval b x.
Proof.
  induction a as [|c a IH]; intros b x; simpl; [ring|].
  rewrite eval_pzadd, eval_scale. simpl. rewrite IH. ring.
Qed.

Lemma length_pzadd : forall u v,
  List.length (pzadd u v) = Nat.max (List.length u) (List.length v).
Proof. induction u as [|c u IH]; intros [|d v]; simpl; try lia. rewrite IH. lia. Qed.

Lemma length_pzconv : forall a b, a <> [] -> b <> [] ->
  List.length (pzconv a b) = (List.length a + List.length b - 1)%nat.
Proof.
  induction a as [|c a IH]; intros b Ha Hb; [contradiction|].
  cbn [pzconv]. rewrite length_pzadd, length_map. cbn [List.length].
  destruct b as [|d b']; [contradiction|]. destruct a as [|c' a'].
  - cbn. lia.
  - rewrite IH by (first [exact Hb | discriminate]). cbn [List.length]. lia.
Qed.

Lemma nth_pzadd : forall u v k, nth k (pzadd u v) 0 = nth k u 0 + nth k v 0.
Proof. induction u as [|c u IH]; intros [|d v] [|k]; simpl; try ring. apply IH. Qed.

Lemma nth_scale : forall c b k, nth k (map (Z.mul c) b) 0 = c * nth k b 0.
Proof. intros c b. induction b as [|d b IH]; intros [|k]; simpl; try ring. apply IH. Qed.

Lemma sum_below_S : forall f n, sum_below f (S n) = sum_below f n + f (N.of_nat n).
Proof. reflexivity. Qed.

Lemma sum_below_ext : forall f g n, (forall i, f i = g i) -> sum_below f n = sum_below g n.
Proof.
  intros f g n H. induction n as [|n IH]; [reflexivity|].
  rewrite 2 sum_below_S, IH, H. reflexivity.
Qed.

Lemma sum_below_shift : forall f n,
  sum_below f (S n) = f 0%N + sum_below (fun i => f (i + 1)%N) n.
Proof.
  intros f n. induction n as [|n IH].
  - cbn. ring.
  - rewrite sum_below_S, IH, sum_below_S. cbv beta.
    rewrite Nat2N.inj_succ, N.add_1_r. ring.
Qed.

Lemma coeff_nil : forall i, coeff [] i = 0.
Proof. intros i. unfold coeff. destruct (N.to_nat i); reflexivity. Qed.

Lemma coeff_cons_succ : forall c a i, coeff (c :: a) (i + 1)%N = coeff a i.
Proof.
  intros c a i. unfold coeff. rewrite N2Nat.inj_add.
  change (N.to_nat 1) with 1%nat. rewrite Nat.add_1_r. reflexivity.
Qed.

Lemma prod_coeff_nil : forall b k, prod_coeff [] b k = 0.
Proof.
  intros b k. unfold prod_coeff.
  rewrite (sum_below_ext _ (fun _ => 0)) by (intros i; cbv beta; rewrite coeff_nil; ring).
  induction (N.to_nat (k + 1)%N) as [|n IH]; [reflexivity|].
  rewrite sum_below_S, IH. reflexivity.
Qed.

Lemma prod_coeff_cons : forall c a b k,
  prod_coeff (c :: a) b (N.of_nat (S k))
  = c * coeff b (N.of_nat (S k)) + prod_coeff a b (N.of_nat k).
Proof.
  intros c a b k. unfold prod_coeff.
  replace (N.to_nat (N.of_nat (S k) + 1)%N) with (S (S k)) by lia.
  replace (N.to_nat (N.of_nat k + 1)%N) with (S k) by lia.
  rewrite sum_below_shift. cbv beta. apply (f_equal2 Z.add).
  - reflexivity.
  - apply sum_below_ext. intros i. cbv beta. rewrite coeff_cons_succ.
    f_equal. f_equal. lia.
Qed.

Lemma nth_pzconv : forall a b k, nth k (pzconv a b) 0 = prod_coeff a b (N.of_nat k).
Proof.
  induction a as [|c a IH]; intros b k.
  - destruct k; cbn [pzconv nth]; rewrite prod_coeff_nil; reflexivity.
  - cbn [pzconv]. rewrite nth_pzadd, nth_scale. destruct k as [|k].
    + unfold prod_coeff.
      replace (N.to_nat (N.of_nat 0 + 1)%N) with 1%nat by reflexivity.
      rewrite sum_below_S. cbn [sum_below nth].
      unfold coeff. rewrite Nat2N.id, N.sub_diag.
      change (N.to_nat 0) with 0%nat. cbn [nth]. ring.
    + cbn [nth]. rewrite IH, prod_coeff_cons. unfold coeff. rewrite Nat2N.id. reflexivity.
Qed.

Lemma pzconv_is_product : forall a b, a <> [] -> b <> [] -> polymul_spec a b (pzconv a b).
Proof.
  intros a b Ha Hb. split.
  - unfold len. rewrite length_pzconv by assumption.
    rewrite Nat2N.inj_sub, Nat2N.inj_add. reflexivity.
  - intros x. apply eval_pzconv.
Qed.

End Conv.

(* ====================================================================== *)
(* Part A.  Finite real sums, complex numbers, vector norms               *)
(* ====================================================================== *)

Section RealSums.
Local Open Scope R_scope.

Lemma sq_nonneg : forall x : R, 0 <= x * x.
Proof. intros x. pose proof (Rle_0_sqr x). unfold Rsqr in *. lra. Qed.

Lemma Rabs_sq : forall x : R, Rabs x * Rabs x = x * x.
Proof. intros x. rewrite <- Rabs_mult. apply Rabs_pos_eq, sq_nonneg. Qed.

Fixpoint rsum (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => rsum f k + f k end.

Lemma rsum_ext : forall f g n, (forall i, (i < n)%nat -> f i = g i) -> rsum f n = rsum g n.
Proof.
  intros f g n; induction n as [|n IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma rsum_le : forall f g n, (forall i, (i < n)%nat -> f i <= g i) -> rsum f n <= rsum g n.
Proof.
  intros f g n; induction n as [|n IH]; intros H; simpl; [lra|].
  pose proof (IH ltac:(intros; apply H; lia)). pose proof (H n ltac:(lia)). lra.
Qed.

Lemma rsum_nonneg : forall f n, (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= rsum f n.
Proof.
  intros f n; induction n as [|n IH]; intros H; simpl; [lra|].
  pose proof (IH ltac:(intros; apply H; lia)). pose proof (H n ltac:(lia)). lra.
Qed.

Lemma rsum_plus : forall f g n, rsum (fun i => f i + g i) n = rsum f n + rsum g n.
Proof. intros f g n; induction n as [|n IH]; simpl; [lra|]. rewrite IH. ring. Qed.

Lemma rsum_minus : forall f g n, rsum (fun i => f i - g i) n = rsum f n - rsum g n.
Proof. intros f g n; induction n as [|n IH]; simpl; [lra|]. rewrite IH. ring. Qed.

Lemma rsum_scal : forall c f n, rsum (fun i => c * f i) n = c * rsum f n.
Proof. intros c f n; induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma rsum_const : forall c n, rsum (fun _ => c) n = INR n * c.
Proof.
  intros c n; induction n as [|n IH]; simpl rsum; [simpl; ring|].
  rewrite IH, S_INR. ring.
Qed.

Lemma rsum_zero : forall f n, (forall i, (i < n)%nat -> f i = 0) -> rsum f n = 0.
Proof.
  intros f n H. rewrite (rsum_ext f (fun _ => 0)) by exact H.
  rewrite rsum_const. ring.
Qed.

Lemma rsum_add_len : forall f n m, rsum f (n + m) = rsum f n + rsum (fun i => f (n + i)%nat) m.
Proof.
  intros f n m; induction m as [|m IH]; simpl.
  - rewrite Nat.add_0_r. ring.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. ring.
Qed.

Lemma rsum_block : forall f a b,
  rsum f (a * b) = rsum (fun q => rsum (fun r => f (b * q + r)%nat) b) a.
Proof.
  intros f a b; induction a as [|a IH]; simpl; [reflexivity|].
  replace (b + a * b)%nat with (a * b + b)%nat by lia.
  rewrite rsum_add_len, IH. f_equal. apply rsum_ext. intros i Hi. f_equal. lia.
Qed.

Lemma rsum_abs : forall f n, Rabs (rsum f n) <= rsum (fun i => Rabs (f i)) n.
Proof.
  intros f n; induction n as [|n IH]; simpl.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma rsum_swap : forall (f : nat -> nat -> R) n m,
  rsum (fun i => rsum (fun j => f i j) m) n = rsum (fun j => rsum (fun i => f i j) n) m.
Proof.
  intros f n; induction n as [|n IH]; intros m; simpl.
  - rewrite rsum_zero; [reflexivity | intros; reflexivity].
  - rewrite IH, <- rsum_plus. reflexivity.
Qed.

Lemma rsum_single : forall (f : nat -> R) k n, (k < n)%nat ->
  (forall i, (i < n)%nat -> i <> k -> f i = 0) -> rsum f n = f k.
Proof.
  intros f k n; induction n as [|n IH]; intros Hk H; [lia|]. simpl.
  destruct (Nat.eq_dec k n) as [->|E].
  - rewrite rsum_zero; [ring|]. intros i Hi. apply H; lia.
  - rewrite IH by (try lia; intros i Hi Hik; apply H; lia). rewrite (H n) by lia. ring.
Qed.

Lemma rsum_term_le : forall f n k, (k < n)%nat -> (forall i, (i < n)%nat -> 0 <= f i) ->
  f k <= rsum f n.
Proof.
  intros f n; induction n as [|n IH]; intros k Hk H; [lia|]. simpl.
  destruct (Nat.eq_dec k n) as [->|E].
  - pose proof (rsum_nonneg f n ltac:(intros; apply H; lia)). lra.
  - pose proof (IH k ltac:(lia) ltac:(intros; apply H; lia)). pose proof (H n ltac:(lia)). lra.
Qed.

Lemma rsum_mono_len : forall f n m, (n <= m)%nat -> (forall i, (i < m)%nat -> 0 <= f i) ->
  rsum f n <= rsum f m.
Proof.
  intros f n m Hnm H. replace m with (n + (m - n))%nat by lia.
  rewrite rsum_add_len. pose proof (rsum_nonneg (fun i => f (n + i)%nat) (m - n)
    ltac:(intros; apply H; lia)). lra.
Qed.

(* sums of squares of non-negative terms are at most the square of the sum *)
Lemma rsum_sq_le : forall f n, (forall i, (i < n)%nat -> 0 <= f i) ->
  rsum (fun i => f i * f i) n <= rsum f n * rsum f n.
Proof.
  intros f n; induction n as [|n IH]; intros H; simpl; [lra|].
  pose proof (IH ltac:(intros; apply H; lia)). pose proof (H n ltac:(lia)).
  pose proof (rsum_nonneg f n ltac:(intros; apply H; lia)). nra.
Qed.

(* Cauchy-Schwarz *)
Lemma cauchy_schwarz_sq : forall f g n,
  rsum (fun i => f i * g i) n * rsum (fun i => f i * g i) n
  <= rsum (fun i => f i * f i) n * rsum (fun i => g i * g i) n.
Proof.
  intros f g n.
  set (A := rsum (fun i => f i * f i) n). set (B := rsum (fun i => g i * g i) n).
  set (S := rsum (fun i => f i * g i) n).
  assert (Q : forall t, 0 <= A - 2 * t * S + t * t * B).
  { intros t.
    assert (E : rsum (fun i => (f i - t * g i) * (f i - t * g i)) n = A - 2 * t * S + t * t * B).
    { unfold A, B, S. rewrite <- (rsum_scal (t * t)), <- (rsum_scal (2 * t)).
      rewrite <- rsum_minus, <- rsum_plus. apply rsum_ext. intros; ring. }
    rewrite <- E. apply rsum_nonneg. intros. apply sq_nonneg. }
  assert (HB : 0 <= B) by (apply rsum_nonneg; intros; nra).
  assert (HA : 0 <= A) by (apply rsum_nonneg; intros; nra).
  destruct (Req_dec B 0) as [B0|Bn].
  - destruct (Req_dec S 0) as [S0|Sn].
    + rewrite S0, B0. nra.
    + exfalso. pose proof (Q ((A + 1) / (2 * S))) as Qt. rewrite B0 in Qt.
      replace (2 * ((A + 1) / (2 * S)) * S) with (A + 1) in Qt by (field; exact Sn). lra.
  - pose proof (Q (S / B)) as Qt.
    replace (A - 2 * (S / B) * S + S / B * (S / B) * B) with (A - S * S / B) in Qt
      by (field; exact Bn).
    assert (Bp : 0 < B) by lra.
    apply Rmult_le_compat_r with (r := B) in Qt; [|lra].
    replace ((A - S * S / B) * B) with (A * B - S * S) in Qt by (field; exact Bn). lra.
Qed.

Lemma sqrt_ge_abs : forall x y, x * x <= y -> Rabs x <= sqrt y.
Proof.
  intros x y H. rewrite <- sqrt_Rsqr_abs. apply sqrt_le_1_alt. unfold Rsqr. lra.
Qed.

Lemma sqrt_le_of_sq : forall x y, 0 <= y -> x <= y * y -> sqrt x <= y.
Proof.
  intros x y Hy H. rewrite <- (sqrt_square y Hy). apply sqrt_le_1_alt. exact H.
Qed.

Lemma cauchy_schwarz : forall f g n,
  rsum (fun i => f i * g i) n
  <= sqrt (rsum (fun i => f i * f i) n) * sqrt (rsum (fun i => g i * g i) n).
Proof.
  intros f g n.
  assert (HA : 0 <= rsum (fun i => f i * f i) n) by (apply rsum_nonneg; intros; nra).
  rewrite <- sqrt_mult_alt by exact HA.
  eapply Rle_trans; [apply Rle_abs | apply sqrt_ge_abs, cauchy_schwarz_sq].
Qed.

End RealSums.

(* ---------------------------------------------------------------------- *)
(* Complex numbers as pairs of reals                                      *)
(* ---------------------------------------------------------------------- *)

Section Complex.
Local Open Scope R_scope.

Definition C : Type := (R * R)%type.
Definition C0 : C := (0, 0).
Definition C1 : C := (1, 0).
Definition Cadd (a b : C) : C := (fst a + fst b, snd a + snd b).
Definition Csub (a b : C) : C := (fst a - fst b, snd a - snd b).
Definition Copp (a : C) : C := (- fst a, - snd a).
Definition Cmul (a b : C) : C := (fst a * fst b - snd a * snd b, fst a * snd b + snd a * fst b).
Definition Cscal (r : R) (a : C) : C := (r * fst a, r * snd a).
Definition Cconj (a : C) : C := (fst a, - snd a).
Definition Cmod2 (a : C) : R := fst a * fst a + snd a * snd a.
Definition Cmod (a : C) : R := sqrt (Cmod2 a).

Lemma Ceq : forall a b : C, fst a = fst b -> snd a = snd b -> a = b.
Proof. intros [a1 a2] [b1 b2]; simpl; intros -> ->; reflexivity. Qed.

Lemma Cmod2_nonneg : forall a, 0 <= Cmod2 a.
Proof. intros a. unfold Cmod2. nra. Qed.

Lemma Cmod_nonneg : forall a, 0 <= Cmod a.
Proof. intros a. apply sqrt_pos. Qed.

Lemma Cmod_sq : forall a, Cmod a * Cmod a = Cmod2 a.
Proof. intros a. apply sqrt_sqrt, Cmod2_nonneg. Qed.

Lemma Cmod2_mul : forall a b, Cmod2 (Cmul a b) = Cmod2 a * Cmod2 b.
Proof. intros a b. unfold Cmod2, Cmul; simpl. ring. Qed.

Lemma Cmod_mul : forall a b, Cmod (Cmul a b) = Cmod a * Cmod b.
Proof. intros a b. unfold Cmod. rewrite Cmod2_mul. apply sqrt_mult_alt, Cmod2_nonneg. Qed.

Lemma Cmod_le_of_sq : forall a x, 0 <= x -> Cmod2 a <= x * x -> Cmod a <= x.
Proof. intros a x Hx H. apply sqrt_le_of_sq; assumption. Qed.

Lemma Cmod_re : forall a, Rabs (fst a) <= Cmod a.
Proof. intros a. apply sqrt_ge_abs. unfold Cmod2. nra. Qed.

Lemma Cmod_im : forall a, Rabs (snd a) <= Cmod a.
Proof. intros a. apply sqrt_ge_abs. unfold Cmod2. nra. Qed.

Lemma Cmod_triangle : forall a b, Cmod (Cadd a b) <= Cmod a + Cmod b.
Proof.
  intros a b. apply Cmod_le_of_sq.
  - pose proof (Cmod_nonneg a). pose proof (Cmod_nonneg b). lra.
  - assert (H : Rabs (fst a * fst b + snd a * snd b) <= Cmod a * Cmod b).
    { unfold Cmod. rewrite <- sqrt_mult_alt by apply Cmod2_nonneg.
      apply sqrt_ge_abs. unfold Cmod2.
      pose proof (sq_nonneg (fst a * snd b - snd a * fst b)). nra. }
    pose proof (Rle_abs (fst a * fst b + snd a * snd b)).
    pose proof (Cmod_sq a). pose proof (Cmod_sq b).
    unfold Cmod2, Cadd in *; simpl in *. nra.
Qed.

Lemma Cmod_opp : forall a, Cmod (Copp a) = Cmod a.
Proof. intros a. unfold Cmod, Cmod2, Copp; simpl. f_equal. ring. Qed.

Lemma Cmod_conj : forall a, Cmod (Cconj a) = Cmod a.
Proof. intros a. unfold Cmod, Cmod2, Cconj; simpl. f_equal. ring. Qed.

Lemma Cmod_sub_sym : forall a b, Cmod (Csub a b) = Cmod (Csub b a).
Proof. intros a b. unfold Cmod, Cmod2, Csub; simpl. f_equal. ring. Qed.

Lemma Cmod_triangle_sub : forall a b, Cmod (Csub a b) <= Cmod a + Cmod b.
Proof.
  intros a b. replace (Csub a b) with (Cadd a (Copp b)) by (apply Ceq; simpl; ring).
  rewrite <- (Cmod_opp b). apply Cmod_triangle.
Qed.

Lemma Cmod_scal : forall r a, Cmod (Cscal r a) = Rabs r * Cmod a.
Proof.
  intros r a. unfold Cmod, Cmod2, Cscal; simpl.
  replace (r * fst a * (r * fst a) + r * snd a * (r * snd a))
    with ((r * r) * (fst a * fst a + snd a * snd a)) by ring.
  rewrite sqrt_mult_alt by nra. f_equal.
  rewrite <- sqrt_Rsqr_abs. reflexivity.
Qed.

Lemma Cmod_le_reim : forall a, Cmod a <= Rabs (fst a) + Rabs (snd a).
Proof.
  intros a. apply Cmod_le_of_sq.
  - pose proof (Rabs_pos (fst a)). pose proof (Rabs_pos (snd a)). lra.
  - unfold Cmod2. pose proof (Rabs_pos (fst a)). pose proof (Rabs_pos (snd a)).
    pose proof (Rabs_sq (fst a)). pose proof (Rabs_sq (snd a)). nra.
Qed.

Definition sq2 : R := sqrt 2.

Lemma sq2_sq : sq2 * sq2 = 2.
Proof. apply sqrt_sqrt. lra. Qed.

Lemma sq2_bounds : 1.4142 <= sq2 <= 1.4143.
Proof.
  pose proof sq2_sq. assert (0 <= sq2) by apply sqrt_pos. split; nra.
Qed.

Lemma reim_le : forall a, Rabs (fst a) + Rabs (snd a) <= sq2 * Cmod a.
Proof.
  intros a. unfold sq2, Cmod. rewrite <- sqrt_mult_alt by lra.
  rewrite <- (Rabs_pos_eq (Rabs (fst a) + Rabs (snd a)))
    by (pose proof (Rabs_pos (fst a)); pose proof (Rabs_pos (snd a)); lra).
  apply sqrt_ge_abs. unfold Cmod2.
  pose proof (Rabs_sq (fst a)). pose proof (Rabs_sq (snd a)).
  pose proof (sq_nonneg (Rabs (fst a) - Rabs (snd a))).
  nra.
Qed.

Definition csum (f : nat -> C) (n : nat) : C :=
  (rsum (fun i => fst (f i)) n, rsum (fun i => snd (f i)) n).

Lemma csum_S : forall f n, csum f (S n) = Cadd (csum f n) (f n).
Proof. intros f n. reflexivity. Qed.

Lemma csum_0 : forall f, csum f 0 = C0.
Proof. intros f. reflexivity. Qed.

Lemma csum_ext : forall f g n, (forall i, (i < n)%nat -> f i = g i) -> csum f n = csum g n.
Proof.
  intros f g n H. unfold csum. f_equal; apply rsum_ext; intros i Hi; rewrite H by exact Hi; reflexivity.
Qed.

Lemma Cmod_csum : forall f n, Cmod (csum f n) <= rsum (fun i => Cmod (f i)) n.
Proof.
  intros f n; induction n as [|n IH].
  - unfold Cmod, Cmod2; simpl. replace (0 * 0 + 0 * 0) with 0 by ring. rewrite sqrt_0. lra.
  - rewrite csum_S. simpl rsum. eapply Rle_trans; [apply Cmod_triangle|]. lra.
Qed.

End Complex.

(* ---------------------------------------------------------------------- *)
(* Complex vectors and their Euclidean norm                               *)
(* ---------------------------------------------------------------------- *)

Section Vectors.
Local Open Scope R_scope.

Definition vec := nat -> C.
Definition vadd (x y : vec) : vec := fun i => Cadd (x i) (y i).
Definition vsub (x y : vec) : vec := fun i => Csub (x i) (y i).
Definition nsq (n : nat) (x : vec) : R := rsum (fun i => Cmod2 (x i)) n.
Definition nrm (n : nat) (x : vec) : R := sqrt (nsq n x).

Lemma nsq_nonneg : forall n x, 0 <= nsq n x.
Proof. intros n x. apply rsum_nonneg. intros; apply Cmod2_nonneg. Qed.

Lemma nrm_nonneg : forall n x, 0 <= nrm n x.
Proof. intros. apply sqrt_pos. Qed.

Lemma nrm_sq : forall n x, nrm n x * nrm n x = nsq n x.
Proof. intros. apply sqrt_sqrt, nsq_nonneg. Qed.

Lemma nsq_ext : forall n x y, (forall i, (i < n)%nat -> x i = y i) -> nsq n x = nsq n y.
Proof. intros n x y H. apply rsum_ext. intros i Hi. rewrite H by exact Hi. reflexivity. Qed.

Lemma nrm_ext : forall n x y, (forall i, (i < n)%nat -> x i = y i) -> nrm n x = nrm n y.
Proof. intros n x y H. unfold nrm. rewrite (nsq_ext n x y H). reflexivity. Qed.

Lemma cs_vec : forall n x y,
  rsum (fun i => Cmod (x i) * Cmod (y i)) n <= nrm n x * nrm n y.
Proof.
  intros n x y. eapply Rle_trans; [apply cauchy_schwarz|].
  unfold nrm, nsq. right. f_equal; f_equal; apply rsum_ext; intros; apply Cmod_sq.
Qed.

Lemma nrm_add : forall n x y, nrm n (vadd x y) <= nrm n x + nrm n y.
Proof.
  intros n x y. unfold nrm at 1. apply sqrt_le_of_sq.
  - pose proof (nrm_nonneg n x). pose proof (nrm_nonneg n y). lra.
  - pose proof (cs_vec n x y) as Hcs. pose proof (nrm_sq n x). pose proof (nrm_sq n y).
    assert (E : nsq n (vadd x y) <= rsum (fun i => Cmod2 (x i) + Cmod2 (y i)
                 + 2 * (Cmod (x i) * Cmod (y i))) n).
    { apply rsum_le. intros i Hi. unfold vadd.
      pose proof (Cmod_triangle (x i) (y i)) as T.
      pose proof (Cmod_nonneg (Cadd (x i) (y i))).
      rewrite <- (Cmod_sq (Cadd (x i) (y i))), <- (Cmod_sq (x i)), <- (Cmod_sq (y i)).
      pose proof (Cmod_nonneg (x i)). pose proof (Cmod_nonneg (y i)). nra. }
    rewrite !rsum_plus, rsum_scal in E. fold (nsq n x) (nsq n y) in E. nra.
Qed.

Lemma nrm_sub_tri : forall n x y z, nrm n (vsub x z) <= nrm n (vsub x y) + nrm n (vsub y z).
Proof.
  intros n x y z. eapply Rle_trans; [|apply nrm_add].
  right. apply nrm_ext. intros i Hi. unfold vsub, vadd. apply Ceq; simpl; ring.
Qed.

Lemma nrm_le_of_sq : forall n x B, 0 <= B -> nsq n x <= B * B -> nrm n x <= B.
Proof. intros n x B HB H. apply sqrt_le_of_sq; assumption. Qed.

(* a pointwise bound alpha * s_i + beta *)
Lemma nrm_pointwise : forall n x (s : nat -> R) alpha beta,
  0 <= alpha -> 0 <= beta -> (forall i, (i < n)%nat -> 0 <= s i) ->
  (forall i, (i < n)%nat -> Cmod (x i) <= alpha * s i + beta) ->
  nrm n x <= alpha * sqrt (rsum (fun i => s i * s i) n) + beta * sqrt (INR n).
Proof.
  intros n x s alpha beta Ha Hb Hs H.
  set (u := fun i : nat => ((alpha * s i)%R, 0%R) : C).
  set (w := fun _ : nat => (beta, 0%R) : C).
  assert (E1 : nrm n x <= nrm n (vadd u w)).
  { apply sqrt_le_1_alt. apply rsum_le. intros i Hi. unfold vadd.
    rewrite <- (Cmod_sq (x i)). unfold u, w, Cmod2, Cadd; simpl.
    pose proof (H i Hi) as Hi'. pose proof (Hs i Hi). pose proof (Cmod_nonneg (x i)).
    nra. }
  assert (E2 : nrm n u = alpha * sqrt (rsum (fun i => s i * s i) n)).
  { unfold nrm, nsq, u, Cmod2; simpl.
    rewrite (rsum_ext _ (fun i => (alpha * alpha) * (s i * s i))) by (intros; ring).
    rewrite rsum_scal, sqrt_mult_alt by nra. rewrite sqrt_square by exact Ha. reflexivity. }
  assert (E3 : nrm n w = beta * sqrt (INR n)).
  { unfold nrm, nsq, w, Cmod2; simpl. rewrite rsum_const.
    replace (INR n * (beta * beta + 0 * 0)) with ((beta * beta) * INR n) by ring.
    rewrite sqrt_mult_alt by nra. rewrite sqrt_square by exact Hb. reflexivity. }
  pose proof (nrm_add n u w). lra.
Qed.

Lemma nrm_elem : forall n x i, (i < n)%nat -> Cmod (x i) <= nrm n x.
Proof.
  intros n x i Hi. unfold Cmod, nrm. apply sqrt_le_1_alt.
  apply (rsum_term_le (fun i => Cmod2 (x i))); [exact Hi | intros; apply Cmod2_nonneg].
Qed.

Lemma nrm_le_l1 : forall n x, nrm n x <= rsum (fun i => Cmod (x i)) n.
Proof.
  intros n x. apply sqrt_le_of_sq; [apply rsum_nonneg; intros; apply Cmod_nonneg|].
  eapply Rle_trans; [|apply rsum_sq_le; intros; apply Cmod_nonneg].
  right. apply rsum_ext. intros. symmetry. apply Cmod_sq.
Qed.

End Vectors.

(* ---------------------------------------------------------------------- *)
(* Complex sums                                                           *)
(* ---------------------------------------------------------------------- *)

Section CSums.
Local Open Scope R_scope.

Lemma rsum_scal_r : forall c f n, rsum (fun i => f i * c) n = rsum f n * c.
Proof. intros c f n. rewrite (rsum_ext _ (fun i => c * f i)) by (intros; ring). rewrite rsum_scal. ring. Qed.

Lemma Cmul_csum_r : forall f n c, Cmul (csum f n) c = csum (fun i => Cmul (f i) c) n.
Proof.
  intros f n c. apply Ceq; unfold Cmul, csum; simpl.
  - rewrite rsum_minus, !rsum_scal_r. reflexivity.
  - rewrite rsum_plus, !rsum_scal_r. reflexivity.
Qed.

Lemma Cmul_csum_l : forall c f n, Cmul c (csum f n) = csum (fun i => Cmul c (f i)) n.
Proof.
  intros c f n. apply Ceq; unfold Cmul, csum; simpl.
  - rewrite rsum_minus, !rsum_scal. reflexivity.
  - rewrite rsum_plus, !rsum_scal. reflexivity.
Qed.

Lemma Cscal_csum : forall r f n, Cscal r (csum f n) = csum (fun i => Cscal r (f i)) n.
Proof. intros r f n. apply Ceq; unfold Cscal, csum; simpl; rewrite rsum_scal; reflexivity. Qed.

Lemma csum_swap : forall (F : nat -> nat -> C) n m,
  csum (fun i => csum (fun j => F i j) m) n = csum (fun j => csum (fun i => F i j) n) m.
Proof. intros F n m. apply Ceq; unfold csum; simpl; apply rsum_swap. Qed.

Lemma csum_add : forall f g n, csum (fun i => Cadd (f i) (g i)) n = Cadd (csum f n) (csum g n).
Proof. intros f g n. apply Ceq; unfold csum, Cadd; simpl; apply rsum_plus. Qed.

Lemma csum_sub : forall f g n, csum (fun i => Csub (f i) (g i)) n = Csub (csum f n) (csum g n).
Proof. intros f g n. apply Ceq; unfold csum, Csub; simpl; apply rsum_minus. Qed.

Lemma Csub_csum_add : forall a f n, Csub a (csum f n) = Cadd a (csum (fun i => Copp (f i)) n).
Proof.
  intros a f n. apply Ceq; unfold Csub, Cadd, Copp, csum; simpl.
  - rewrite (rsum_ext (fun i => - fst (f i)) (fun i => -1 * fst (f i))) by (intros; ring).
    rewrite rsum_scal. ring.
  - rewrite (rsum_ext (fun i => - snd (f i)) (fun i => -1 * snd (f i))) by (intros; ring).
    rewrite rsum_scal. ring.
Qed.

Lemma csum_zero : forall f n, (forall i, (i < n)%nat -> f i = C0) -> csum f n = C0.
Proof.
  intros f n H. apply Ceq; unfold csum; simpl; apply rsum_zero; intros i Hi; rewrite H by exact Hi; reflexivity.
Qed.

Lemma csum_add_len : forall f n m,
  csum f (n + m) = Cadd (csum f n) (csum (fun i => f (n + i)%nat) m).
Proof. intros f n m. apply Ceq; unfold csum, Cadd; simpl; apply rsum_add_len. Qed.

Lemma csum_single : forall f k n, (k < n)%nat ->
  (forall i, (i < n)%nat -> i <> k -> f i = C0) -> csum f n = f k.
Proof.
  intros f k n Hk H. apply Ceq; unfold csum; simpl.
  - apply (rsum_single (fun i => fst (f i)) k n Hk). intros i Hi Hik; rewrite H by assumption; reflexivity.
  - apply (rsum_single (fun i => snd (f i)) k n Hk). intros i Hi Hik; rewrite H by assumption; reflexivity.
Qed.

Lemma rsum_triangle : forall (F : nat -> nat -> R) n,
  rsum (fun q => rsum (fun t => F t (q - t)%nat) (S q)) n
  = rsum (fun t => rsum (fun m => F t m) (n - t)) n.
Proof.
  intros F n; induction n as [|n IH]; [reflexivity|].
  transitivity (rsum (fun q => rsum (fun t => F t (q - t)%nat) (S q)) n
                + rsum (fun t => F t (n - t)%nat) (S n)); [reflexivity|].
  rewrite IH.
  rewrite (rsum_ext (fun t => rsum (fun m => F t m) (S n - t)) (fun t => rsum (fun m => F t m) (n - t) + F t (n - t)%nat)).
  - simpl rsum at 3. rewrite rsum_plus. replace (S n - n)%nat with 1%nat by lia.
    simpl. rewrite !Nat.sub_diag. simpl. ring.
  - intros t Ht. replace (S n - t)%nat with (S (n - t)) by lia. reflexivity.
Qed.

Lemma csum_triangle : forall (F : nat -> nat -> C) n,
  csum (fun q => csum (fun t => F t (q - t)%nat) (S q)) n
  = csum (fun t => csum (fun m => F t m) (n - t)) n.
Proof.
  intros F n. apply Ceq; unfold csum; simpl.
  - exact (rsum_triangle (fun t m => fst (F t m)) n).
  - exact (rsum_triangle (fun t m => snd (F t m)) n).
Qed.

Lemma Cmul_zero_l : forall a b, a <> C0 -> Cmul a b = C0 -> b = C0.
Proof.
  intros a b Ha H.
  assert (E : Cmod2 a * Cmod2 b = 0) by (rewrite <- Cmod2_mul, H; unfold Cmod2; simpl; ring).
  assert (Pa : Cmod2 a <> 0).
  { intro E0. apply Ha. unfold Cmod2 in E0. destruct a as [a1 a2]; simpl in *.
    assert (a1 = 0) by nra. assert (a2 = 0) by nra. subst. reflexivity. }
  assert (Eb : Cmod2 b = 0) by (apply Rmult_integral in E; tauto).
  unfold Cmod2 in Eb. destruct b as [b1 b2]; simpl in *.
  assert (b1 = 0) by nra. assert (b2 = 0) by nra. subst. reflexivity.
Qed.

End CSums.

(* ---------------------------------------------------------------------- *)
(* Roots of unity                                                         *)
(* ---------------------------------------------------------------------- *)

Section Roots.
Local Open Scope R_scope.

Definition cis (t : R) : C := (cos t, sin t).

Lemma cis_add : forall a b, cis (a + b) = Cmul (cis a) (cis b).
Proof. intros a b. apply Ceq; unfold cis, Cmul; simpl; [rewrite cos_plus | rewrite sin_plus]; ring. Qed.

Lemma Cmod2_cis : forall t, Cmod2 (cis t) = 1.
Proof. intros t. unfold Cmod2, cis; simpl. pose proof (sin2_cos2 t). unfold Rsqr in *. lra. Qed.

Lemma Cmod_cis : forall t, Cmod (cis t) = 1.
Proof. intros t. unfold Cmod. rewrite Cmod2_cis. apply sqrt_1. Qed.

Lemma cis_neg : forall t, cis (- t) = Cconj (cis t).
Proof. intros t. unfold cis, Cconj. rewrite cos_neg, sin_neg. reflexivity. Qed.

Lemma cos_sin_2PI_Z : forall z : Z, cos (2 * PI * IZR z) = 1 /\ sin (2 * PI * IZR z) = 0.
Proof.
  intros z. destruct (Z_le_gt_dec 0 z) as [Hz|Hz].
  - rewrite <- (Z2Nat.id z Hz), <- INR_IZR_INZ.
    pose proof (cos_period 0 (Z.to_nat z)) as H1. pose proof (sin_period 0 (Z.to_nat z)) as H2.
    rewrite Rplus_0_l, cos_0 in H1. rewrite Rplus_0_l, sin_0 in H2.
    replace (2 * PI * INR (Z.to_nat z)) with (2 * INR (Z.to_nat z) * PI) by ring. auto.
  - replace z with (- (- z))%Z by lia. rewrite opp_IZR.
    replace (2 * PI * - IZR (- z)) with (- (2 * PI * IZR (- z))) by ring.
    rewrite cos_neg, sin_neg.
    assert (Hz' : (0 <= - z)%Z) by lia.
    rewrite <- (Z2Nat.id (- z) Hz'), <- INR_IZR_INZ.
    pose proof (cos_period 0 (Z.to_nat (- z))) as H1. pose proof (sin_period 0 (Z.to_nat (- z))) as H2.
    rewrite Rplus_0_l, cos_0 in H1. rewrite Rplus_0_l, sin_0 in H2.
    replace (2 * PI * INR (Z.to_nat (- z))) with (2 * INR (Z.to_nat (- z)) * PI) by ring.
    split; [exact H1 | rewrite H2; ring].
Qed.

Variable Nn : nat.
Hypothesis Nn_pos : (0 < Nn)%nat.

Definition EN (z : Z) : C := cis (2 * PI * IZR z / INR Nn).

Lemma INR_Nn_pos : 0 < INR Nn.
Proof. apply lt_0_INR. exact Nn_pos. Qed.

Lemma EN_add : forall a b, EN (a + b) = Cmul (EN a) (EN b).
Proof.
  intros a b. unfold EN. rewrite <- cis_add. f_equal. rewrite plus_IZR.
  pose proof INR_Nn_pos. field. lra.
Qed.

Lemma EN_0 : EN 0 = C1.
Proof. unfold EN, cis, C1. simpl. replace (2 * PI * 0 / INR Nn) with 0 by (pose proof INR_Nn_pos; field; lra).
  rewrite cos_0, sin_0. reflexivity. Qed.

Lemma Cmod_EN : forall z, Cmod (EN z) = 1.
Proof. intros. apply Cmod_cis. Qed.

Lemma Cmod2_EN : forall z, Cmod2 (EN z) = 1.
Proof. intros. apply Cmod2_cis. Qed.

Lemma EN_opp : forall z, EN (- z) = Cconj (EN z).
Proof.
  intros z. unfold EN. rewrite <- cis_neg. f_equal. rewrite opp_IZR. pose proof INR_Nn_pos. field. lra.
Qed.

Lemma EN_mulN : forall z, EN (z * Z.of_nat Nn) = C1.
Proof.
  intros z. unfold EN, cis, C1.
  replace (2 * PI * IZR (z * Z.of_nat Nn) / INR Nn) with (2 * PI * IZR z).
  - destruct (cos_sin_2PI_Z z) as [-> ->]. reflexivity.
  - rewrite mult_IZR, <- INR_IZR_INZ. pose proof INR_Nn_pos. field. lra.
Qed.

Lemma EN_ne1 : forall z, (0 < Z.abs z < Z.of_nat Nn)%Z -> EN z <> C1.
Proof.
  intros z Hz E. unfold EN, cis, C1 in E. injection E as Ec Es.
  set (h := PI * IZR z / INR Nn).
  assert (Eh : 2 * PI * IZR z / INR Nn = 2 * h) by (unfold h; pose proof INR_Nn_pos; field; lra).
  rewrite Eh, cos_2a_sin in Ec.
  assert (Hs : sin h = 0) by nra.
  pose proof INR_Nn_pos. pose proof PI_RGT_0.
  assert (HN : IZR (Z.of_nat Nn) = INR Nn) by (rewrite <- INR_IZR_INZ; reflexivity).
  destruct (Z_le_gt_dec 0 z) as [Hp|Hn].
  - assert (Hz1 : 0 < IZR z) by (apply IZR_lt; lia).
    assert (Hz2 : IZR z < INR Nn) by (rewrite <- HN; apply IZR_lt; lia).
    assert (0 < h) by (unfold h; apply Rdiv_lt_0_compat; nra).
    assert (h < PI).
    { unfold h. apply Rmult_lt_reg_r with (INR Nn); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    pose proof (sin_gt_0 h ltac:(lra) ltac:(lra)). lra.
  - assert (Hz1 : IZR z < 0) by (apply IZR_lt; lia).
    assert (Hz2 : - INR Nn < IZR z) by (rewrite <- HN, <- opp_IZR; apply IZR_lt; lia).
    assert (h < 0).
    { unfold h. unfold Rdiv. apply Rmult_lt_reg_r with (INR Nn); [lra|].
      rewrite Rmult_assoc, Rinv_l by lra. nra. }
    assert (- PI < h).
    { unfold h. apply Rmult_lt_reg_r with (INR Nn); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    pose proof (sin_gt_0 (- h) ltac:(lra) ltac:(lra)). rewrite sin_neg in H3. lra.
Qed.

(* geometric sums of a root of unity *)
Lemma EN_geo : forall d n,
  Cmul (Csub (EN d) C1) (csum (fun k => EN (d * Z.of_nat k)) n)
  = Csub (EN (d * Z.of_nat n)) C1.
Proof.
  intros d n; induction n as [|n IH].
  - rewrite csum_0. replace (d * Z.of_nat 0)%Z with 0%Z by lia. rewrite EN_0.
    apply Ceq; unfold Cmul, Csub, C0, C1; simpl; ring.
  - rewrite csum_S. replace (d * Z.of_nat (S n))%Z with (d * Z.of_nat n + d)%Z by lia.
    rewrite EN_add.
    transitivity (Cadd (Cmul (Csub (EN d) C1) (csum (fun k => EN (d * Z.of_nat k)) n))
                       (Cmul (Csub (EN d) C1) (EN (d * Z.of_nat n))));
      [apply Ceq; unfold Cmul, Cadd, Csub; simpl; ring|].
    rewrite IH. apply Ceq; unfold Cmul, Cadd, Csub, C1; simpl; ring.
Qed.

Lemma EN_orth : forall n q, (n < Nn)%nat -> (q < Nn)%nat ->
  csum (fun k => EN ((Z.of_nat n - Z.of_nat q) * Z.of_nat k)) Nn
  = if Nat.eq_dec n q then (INR Nn, 0) else C0.
Proof.
  intros n q Hn Hq. destruct (Nat.eq_dec n q) as [->|E].
  - rewrite (csum_ext _ (fun _ => C1)).
    + apply Ceq; unfold csum, C1; simpl; rewrite rsum_const; ring.
    + intros k Hk. replace ((Z.of_nat q - Z.of_nat q) * Z.of_nat k)%Z with 0%Z by lia. apply EN_0.
  - apply (Cmul_zero_l (Csub (EN (Z.of_nat n - Z.of_nat q)) C1)).
    + intro H. apply (EN_ne1 (Z.of_nat n - Z.of_nat q)); [lia|].
      destruct (EN (Z.of_nat n - Z.of_nat q)) as [a b]. unfold Csub, C0, C1 in H; simpl in H.
      injection H as H1 H2. unfold C1. f_equal; lra.
    + rewrite EN_geo, EN_mulN. apply Ceq; unfold Csub, C1, C0; simpl; ring.
Qed.

(* the inverse transform inverts the forward one *)
Lemma dft_inversion : forall (d : vec) q, (q < Nn)%nat ->
  csum (fun k => Cmul (csum (fun n => Cmul (d n) (EN (Z.of_nat n * Z.of_nat k))) Nn)
                      (EN (- (Z.of_nat k * Z.of_nat q)))) Nn
  = Cscal (INR Nn) (d q).
Proof.
  intros d q Hq.
  rewrite (csum_ext _ (fun k => csum (fun n => Cmul (d n) (EN ((Z.of_nat n - Z.of_nat q) * Z.of_nat k))) Nn)).
  - rewrite csum_swap.
    rewrite (csum_ext _ (fun n => Cmul (d n) (if Nat.eq_dec n q then (INR Nn, 0) else C0))).
    + rewrite (csum_single _ q); [ | exact Hq | ].
      * destruct (Nat.eq_dec q q) as [_|E]; [|congruence].
        apply Ceq; unfold Cmul, Cscal; simpl; ring.
      * intros i Hi Hiq. destruct (Nat.eq_dec i q) as [E|_]; [congruence|].
        apply Ceq; unfold Cmul, C0; simpl; ring.
    + intros n Hn. rewrite <- EN_orth by assumption. rewrite Cmul_csum_l. reflexivity.
  - intros k Hk. rewrite Cmul_csum_r. apply csum_ext. intros n Hn.
    replace ((Z.of_nat n - Z.of_nat q) * Z.of_nat k)%Z
      with (Z.of_nat n * Z.of_nat k + - (Z.of_nat k * Z.of_nat q))%Z by ring.
    rewrite EN_add. apply Ceq; unfold Cmul; simpl; ring.
Qed.

End Roots.

(* ---------------------------------------------------------------------- *)
(* The Cauchy product: evaluation is multiplicative                       *)
(* ---------------------------------------------------------------------- *)

Section Cauchy.
Local Open Scope R_scope.

Definition conv (f g : vec) (q : nat) : C :=
  csum (fun t => Cmul (f t) (g (q - t)%nat)) (S q).

Lemma cauchy_product : forall (f g p : vec) (na nb Nn : nat),
  (forall n, (na <= n)%nat -> f n = C0) -> (forall n, (nb <= n)%nat -> g n = C0) ->
  (na + nb <= S Nn)%nat ->
  (forall a b, p (a + b)%nat = Cmul (p a) (p b)) ->
  Cmul (csum (fun n => Cmul (f n) (p n)) Nn) (csum (fun m => Cmul (g m) (p m)) Nn)
  = csum (fun q => Cmul (conv f g q) (p q)) Nn.
Proof.
  intros f g p na nb Nn Hf Hg Hn Hp.
  set (F := fun t m => Cmul (Cmul (f t) (g m)) (p (t + m)%nat)).
  transitivity (csum (fun t => csum (fun m => F t m) Nn) Nn).
  { rewrite Cmul_csum_r. apply csum_ext. intros t Ht. rewrite Cmul_csum_l. apply csum_ext.
    intros m Hm. unfold F. rewrite Hp. apply Ceq; unfold Cmul; simpl; ring. }
  transitivity (csum (fun q => csum (fun t => F t (q - t)%nat) (S q)) Nn).
  2:{ apply csum_ext. intros q Hq. unfold conv. rewrite Cmul_csum_r. apply csum_ext.
      intros t Ht. unfold F. replace (t + (q - t))%nat with q by lia. reflexivity. }
  rewrite csum_triangle. apply csum_ext. intros t Ht.
  replace Nn with ((Nn - t) + t)%nat at 1 by lia. rewrite csum_add_len.
  rewrite (csum_zero (fun i => F t (Nn - t + i)%nat)).
  - apply Ceq; unfold Cadd, C0; simpl; ring.
  - intros i Hi. unfold F. destruct (Nat.lt_ge_cases t na) as [Hta|Hta].
    + rewrite (Hg (Nn - t + i)%nat) by lia. apply Ceq; unfold Cmul, C0; simpl; ring.
    + rewrite (Hf t) by lia. apply Ceq; unfold Cmul, C0; simpl; ring.
Qed.

End Cauchy.

(* ====================================================================== *)
(* Part C.  The exact radix-2 transform (Stockham order, natural in/out)  *)
(* ====================================================================== *)

Section Stage.
Local Open Scope R_scope.

(* One stage on a vector of length 2*half, butterflies of span r :
   output j (j < half) and half + j combine inputs i1 = j + r*(j/r) and
   i1 + r, with the twiddle of index j/r. *)
Definition sj (half i : nat) : nat := if (i <? half)%nat then i else (i - half)%nat.
Definition sq (r j : nat) : nat := (j / r)%nat.
Definition si1 (r j : nat) : nat := (j + r * (j / r))%nat.

Definition stage (half r : nat) (bp bm : nat -> C -> C -> C) (x : vec) : vec :=
  fun i => let j := sj half i in
           if (i <? half)%nat then bp (sq r j) (x (si1 r j)) (x (si1 r j + r)%nat)
           else bm (sq r j) (x (si1 r j)) (x (si1 r j + r)%nat).

Lemma stage_lo : forall half r bp bm x j, (j < half)%nat ->
  stage half r bp bm x j = bp (sq r j) (x (si1 r j)) (x (si1 r j + r)%nat).
Proof.
  intros. unfold stage, sj. destruct (Nat.ltb_spec j half); [reflexivity | lia].
Qed.

Lemma stage_hi : forall half r bp bm x j, (j < half)%nat ->
  stage half r bp bm x (half + j)%nat = bm (sq r j) (x (si1 r j)) (x (si1 r j + r)%nat).
Proof.
  intros. unfold stage, sj. destruct (Nat.ltb_spec (half + j) half); [lia|].
  replace (half + j - half)%nat with j by lia. reflexivity.
Qed.

Lemma div_mod_r : forall r q rho, (rho < r)%nat -> ((r * q + rho) / r = q)%nat.
Proof.
  intros r q rho H. rewrite Nat.mul_comm, Nat.div_add_l by lia. rewrite Nat.div_small by exact H. lia.
Qed.

Lemma rsum_halves : forall G half, rsum G (2 * half) = rsum (fun j => G j + G (half + j)%nat) half.
Proof.
  intros G half. replace (2 * half)%nat with (half + half)%nat by lia.
  rewrite rsum_add_len, rsum_plus. reflexivity.
Qed.

(* every input index is read by exactly one butterfly *)
Lemma bfly_sum : forall (F : nat -> R) r M,
  rsum (fun j => F (si1 r j) + F (si1 r j + r)%nat) (M * r) = rsum F (M * (2 * r)).
Proof.
  intros F r M. destruct (Nat.eq_dec r 0) as [->|Hr].
  - rewrite !Nat.mul_0_r. reflexivity.
  - rewrite !rsum_block. apply rsum_ext. intros q Hq.
    replace (2 * r)%nat with (r + r)%nat by lia. rewrite rsum_add_len, <- rsum_plus.
    apply rsum_ext. intros rho Hrho. unfold si1. rewrite div_mod_r by exact Hrho.
    f_equal; f_equal; lia.
Qed.

Lemma par_law : forall u z, Cmod2 (Cadd u z) + Cmod2 (Csub u z) = 2 * Cmod2 u + 2 * Cmod2 z.
Proof. intros u z. unfold Cmod2, Cadd, Csub; simpl. ring. Qed.

(* the stage with unit twiddles doubles the squared norm *)
Lemma stage_nsq : forall (w : nat -> C) r M x,
  (forall q, Cmod2 (w q) = 1) ->
  nsq (M * (2 * r)) (stage (M * r) r (fun q u v => Cadd u (Cmul (w q) v))
                        (fun q u v => Csub u (Cmul (w q) v)) x)
  = 2 * nsq (M * (2 * r)) x.
Proof.
  intros w r M x Hw. unfold nsq.
  replace (M * (2 * r))%nat with (2 * (M * r))%nat at 1 by lia.
  rewrite rsum_halves.
  rewrite (rsum_ext _ (fun j => 2 * (Cmod2 (x (si1 r j)) + Cmod2 (x (si1 r j + r)%nat)))).
  - rewrite rsum_scal. f_equal. apply (bfly_sum (fun i => Cmod2 (x i))).
  - intros j Hj. rewrite stage_lo, stage_hi by exact Hj. rewrite par_law, Cmod2_mul, Hw. ring.
Qed.

Lemma stage_sub : forall half r (w : nat -> C) x y i,
  stage half r (fun q u v => Cadd u (Cmul (w q) v)) (fun q u v => Csub u (Cmul (w q) v)) (vsub x y) i
  = Csub (stage half r (fun q u v => Cadd u (Cmul (w q) v)) (fun q u v => Csub u (Cmul (w q) v)) x i)
         (stage half r (fun q u v => Cadd u (Cmul (w q) v)) (fun q u v => Csub u (Cmul (w q) v)) y i).
Proof.
  intros. unfold stage, vsub. destruct (i <? half)%nat; apply Ceq; unfold Cadd, Csub, Cmul; simpl; ring.
Qed.

Lemma csum_evenodd : forall f M,
  csum f (2 * M) = Cadd (csum (fun t => f (2 * t)%nat) M) (csum (fun t => f (2 * t + 1)%nat) M).
Proof.
  intros f M; induction M as [|M IH].
  - apply Ceq; unfold csum, Cadd; simpl; ring.
  - replace (2 * S M)%nat with (S (S (2 * M))) by lia. rewrite !csum_S, IH.
    replace (S (2 * M)) with (2 * M + 1)%nat by lia.
    apply Ceq; unfold Cadd; simpl; ring.
Qed.

(* the exact butterflies of a stage of span r, on N points, direction sg *)
Definition Wex (Nn : nat) (sg : Z) (r q : nat) : C := EN Nn (sg * Z.of_nat r * Z.of_nat q).
Definition bpx (Nn : nat) (sg : Z) (r : nat) (q : nat) (u v : C) : C := Cadd u (Cmul (Wex Nn sg r q) v).
Definition bmx (Nn : nat) (sg : Z) (r : nat) (q : nat) (u v : C) : C := Csub u (Cmul (Wex Nn sg r q) v).

Lemma EN_half : forall Nn half sg, Nn = (2 * half)%nat -> (0 < half)%nat -> (sg = 1 \/ sg = -1)%Z ->
  EN Nn (sg * Z.of_nat half) = Copp C1.
Proof.
  intros Nn half sg HN Hh Hs. unfold EN, cis, Copp, C1. simpl.
  assert (Hh' : 0 < INR half) by (apply lt_0_INR; exact Hh).
  replace (2 * PI * IZR (sg * Z.of_nat half) / INR Nn) with (IZR sg * PI).
  - destruct Hs as [-> | ->]; simpl.
    + rewrite Rmult_1_l, cos_PI, sin_PI. f_equal; ring.
    + replace (-1 * PI) with (- PI) by ring. rewrite cos_neg, sin_neg, cos_PI, sin_PI. f_equal; ring.
  - rewrite HN, mult_IZR, <- INR_IZR_INZ, mult_INR. simpl. field. lra.
Qed.

(* the key step: from DFTs of length M over stride 2R to length 2M over stride R *)
Lemma stage_step : forall (sg : Z) (R M Nn : nat) (x y : vec),
  (sg = 1 \/ sg = -1)%Z -> (0 < R)%nat -> (0 < M)%nat -> Nn = (2 * R * M)%nat ->
  (forall rho k, (rho < 2 * R)%nat -> (k < M)%nat ->
     y (rho + 2 * R * k)%nat = csum (fun t => Cmul (x (rho + 2 * R * t)%nat)
                                  (EN Nn (sg * Z.of_nat (2 * R) * Z.of_nat t * Z.of_nat k))) M) ->
  forall rho k, (rho < R)%nat -> (k < 2 * M)%nat ->
    stage (M * R) R (bpx Nn sg R) (bmx Nn sg R) y (rho + R * k)%nat
    = csum (fun t => Cmul (x (rho + R * t)%nat) (EN Nn (sg * Z.of_nat R * Z.of_nat t * Z.of_nat k))) (2 * M).
Proof.
  intros sg R M Nn x y Hs HR HM HN Hy rho k Hrho Hk.
  assert (HNpos : (0 < Nn)%nat) by nia.
  rewrite csum_evenodd.
  destruct (Nat.lt_ge_cases k M) as [Hk1|Hk1].
  - assert (Hj : (rho + R * k < M * R)%nat) by nia.
    rewrite stage_lo by exact Hj. unfold bpx, sq, si1.
    replace (rho + R * k)%nat with (R * k + rho)%nat by lia.
    rewrite div_mod_r by exact Hrho.
    replace (R * k + rho + R * k)%nat with (rho + 2 * R * k)%nat by lia.
    replace (rho + 2 * R * k + R)%nat with ((rho + R) + 2 * R * k)%nat by lia.
    rewrite Hy by lia. rewrite Hy by lia.
    unfold Wex. rewrite Cmul_csum_l. f_equal.
    + apply csum_ext. intros t Ht. f_equal; [f_equal; lia|].
      f_equal. rewrite !Nat2Z.inj_mul. simpl Z.of_nat. ring.
    + apply csum_ext. intros t Ht.
      replace (rho + R * (2 * t + 1))%nat with (rho + R + 2 * R * t)%nat by lia.
      replace (sg * Z.of_nat R * Z.of_nat (2 * t + 1) * Z.of_nat k)%Z
        with (sg * Z.of_nat (2 * R) * Z.of_nat t * Z.of_nat k + sg * Z.of_nat R * Z.of_nat k)%Z
        by (zc; ring).
      rewrite EN_add by exact HNpos. apply Ceq; unfold Cmul; simpl; ring.
  - set (k0 := (k - M)%nat).
    assert (Hk0 : (k0 < M)%nat) by (unfold k0; lia).
    replace (rho + R * k)%nat with (M * R + (R * k0 + rho))%nat by (unfold k0; nia).
    rewrite stage_hi by nia. unfold bmx, sq, si1.
    rewrite div_mod_r by exact Hrho.
    replace (R * k0 + rho + R * k0)%nat with (rho + 2 * R * k0)%nat by lia.
    replace (rho + 2 * R * k0 + R)%nat with ((rho + R) + 2 * R * k0)%nat by lia.
    rewrite Hy by lia. rewrite Hy by lia.
    unfold Wex. rewrite Cmul_csum_l. rewrite Csub_csum_add. f_equal.
    + apply csum_ext. intros t Ht. f_equal; [f_equal; lia|].
      replace (sg * Z.of_nat R * Z.of_nat (2 * t) * Z.of_nat k)%Z
        with (sg * Z.of_nat (2 * R) * Z.of_nat t * Z.of_nat k0 + (sg * Z.of_nat t) * Z.of_nat Nn)%Z
        by (unfold k0; rewrite HN; zc; ring).
      rewrite EN_add, EN_mulN by exact HNpos. apply Ceq; unfold Cmul, C1; simpl; ring.
    + apply csum_ext. intros t Ht.
      replace (rho + R * (2 * t + 1))%nat with (rho + R + 2 * R * t)%nat by lia.
      replace (sg * Z.of_nat R * Z.of_nat (2 * t + 1) * Z.of_nat k)%Z
        with (sg * Z.of_nat (2 * R) * Z.of_nat t * Z.of_nat k0 + sg * Z.of_nat R * Z.of_nat k0
              + (sg * Z.of_nat t) * Z.of_nat Nn + sg * Z.of_nat (R * M))%Z
        by (unfold k0; rewrite HN; zc; ring).
      rewrite !EN_add by exact HNpos. rewrite EN_mulN by exact HNpos.
      rewrite (EN_half Nn (R * M) sg) by (try lia; exact Hs).
      apply Ceq; unfold Cmul, Copp, C1; simpl; ring.
Qed.

End Stage.

(* The exact transform: lg stages on 2^lg points. *)
Section ExactFFT.
Local Open Scope R_scope.

Definition hlf (lg : nat) : nat := (2 ^ (lg - 1))%nat.
Definition spn (lg s : nat) : nat := (2 ^ (lg - 1 - s))%nat.

Fixpoint fft_ex (sg : Z) (lg s : nat) (x : vec) : vec :=
  match s with
  | O => x
  | S s' => stage (hlf lg) (spn lg s') (bpx (2 ^ lg) sg (spn lg s')) (bmx (2 ^ lg) sg (spn lg s'))
                  (fft_ex sg lg s' x)
  end.

Lemma pow2_pos : forall n, (0 < 2 ^ n)%nat.
Proof. intros n. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma hlf_split : forall lg s, (s < lg)%nat -> hlf lg = (2 ^ s * spn lg s)%nat.
Proof. intros lg s H. unfold hlf, spn. rewrite <- Nat.pow_add_r. f_equal. lia. Qed.

Lemma spn_double : forall lg s, (s < lg)%nat -> (2 ^ (lg - s) = 2 * spn lg s)%nat.
Proof.
  intros lg s H. unfold spn. replace (lg - s)%nat with (S (lg - 1 - s)) by lia. reflexivity.
Qed.

Lemma pow_lg_split : forall lg s, (s < lg)%nat -> (2 ^ lg = 2 * spn lg s * 2 ^ s)%nat.
Proof.
  intros lg s H. rewrite <- spn_double by exact H. rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

Lemma fft_ex_inv : forall sg lg x, (sg = 1 \/ sg = -1)%Z -> forall s, (s <= lg)%nat ->
  forall rho k, (rho < 2 ^ (lg - s))%nat -> (k < 2 ^ s)%nat ->
  fft_ex sg lg s x (rho + 2 ^ (lg - s) * k)%nat
  = csum (fun t => Cmul (x (rho + 2 ^ (lg - s) * t)%nat)
             (EN (2 ^ lg) (sg * Z.of_nat (2 ^ (lg - s)) * Z.of_nat t * Z.of_nat k))) (2 ^ s).
Proof.
  intros sg lg x Hs s. induction s as [|s IH]; intros Hsl rho k Hrho Hk.
  - simpl in Hk. assert (k = 0%nat) by lia. subst k. simpl fft_ex.
    rewrite Nat.mul_0_r, Nat.add_0_r.
    unfold csum; simpl. rewrite Nat.mul_0_r, Nat.add_0_r. rewrite Z.mul_0_r.
    replace (2 * PI * 0 / INR (2 ^ lg)) with 0 by (pose proof (lt_0_INR _ (pow2_pos lg)); field; lra).
    rewrite cos_0, sin_0. apply Ceq; simpl; ring.
  - simpl fft_ex. rewrite (hlf_split lg s) by lia.
    replace (lg - S s)%nat with (lg - 1 - s)%nat in * by lia. fold (spn lg s) in *.
    replace (2 ^ S s)%nat with (2 * 2 ^ s)%nat in * by reflexivity.
    apply (stage_step sg (spn lg s) (2 ^ s) (2 ^ lg) x (fft_ex sg lg s x)); auto.
    + unfold spn. apply pow2_pos.
    + apply pow2_pos.
    + apply pow_lg_split. lia.
    + intros rho' k' Hr Hk'. rewrite <- spn_double by lia. apply IH; [lia | rewrite spn_double by lia; exact Hr | exact Hk'].
Qed.

(* the transform is the DFT *)
Theorem fft_ex_dft : forall sg lg x, (sg = 1 \/ sg = -1)%Z -> forall k, (k < 2 ^ lg)%nat ->
  fft_ex sg lg lg x k = csum (fun t => Cmul (x t) (EN (2 ^ lg) (sg * Z.of_nat t * Z.of_nat k))) (2 ^ lg).
Proof.
  intros sg lg x Hs k Hk.
  pose proof (fft_ex_inv sg lg x Hs lg (le_n _) 0 k) as H.
  rewrite Nat.sub_diag in H. simpl in H. rewrite Nat.add_0_r in H. replace (k + 0)%nat with k in H by lia.
  rewrite H by lia. apply csum_ext. intros t Ht. f_equal; [f_equal; lia | f_equal; lia].
Qed.

Lemma Cmod2_Wex : forall Nn sg r q, (0 < Nn)%nat -> Cmod2 (Wex Nn sg r q) = 1.
Proof. intros. unfold Wex. apply Cmod2_EN. Qed.

Lemma ex_stage_nsq : forall sg lg s x, (s < lg)%nat ->
  nsq (2 ^ lg) (stage (hlf lg) (spn lg s) (bpx (2 ^ lg) sg (spn lg s)) (bmx (2 ^ lg) sg (spn lg s)) x)
  = 2 * nsq (2 ^ lg) x.
Proof.
  intros sg lg s x Hs. rewrite (hlf_split lg s Hs).
  replace (2 ^ lg)%nat with (2 ^ s * (2 * spn lg s))%nat by (rewrite (pow_lg_split lg s Hs); lia).
  unfold bpx, bmx. apply stage_nsq. intros q. apply Cmod2_Wex.
  pose proof (pow2_pos s). unfold spn. pose proof (pow2_pos (lg - 1 - s)). nia.
Qed.

Lemma nrm_scal_sq : forall n x y c, 0 <= c -> nsq n y = c * c * nsq n x -> nrm n y = c * nrm n x.
Proof.
  intros n x y c Hc H. unfold nrm. rewrite H, sqrt_mult_alt by (apply Rmult_le_pos; lra).
  rewrite sqrt_square by exact Hc. reflexivity.
Qed.

Lemma ex_stage_nrm : forall sg lg s x, (s < lg)%nat ->
  nrm (2 ^ lg) (stage (hlf lg) (spn lg s) (bpx (2 ^ lg) sg (spn lg s)) (bmx (2 ^ lg) sg (spn lg s)) x)
  = sq2 * nrm (2 ^ lg) x.
Proof.
  intros. apply nrm_scal_sq; [apply sqrt_pos|]. rewrite ex_stage_nsq by assumption.
  rewrite sq2_sq. reflexivity.
Qed.

Lemma fft_ex_nrm : forall sg lg s x, (s <= lg)%nat ->
  nrm (2 ^ lg) (fft_ex sg lg s x) = sq2 ^ s * nrm (2 ^ lg) x.
Proof.
  intros sg lg s x; induction s as [|s IH]; intros Hs; simpl; [ring|].
  rewrite ex_stage_nrm by lia. rewrite IH by lia. ring.
Qed.

Lemma fft_ex_sub : forall sg lg s x y i,
  fft_ex sg lg s (vsub x y) i = Csub (fft_ex sg lg s x i) (fft_ex sg lg s y i).
Proof.
  intros sg lg s; induction s as [|s IH]; intros x y i; simpl; [reflexivity|].
  unfold bpx, bmx.
  rewrite <- stage_sub. unfold stage. destruct (i <? hlf lg)%nat; rewrite !IH; reflexivity.
Qed.

Lemma sq2_pow_lg : forall lg, sq2 ^ lg * sq2 ^ lg = INR (2 ^ lg).
Proof.
  intros lg. rewrite <- Rpow_mult_distr, sq2_sq, pow_INR. reflexivity.
Qed.

End ExactFFT.

(* ====================================================================== *)
(* Part D.  The rounded transform and its error                           *)
(* ====================================================================== *)

Section Rounding.
Local Open Scope R_scope.

Definition eps : R := u / 2.

Lemma eps_val : eps = / 9007199254740992.
Proof. unfold eps. rewrite u_val. field. Qed.

Lemma eta_tiny : eta_max <= eps / 1267650600228229401496703205376.
Proof.
  unfold eta_max. rewrite eps_val.
  apply Rle_trans with (Raux.bpow Zaux.radix2 (-153)); [apply Raux.bpow_le; lia|].
  change (Raux.bpow Zaux.radix2 (-153)) with (/ IZR (Z.pow_pos 2 153)).
  replace (IZR (Z.pow_pos 2 153)) with (9007199254740992 * 1267650600228229401496703205376)
    by (rewrite <- mult_IZR; reflexivity).
  unfold Rdiv. rewrite <- Rinv_mult. lra.
Qed.

Lemma eta_nonneg : 0 <= eta_max.
Proof. pose proof eta_max_pos. lra. Qed.

Lemma rnd_e : forall z, Rabs (rnd z - z) <= eps * Rabs z + eta_max.
Proof.
  intros z. destruct (rnd_model z) as (e & t & He & Ht & _ & ->).
  replace (z * (1 + e) + t - z) with (z * e + t) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult.
  pose proof (Rabs_pos z). unfold eps.
  assert (Rabs z * Rabs e <= Rabs z * (u / 2)) by (apply Rmult_le_compat_l; lra). lra.
Qed.

Lemma abs_tri3 : forall a b c, Rabs (a + b + c) <= Rabs a + Rabs b + Rabs c.
Proof.
  intros a b c. eapply Rle_trans; [apply Rabs_triang|].
  pose proof (Rabs_triang a b). lra.
Qed.

Lemma rnd_sub2_err : forall x1 x2,
  Rabs (rnd (rnd x1 - rnd x2) - (x1 - x2)) <= 2.0001 * eps * (Rabs x1 + Rabs x2) + 4 * eta_max.
Proof.
  intros x1 x2. set (p := rnd x1 - rnd x2).
  pose proof (rnd_e x1) as E1. pose proof (rnd_e x2) as E2. pose proof (rnd_e p) as E3.
  assert (Hp : Rabs p <= Rabs x1 + Rabs x2 + Rabs (rnd x1 - x1) + Rabs (rnd x2 - x2)).
  { unfold p. replace (rnd x1 - rnd x2) with ((x1 - x2) + (rnd x1 - x1) + (- (rnd x2 - x2))) by ring.
    eapply Rle_trans; [apply abs_tri3|]. rewrite Rabs_Ropp.
    pose proof (Rabs_triang x1 (- x2)). rewrite Rabs_Ropp in H. unfold Rminus at 1. lra. }
  replace (rnd p - (x1 - x2)) with ((rnd p - p) + (rnd x1 - x1) + (- (rnd x2 - x2))) by (unfold p; ring).
  eapply Rle_trans; [apply abs_tri3|]. rewrite Rabs_Ropp.
  pose proof eta_nonneg. pose proof (Rabs_pos x1). pose proof (Rabs_pos x2).
  pose proof eta_tiny. rewrite eps_val in *. lra.
Qed.

Lemma rnd_add2_err : forall x1 x2,
  Rabs (rnd (rnd x1 + rnd x2) - (x1 + x2)) <= 2.0001 * eps * (Rabs x1 + Rabs x2) + 4 * eta_max.
Proof.
  intros x1 x2. set (p := rnd x1 + rnd x2).
  pose proof (rnd_e x1) as E1. pose proof (rnd_e x2) as E2. pose proof (rnd_e p) as E3.
  assert (Hp : Rabs p <= Rabs x1 + Rabs x2 + Rabs (rnd x1 - x1) + Rabs (rnd x2 - x2)).
  { unfold p. replace (rnd x1 + rnd x2) with ((x1 + x2) + (rnd x1 - x1) + (rnd x2 - x2)) by ring.
    eapply Rle_trans; [apply abs_tri3|].
    pose proof (Rabs_triang x1 x2). lra. }
  replace (rnd p - (x1 + x2)) with ((rnd p - p) + (rnd x1 - x1) + (rnd x2 - x2)) by (unfold p; ring).
  eapply Rle_trans; [apply abs_tri3|].
  pose proof eta_nonneg. pose proof (Rabs_pos x1). pose proof (Rabs_pos x2).
  pose proof eta_tiny. rewrite eps_val in *. lra.
Qed.

Lemma cs2a : forall a b : C, Rabs (fst a) * Rabs (fst b) + Rabs (snd a) * Rabs (snd b) <= Cmod a * Cmod b.
Proof.
  intros a b. unfold Cmod. rewrite <- sqrt_mult_alt by apply Cmod2_nonneg.
  rewrite <- (Rabs_pos_eq (Rabs (fst a) * Rabs (fst b) + Rabs (snd a) * Rabs (snd b))).
  2:{ pose proof (Rabs_pos (fst a)). pose proof (Rabs_pos (fst b)).
      pose proof (Rabs_pos (snd a)). pose proof (Rabs_pos (snd b)). nra. }
  apply sqrt_ge_abs. unfold Cmod2.
  pose proof (Rabs_sq (fst a)). pose proof (Rabs_sq (fst b)).
  pose proof (Rabs_sq (snd a)). pose proof (Rabs_sq (snd b)).
  pose proof (sq_nonneg (Rabs (fst a) * Rabs (snd b) - Rabs (snd a) * Rabs (fst b))). nra.
Qed.

Lemma cs2b : forall a b : C, Rabs (fst a) * Rabs (snd b) + Rabs (snd a) * Rabs (fst b) <= Cmod a * Cmod b.
Proof.
  intros a b. pose proof (cs2a a (snd b, fst b)) as H. simpl in H.
  replace (Cmod (snd b, fst b)) with (Cmod b) in H by (unfold Cmod, Cmod2; simpl; f_equal; ring).
  exact H.
Qed.

Definition cmulr (a b : C) : C :=
  (rnd (rnd (fst a * fst b) - rnd (snd a * snd b)), rnd (rnd (fst a * snd b) + rnd (snd a * fst b))).
Definition caddr (a b : C) : C := (rnd (fst a + fst b), rnd (snd a + snd b)).
Definition csubr (a b : C) : C := (rnd (fst a - fst b), rnd (snd a - snd b)).

Lemma cmulr_err : forall a b,
  Cmod (Csub (cmulr a b) (Cmul a b)) <= 4.0002 * eps * (Cmod a * Cmod b) + 8 * eta_max.
Proof.
  intros a b. eapply Rle_trans; [apply Cmod_le_reim|]. unfold cmulr, Cmul, Csub; simpl.
  pose proof (rnd_sub2_err (fst a * fst b) (snd a * snd b)) as H1.
  pose proof (rnd_add2_err (fst a * snd b) (snd a * fst b)) as H2.
  rewrite !Rabs_mult in H1, H2.
  pose proof (cs2a a b). pose proof (cs2b a b). rewrite eps_val in *. lra.
Qed.

Lemma caddr_err : forall a b,
  Cmod (Csub (caddr a b) (Cadd a b)) <= 1.4143 * eps * Cmod (Cadd a b) + 2 * eta_max.
Proof.
  intros a b. eapply Rle_trans; [apply Cmod_le_reim|]. unfold caddr, Cadd, Csub; simpl.
  pose proof (rnd_e (fst a + fst b)). pose proof (rnd_e (snd a + snd b)).
  pose proof (reim_le (Cadd a b)) as R. unfold Cadd in R; simpl in R.
  pose proof sq2_bounds. pose proof (Cmod_nonneg (Cadd a b)). unfold Cadd in H2; simpl in H2.
  assert (sq2 * Cmod (fst a + fst b, snd a + snd b) <= 1.4143 * Cmod (fst a + fst b, snd a + snd b))
    by (apply Rmult_le_compat_r; lra).
  rewrite eps_val in *. lra.
Qed.

Lemma csubr_err : forall a b,
  Cmod (Csub (csubr a b) (Csub a b)) <= 1.4143 * eps * Cmod (Csub a b) + 2 * eta_max.
Proof.
  intros a b. pose proof (caddr_err a (Copp b)) as H.
  replace (Cadd a (Copp b)) with (Csub a b) in H by (apply Ceq; simpl; ring).
  replace (caddr a (Copp b)) with (csubr a b) in H by (unfold caddr, csubr, Copp; simpl; reflexivity).
  exact H.
Qed.

Definition bfp (w u v : C) : C := caddr u (cmulr w v).
Definition bfm (w u v : C) : C := csubr u (cmulr w v).

Lemma bf_err_gen : forall (w W u v : C) delta (y z ex : C),
  Cmod W = 1 -> Cmod (Csub w W) <= delta -> 0 <= delta <= 0.001 ->
  Cmod (Csub y z) <= 1.4143 * eps * Cmod z + 2 * eta_max ->
  Cmod z <= Cmod u + Cmod (cmulr w v) ->
  Cmod (Csub y ex) <= Cmod (Csub y z) + Cmod (Csub (cmulr w v) (Cmul w v)) + Cmod (Csub w W) * Cmod v ->
  Cmod (Csub y ex) <= (5.43 * eps + delta) * (Cmod u + Cmod v) + 11 * eta_max.
Proof.
  intros w W u v delta y z ex HW Hw Hd Hy Hz Hdec.
  pose proof (cmulr_err w v) as Ht.
  assert (Hwh : Cmod w <= 1 + delta).
  { replace w with (Cadd W (Csub w W)) by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. lra. }
  set (U := Cmod u) in *. set (V := Cmod v) in *. set (Wh := Cmod w) in *.
  assert (HU : 0 <= U) by apply Cmod_nonneg. assert (HV : 0 <= V) by apply Cmod_nonneg.
  assert (HWh : 0 <= Wh) by apply Cmod_nonneg.
  assert (HT : Cmod (cmulr w v) <= Wh * V + Cmod (Csub (cmulr w v) (Cmul w v))).
  { replace (cmulr w v) with (Cadd (Cmul w v) (Csub (cmulr w v) (Cmul w v))) at 1 by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_mul. unfold Wh, V; lra. }
  assert (HWV : Wh * V <= V + delta * V) by nra.
  assert (HdV : delta * V <= 0.001 * V) by nra.
  assert (HdV2 : Cmod (Csub w W) * V <= delta * V) by (apply Rmult_le_compat_r; lra).
  assert (HdU : 0 <= delta * U) by nra.
  pose proof eta_nonneg. pose proof eta_tiny.
  pose proof (Cmod_nonneg (Csub (cmulr w v) (Cmul w v))).
  pose proof (Cmod_nonneg z).
  rewrite eps_val in *. nra.
Qed.

Lemma bfp_err : forall (w W u v : C) delta,
  Cmod W = 1 -> Cmod (Csub w W) <= delta -> 0 <= delta <= 0.001 ->
  Cmod (Csub (bfp w u v) (Cadd u (Cmul W v))) <= (5.43 * eps + delta) * (Cmod u + Cmod v) + 11 * eta_max.
Proof.
  intros w W u v delta HW Hw Hd.
  apply (bf_err_gen w W u v delta _ (Cadd u (cmulr w v))); auto.
  - apply caddr_err.
  - apply Cmod_triangle.
  - replace (Csub (bfp w u v) (Cadd u (Cmul W v)))
      with (Cadd (Cadd (Csub (bfp w u v) (Cadd u (cmulr w v))) (Csub (cmulr w v) (Cmul w v)))
                 (Cmul (Csub w W) v)) by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_mul.
    pose proof (Cmod_triangle (Csub (bfp w u v) (Cadd u (cmulr w v))) (Csub (cmulr w v) (Cmul w v))).
    lra.
Qed.

Lemma bfm_err : forall (w W u v : C) delta,
  Cmod W = 1 -> Cmod (Csub w W) <= delta -> 0 <= delta <= 0.001 ->
  Cmod (Csub (bfm w u v) (Csub u (Cmul W v))) <= (5.43 * eps + delta) * (Cmod u + Cmod v) + 11 * eta_max.
Proof.
  intros w W u v delta HW Hw Hd.
  apply (bf_err_gen w W u v delta _ (Csub u (cmulr w v))); auto.
  - apply csubr_err.
  - apply Cmod_triangle_sub.
  - replace (Csub (bfm w u v) (Csub u (Cmul W v)))
      with (Cadd (Csub (Csub (bfm w u v) (Csub u (cmulr w v))) (Csub (cmulr w v) (Cmul w v)))
                 (Copp (Cmul (Csub w W) v))) by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_opp, Cmod_mul.
    pose proof (Cmod_triangle_sub (Csub (bfm w u v) (Csub u (cmulr w v))) (Csub (cmulr w v) (Cmul w v))).
    lra.
Qed.

End Rounding.

Section RoundedFFT.
Local Open Scope R_scope.

Definition cstage (half r : nat) (tw : nat -> C) (x : vec) : vec :=
  stage half r (fun q u v => bfp (tw q) u v) (fun q u v => bfm (tw q) u v) x.

Lemma cstage_err : forall (r M : nat) (tw W : nat -> C) (x : vec) delta,
  (0 < r)%nat ->
  (forall q, (q < M)%nat -> Cmod (W q) = 1 /\ Cmod (Csub (tw q) (W q)) <= delta) ->
  0 <= delta <= 0.001 ->
  nrm (M * (2 * r)) (vsub (cstage (M * r) r tw x)
        (stage (M * r) r (fun q u v => Cadd u (Cmul (W q) v)) (fun q u v => Csub u (Cmul (W q) v)) x))
  <= 2 * (5.43 * eps + delta) * nrm (M * (2 * r)) x + 11 * eta_max * sqrt (INR (M * (2 * r))).
Proof.
  intros r M tw W x delta Hr HW Hd.
  set (s := fun i => Cmod (x (si1 r (sj (M * r) i))) + Cmod (x (si1 r (sj (M * r) i) + r)%nat)).
  assert (Hq : forall j, (j < M * r)%nat -> (sq r j < M)%nat).
  { intros j Hj. unfold sq. apply Nat.Div0.div_lt_upper_bound. lia. }
  eapply Rle_trans.
  - apply (nrm_pointwise _ _ s (5.43 * eps + delta) (11 * eta_max)).
    + rewrite eps_val. lra.
    + pose proof eta_nonneg. lra.
    + intros i Hi. unfold s. pose proof (Cmod_nonneg (x (si1 r (sj (M * r) i)))).
      pose proof (Cmod_nonneg (x (si1 r (sj (M * r) i) + r)%nat)). lra.
    + intros i Hi. unfold vsub, cstage, stage, s.
      assert (Hj : (sj (M * r) i < M * r)%nat) by (unfold sj; destruct (Nat.ltb_spec i (M * r)); lia).
      destruct (HW (sq r (sj (M * r) i)) (Hq _ Hj)) as [HW1 HW2].
      destruct (i <? M * r)%nat.
      * apply bfp_err; assumption.
      * apply bfm_err; assumption.
  - assert (Hs : sqrt (rsum (fun i => s i * s i) (M * (2 * r))) <= 2 * nrm (M * (2 * r)) x).
    { apply sqrt_le_of_sq; [pose proof (nrm_nonneg (M * (2 * r)) x); lra|].
      replace (2 * nrm (M * (2 * r)) x * (2 * nrm (M * (2 * r)) x)) with (4 * nsq (M * (2 * r)) x)
        by (rewrite <- nrm_sq; ring).
      replace (M * (2 * r))%nat with (2 * (M * r))%nat at 1 by lia.
      rewrite rsum_halves. unfold nsq. rewrite <- (bfly_sum (fun i => Cmod2 (x i))).
      rewrite <- rsum_scal. apply rsum_le. intros j Hj. unfold s, sj.
      destruct (Nat.ltb_spec j (M * r)); [|lia].
      destruct (Nat.ltb_spec (M * r + j) (M * r)); [lia|].
      replace (M * r + j - M * r)%nat with j by lia.
      rewrite <- (Cmod_sq (x (si1 r j))), <- (Cmod_sq (x (si1 r j + r)%nat)).
      pose proof (sq_nonneg (Cmod (x (si1 r j)) - Cmod (x (si1 r j + r)%nat))). nra. }
    pose proof (sqrt_pos (INR (M * (2 * r)))). pose proof eta_nonneg.
    assert (0 <= 5.43 * eps + delta) by (rewrite eps_val; lra).
    assert ((5.43 * eps + delta) * sqrt (rsum (fun i => s i * s i) (M * (2 * r)))
            <= (5.43 * eps + delta) * (2 * nrm (M * (2 * r)) x)) by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

Fixpoint cfft (lg : nat) (tw : nat -> nat -> C) (s : nat) (x : vec) : vec :=
  match s with
  | O => x
  | S s' => cstage (hlf lg) (spn lg s') (tw s') (cfft lg tw s' x)
  end.

Definition Gsum (delta : nat -> R) (s : nat) : R := rsum (fun t => 2 * (5.43 * eps + delta t)) s.

Lemma err_arith : forall E E' P X Gs a sqv eta',
  0 <= X -> 1 <= P -> 1.4142 <= sqv -> 0 <= E -> 0 <= Gs -> 0.78 * Gs <= 0.09 -> 0 <= a ->
  0 <= eta' <= 0.01 * a ->
  E <= P * (X + 1) * (0.78 * Gs) -> E' <= a * (P * X + E) + eta' + sqv * E ->
  E' <= sqv * P * (X + 1) * (0.78 * (Gs + a)).
Proof.
  intros E E' P X Gs a sqv eta' HX HP Hsq HE HG HG2 Ha He H1 H2.
  set (Q := P * (X + 1)) in *.
  assert (HQ : 1 <= Q) by (unfold Q; nra).
  assert (A1 : a * E <= a * (Q * 0.09)) by (apply Rmult_le_compat_l; nra).
  assert (A2 : sqv * E <= sqv * (Q * (0.78 * Gs))) by (apply Rmult_le_compat_l; nra).
  assert (A3 : a * (P * X) <= a * Q) by (apply Rmult_le_compat_l; [lra | unfold Q; nra]).
  assert (A4 : eta' <= 0.01 * (a * Q)) by nra.
  assert (A5 : 1.1 * (a * Q) <= 0.78 * sqv * (a * Q)) by (assert (0 <= a * Q) by nra; nra).
  replace (sqv * P * (X + 1) * (0.78 * (Gs + a))) with (sqv * (Q * (0.78 * Gs)) + 0.78 * sqv * (a * Q))
    by (unfold Q; ring).
  nra.
Qed.

Lemma sqrt_pow2_le : forall lg, (lg <= 20)%nat -> sqrt (INR (2 ^ lg)) <= 1024.
Proof.
  intros lg H. apply sqrt_le_of_sq; [lra|].
  rewrite pow_INR. simpl INR.
  apply Rle_trans with (2 ^ 20); [apply Rle_pow; [lra | exact H] | lra].
Qed.

Theorem cfft_err : forall (sg : Z) (lg : nat) (tw : nat -> nat -> C) (delta : nat -> R) (x : vec),
  (sg = 1 \/ sg = -1)%Z -> (1 <= lg <= 20)%nat ->
  (forall s q, (s < lg)%nat -> (q < 2 ^ s)%nat ->
     Cmod (Csub (tw s q) (Wex (2 ^ lg) sg (spn lg s) q)) <= delta s) ->
  (forall s, (s < lg)%nat -> 0 <= delta s <= 0.001) ->
  0.78 * Gsum delta lg <= 0.09 ->
  forall s, (s <= lg)%nat ->
  nrm (2 ^ lg) (vsub (cfft lg tw s x) (fft_ex sg lg s x))
  <= sq2 ^ s * (nrm (2 ^ lg) x + 1) * (0.78 * Gsum delta s).
Proof.
  intros sg lg tw delta x Hsg Hlg Htw Hd HG s. induction s as [|s IH]; intros Hs.
  - simpl. unfold Gsum. simpl.
    replace (nrm (2 ^ lg) (vsub x x)) with 0. { pose proof (nrm_nonneg (2 ^ lg) x). lra. }
    unfold nrm, nsq. rewrite rsum_zero; [symmetry; apply sqrt_0|].
    intros i Hi. unfold vsub, Csub, Cmod2; simpl. ring.
  - assert (HGs : 0.78 * Gsum delta s <= 0.09).
    { eapply Rle_trans; [|exact HG]. apply Rmult_le_compat_l; [lra|].
      apply rsum_mono_len; [lia|]. intros t Ht. pose proof (Hd t ltac:(lia)). rewrite eps_val. lra. }
    pose proof (IH ltac:(lia)) as IHs.
    set (xs := cfft lg tw s x) in *. set (ys := fft_ex sg lg s x) in *.
    set (E := nrm (2 ^ lg) (vsub xs ys)) in *.
    set (r := spn lg s).
    assert (Hr : (0 < r)%nat) by apply pow2_pos.
    assert (HN : (2 ^ lg = 2 ^ s * (2 * r))%nat) by (unfold r; rewrite (pow_lg_split lg s) by lia; lia).
    assert (Hh : hlf lg = (2 ^ s * r)%nat) by (unfold r; apply hlf_split; lia).
    assert (Hloc := cstage_err r (2 ^ s) (tw s) (Wex (2 ^ lg) sg r) xs (delta s) Hr
                      ltac:(intros q Hq; split; [unfold Wex; apply Cmod_EN; apply pow2_pos | apply Htw; [lia | exact Hq]])
                      (Hd s ltac:(lia))).
    rewrite <- HN, <- Hh in Hloc.
    assert (Hlin : nrm (2 ^ lg) (vsub (stage (hlf lg) r (bpx (2 ^ lg) sg r) (bmx (2 ^ lg) sg r) xs)
                                   (stage (hlf lg) r (bpx (2 ^ lg) sg r) (bmx (2 ^ lg) sg r) ys))
                   = sq2 * E).
    { unfold E. rewrite <- (ex_stage_nrm sg lg s (vsub xs ys)) by lia. fold r.
      apply nrm_ext. intros i Hi. unfold bpx, bmx. unfold vsub at 1. rewrite stage_sub. reflexivity. }
    assert (Hxs : nrm (2 ^ lg) xs <= sq2 ^ s * nrm (2 ^ lg) x + E).
    { rewrite <- (fft_ex_nrm sg lg s x) by lia. fold ys.
      eapply Rle_trans; [|apply nrm_add]. right. apply nrm_ext. intros i Hi.
      unfold vadd, vsub. apply Ceq; simpl; ring. }
    simpl cfft. simpl fft_ex. fold xs ys r.
    assert (Htri := nrm_sub_tri (2 ^ lg)
               (cstage (hlf lg) r (tw s) xs)
               (stage (hlf lg) r (bpx (2 ^ lg) sg r) (bmx (2 ^ lg) sg r) xs)
               (stage (hlf lg) r (bpx (2 ^ lg) sg r) (bmx (2 ^ lg) sg r) ys)).
    unfold bpx, bmx in Htri, Hlin. rewrite Hlin in Htri. unfold bpx, bmx.
    assert (Ha : 0 <= 2 * (5.43 * eps + delta s)) by (pose proof (Hd s ltac:(lia)); rewrite eps_val; lra).
    assert (Hloc' : nrm (2 ^ lg) (vsub (cstage (hlf lg) r (tw s) xs)
                   (stage (hlf lg) r (fun q u v => Cadd u (Cmul (Wex (2 ^ lg) sg r q) v))
                      (fun q u v => Csub u (Cmul (Wex (2 ^ lg) sg r q) v)) xs))
             <= 2 * (5.43 * eps + delta s) * (sq2 ^ s * nrm (2 ^ lg) x + E) + 11 * eta_max * sqrt (INR (2 ^ lg))).
    { eapply Rle_trans; [exact Hloc|].
      assert (2 * (5.43 * eps + delta s) * nrm (2 ^ lg) xs <=
              2 * (5.43 * eps + delta s) * (sq2 ^ s * nrm (2 ^ lg) x + E)) by (apply Rmult_le_compat_l; lra).
      lra. }
    unfold Gsum. simpl rsum. fold (Gsum delta s).
    rewrite <- tech_pow_Rmult.
    apply (err_arith E _ (sq2 ^ s) (nrm (2 ^ lg) x) (Gsum delta s) (2 * (5.43 * eps + delta s)) sq2
             (11 * eta_max * sqrt (INR (2 ^ lg)))).
    + apply nrm_nonneg.
    + apply pow_R1_Rle. pose proof sq2_bounds. lra.
    + pose proof sq2_bounds. lra.
    + apply nrm_nonneg.
    + unfold Gsum. apply rsum_nonneg. intros t Ht. pose proof (Hd t ltac:(lia)). rewrite eps_val. lra.
    + exact HGs.
    + exact Ha.
    + pose proof (sqrt_pow2_le lg ltac:(lia)). pose proof (sqrt_pos (INR (2 ^ lg))).
      pose proof eta_nonneg. pose proof eta_tiny. pose proof (Hd s ltac:(lia)).
      split; [nra|]. rewrite eps_val in *. nra.
    + exact IHs.
    + lra.
Qed.

End RoundedFFT.

(* ====================================================================== *)
(* Part E.  Twiddles: half-angle bases and the per-stage tables           *)
(* ====================================================================== *)

Section Twiddles.
Local Open Scope R_scope.

Lemma sqrt_bnd : forall x lo hi, 0 <= lo -> 0 <= hi -> lo * lo <= x <= hi * hi -> lo <= sqrt x <= hi.
Proof.
  intros x lo hi Hl Hh H. split.
  - rewrite <- (sqrt_square lo) by exact Hl. apply sqrt_le_1_alt. lra.
  - apply sqrt_le_of_sq; lra.
Qed.

Lemma abs_inv : forall x y, Rabs x <= y -> - y <= x <= y.
Proof. intros x y H. unfold Rabs in H. destruct (Rcase_abs x); lra. Qed.

(* exact base values cos, sin of 2 pi / 2^q, by the half-angle recursion *)
Definition hstep (b : C) : C :=
  let c' := sqrt ((1 + fst b) / 2) in (c', snd b / (2 * c')).

Fixpoint bex (n : nat) : C :=
  match n with S ((S (S _)) as m) => hstep (bex m) | _ => (0, 1) end.

(* the rounded recursion, as the code computes it *)
Definition hstepr (b : C) : C :=
  let c' := rnd (sqrt (rnd (rnd (1 + fst b) * / 2))) in (c', rnd (snd b / rnd (2 * c'))).

Fixpoint bser (n : nat) : C :=
  match n with S ((S (S _)) as m) => hstepr (bser m) | _ => (0, 1) end.

Lemma bex_S : forall q, (2 <= q)%nat -> bex (S q) = hstep (bex q).
Proof. intros q H. destruct q as [|[|q]]; [lia | lia | reflexivity]. Qed.

Lemma bser_S : forall q, (2 <= q)%nat -> bser (S q) = hstepr (bser q).
Proof. intros q H. destruct q as [|[|q]]; [lia | lia | reflexivity]. Qed.

Lemma bex_cis : forall q, (2 <= q)%nat -> bex q = cis (2 * PI / 2 ^ q).
Proof.
  intros q Hq. induction q as [|q IH]; [lia|].
  destruct (Nat.eq_dec q 1) as [->|Hq1].
  - simpl. unfold cis. replace (2 * PI / (2 * (2 * 1))) with (PI / 2) by field.
    rewrite cos_PI2, sin_PI2. reflexivity.
  - rewrite bex_S by lia. rewrite IH by lia. unfold hstep, cis; simpl.
    set (h := 2 * PI / (2 * 2 ^ q)).
    assert (Eh : 2 * PI / 2 ^ q = 2 * h) by (unfold h; field; apply pow_nonzero; lra).
    rewrite Eh.
    assert (Hp : 4 <= 2 ^ q).
    { replace 4 with (2 ^ 2) by ring. apply Rle_pow; [lra | lia]. }
    pose proof PI_RGT_0.
    assert (H0 : 0 < h) by (unfold h; apply Rdiv_lt_0_compat; nra).
    assert (H1 : h <= PI / 4).
    { unfold h. apply Rmult_le_reg_r with (2 * 2 ^ q); [nra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by nra. nra. }
    assert (Hc : 0 < cos h) by (apply cos_gt_0; lra).
    assert (Ec : sqrt ((1 + cos (2 * h)) / 2) = cos h).
    { rewrite cos_2a_cos. replace ((1 + (2 * cos h * cos h - 1)) / 2) with (cos h * cos h) by field.
      apply sqrt_square. lra. }
    rewrite Ec. f_equal. rewrite sin_2a. field. lra.
Qed.

(* numeric facts on the exact recursion *)
Lemma bex_3 : 0.7071 <= fst (bex 3) <= 0.70711 /\ 0.7071 <= snd (bex 3) <= 0.7072.
Proof.
  simpl. unfold hstep; simpl.
  replace ((1 + 0) / 2) with (/ 2) by field.
  assert (Hs : 0.707106 <= sqrt (/ 2) <= 0.707107) by (apply sqrt_bnd; lra).
  assert (A : / (2 * 0.707107) <= / (2 * sqrt (/ 2))) by (apply Rinv_le_contravar; lra).
  assert (B : / (2 * sqrt (/ 2)) <= / (2 * 0.707106)) by (apply Rinv_le_contravar; lra).
  unfold Rdiv. rewrite Rmult_1_l. lra.
Qed.

Definition binv (b : C) : Prop := 0.7071 <= fst b <= 1 /\ 0 <= snd b <= 0.7072.

Lemma hstep_inv : forall b, binv b ->
  binv (hstep b) /\ 0.92 <= fst (hstep b) /\ fst (hstep b) = sqrt ((1 + fst b) / 2)
  /\ snd (hstep b) = snd b / (2 * fst (hstep b)).
Proof.
  intros [c s] [Hc Hs]. unfold hstep; simpl in *.
  assert (Hq : 0.92 <= sqrt ((1 + c) / 2) <= 1).
  { apply sqrt_bnd; lra. }
  assert (Hs' : 0 <= s / (2 * sqrt ((1 + c) / 2)) <= 0.7072).
  { split.
    - unfold Rdiv. apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra].
    - apply Rmult_le_reg_r with (2 * sqrt ((1 + c) / 2)); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  unfold binv; simpl. repeat split; lra.
Qed.

Lemma bex_inv : forall q, (3 <= q)%nat -> binv (bex q).
Proof.
  intros q Hq. induction q as [|q IH]; [lia|].
  destruct (Nat.eq_dec q 2) as [->|E].
  - pose proof bex_3. unfold binv. lra.
  - rewrite bex_S by lia. apply hstep_inv, IH. lia.
Qed.

Lemma sqrt_diff : forall a b, 0 <= a -> 0 <= b -> 1.4 <= sqrt a + sqrt b ->
  Rabs (sqrt a - sqrt b) <= Rabs (a - b) / 1.4.
Proof.
  intros a b Ha Hb H.
  assert (E : (sqrt a - sqrt b) * (sqrt a + sqrt b) = a - b).
  { replace ((sqrt a - sqrt b) * (sqrt a + sqrt b)) with (sqrt a * sqrt a - sqrt b * sqrt b) by ring.
    rewrite !sqrt_sqrt by assumption. reflexivity. }
  rewrite <- E, Rabs_mult, (Rabs_pos_eq (sqrt a + sqrt b)) by lra.
  pose proof (Rabs_pos (sqrt a - sqrt b)).
  apply Rmult_le_reg_r with 1.4; [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra.
Qed.

(* one rounded half-angle step against the exact one *)
Lemma hstepr_err : forall (b bh : C) (E : R),
  binv b \/ b = (0, 1) ->
  Rabs (fst bh - fst b) <= 4 * eps -> Rabs (snd bh - snd b) <= E -> 0 <= E <= 7 * eps ->
  (b = (0, 1) -> E = 0) ->
  Rabs (fst (hstepr bh) - fst (hstep b)) <= 4 * eps /\ Rabs (snd (hstepr bh) - snd (hstep b)) <= 7 * eps.
Proof.
  intros [c s] [ch sh] E Hb Hc Hs HE HE0. simpl in *.
  assert (Hc01 : 0 <= c <= 1 /\ 0 <= s <= 1) by (destruct Hb as [[H1 H2]|H]; [simpl in *; lra | injection H; intros; subst; lra]).
  pose proof eta_nonneg as Hn. pose proof eta_tiny as Ht.
  pose proof (eps_val) as Ev.
  assert (Eps : 0 < eps) by (rewrite Ev; lra).
  unfold hstepr, hstep; simpl.
  (* the cosine *)
  set (x := (1 + c) / 2).
  set (y1 := rnd (1 + ch)). set (xh := rnd (y1 * / 2)).
  pose proof (rnd_e (1 + ch)) as E1. fold y1 in E1.
  pose proof (rnd_e (y1 * / 2)) as E2. fold xh in E2.
  assert (Hch : -0.01 <= ch <= 1.01) by (apply abs_inv in Hc; rewrite Ev in Hc; lra).
  assert (Hy1 : 0.98 <= y1 <= 2.03).
  { apply abs_inv in E1. rewrite Rabs_pos_eq in E1 by lra. rewrite Ev in *. lra. }
  assert (Hx : Rabs (xh - x) <= 4.03 * eps).
  { apply abs_inv in E1. apply abs_inv in Hc.
    rewrite Rabs_pos_eq in E1 by lra. rewrite (Rabs_pos_eq (y1 * / 2)) in E2 by lra.
    apply abs_inv in E2. unfold x. apply Rabs_le. rewrite Ev in *. lra. }
  assert (Hxr : 0.5 <= x <= 1) by (unfold x; lra).
  assert (Hxh : 0.49 <= xh <= 1.01) by (apply abs_inv in Hx; rewrite Ev in Hx; lra).
  set (cp := sqrt x). set (cph := rnd (sqrt xh)).
  assert (Hcp : 0.7071 <= cp <= 1).
  { unfold cp. apply sqrt_bnd; lra. }
  assert (Hsxh : 0.7 <= sqrt xh <= 1.005).
  { apply sqrt_bnd; lra. }
  assert (Hcpe : Rabs (cph - cp) <= 3.9 * eps).
  { pose proof (rnd_e (sqrt xh)) as E3. fold cph in E3.
    pose proof (sqrt_diff xh x ltac:(lra) ltac:(lra) ltac:(fold cp; lra)) as D.
    rewrite (Rabs_pos_eq (sqrt xh)) in E3 by lra.
    replace (cph - cp) with ((cph - sqrt xh) + (sqrt xh - sqrt x)) by (unfold cp; ring).
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Ev in *. lra. }
  split; [rewrite Ev in *; lra|].
  (* the sine *)
  set (dh := rnd (2 * cph)).
  pose proof (rnd_e (2 * cph)) as E4. fold dh in E4.
  assert (Hcph : 0.7 <= cph <= 1.01) by (apply abs_inv in Hcpe; rewrite Ev in Hcpe; lra).
  rewrite (Rabs_pos_eq (2 * cph)) in E4 by lra.
  assert (Hd : Rabs (dh - 2 * cp) <= 10.1 * eps).
  { replace (dh - 2 * cp) with ((dh - 2 * cph) + 2 * (cph - cp)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult, (Rabs_pos_eq 2) by lra. rewrite Ev in *. lra. }
  assert (Hdh : 1.39 <= dh) by (apply abs_inv in Hd; rewrite Ev in Hd; lra).
  set (q := sh / dh).
  pose proof (rnd_e q) as E5.
  assert (Hshb : -0.01 <= sh <= 1.01) by (apply abs_inv in Hs; rewrite Ev in *; lra).
  assert (Hq : Rabs (q - s / (2 * cp)) <= Rabs (sh - s) / dh + s * (10.1 * eps) / (dh * (2 * cp))).
  { replace (q - s / (2 * cp)) with ((sh - s) / dh + s * (2 * cp - dh) / (dh * (2 * cp)))
      by (unfold q; field; lra).
    eapply Rle_trans; [apply Rabs_triang|].
    unfold Rdiv. rewrite !Rabs_mult, (Rabs_pos_eq (/ dh)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
    rewrite (Rabs_pos_eq s) by lra. rewrite (Rabs_pos_eq (/ (dh * (2 * cp)))) by (apply Rlt_le, Rinv_0_lt_compat; apply Rmult_lt_0_compat; lra).
    rewrite Rabs_minus_sym in Hd.
    apply Rplus_le_compat_l. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; apply Rmult_lt_0_compat; lra|].
    apply Rmult_le_compat_l; lra. }
  assert (Hqa : Rabs q <= 1.01 / 1.39).
  { unfold q. unfold Rdiv. rewrite Rabs_mult, Rabs_pos_eq with (x := / dh) by (apply Rlt_le, Rinv_0_lt_compat; lra).
    apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | apply Rabs_le; lra |].
    apply Rinv_le_contravar; lra. }
  replace (rnd q - s / (2 * cp)) with ((rnd q - q) + (q - s / (2 * cp))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  destruct Hb as [Hbi|Hb0].
  - (* generic step: cp >= 0.92 *)
    destruct Hbi as [Hbc Hbs]; simpl in Hbc, Hbs.
    assert (Hcp2 : 0.92 <= cp).
    { unfold cp, x. pose proof (sqrt_bnd ((1 + c) / 2) 0.92 1 ltac:(lra) ltac:(lra) ltac:(lra)). lra. }
    assert (Hdh2 : 1.83 <= dh) by (apply abs_inv in Hd; rewrite Ev in Hd; lra).
    assert (T1 : Rabs (sh - s) / dh <= E / 1.83).
    { unfold Rdiv. apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | exact Hs |].
      apply Rinv_le_contravar; lra. }
    assert (T2 : s * (10.1 * eps) / (dh * (2 * cp)) <= 0.7072 * (10.1 * eps) / (1.83 * 1.84)).
    { unfold Rdiv. apply Rmult_le_compat;
        [apply Rmult_le_pos; lra | apply Rlt_le, Rinv_0_lt_compat; apply Rmult_lt_0_compat; lra
        | apply Rmult_le_compat_r; lra |].
      apply Rinv_le_contravar; [lra | apply Rmult_le_compat; lra]. }
    assert (Hqa2 : Rabs q <= 1.01 / 1.83).
    { unfold q. unfold Rdiv. rewrite Rabs_mult, Rabs_pos_eq with (x := / dh) by (apply Rlt_le, Rinv_0_lt_compat; lra).
      apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | apply Rabs_le; lra |].
      apply Rinv_le_contravar; lra. }
    rewrite Ev in *. lra.
  - (* first step: from (0, 1), exact sine *)
    injection Hb0 as -> ->. rewrite (HE0 eq_refl) in Hs.
    assert (T1 : Rabs (sh - 1) / dh <= 0) by (unfold Rdiv; apply abs_inv in Hs;
      replace (sh - 1) with 0 by lra; rewrite Rabs_R0; lra).
    assert (Hcp2 : 0.7071 <= cp) by lra.
    assert (T2 : 1 * (10.1 * eps) / (dh * (2 * cp)) <= 10.1 * eps / (1.39 * 1.4142)).
    { unfold Rdiv. rewrite Rmult_1_l. apply Rmult_le_compat_l; [lra|].
      apply Rinv_le_contravar; [lra | apply Rmult_le_compat; lra]. }
    rewrite Ev in *. lra.
Qed.

Lemma bser_err : forall q, (2 <= q)%nat ->
  Rabs (fst (bser q) - fst (bex q)) <= 4 * eps /\
  Rabs (snd (bser q) - snd (bex q)) <= (if Nat.eq_dec q 2 then 0 else 7 * eps).
Proof.
  intros q Hq. pose proof eps_val as Ev.
  induction q as [|q IH]; [lia|].
  destruct (Nat.eq_dec q 1) as [->|E1].
  - simpl. rewrite !Rminus_diag, Rabs_R0. split; [rewrite Ev; lra | lra].
  - rewrite bser_S, bex_S by lia.
    destruct (IH ltac:(lia)) as [Hc Hs].
    destruct (Nat.eq_dec (S q) 2) as [E2|_]; [lia|].
    destruct (Nat.eq_dec q 2) as [->|E3].
    + apply (hstepr_err _ _ 0); [right; reflexivity | exact Hc | exact Hs | split; [lra | rewrite Ev; lra] | intros; reflexivity].
    + apply (hstepr_err _ _ (7 * eps)); auto.
      * left. apply bex_inv. lia.
      * rewrite Ev; lra.
      * intros H. exfalso. pose proof (bex_inv q ltac:(lia)) as Hi. rewrite H in Hi.
        unfold binv in Hi; simpl in Hi. lra.
Qed.

Lemma bser_cmod_err : forall q, (2 <= q)%nat -> Cmod (Csub (bser q) (bex q)) <= 11 * eps.
Proof.
  intros q Hq. eapply Rle_trans; [apply Cmod_le_reim|]. destruct (bser_err q Hq) as [H1 H2].
  unfold Csub; simpl. destruct (Nat.eq_dec q 2); pose proof eps_val; lra.
Qed.

Lemma Cmod_bex : forall q, (2 <= q)%nat -> Cmod (bex q) = 1.
Proof. intros. rewrite bex_cis by assumption. apply Cmod_cis. Qed.

(* the per-stage twiddle tables: stage s holds w^k, k < 2^s, w = exp(2 i pi / 2^(s+1)) *)
Fixpoint twr (s k : nat) : C :=
  match s with
  | O => C1
  | S s' => if Nat.even k then twr s' (Nat.div2 k) else cmulr (twr s' (Nat.div2 k)) (bser (s' + 2))
  end.

Definition Wf (s k : nat) : C := cis (2 * PI * INR k / 2 ^ (S s)).

Lemma Wf_even : forall s k, Wf (S s) (2 * k) = Wf s k.
Proof. intros s k. unfold Wf. f_equal. rewrite mult_INR. simpl. field; repeat split; try apply pow_nonzero; lra. Qed.

Lemma Wf_odd : forall s k, Wf (S s) (2 * k + 1) = Cmul (Wf s k) (bex (s + 2)).
Proof.
  intros s k. rewrite bex_cis by lia. unfold Wf. rewrite <- cis_add. f_equal.
  rewrite plus_INR, mult_INR, pow_add. simpl. field; repeat split; try apply pow_nonzero; lra.
Qed.

Lemma twr_err : forall s k, (s <= 20)%nat -> (k < 2 ^ s)%nat ->
  Cmod (Csub (twr s k) (Wf s k)) <= 15.1 * INR s * eps.
Proof.
  intros s. pose proof eps_val as Ev. pose proof eta_nonneg. pose proof eta_tiny.
  induction s as [|s IH]; intros k Hs Hk.
  - simpl in Hk. assert (k = 0%nat) by lia. subst k. simpl. unfold Wf, cis, C1, Csub; simpl.
    replace (2 * PI * 0 / (2 * 1)) with 0 by field. rewrite cos_0, sin_0.
    replace (1 - 1) with 0 by ring. replace (0 - 0) with 0 by ring.
    unfold Cmod, Cmod2; simpl. replace (0 * 0 + 0 * 0) with 0 by ring. rewrite sqrt_0. lra.
  - assert (Hk2 : (Nat.div2 k < 2 ^ s)%nat).
    { pose proof (Nat.div2_odd k) as D. simpl in Hk. destruct (Nat.odd k); simpl in D; lia. }
    pose proof (IH (Nat.div2 k) ltac:(lia) Hk2) as Hd.
    assert (Hs1 : 15.1 * INR s * eps <= 0.001).
    { assert (INR s <= 20) by (replace 20 with (INR 20) by (simpl; lra); apply le_INR; lia).
      rewrite Ev. pose proof (pos_INR s). nra. }
    rewrite S_INR.
    simpl twr. pose proof (Nat.div2_odd k) as D. destruct (Nat.even k) eqn:Ek.
    + rewrite <- Nat.negb_odd in Ek. destruct (Nat.odd k); [discriminate|]. simpl in D.
      assert (HW : Wf (S s) k = Wf s (Nat.div2 k)) by (rewrite <- (Wf_even s (Nat.div2 k)); f_equal; lia).
      rewrite HW. pose proof (pos_INR s). rewrite Ev in *. lra.
    + rewrite <- Nat.negb_odd in Ek. destruct (Nat.odd k); [|discriminate]. simpl in D.
      assert (HWo : Wf (S s) k = Cmul (Wf s (Nat.div2 k)) (bex (s + 2))) by (rewrite <- (Wf_odd s (Nat.div2 k)); f_equal; lia).
      rewrite HWo.
      set (t := twr s (Nat.div2 k)) in *. set (W := Wf s (Nat.div2 k)) in *.
      set (b := bex (s + 2)). set (bh := bser (s + 2)).
      pose proof (bser_cmod_err (s + 2) ltac:(lia)) as Hb. fold b bh in Hb.
      pose proof (cmulr_err t bh) as Hm.
      assert (HW : Cmod W = 1) by apply Cmod_cis.
      assert (Hb1 : Cmod b = 1) by (apply Cmod_bex; lia).
      assert (Ht : Cmod t <= 1 + 15.1 * INR s * eps).
      { replace t with (Cadd W (Csub t W)) by (apply Ceq; simpl; ring).
        eapply Rle_trans; [apply Cmod_triangle|]. lra. }
      assert (Hbh : Cmod bh <= 1 + 11 * eps).
      { replace bh with (Cadd b (Csub bh b)) by (apply Ceq; simpl; ring).
        eapply Rle_trans; [apply Cmod_triangle|]. lra. }
      replace (Csub (cmulr t bh) (Cmul W b))
        with (Cadd (Cadd (Csub (cmulr t bh) (Cmul t bh)) (Cmul (Csub t W) bh)) (Cmul W (Csub bh b)))
        by (apply Ceq; simpl; ring).
      eapply Rle_trans; [apply Cmod_triangle|].
      eapply Rle_trans; [apply Rplus_le_compat_r, Cmod_triangle|].
      rewrite !Cmod_mul, HW.
      pose proof (Cmod_nonneg t). pose proof (Cmod_nonneg bh). pose proof (Cmod_nonneg (Csub t W)).
      assert (P1 : Cmod t * Cmod bh <= (1 + 15.1 * INR s * eps) * (1 + 11 * eps)) by (apply Rmult_le_compat; lra).
      assert (P2 : Cmod (Csub t W) * Cmod bh <= 15.1 * INR s * eps * (1 + 11 * eps)) by (apply Rmult_le_compat; lra).
      pose proof (pos_INR s). rewrite Ev in *. nra.
Qed.

Lemma twr_bound : forall s k, (s <= 20)%nat -> (k < 2 ^ s)%nat -> Cmod (twr s k) <= 1.001.
Proof.
  intros s k Hs Hk. pose proof (twr_err s k Hs Hk) as H.
  assert (HW : Cmod (Wf s k) = 1) by apply Cmod_cis.
  replace (twr s k) with (Cadd (Wf s k) (Csub (twr s k) (Wf s k))) by (apply Ceq; simpl; ring).
  eapply Rle_trans; [apply Cmod_triangle|].
  assert (INR s <= 20) by (replace 20 with (INR 20) by (simpl; lra); apply le_INR; lia).
  pose proof eps_val. pose proof (pos_INR s). nra.
Qed.

(* the stage twiddles against the exact ones of the transform *)
Lemma Wex_Wf : forall lg s k, (s < lg)%nat ->
  Wex (2 ^ lg) 1 (spn lg s) k = Wf s k /\ Wex (2 ^ lg) (-1) (spn lg s) k = Cconj (Wf s k).
Proof.
  intros lg s k Hs. unfold Wex, EN, Wf.
  assert (Hsp : INR (spn lg s) <> 0) by (apply not_0_INR; unfold spn; pose proof (pow2_pos (lg - 1 - s)); lia).
  assert (HN : INR (2 ^ lg) <> 0) by (apply not_0_INR; pose proof (pow2_pos lg); lia).
  assert (E : 2 * PI * IZR (1 * Z.of_nat (spn lg s) * Z.of_nat k) / INR (2 ^ lg) = 2 * PI * INR k / 2 ^ S s).
  { rewrite Z.mul_1_l, mult_IZR, <- !INR_IZR_INZ, (pow_lg_split lg s Hs), !mult_INR, pow_INR.
    rewrite <- tech_pow_Rmult. replace (INR 2) with 2 by (simpl; lra).
    field. split; [apply pow_nonzero; lra | exact Hsp]. }
  split.
  - rewrite E. reflexivity.
  - rewrite <- cis_neg. f_equal. rewrite <- E.
    replace (-1 * Z.of_nat (spn lg s) * Z.of_nat k)%Z with (- (1 * Z.of_nat (spn lg s) * Z.of_nat k))%Z by ring.
    rewrite opp_IZR. field. exact HN.
Qed.

Lemma Cmod_conj_sub : forall a b, Cmod (Csub (Cconj a) (Cconj b)) = Cmod (Csub a b).
Proof. intros. unfold Cmod, Cmod2, Csub, Cconj; simpl. f_equal. ring. Qed.

End Twiddles.

(* ====================================================================== *)
(* Part F.  The program                                                   *)
(* ====================================================================== *)

Local Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

(* the one loop: for i = lo .. hi - 1, s := f i s *)
Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (f : int -> St -> St) (i : int) (s : St)
    (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.

Definition loop (hi : int) (f : int -> St -> St) (i : int) (s : St) : St :=
  wloop hi f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* the smallest k with L <= 2^k (k < 63) *)
Fixpoint lg_find (L k : int) (H : Acc (Zwf 0) (gap 62 k)) {struct H} : int :=
  match bdec (k <? 62) with
  | left Hk => if L <=? (1 << k) then k else lg_find L (k + 1) (Acc_inv H (dec_step 62 k Hk))
  | right _ => k
  end.

Definition log2up (L : int) : int := lg_find L 0 (Zwf_well_founded 0 (gap 62 0)).

(* --- twiddles: stage s (s < lg) at offsets 2^s .. 2^(s+1) - 1 --- *)

Definition tw_cell (m hm : int) (bc bs : float) (k : int) (st : array float * array float)
    : array float * array float :=
  let '(tre, tim) := st in
  let src := hm + (k >> 1) in
  let ar := tre.[src] in
  let ai := tim.[src] in
  if (k land 1) =? 0 then (tre.[m + k <- ar], tim.[m + k <- ai])
  else (tre.[m + k <- (ar * bc - ai * bs)%float], tim.[m + k <- (ar * bs + ai * bc)%float]).

Definition tw_stage (s : int) (st : array float * array float * float * float)
    : array float * array float * float * float :=
  let '(tre, tim, bc, bs) := st in
  let m := 1 << s in
  let '(tre, tim) := loop m (tw_cell m (1 << (s - 1)) bc bs) 0 (tre, tim) in
  let c' := PrimFloat.sqrt ((1 + bc) * 0.5)%float in
  (tre, tim, c', (bs / (2 * c'))%float).

Definition build_tw (lg N : int) : array float * array float :=
  let tre := (PArray.make N 0%float).[1 <- 1%float] in
  let tim := PArray.make N 0%float in
  let '(tre, tim, _, _) := loop lg tw_stage 1 (tre, tim, 0%float, 1%float) in
  (tre, tim).

(* --- one stage of the transform: span r = 2^sh, twiddles at m + q --- *)

Definition bfly (sh m half : int) (neg : bool) (sre sim tre tim : array float)
    (j : int) (st : array float * array float) : array float * array float :=
  let '(dre, dim) := st in
  let q := j >> sh in
  let i1 := j + (q << sh) in
  let i2 := i1 + (1 << sh) in
  let wr := tre.[m + q] in
  let wi := if neg then (- tim.[m + q])%float else tim.[m + q] in
  let ur := sre.[i1] in
  let ui := sim.[i1] in
  let vr := sre.[i2] in
  let vi := sim.[i2] in
  let tr := (wr * vr - wi * vi)%float in
  let ti := (wr * vi + wi * vr)%float in
  (dre.[j <- (ur + tr)%float].[j + half <- (ur - tr)%float],
   dim.[j <- (ui + ti)%float].[j + half <- (ui - ti)%float]).

Definition fft_stage (lg half : int) (neg : bool) (tre tim : array float) (s : int)
    (st : array float * array float * array float * array float)
    : array float * array float * array float * array float :=
  let '(sre, sim, dre, dim) := st in
  let '(dre, dim) := loop half (bfly (lg - 1 - s) (1 << s) half neg sre sim tre tim) 0 (dre, dim) in
  (dre, dim, sre, sim).

Definition fft (lg half : int) (neg : bool) (tre tim : array float) (re im : array float)
    : array float * array float :=
  let N := half + half in
  let '(re, im, _, _) := loop lg (fft_stage lg half neg tre tim) 0
                            (re, im, PArray.make N 0%float, PArray.make N 0%float) in
  (re, im).

(* --- limbs: c = sum_i (d_i - 32) 64^i, d_i the base-64 digits of c + KOFF --- *)

Definition KOFF : int := 34905131040.

Definition limb (c i : int) : float :=
  (of_uint63 (((c + KOFF) >> (6 * i)) land 63) - 32)%float.

Definition load (x : array sint) (n N i : int) : array float :=
  loop n (fun t a => a.[t <- limb x.[t] i]) 0 (PArray.make N 0%float).

Definition copy_out (N off : int) (yr yi : array float) (st : array float * array float)
    : array float * array float :=
  loop N (fun k st => let '(BR, BI) := st in (BR.[off + k <- yr.[k]], BI.[off + k <- yi.[k]])) 0 st.

Definition NL : int := 6.

Definition fwd_all (x : array sint) (n lg half : int) (tre tim : array float)
    : array float * array float :=
  let N := half + half in
  loop NL (fun i st =>
      let '(yr, yi) := fft lg half false tre tim (load x n N i) (PArray.make N 0%float) in
      copy_out N (i * N) yr yi st) 0 (PArray.make (NL * N) 0%float, PArray.make (NL * N) 0%float).

(* --- pointwise products: P = sum_{i+j=w} A_i B_j + I * sum_{i+j=w+1} A_i B_j, w = 2g --- *)

Definition cacc (ar ai br bi : float) (st : float * float) : float * float :=
  let '(qr, qi) := st in ((qr + (ar * br - ai * bi))%float, (qi + (ar * bi + ai * br))%float).

Definition pterm (w N k : int) (AR AI BR BI : array float) (i : int) (st : float * float) : float * float :=
  if andb (i <=? w) (w - i <? NL) then
    cacc AR.[i * N + k] AI.[i * N + k] BR.[(w - i) * N + k] BI.[(w - i) * N + k] st
  else st.

Definition pcell (g N : int) (AR AI BR BI : array float) (k : int) (st : array float * array float)
    : array float * array float :=
  let '(pr, pim) := st in
  let '(q0r, q0i) := loop NL (pterm (g + g) N k AR AI BR BI) 0 (0%float, 0%float) in
  let '(q1r, q1i) := loop NL (pterm (g + g + 1) N k AR AI BR BI) 0 (0%float, 0%float) in
  (pr.[k <- (q0r - q1i)%float], pim.[k <- (q0i + q1r)%float]).

Definition products (g N : int) (AR AI BR BI : array float) : array float * array float :=
  loop N (pcell g N AR AI BR BI) 0 (PArray.make N 0%float, PArray.make N 0%float).

(* --- reading back: nearest integer of z (|z| < 2^51) as a 63-bit word --- *)

Definition MAGIC : float := 6755399441055744%float.
Definition MAGICI : int := 6755399441055744.

Definition toint (z : float) : int :=
  let (f, _) := frshiftexp (z + MAGIC)%float in normfr_mantissa f - MAGICI.

Definition accum (g L : int) (invN : float) (yr yi : array float) (R : array int) : array int :=
  loop L (fun q R =>
      let d0 := toint (yr.[q] * invN)%float in
      let d1 := toint (yi.[q] * invN)%float in
      R.[q <- R.[q] + (d0 << (12 * g)) + (d1 << (12 * g + 6))]) 0 R.

Definition polymul_impl (x y : array sint) : array sint :=
  let na := PArray.length x in
  let nb := PArray.length y in
  let L := na + nb - 1 in
  let lg := log2up L in
  let half := 1 << (lg - 1) in
  let N := half + half in
  let '(tre, tim) := build_tw lg N in
  let '(AR, AI) := fwd_all x na lg half tre tim in
  let '(BR, BI) := fwd_all y nb lg half tre tim in
  let invN := (1 / of_uint63 N)%float in
  loop NL (fun g R =>
      let '(pr, pim) := products g N AR AI BR BI in
      let '(yr, yi) := fft lg half true tre tim pr pim in
      accum g L invN yr yi R) 0 (PArray.make L 0).

(* ====================================================================== *)
(* Part G.  The program against the rounded mirrors                       *)
(* ====================================================================== *)

Section LoopProof.
Context {St : Type}.

Lemma wloop_eq : forall (hi : int) (f : int -> St -> St) i s H,
  wloop hi f i s H =
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep. unfold loop.
  assert (G : forall n i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = n ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t -> P hi (wloop hi f i t H)).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H En Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      apply (IH (gap hi (i + 1))).
      + rewrite <- En. apply dec_step; exact Hlt.
      + reflexivity.
      + pose proof (to_Z_bounded hi). assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
      + apply Hstep; auto; lia.
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      assert (to_Z i = to_Z hi) by lia. apply to_Z_inj in H1. subst i. exact Pt. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

End LoopProof.

Lemma lg_find_eq : forall L k H, lg_find L k H =
  match bdec (k <? 62) with
  | left Hk => if L <=? (1 << k) then k else lg_find L (k + 1) (Acc_inv H (dec_step 62 k Hk))
  | right _ => k
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma lg_find_spec : forall L z k H, gap 62 k = z -> (to_Z k <= 62)%Z ->
  (forall k', (to_Z k' < to_Z k)%Z -> to_Z L > 2 ^ to_Z k')%Z ->
  (to_Z k <= to_Z (lg_find L k H) <= 62)%Z /\
  (forall k', (to_Z k' < to_Z (lg_find L k H))%Z -> to_Z L > 2 ^ to_Z k')%Z /\
  (to_Z (lg_find L k H) < 62 -> to_Z L <= 2 ^ to_Z (lg_find L k H))%Z.
Proof.
  intros L z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k H Hz Hk Hpre. rewrite lg_find_eq.
  destruct (bdec (k <? 62)) as [Hlt|Hge].
  - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'. change (to_Z 62) with 62%Z in Hlt'.
    assert (Hsh : to_Z (1 << k) = (2 ^ to_Z k)%Z).
    { rewrite lsl_spec. change (to_Z 1) with 1%Z. rewrite Z.mul_1_l. apply Z.mod_small.
      pose proof (to_Z_bounded k). split; [lia|].
      change wB with (2 ^ 63)%Z. apply Z.pow_lt_mono_r; lia. }
    destruct (L <=? 1 << k) eqn:E.
    + rewrite Uint63.leb_spec, Hsh in E. split; [lia|]. split; [exact Hpre|]. intros _. exact E.
    + rewrite <- Bool.not_true_iff_false, Uint63.leb_spec, Hsh in E.
      assert (Hk1 : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
      destruct (IH (gap 62 (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hlt) (k + 1)
                 (Acc_inv H (dec_step 62 k Hlt)) eq_refl ltac:(lia)) as [A [B C]].
      * intros k' Hk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [Ee|Ne]; [rewrite Ee; lia | apply Hpre; lia].
      * split; [lia|]. split; assumption.
  - assert (~ (to_Z k < 62)%Z) by (rewrite <- (Uint63.ltb_spec k 62); congruence).
    split; [lia|]. split; [exact Hpre | lia].
Qed.

Lemma log2up_spec : forall L : int, (3 <= to_Z L <= 2 ^ 18)%Z ->
  (1 <= to_Z (log2up L) <= 18 /\ to_Z L <= 2 ^ to_Z (log2up L) < 2 * to_Z L)%Z.
Proof.
  intros L HL. unfold log2up.
  destruct (lg_find_spec L _ 0 (Zwf_well_founded 0 (gap 62 0)) eq_refl ltac:(change (to_Z 0) with 0%Z; lia)
              ltac:(intros k' Hk'; change (to_Z 0) with 0%Z in Hk'; pose proof (to_Z_bounded k'); lia))
    as [A [B C]].
  set (r := lg_find L 0 _) in *.
  assert (Hr18 : (to_Z r <= 18)%Z).
  { destruct (Z_le_gt_dec (to_Z r) 18) as [|Hgt]; [assumption|].
    exfalso. specialize (B 18 ltac:(change (to_Z 18) with 18%Z; lia)).
    change (to_Z 18) with 18%Z in B. lia. }
  assert (HC : (to_Z L <= 2 ^ to_Z r)%Z) by (apply C; lia).
  assert (Hr1 : (1 <= to_Z r)%Z).
  { destruct (Z_le_gt_dec 1 (to_Z r)) as [|Hlt]; [assumption|].
    assert (to_Z r = 0%Z) by lia. rewrite H in HC. simpl in HC. lia. }
  split; [lia|]. split; [exact HC|].
  specialize (B (r - 1) ltac:(sia)).
  assert (E : to_Z (r - 1) = (to_Z r - 1)%Z) by sia. rewrite E in B.
  replace (to_Z r) with (to_Z r - 1 + 1)%Z at 1 by lia.
  rewrite Z.pow_add_r by lia. lia.
Qed.

(* PArray plumbing, at [array float] and [array int] *)
Lemma fget_set_same : forall (t : array float) (i : int) (v : float),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same float t i v H). Qed.

Lemma fget_set_other : forall (t : array float) (i j : int) (v : float),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other float t i j v H). Qed.

Lemma flength_set : forall (t : array float) (i : int) (v : float),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set float t i v). Qed.

Lemma flength_make : forall (n : int) (v : float), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  assert (E : PArray.length (PArray.make n v) = if n <=? max_length then n else max_length)
    by exact (length_make float n v).
  etransitivity; [exact E|].
  replace (n <=? max_length) with true; [reflexivity|]. symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma fget_make : forall (n i : int) (v : float), (PArray.make n v).[i] = v.
Proof. intros n i v. exact (get_make float v n i). Qed.

Lemma iget_set_same : forall (t : array int) (i : int) (v : int),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same int t i v H). Qed.

Lemma iget_set_other : forall (t : array int) (i j : int) (v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.

Lemma ilength_set : forall (t : array int) (i : int) (v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.

Lemma ilength_make : forall (n : int) (v : int), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  assert (E : PArray.length (PArray.make n v) = if n <=? max_length then n else max_length)
    by exact (length_make int n v).
  etransitivity; [exact E|].
  replace (n <=? max_length) with true; [reflexivity|]. symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma ltb_true : forall i n : int, (to_Z i < to_Z n)%Z -> (i <? n) = true.
Proof. intros. rewrite Uint63.ltb_spec. exact H. Qed.

Lemma int_neq : forall i j : int, to_Z i <> to_Z j -> i <> j.
Proof. intros i j H E. apply H. rewrite E. reflexivity. Qed.

Lemma of_nat_to_Z : forall n : nat, (Z.of_nat n < wB)%Z -> to_Z (of_nat n) = Z.of_nat n.
Proof.
  intros n H. rewrite of_Z_spec. apply Z.mod_small. lia.
Qed.

Lemma of_nat_to_nat : forall i : int, of_nat (Z.to_nat (to_Z i)) = i.
Proof.
  intros i. apply to_Z_inj. pose proof (to_Z_bounded i).
  rewrite of_nat_to_Z by lia. lia.
Qed.

Lemma lsl_val : forall (a k : int), (to_Z a * 2 ^ to_Z k < wB)%Z ->
  to_Z (a << k) = (to_Z a * 2 ^ to_Z k)%Z.
Proof.
  intros a k H. rewrite lsl_spec. apply Z.mod_small. pose proof (to_Z_bounded a).
  pose proof (Z.pow_nonneg 2 (to_Z k) ltac:(lia)). nia.
Qed.

Lemma pow2_Z_small : forall k : int, (to_Z k <= 30)%Z -> to_Z (1 << k) = (2 ^ to_Z k)%Z.
Proof.
  intros k H. rewrite lsl_val; change (to_Z 1) with 1%Z; [lia|].
  pose proof (to_Z_bounded k). rewrite Z.mul_1_l.
  apply Z.le_lt_trans with (2 ^ 30)%Z; [apply Z.pow_le_mono_r; lia | reflexivity].
Qed.

Lemma lsr_val : forall (a k : int), to_Z (a >> k) = (to_Z a / 2 ^ to_Z k)%Z.
Proof. intros. apply lsr_spec. Qed.

(* floats: transport with explicit magnitude bounds *)
Section FloatOps.
Local Open Scope R_scope.

Definition bp (k : Z) : R := Raux.bpow Zaux.radix2 k.

Lemma bp_ge1 : forall k, (0 <= k)%Z -> 1 <= bp k.
Proof. intros k Hk. unfold bp. change 1 with (Raux.bpow Zaux.radix2 0). apply Raux.bpow_le. exact Hk. Qed.

Lemma bp_gap : forall a b, (0 <= a)%Z -> (a + 3 <= b)%Z -> 8 * bp a <= bp b.
Proof.
  intros a b Ha Hab. unfold bp. replace b with (a + (b - a))%Z by lia.
  rewrite Raux.bpow_plus. pose proof (Raux.bpow_ge_0 Zaux.radix2 a).
  assert (8 <= Raux.bpow Zaux.radix2 (b - a)).
  { change 8 with (Raux.bpow Zaux.radix2 3). apply Raux.bpow_le. lia. }
  nra.
Qed.

Lemma bp_mul : forall a b, bp (a + b) = bp a * bp b.
Proof. intros. unfold bp. apply Raux.bpow_plus. Qed.

Lemma bp_big : forall k, (10 <= k)%Z -> 1024 <= bp k.
Proof. intros k Hk. unfold bp. change 1024 with (Raux.bpow Zaux.radix2 10). apply Raux.bpow_le. lia. Qed.

Lemma bp900_big : 1024 <= bp 900.
Proof. unfold bp. change 1024 with (Raux.bpow Zaux.radix2 10). apply Raux.bpow_le. lia. Qed.

Lemma bp800_big : 1024 <= bp 800.
Proof. unfold bp. change 1024 with (Raux.bpow Zaux.radix2 10). apply Raux.bpow_le. lia. Qed.

Lemma ovf_ok : forall z, Rabs z <= bp 1000 -> Rabs (rnd z) < Raux.bpow Zaux.radix2 1024.
Proof. intros z H. apply rnd_no_overflow_small. exact H. Qed.

Lemma rnd_bnd : forall z M, Rabs z <= M -> Rabs (rnd z) <= 2 * M + 1.
Proof.
  intros z M H. pose proof (rnd_e z). pose proof eps_val. pose proof eta_nonneg. pose proof eta_tiny.
  pose proof (Rabs_pos z).
  replace (rnd z) with ((rnd z - z) + z) by ring. eapply Rle_trans; [apply Rabs_triang|].
  rewrite eps_val in *. lra.
Qed.

Lemma rmul_ok : forall (a b : float) x y A B, repr a x -> repr b y ->
  Rabs x <= A -> Rabs y <= B -> A * B <= bp 900 ->
  repr (a * b)%float (rnd (x * y)) /\ Rabs (rnd (x * y)) <= 2 * (A * B) + 1.
Proof.
  intros a b x y A B Ha Hb HA HB HAB.
  assert (H : Rabs (x * y) <= A * B).
  { rewrite Rabs_mult. apply Rmult_le_compat; auto using Rabs_pos. }
  split; [|apply rnd_bnd; exact H].
  apply repr_mul; auto. apply ovf_ok. pose proof (bp_gap 900 1000 ltac:(lia) ltac:(lia)).
  pose proof (bp_ge1 900 ltac:(lia)). lra.
Qed.

Lemma radd_ok : forall (a b : float) x y A B, repr a x -> repr b y ->
  Rabs x <= A -> Rabs y <= B -> A + B <= bp 900 ->
  repr (a + b)%float (rnd (x + y)) /\ Rabs (rnd (x + y)) <= 2 * (A + B) + 1.
Proof.
  intros a b x y A B Ha Hb HA HB HAB.
  assert (H : Rabs (x + y) <= A + B) by (eapply Rle_trans; [apply Rabs_triang | lra]).
  split; [|apply rnd_bnd; exact H].
  apply repr_add; auto. apply ovf_ok. pose proof (bp_gap 900 1000 ltac:(lia) ltac:(lia)).
  pose proof (bp_ge1 900 ltac:(lia)). lra.
Qed.

Lemma rsub_ok : forall (a b : float) x y A B, repr a x -> repr b y ->
  Rabs x <= A -> Rabs y <= B -> A + B <= bp 900 ->
  repr (a - b)%float (rnd (x - y)) /\ Rabs (rnd (x - y)) <= 2 * (A + B) + 1.
Proof.
  intros a b x y A B Ha Hb HA HB HAB.
  assert (H : Rabs (x - y) <= A + B).
  { unfold Rminus. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra. }
  split; [|apply rnd_bnd; exact H].
  apply repr_sub; auto. apply ovf_ok. pose proof (bp_gap 900 1000 ltac:(lia) ltac:(lia)).
  pose proof (bp_ge1 900 ltac:(lia)). lra.
Qed.

Lemma repr_cmulr : forall (ar ai br bi : float) (a b : C) A B,
  repr ar (fst a) -> repr ai (snd a) -> repr br (fst b) -> repr bi (snd b) ->
  Rabs (fst a) <= A -> Rabs (snd a) <= A -> Rabs (fst b) <= B -> Rabs (snd b) <= B ->
  0 <= A -> 0 <= B -> A * B <= bp 800 ->
  repr (ar * br - ai * bi)%float (fst (cmulr a b)) /\ repr (ar * bi + ai * br)%float (snd (cmulr a b)) /\
  Rabs (fst (cmulr a b)) <= 8 * (A * B) + 5 /\ Rabs (snd (cmulr a b)) <= 8 * (A * B) + 5.
Proof.
  intros ar ai br bi a b A B Har Hai Hbr Hbi H1 H2 H3 H4 HA HB HAB.
  pose proof (bp_gap 800 900 ltac:(lia) ltac:(lia)). pose proof (bp_ge1 800 ltac:(lia)).
  assert (HAB' : A * B <= bp 900) by lra.
  destruct (rmul_ok ar br _ _ A B Har Hbr H1 H3 HAB') as [R1 B1].
  destruct (rmul_ok ai bi _ _ A B Hai Hbi H2 H4 HAB') as [R2 B2].
  destruct (rmul_ok ar bi _ _ A B Har Hbi H1 H4 HAB') as [R3 B3].
  destruct (rmul_ok ai br _ _ A B Hai Hbr H2 H3 HAB') as [R4 B4].
  destruct (rsub_ok _ _ _ _ _ _ R1 R2 B1 B2 ltac:(lra)) as [R5 B5].
  destruct (radd_ok _ _ _ _ _ _ R3 R4 B3 B4 ltac:(lra)) as [R6 B6].
  unfold cmulr; simpl. split; [exact R5|]. split; [exact R6|]. split; lra.
Qed.

Lemma repr_lit_half : repr (0.5)%float (/ 2).
Proof. split; [reflexivity|]. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl. field. Qed.

Lemma repr_lit_two : repr (2)%float 2.
Proof. split; [reflexivity|]. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl. field. Qed.

Lemma repr_lit_one : repr (1)%float 1.
Proof. split; [reflexivity|]. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl. field. Qed.

Lemma repr_lit_zero : repr (0)%float 0.
Proof. split; [reflexivity|]. reflexivity. Qed.

Lemma repr_lit_32 : repr (32)%float 32.
Proof. split; [reflexivity|]. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl. field. Qed.

Lemma repr_lit_magic : repr MAGIC 6755399441055744.
Proof. split; [reflexivity|]. unfold fval, MAGIC. vm_compute Prim2SF. cbv iota beta. simpl. field. Qed.

End FloatOps.

Lemma nat_even_mod : forall n, Nat.even n = (Z.of_nat n mod 2 =? 0)%Z.
Proof.
  intros n. destruct (Nat.Even_or_Odd n) as [[p Hp]|[p Hp]]; subst n.
  - replace (2 * p)%nat with (0 + 2 * p)%nat by lia. rewrite Nat.even_add_mul_2.
    replace (Z.of_nat (0 + 2 * p)) with (0 + Z.of_nat p * 2)%Z by lia.
    rewrite Z_mod_plus_full. reflexivity.
  - replace (2 * p + 1)%nat with (1 + 2 * p)%nat by lia. rewrite Nat.even_add_mul_2.
    replace (Z.of_nat (1 + 2 * p)) with (1 + Z.of_nat p * 2)%Z by lia.
    rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma parity_int : forall k : int, ((k land 1) =? 0) = Nat.even (Z.to_nat (to_Z k)).
Proof.
  intros k. rewrite nat_even_mod. pose proof (to_Z_bounded k). rewrite Z2Nat.id by lia.
  destruct ((k land 1) =? 0) eqn:E.
  - apply Uint63.eqb_spec in E. assert (E' : to_Z (k land 1) = 0%Z) by (rewrite E; reflexivity).
    rewrite land_spec' in E'. change (to_Z 1) with (Z.ones 1) in E'. rewrite Z.land_ones in E' by lia.
    change (2 ^ 1)%Z with 2%Z in E'. rewrite E'. reflexivity.
  - assert (E' : to_Z (k land 1) <> 0%Z).
    { intro F. assert (k land 1 = 0) by (apply to_Z_inj; exact F).
      rewrite <- Uint63.eqb_spec in H0. congruence. }
    rewrite land_spec' in E'. change (to_Z 1) with (Z.ones 1) in E'. rewrite Z.land_ones in E' by lia.
    change (2 ^ 1)%Z with 2%Z in E'. symmetry. apply Z.eqb_neq. exact E'.
Qed.

Section TwBuild.
Local Open Scope R_scope.

Definition TWrep (tre tim : array float) (S : nat) : Prop :=
  forall s k, (s < S)%nat -> (k < 2 ^ s)%nat ->
    repr tre.[of_nat (2 ^ s + k)] (fst (twr s k)) /\ repr tim.[of_nat (2 ^ s + k)] (snd (twr s k)).

Lemma bex_bnd : forall q, (2 <= q)%nat -> 0 <= fst (bex q) <= 1 /\ 0 <= snd (bex q) <= 1.
Proof.
  intros q Hq. destruct (Nat.eq_dec q 2) as [->|E]; [simpl; lra|].
  pose proof (bex_inv q ltac:(lia)) as [H1 H2]. lra.
Qed.

Lemma bser_bnd : forall q, (2 <= q)%nat ->
  -0.01 <= fst (bser q) <= 1.01 /\ -0.01 <= snd (bser q) <= 1.01.
Proof.
  intros q Hq. destruct (bser_err q Hq) as [H1 H2]. pose proof (bex_bnd q Hq).
  apply abs_inv in H1. assert (H2' : Rabs (snd (bser q) - snd (bex q)) <= 7 * eps)
    by (destruct (Nat.eq_dec q 2); [pose proof eps_val; lra | exact H2]).
  apply abs_inv in H2'. pose proof eps_val. lra.
Qed.

Lemma twr_comp : forall s k, (s <= 20)%nat -> (k < 2 ^ s)%nat ->
  Rabs (fst (twr s k)) <= 2 /\ Rabs (snd (twr s k)) <= 2.
Proof.
  intros s k Hs Hk. pose proof (twr_bound s k Hs Hk).
  pose proof (Cmod_re (twr s k)). pose proof (Cmod_im (twr s k)). lra.
Qed.

Lemma repr_hstepr : forall (bc bs : float) (b : C),
  repr bc (fst b) -> repr bs (snd b) -> -0.01 <= fst b <= 1.01 -> -0.01 <= snd b <= 1.01 ->
  repr (PrimFloat.sqrt ((1 + bc) * 0.5))%float (fst (hstepr b)) /\
  repr (bs / (2 * PrimFloat.sqrt ((1 + bc) * 0.5)))%float (snd (hstepr b)).
Proof.
  intros bc bs [c s] Hc Hs Hcb Hsb. simpl in *. unfold hstepr; simpl.
  pose proof bp900_big as B9.
  destruct (radd_ok 1 bc 1 c 1 1.01 repr_lit_one Hc ltac:(rewrite Rabs_R1; lra)
             ltac:(apply Rabs_le; lra) ltac:(lra)) as [R1 _].
  pose proof (rnd_e (1 + c)) as E1. rewrite (Rabs_pos_eq (1 + c)) in E1 by lra.
  pose proof eps_val as Ev. pose proof eta_nonneg. pose proof eta_tiny.
  assert (Hy : 0.98 <= rnd (1 + c) <= 2.03) by (apply abs_inv in E1; rewrite Ev in *; lra).
  destruct (rmul_ok _ _ _ _ 2.03 1 R1 repr_lit_half ltac:(apply Rabs_le; lra)
             ltac:(rewrite Rabs_pos_eq; lra) ltac:(lra)) as [R2 _].
  pose proof (rnd_e (rnd (1 + c) * / 2)) as E2.
  rewrite (Rabs_pos_eq (rnd (1 + c) * / 2)) in E2 by lra.
  assert (Hx : 0.48 <= rnd (rnd (1 + c) * / 2) <= 1.02) by (apply abs_inv in E2; rewrite Ev in *; lra).
  pose proof (repr_sqrt _ _ R2 ltac:(lra)) as R3.
  set (x := rnd (rnd (1 + c) * / 2)) in *.
  assert (Hsq : 0.69 <= sqrt x <= 1.01) by (apply sqrt_bnd; lra).
  pose proof (rnd_e (sqrt x)) as E3. rewrite (Rabs_pos_eq (sqrt x)) in E3 by lra.
  assert (Hc' : 0.68 <= rnd (sqrt x) <= 1.02) by (apply abs_inv in E3; rewrite Ev in *; lra).
  split; [exact R3|].
  destruct (rmul_ok _ _ _ _ 2 1.02 repr_lit_two R3 ltac:(rewrite Rabs_pos_eq; lra)
             ltac:(apply Rabs_le; lra) ltac:(lra)) as [R4 _].
  pose proof (rnd_e (2 * rnd (sqrt x))) as E4. rewrite (Rabs_pos_eq (2 * rnd (sqrt x))) in E4 by lra.
  assert (Hd : 1.3 <= rnd (2 * rnd (sqrt x))) by (apply abs_inv in E4; rewrite Ev in *; lra).
  apply repr_div; auto; [lra|]. apply ovf_ok.
  unfold Rdiv. rewrite Rabs_mult. rewrite (Rabs_pos_eq (/ _)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
  assert (/ rnd (2 * rnd (sqrt x)) <= 1) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
  assert (Rabs s <= 1.01) by (apply Rabs_le; lra).
  pose proof (Rabs_pos s). pose proof (Rinv_0_lt_compat (rnd (2 * rnd (sqrt x))) ltac:(lra)).
  assert (Rabs s * / rnd (2 * rnd (sqrt x)) <= 1.01 * 1) by (apply Rmult_le_compat; lra).
  pose proof (bp_big 1000 ltac:(lia)). lra.
Qed.

Lemma of_nat_eq : forall (i : int) (n : nat), to_Z i = Z.of_nat n -> i = of_nat n.
Proof.
  intros i n H. apply to_Z_inj. pose proof (to_Z_bounded i). rewrite of_nat_to_Z by lia. exact H.
Qed.

Lemma pow2_lt_pow2 : forall a b, (a < b)%nat -> (2 ^ a + 2 ^ a <= 2 ^ b)%nat.
Proof.
  intros a b H. replace (2 ^ a + 2 ^ a)%nat with (2 ^ S a)%nat by (simpl; lia).
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma tw_stage_spec : forall (lg s : nat) (Ni : int) tre tim bc bs,
  (1 <= s)%nat -> (s < lg)%nat -> (lg <= 18)%nat -> to_Z Ni = Z.of_nat (2 ^ lg) ->
  PArray.length tre = Ni -> PArray.length tim = Ni -> TWrep tre tim s ->
  repr bc (fst (bser (s + 1))) -> repr bs (snd (bser (s + 1))) ->
  match tw_stage (of_nat s) (tre, tim, bc, bs) with
  | (tre', tim', bc', bs') =>
    PArray.length tre' = Ni /\ PArray.length tim' = Ni /\ TWrep tre' tim' (S s) /\
    repr bc' (fst (bser (s + 2))) /\ repr bs' (snd (bser (s + 2)))
  end.
Proof.
  intros lg s Ni tre tim bc bs Hs1 Hsl Hlg HN Ltre Ltim Htw Hbc Hbs.
  assert (Hpl : (2 ^ s + 2 ^ s <= 2 ^ lg)%nat) by (apply pow2_lt_pow2; lia).
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (Hps : (1 <= 2 ^ (s - 1))%nat) by (pose proof (pow2_pos (s - 1)); lia).
  assert (Hps2 : (2 ^ s = 2 * 2 ^ (s - 1))%nat) by (replace s with (S (s - 1)) at 1 by lia; reflexivity).
  assert (Hsz : to_Z (of_nat s) = Z.of_nat s) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  assert (Hm : to_Z (1 << of_nat s) = Z.of_nat (2 ^ s)).
  { rewrite pow2_Z_small by lia. rewrite Hsz. rewrite Nat2Z.inj_pow. reflexivity. }
  assert (Hhm : to_Z (1 << (of_nat s - 1)) = Z.of_nat (2 ^ (s - 1))).
  { assert (E : to_Z (of_nat s - 1) = Z.of_nat (s - 1)) by (rewrite Uint63.sub_spec, Hsz; change (to_Z 1) with 1%Z;
      rewrite Z.mod_small by (change wB with (2^63)%Z; lia); lia).
    rewrite pow2_Z_small by lia. rewrite E, Nat2Z.inj_pow. reflexivity. }
  unfold tw_stage.
  set (m := 1 << of_nat s). set (hm := 1 << (of_nat s - 1)).
  assert (Hmz : to_Z m = Z.of_nat (2 ^ s)) by exact Hm.
  assert (Hhmz : to_Z hm = Z.of_nat (2 ^ (s - 1))) by exact Hhm.
  set (P := fun (k : int) (st : array float * array float) =>
    PArray.length (fst st) = Ni /\ PArray.length (snd st) = Ni /\ TWrep (fst st) (snd st) s /\
    forall k', (k' < Z.to_nat (to_Z k))%nat ->
      repr (fst st).[of_nat (2 ^ s + k')] (fst (twr s k')) /\ repr (snd st).[of_nat (2 ^ s + k')] (snd (twr s k'))).
  assert (HL : P m (loop m (tw_cell m hm bc bs) 0 (tre, tim))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. lia.
    - unfold P; simpl. split; [exact Ltre|]. split; [exact Ltim|]. split; [exact Htw|].
      intros k' Hk'. change (to_Z 0) with 0%Z in Hk'. simpl in Hk'. lia.
    - intros j [t1 t2] Hj [L1 [L2 [T1 T2]]]. simpl in L1, L2, T1, T2.
      change (to_Z 0) with 0%Z in Hj. rewrite Hmz in Hj.
      set (kn := Z.to_nat (to_Z j)).
      assert (Hkn : (kn < 2 ^ s)%nat) by (unfold kn; lia).
      assert (Hj1 : Z.to_nat (to_Z (j + 1)) = S kn) by (unfold kn; rewrite Uint63.add_spec; change (to_Z 1) with 1%Z;
        rewrite Z.mod_small by (change wB with (2^63)%Z; lia); lia).
      assert (Hsrc : (hm + (j >> 1))%uint63 = of_nat (2 ^ (s - 1) + Nat.div2 kn)).
      { apply of_nat_eq. rewrite Uint63.add_spec, lsr_val. change (to_Z 1) with 1%Z.
        rewrite Hhmz, Nat.div2_div. rewrite Z.mod_small.
        - rewrite Nat2Z.inj_add, Nat2Z.inj_div. unfold kn. rewrite Z2Nat.id by lia. reflexivity.
        - pose proof (Z.div_le_upper_bound (to_Z j) 2 (to_Z j) ltac:(lia) ltac:(lia)).
          pose proof (Z.div_pos (to_Z j) 2 ltac:(lia) ltac:(lia)). change wB with (2^63)%Z. lia. }
      assert (Hdst : (m + j)%uint63 = of_nat (2 ^ s + kn)).
      { apply of_nat_eq. rewrite Uint63.add_spec. rewrite Hmz.
        rewrite Z.mod_small by (change wB with (2^63)%Z; lia). unfold kn. rewrite Nat2Z.inj_add, Z2Nat.id by lia. reflexivity. }
      assert (Hd2 : (Nat.div2 kn < 2 ^ (s - 1))%nat) by (rewrite Nat.div2_div; apply Nat.Div0.div_lt_upper_bound; lia).
      destruct (T1 (s - 1)%nat (Nat.div2 kn) ltac:(lia) Hd2) as [Ra Rb].
      assert (Hlt : (of_nat (2 ^ s + kn) <? Ni) = true).
      { apply ltb_true. rewrite of_nat_to_Z by (change wB with (2^63)%Z; lia). lia. }
      assert (Hneq : forall s' k', (s' < s)%nat -> (k' < 2 ^ s')%nat -> of_nat (2 ^ s + kn) <> of_nat (2 ^ s' + k')).
      { intros s' k' Hs' Hk'. apply int_neq. rewrite !of_nat_to_Z by (change wB with (2^63)%Z;
          pose proof (Nat.pow_le_mono_r 2 s' s ltac:(lia) ltac:(lia)); lia).
        pose proof (pow2_lt_pow2 s' s Hs'). lia. }
      assert (Hneq2 : forall k', (k' < kn)%nat -> of_nat (2 ^ s + kn) <> of_nat (2 ^ s + k')).
      { intros k' Hk'. apply int_neq. rewrite !of_nat_to_Z by (change wB with (2^63)%Z; lia). lia. }
      assert (Htws : twr s kn = if Nat.even kn then twr (s - 1) (Nat.div2 kn)
                               else cmulr (twr (s - 1) (Nat.div2 kn)) (bser (s + 1))).
      { replace s with (S (s - 1)) at 1 by lia. simpl. replace (s - 1 + 2)%nat with (s + 1)%nat by lia. reflexivity. }
      unfold tw_cell. rewrite Hsrc, Hdst, parity_int. fold kn.
      unfold P; simpl. rewrite Hj1.
      destruct (Nat.even kn) eqn:Ev.
      + simpl. rewrite !flength_set. split; [exact L1|]. split; [exact L2|]. split.
        * intros s' k' Hs' Hk'. rewrite !fget_set_other by (apply Hneq; assumption). apply T1; assumption.
        * intros k' Hk'. destruct (Nat.eq_dec k' kn) as [->|Ne].
          -- rewrite !fget_set_same by (rewrite ?L1, ?L2; exact Hlt). rewrite Htws. split; assumption.
          -- rewrite !fget_set_other by (apply Hneq2; lia). apply T2. lia.
      + simpl.
        destruct (twr_comp (s - 1) (Nat.div2 kn) ltac:(lia) Hd2) as [Ba Bb].
        destruct (bser_bnd (s + 1) ltac:(lia)) as [Bc Bs].
        destruct (repr_cmulr _ _ _ _ (twr (s - 1) (Nat.div2 kn)) (bser (s + 1)) 2 2 Ra Rb Hbc Hbs Ba Bb
                   ltac:(apply Rabs_le; lra) ltac:(apply Rabs_le; lra) ltac:(lra) ltac:(lra)
                   ltac:(pose proof bp800_big; lra))
          as [Rr [Ri _]].
        rewrite !flength_set. split; [exact L1|]. split; [exact L2|]. split.
        * intros s' k' Hs' Hk'. rewrite !fget_set_other by (apply Hneq; assumption). apply T1; assumption.
        * intros k' Hk'. destruct (Nat.eq_dec k' kn) as [->|Ne].
          -- rewrite !fget_set_same by (rewrite ?L1, ?L2; exact Hlt). rewrite Htws. split; assumption.
          -- rewrite !fget_set_other by (apply Hneq2; lia). apply T2. lia. }
  destruct (loop m (tw_cell m hm bc bs) 0 (tre, tim)) as [t1 t2] eqn:Eloop.
  destruct HL as [L1 [L2 [T1 T2]]]. simpl in L1, L2, T1, T2. rewrite Hmz, Nat2Z.id in T2.
  destruct (bser_bnd (s + 1) ltac:(lia)) as [Bc Bs].
  destruct (repr_hstepr bc bs (bser (s + 1)) Hbc Hbs Bc Bs) as [Rc Rs].
  replace (s + 2)%nat with (S (s + 1)) by lia. rewrite bser_S by lia.
  split; [exact L1|]. split; [exact L2|]. split; [|split; assumption].
  intros s' k' Hs' Hk'. destruct (Nat.eq_dec s' s) as [->|Ne]; [apply T2; exact Hk' | apply T1; [lia | exact Hk']].
Qed.

End TwBuild.

Lemma to_nat_succ : forall j : int, (to_Z j < 4194303)%Z -> Z.to_nat (to_Z (j + 1)) = S (Z.to_nat (to_Z j)).
Proof.
  intros j H. pose proof (to_Z_bounded j). rewrite Uint63.add_spec. change (to_Z 1) with 1%Z.
  rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia.
Qed.

Lemma build_tw_spec : forall (lg : nat) (Ni : int), (2 <= lg <= 18)%nat ->
  to_Z Ni = Z.of_nat (2 ^ lg) ->
  match build_tw (of_nat lg) Ni with (tre, tim) => TWrep tre tim lg end.
Proof.
  intros lg Ni Hlg HN.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (Hlz : to_Z (of_nat lg) = Z.of_nat lg) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  assert (Hp4 : (4 <= Z.of_nat (2 ^ lg))%Z).
  { rewrite Nat2Z.inj_pow. change 4%Z with (Z.of_nat 2 ^ 2)%Z. apply Z.pow_le_mono_r; lia. }
  unfold build_tw.
  set (P := fun (s : int) (st : array float * array float * float * float) =>
    match st with (tre, tim, bc, bs) =>
      PArray.length tre = Ni /\ PArray.length tim = Ni /\ TWrep tre tim (Z.to_nat (to_Z s)) /\
      repr bc (fst (bser (Z.to_nat (to_Z s) + 1))) /\ repr bs (snd (bser (Z.to_nat (to_Z s) + 1)))
    end).
  assert (HL : P (of_nat lg) (loop (of_nat lg) tw_stage 1
                   ((PArray.make Ni 0%float).[1 <- 1%float], PArray.make Ni 0%float, 0%float, 1%float))).
  { apply for_inv.
    - change (to_Z 1) with 1%Z. lia.
    - unfold P. change (Z.to_nat (to_Z 1)) with 1%nat. simpl.
      assert (L0 : PArray.length (PArray.make Ni 0%float) = Ni) by (apply flength_make; lia).
      rewrite flength_set, L0. split; [reflexivity|]. split; [reflexivity|]. split; [|split; [exact repr_lit_zero | exact repr_lit_one]].
      intros s k Hs Hk. assert (s = 0%nat) by lia. subst s. simpl in Hk. assert (k = 0%nat) by lia. subst k.
      change (of_nat (2 ^ 0 + 0)) with 1. rewrite fget_make.
      rewrite fget_set_same by (rewrite L0; apply ltb_true; change (to_Z 1) with 1%Z; lia).
      simpl. split; [exact repr_lit_one | exact repr_lit_zero].
    - intros j [[[tre tim] bc] bs] Hj Hp. unfold P in Hp |- *. destruct Hp as [L1 [L2 [T [Rc Rs]]]].
      change (to_Z 1) with 1%Z in Hj. rewrite Hlz in Hj.
      pose proof (tw_stage_spec lg (Z.to_nat (to_Z j)) Ni tre tim bc bs ltac:(lia) ltac:(lia) ltac:(lia) HN L1 L2 T Rc Rs) as H.
      rewrite of_nat_to_nat in H.
      destruct (tw_stage j (tre, tim, bc, bs)) as [[[t1 t2] c'] s'].
      rewrite to_nat_succ by lia. replace (S (Z.to_nat (to_Z j)) + 1)%nat with (Z.to_nat (to_Z j) + 2)%nat by lia.
      exact H. }
  destruct (loop (of_nat lg) tw_stage 1 _) as [[[tre tim] bc] bs].
  unfold P in HL. destruct HL as [_ [_ [T _]]]. rewrite Hlz, Nat2Z.id in T. exact T.
Qed.

Section FFTProof.
Local Open Scope R_scope.

Definition Bg : R := bp 400.

Definition crep (re im : array float) (n : nat) (x : vec) : Prop :=
  forall i, (i < n)%nat -> repr re.[of_nat i] (fst (x i)) /\ repr im.[of_nat i] (snd (x i)).

Definition cbnd (n : nat) (x : vec) (B : R) : Prop :=
  forall i, (i < n)%nat -> Rabs (fst (x i)) <= B /\ Rabs (snd (x i)) <= B.

Definition twc (neg : bool) (s q : nat) : C := if neg then Cconj (twr s q) else twr s q.

Lemma Bg_facts : 1 <= Bg /\ 2 * Bg <= bp 800 /\ 17 * Bg + 5 + Bg <= bp 900.
Proof.
  unfold Bg. pose proof (bp_ge1 400 ltac:(lia)).
  pose proof (bp_gap 400 800 ltac:(lia) ltac:(lia)). pose proof (bp_gap 400 900 ltac:(lia) ltac:(lia)).
  replace 900%Z with (400 + 500)%Z by lia. rewrite bp_mul.
  replace 800%Z with (400 + 400)%Z in * by lia. rewrite bp_mul in *.
  pose proof (bp_big 500 ltac:(lia)). pose proof (bp_big 400 ltac:(lia)). nra.
Qed.

Lemma repr_bfly : forall (wr wi ur ui vr vi : float) (w u v : C),
  repr wr (fst w) -> repr wi (snd w) -> repr ur (fst u) -> repr ui (snd u) ->
  repr vr (fst v) -> repr vi (snd v) ->
  Rabs (fst w) <= 2 -> Rabs (snd w) <= 2 ->
  Rabs (fst u) <= Bg -> Rabs (snd u) <= Bg -> Rabs (fst v) <= Bg -> Rabs (snd v) <= Bg ->
  repr (ur + (wr * vr - wi * vi))%float (fst (bfp w u v)) /\
  repr (ur - (wr * vr - wi * vi))%float (fst (bfm w u v)) /\
  repr (ui + (wr * vi + wi * vr))%float (snd (bfp w u v)) /\
  repr (ui - (wr * vi + wi * vr))%float (snd (bfm w u v)).
Proof.
  intros wr wi ur ui vr vi w u v Hwr Hwi Hur Hui Hvr Hvi Bw1 Bw2 Bu1 Bu2 Bv1 Bv2.
  destruct Bg_facts as [G1 [G2 G3]].
  destruct (repr_cmulr wr wi vr vi w v 2 Bg Hwr Hwi Hvr Hvi Bw1 Bw2 Bv1 Bv2 ltac:(lra) ltac:(lra) ltac:(lra))
    as [Rt1 [Rt2 [Bt1 Bt2]]].
  unfold bfp, bfm, caddr, csubr; simpl.
  destruct (radd_ok _ _ _ _ Bg (8 * (2 * Bg) + 5) Hur Rt1 Bu1 Bt1 ltac:(lra)) as [R1 _].
  destruct (rsub_ok _ _ _ _ Bg (8 * (2 * Bg) + 5) Hur Rt1 Bu1 Bt1 ltac:(lra)) as [R2 _].
  destruct (radd_ok _ _ _ _ Bg (8 * (2 * Bg) + 5) Hui Rt2 Bu2 Bt2 ltac:(lra)) as [R3 _].
  destruct (rsub_ok _ _ _ _ Bg (8 * (2 * Bg) + 5) Hui Rt2 Bu2 Bt2 ltac:(lra)) as [R4 _].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3 | exact R4].
Qed.

Lemma twc_comp : forall neg s q, (s <= 20)%nat -> (q < 2 ^ s)%nat ->
  Rabs (fst (twc neg s q)) <= 2 /\ Rabs (snd (twc neg s q)) <= 2.
Proof.
  intros neg s q Hs Hq. destruct (twr_comp s q Hs Hq). unfold twc. destruct neg; simpl; [rewrite Rabs_Ropp|]; auto.
Qed.

Lemma stage_spec : forall (lg s : nat) (Ni hi : int) (neg : bool) (tre tim sre sim dre dim : array float) (x : vec),
  (2 <= lg <= 18)%nat -> (s < lg)%nat -> to_Z Ni = Z.of_nat (2 ^ lg) -> to_Z hi = Z.of_nat (hlf lg) ->
  PArray.length sre = Ni -> PArray.length sim = Ni -> PArray.length dre = Ni -> PArray.length dim = Ni ->
  TWrep tre tim lg -> crep sre sim (2 ^ lg) x -> cbnd (2 ^ lg) x Bg ->
  match loop hi (bfly (of_nat lg - 1 - of_nat s) (1 << of_nat s) hi neg sre sim tre tim) 0 (dre, dim) with
  | (d1, d2) => PArray.length d1 = Ni /\ PArray.length d2 = Ni /\
                crep d1 d2 (2 ^ lg) (cstage (hlf lg) (spn lg s) (twc neg s) x)
  end.
Proof.
  intros lg s Ni hi neg tre tim sre sim dre dim x Hlg Hs HN Hh Lsr Lsi Ldr Ldi Htw Hx Bx.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (HNh : (2 ^ lg = 2 * hlf lg)%nat).
  { unfold hlf. replace lg with (S (lg - 1)) at 1 by lia. reflexivity. }
  assert (Hhs : hlf lg = (2 ^ s * spn lg s)%nat) by (apply hlf_split; lia).
  assert (Hsp : (0 < spn lg s)%nat) by apply pow2_pos.
  assert (Hps : (0 < 2 ^ s)%nat) by apply pow2_pos.
  assert (Hsl2 : (2 ^ s <= 2 ^ lg)%nat) by (apply Nat.pow_le_mono_r; lia).
  assert (Hlz : to_Z (of_nat lg) = Z.of_nat lg) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  assert (Hsz : to_Z (of_nat s) = Z.of_nat s) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  set (sh := (of_nat lg - 1 - of_nat s)%uint63).
  assert (Hsh : to_Z sh = Z.of_nat (lg - 1 - s)).
  { unfold sh. rewrite !Uint63.sub_spec, Hlz, Hsz. change (to_Z 1) with 1%Z.
    rewrite (Z.mod_small (Z.of_nat lg - 1)) by (change wB with (2^63)%Z; lia).
    rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
  assert (Hspz : (2 ^ to_Z sh)%Z = Z.of_nat (spn lg s)) by (rewrite Hsh; unfold spn; rewrite Nat2Z.inj_pow; reflexivity).
  set (m := 1 << of_nat s).
  assert (Hm : to_Z m = Z.of_nat (2 ^ s)) by (unfold m; rewrite pow2_Z_small by lia; rewrite Hsz, Nat2Z.inj_pow; reflexivity).
  set (P := fun (j : int) (st : array float * array float) =>
    PArray.length (fst st) = Ni /\ PArray.length (snd st) = Ni /\
    forall i, ((i < Z.to_nat (to_Z j))%nat \/ (hlf lg <= i < hlf lg + Z.to_nat (to_Z j))%nat) ->
      repr (fst st).[of_nat i] (fst (cstage (hlf lg) (spn lg s) (twc neg s) x i)) /\
      repr (snd st).[of_nat i] (snd (cstage (hlf lg) (spn lg s) (twc neg s) x i))).
  assert (HL : P hi (loop hi (bfly sh m hi neg sre sim tre tim) 0 (dre, dim))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. lia.
    - unfold P; simpl. split; [exact Ldr|]. split; [exact Ldi|]. intros i Hi. change (to_Z 0) with 0%Z in Hi. simpl in Hi. lia.
    - intros j [d1 d2] Hj [L1 [L2 T]]. simpl in L1, L2, T. change (to_Z 0) with 0%Z in Hj. rewrite Hh in Hj.
      set (jn := Z.to_nat (to_Z j)).
      assert (Hjn : (jn < hlf lg)%nat) by (unfold jn; lia).
      assert (Hjz : to_Z j = Z.of_nat jn) by (unfold jn; lia).
      set (qn := sq (spn lg s) jn). set (i1 := si1 (spn lg s) jn).
      assert (Hqn : (qn < 2 ^ s)%nat) by (unfold qn, sq; apply Nat.Div0.div_lt_upper_bound; lia).
      assert (Hq : to_Z (j >> sh) = Z.of_nat qn).
      { rewrite lsr_val, Hspz, Hjz. unfold qn, sq. rewrite Nat2Z.inj_div. reflexivity. }
      assert (Hqr : (spn lg s * qn <= jn)%nat) by (unfold qn, sq; apply Nat.Div0.mul_div_le).
      assert (Hi1n : (i1 + spn lg s < 2 ^ lg)%nat).
      { unfold i1, si1. fold (sq (spn lg s) jn). fold qn.
        assert (A : (spn lg s * (qn + 1) <= spn lg s * 2 ^ s)%nat) by (apply Nat.mul_le_mono_l; lia).
        rewrite Nat.mul_add_distr_l, Nat.mul_1_r in A. rewrite Nat.mul_comm in Hhs.
        clear - A Hjn Hhs HNh. lia. }
      assert (Hi1 : (j + ((j >> sh) << sh))%uint63 = of_nat i1).
      { apply of_nat_eq. rewrite Uint63.add_spec, lsl_val.
        - rewrite Hq, Hspz, Hjz. rewrite Z.mod_small by (change wB with (2^63)%Z; unfold i1, si1 in Hi1n; lia).
          unfold i1, si1. fold (sq (spn lg s) jn). fold qn. lia.
        - rewrite Hq, Hspz. rewrite Z.mul_comm, <- Nat2Z.inj_mul. change wB with (2^63)%Z.
          clear - Hqr Hjn Hp18 HNh. lia. }
      assert (Hi2 : (j + ((j >> sh) << sh) + (1 << sh))%uint63 = of_nat (i1 + spn lg s)).
      { apply of_nat_eq. rewrite Uint63.add_spec. rewrite Hi1, of_nat_to_Z by (change wB with (2^63)%Z; lia).
        rewrite pow2_Z_small by lia. rewrite Hspz. rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
      assert (Htwi : (m + (j >> sh))%uint63 = of_nat (2 ^ s + qn)).
      { apply of_nat_eq. rewrite Uint63.add_spec, Hm, Hq. rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
      assert (Hjh : (j + hi)%uint63 = of_nat (hlf lg + jn)).
      { apply of_nat_eq. rewrite Uint63.add_spec, Hh, Hjz. rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
      assert (Hjo : j = of_nat jn) by (apply of_nat_eq; exact Hjz).
      destruct (Htw s qn Hs Hqn) as [Rw1 Rw2].
      assert (Rwr : repr tre.[of_nat (2 ^ s + qn)] (fst (twc neg s qn))) by (unfold twc; destruct neg; exact Rw1).
      assert (Rwi : repr (if neg then (- tim.[of_nat (2 ^ s + qn)])%float else tim.[of_nat (2 ^ s + qn)]) (snd (twc neg s qn))).
      { unfold twc. destruct neg; [apply repr_opp; exact Rw2 | exact Rw2]. }
      assert (Hi1a : (i1 < 2 ^ lg)%nat) by (clear - Hi1n; lia).
      destruct (Hx i1 Hi1a) as [Ru1 Ru2]. destruct (Hx (i1 + spn lg s)%nat Hi1n) as [Rv1 Rv2].
      destruct (Bx i1 Hi1a) as [Bu1 Bu2]. destruct (Bx (i1 + spn lg s)%nat Hi1n) as [Bv1 Bv2].
      destruct (twc_comp neg s qn ltac:(lia) Hqn) as [Bw1 Bw2].
      destruct (repr_bfly _ _ _ _ _ _ _ _ _ Rwr Rwi Ru1 Ru2 Rv1 Rv2 Bw1 Bw2 Bu1 Bu2 Bv1 Bv2) as [Y1 [Y2 [Y3 Y4]]].
      assert (Ev1 : cstage (hlf lg) (spn lg s) (twc neg s) x jn = bfp (twc neg s qn) (x i1) (x (i1 + spn lg s)%nat))
        by (unfold cstage; rewrite stage_lo by exact Hjn; reflexivity).
      assert (Ev2 : cstage (hlf lg) (spn lg s) (twc neg s) x (hlf lg + jn)%nat = bfm (twc neg s qn) (x i1) (x (i1 + spn lg s)%nat))
        by (unfold cstage; rewrite stage_hi by exact Hjn; reflexivity).
      assert (OK : forall a, (a < 2 ^ lg)%nat -> to_Z (of_nat a) = Z.of_nat a).
      { intros a Ha. apply of_nat_to_Z. change wB with (2^63)%Z. clear - Ha Hp18. lia. }
      assert (Hjl : (jn < 2 ^ lg)%nat) by (clear - Hjn HNh; lia).
      assert (Hjl2 : (hlf lg + jn < 2 ^ lg)%nat) by (clear - Hjn HNh; lia).
      assert (Hne : of_nat (hlf lg + jn) <> of_nat jn).
      { apply int_neq. rewrite !OK by assumption. pose proof (pow2_pos (lg - 1)). unfold hlf in *. clear - H. lia. }
      assert (Hlt1 : (of_nat jn <? Ni) = true) by (apply ltb_true; rewrite OK by assumption; clear - Hjl HN; lia).
      assert (Hlt2 : (of_nat (hlf lg + jn) <? Ni) = true) by (apply ltb_true; rewrite OK by assumption; clear - Hjl2 HN; lia).
      unfold bfly. fold m. rewrite Hi2, Hi1, Htwi, Hjh.
      unfold P; simpl. rewrite !flength_set. split; [exact L1|]. split; [exact L2|].
      rewrite to_nat_succ by (clear - Hj Hp18 HNh; lia). fold jn. intros i Hi.
      rewrite <- Hjo in Hne, Hlt1.
      destruct (Nat.eq_dec i jn) as [->|Ni1].
      + rewrite <- Hjo. rewrite (fget_set_other (d1.[j <- _])) by exact Hne.
        rewrite (fget_set_other (d2.[j <- _])) by exact Hne.
        rewrite (fget_set_same d1) by (rewrite L1; exact Hlt1).
        rewrite (fget_set_same d2) by (rewrite L2; exact Hlt1).
        rewrite Ev1. split; assumption.
      + destruct (Nat.eq_dec i (hlf lg + jn)) as [->|Ni2].
        * rewrite (fget_set_same (d1.[j <- _])) by (rewrite flength_set, L1; exact Hlt2).
          rewrite (fget_set_same (d2.[j <- _])) by (rewrite flength_set, L2; exact Hlt2).
          rewrite Ev2. split; assumption.
        * assert (Hil : (i < 2 ^ lg)%nat) by (clear - Hi Hjn HNh; lia).
          assert (D1 : of_nat i <> j).
          { rewrite Hjo. apply int_neq. rewrite !OK by assumption. clear - Ni1. lia. }
          assert (D2 : of_nat (hlf lg + jn) <> of_nat i).
          { apply int_neq. rewrite !OK by assumption. clear - Ni2. lia. }
          assert (D1' : j <> of_nat i) by (intro E; apply D1; symmetry; exact E).
          rewrite (fget_set_other (d1.[j <- _])) by exact D2.
          rewrite (fget_set_other (d2.[j <- _])) by exact D2.
          rewrite (fget_set_other d1) by exact D1'. rewrite (fget_set_other d2) by exact D1'.
          apply T. clear - Hi Ni1 Ni2. lia. }
  fold sh m.
  destruct (loop hi (bfly sh m hi neg sre sim tre tim) 0 (dre, dim)) as [d1 d2].
  destruct HL as [L1 [L2 T]]. simpl in L1, L2, T. split; [exact L1|]. split; [exact L2|].
  intros i Hi. apply T. rewrite Hh, Nat2Z.id. lia.
Qed.

End FFTProof.

Section FFTRun.
Local Open Scope R_scope.

Lemma fft_spec : forall (lg : nat) (Ni hi : int) (neg : bool) (tre tim re im : array float) (x0 : vec),
  (2 <= lg <= 18)%nat -> to_Z Ni = Z.of_nat (2 ^ lg) -> to_Z hi = Z.of_nat (hlf lg) ->
  PArray.length re = Ni -> PArray.length im = Ni ->
  TWrep tre tim lg -> crep re im (2 ^ lg) x0 ->
  (forall s, (s <= lg)%nat -> cbnd (2 ^ lg) (cfft lg (twc neg) s x0) Bg) ->
  match fft (of_nat lg) hi neg tre tim re im with
  | (yr, yi) => PArray.length yr = Ni /\ PArray.length yi = Ni /\ crep yr yi (2 ^ lg) (cfft lg (twc neg) lg x0)
  end.
Proof.
  intros lg Ni hi neg tre tim re im x0 Hlg HN Hh Lr Li Htw Hx Hb.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (HNh : (2 ^ lg = 2 * hlf lg)%nat).
  { unfold hlf. replace lg with (S (lg - 1)) at 1 by lia. reflexivity. }
  assert (Hlz : to_Z (of_nat lg) = Z.of_nat lg) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  assert (HhN : (hi + hi)%uint63 = Ni).
  { apply to_Z_inj. rewrite Uint63.add_spec, Hh, HN. rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
  unfold fft. rewrite HhN.
  assert (L0 : PArray.length (PArray.make Ni 0%float) = Ni) by (apply flength_make; lia).
  set (P := fun (s : int) (st : array float * array float * array float * array float) =>
    match st with (a, b, c, d) =>
      PArray.length a = Ni /\ PArray.length b = Ni /\ PArray.length c = Ni /\ PArray.length d = Ni /\
      crep a b (2 ^ lg) (cfft lg (twc neg) (Z.to_nat (to_Z s)) x0)
    end).
  assert (HL : P (of_nat lg) (loop (of_nat lg) (fft_stage (of_nat lg) hi neg tre tim) 0
                   (re, im, PArray.make Ni 0%float, PArray.make Ni 0%float))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. lia.
    - unfold P. change (Z.to_nat (to_Z 0)) with 0%nat. simpl.
      split; [exact Lr|]. split; [exact Li|]. split; [exact L0|]. split; [exact L0|]. exact Hx.
    - intros j [[[a b] c] d] Hj Hp. unfold P in Hp |- *. destruct Hp as [La [Lb [Lc [Ld Ha]]]].
      change (to_Z 0) with 0%Z in Hj. rewrite Hlz in Hj.
      set (jn := Z.to_nat (to_Z j)).
      pose proof (stage_spec lg jn Ni hi neg tre tim a b c d (cfft lg (twc neg) jn x0)
                    Hlg ltac:(unfold jn; lia) HN Hh La Lb Lc Ld Htw Ha (Hb jn ltac:(unfold jn; lia))) as H.
      unfold fft_stage. assert (Ej : of_nat jn = j) by apply of_nat_to_nat. rewrite Ej in H.
      destruct (loop hi (bfly (of_nat lg - 1 - j) (1 << j) hi neg a b tre tim) 0 (c, d)) as [d1 d2].
      destruct H as [L1 [L2 H]].
      rewrite to_nat_succ by lia. fold jn.
      split; [exact L1|]. split; [exact L2|]. split; [exact La|]. split; [exact Lb|]. exact H. }
  destruct (loop (of_nat lg) (fft_stage (of_nat lg) hi neg tre tim) 0 _) as [[[a b] c] d].
  unfold P in HL. destruct HL as [La [Lb [_ [_ H]]]]. rewrite Hlz, Nat2Z.id in H.
  split; [exact La|]. split; [exact Lb | exact H].
Qed.

End FFTRun.

(* ---------------------------------------------------------------------- *)
(* The concrete error budget                                              *)
(* ---------------------------------------------------------------------- *)

Section Budget.
Local Open Scope R_scope.

Definition dlt (s : nat) : R := 15.1 * INR s * eps.

Lemma dlt_ok : forall s, (s <= 20)%nat -> 0 <= dlt s <= 0.001.
Proof.
  intros s Hs. unfold dlt. pose proof (pos_INR s). pose proof eps_val.
  assert (INR s <= 20) by (replace 20 with (INR 20) by (simpl; lra); apply le_INR; lia).
  split; [rewrite H0; nra | rewrite H0; nra].
Qed.

Lemma Gsum_closed : forall n, Gsum dlt n = (10.86 * INR n + 15.1 * (INR n * (INR n - 1))) * eps.
Proof.
  intros n. unfold Gsum, dlt. induction n as [|n IH]; simpl rsum.
  - simpl. ring.
  - rewrite IH, S_INR. replace 10.86 with (1086 / 100) by lra. replace 15.1 with (151 / 10) by lra.
    replace 5.43 with (543 / 100) by lra. field.
Qed.

Lemma Gsum_bound : forall lg, (lg <= 18)%nat -> Gsum dlt lg <= 4817 * eps.
Proof.
  intros lg H. rewrite Gsum_closed. pose proof (pos_INR lg). pose proof eps_val.
  assert (INR lg <= 18) by (replace 18 with (INR 18) by (simpl; lra); apply le_INR; lia).
  assert (0 < eps) by lra.
  apply Rmult_le_compat_r; [lra|]. nra.
Qed.

Definition sgn (neg : bool) : Z := if neg then (-1)%Z else 1%Z.

Lemma twc_err : forall neg lg s q, (s < lg)%nat -> (lg <= 20)%nat -> (q < 2 ^ s)%nat ->
  Cmod (Csub (twc neg s q) (Wex (2 ^ lg) (sgn neg) (spn lg s) q)) <= dlt s.
Proof.
  intros neg lg s q Hs Hlg Hq. destruct (Wex_Wf lg s q Hs) as [E1 E2].
  pose proof (twr_err s q ltac:(lia) Hq) as H. unfold twc, sgn, dlt. destruct neg.
  - rewrite E2, Cmod_conj_sub. exact H.
  - rewrite E1. exact H.
Qed.

Lemma cfft_err_c : forall neg lg x, (2 <= lg <= 18)%nat ->
  nrm (2 ^ lg) (vsub (cfft lg (twc neg) lg x) (fft_ex (sgn neg) lg lg x))
  <= sq2 ^ lg * (nrm (2 ^ lg) x + 1) * (3757.3 * eps).
Proof.
  intros neg lg x Hlg.
  assert (HG : 0.78 * Gsum dlt lg <= 0.09) by (pose proof (Gsum_bound lg ltac:(lia)); pose proof eps_val; lra).
  pose proof (cfft_err (sgn neg) lg (twc neg) dlt x ltac:(unfold sgn; destruct neg; auto) ltac:(lia)
                ltac:(intros; apply twc_err; lia) ltac:(intros s' Hs'; apply dlt_ok; lia) HG lg (le_n _)) as H.
  eapply Rle_trans; [exact H|]. apply Rmult_le_compat_l.
  - apply Rmult_le_pos; [apply pow_le; pose proof sq2_bounds; lra | pose proof (nrm_nonneg (2 ^ lg) x); lra].
  - pose proof (Gsum_bound lg ltac:(lia)). pose proof eps_val. lra.
Qed.

Lemma sq2_pow_le : forall s, (s <= 18)%nat -> 1 <= sq2 ^ s <= 512.
Proof.
  intros s Hs. pose proof sq2_bounds. split; [apply pow_R1_Rle; lra|].
  apply Rle_trans with (sq2 ^ 18); [apply Rle_pow; [lra | exact Hs]|].
  replace 18%nat with (2 * 9)%nat by reflexivity. rewrite pow_mult.
  replace (sq2 ^ 2) with (sq2 * sq2) by ring. rewrite sq2_sq. simpl. lra.
Qed.

Lemma cfft_bound : forall neg lg x, (2 <= lg <= 18)%nat -> nrm (2 ^ lg) x <= bp 100 ->
  forall s, (s <= lg)%nat -> cbnd (2 ^ lg) (cfft lg (twc neg) s x) Bg.
Proof.
  intros neg lg x Hlg Hx s Hs i Hi.
  assert (HG : 0.78 * Gsum dlt lg <= 0.09) by (pose proof (Gsum_bound lg ltac:(lia)); pose proof eps_val; lra).
  pose proof (cfft_err (sgn neg) lg (twc neg) dlt x ltac:(unfold sgn; destruct neg; auto) ltac:(lia)
                ltac:(intros; apply twc_err; lia) ltac:(intros s' Hs'; apply dlt_ok; lia) HG s Hs) as H.
  assert (HGs : 0.78 * Gsum dlt s <= 0.09).
  { eapply Rle_trans; [|exact HG]. apply Rmult_le_compat_l; [lra|].
    apply rsum_mono_len; [exact Hs|]. intros t _. pose proof (dlt_ok t). unfold dlt in *.
    pose proof (pos_INR t). pose proof eps_val. nra. }
  pose proof (fft_ex_nrm (sgn neg) lg s x Hs) as E.
  assert (Hn : nrm (2 ^ lg) (cfft lg (twc neg) s x) <= sq2 ^ s * nrm (2 ^ lg) x + sq2 ^ s * (nrm (2 ^ lg) x + 1) * 0.09).
  { eapply Rle_trans; [|apply Rplus_le_compat; [right; exact E|]].
    - rewrite (nrm_ext _ (cfft lg (twc neg) s x) (vadd (fft_ex (sgn neg) lg s x) (vsub (cfft lg (twc neg) s x) (fft_ex (sgn neg) lg s x))))
        by (intros j _; unfold vadd, vsub; apply Ceq; simpl; ring).
      apply nrm_add.
    - eapply Rle_trans; [exact H|]. apply Rmult_le_compat_l; [|exact HGs].
      apply Rmult_le_pos; [apply pow_le; pose proof sq2_bounds; lra | pose proof (nrm_nonneg (2 ^ lg) x); lra]. }
  pose proof (nrm_elem (2 ^ lg) (cfft lg (twc neg) s x) i Hi) as Hel.
  pose proof (Cmod_re (cfft lg (twc neg) s x i)). pose proof (Cmod_im (cfft lg (twc neg) s x i)).
  pose proof (sq2_pow_le s ltac:(lia)). pose proof (nrm_nonneg (2 ^ lg) x).
  assert (HB : sq2 ^ s * nrm (2 ^ lg) x + sq2 ^ s * (nrm (2 ^ lg) x + 1) * 0.09 <= 512 * bp 100 + 512 * (bp 100 + 1) * 0.09).
  { apply Rplus_le_compat; [apply Rmult_le_compat; lra|]. apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat; lra. }
  assert (HBg : 512 * bp 100 + 512 * (bp 100 + 1) * 0.09 <= Bg).
  { unfold Bg. replace 400%Z with (100 + 300)%Z by lia. rewrite bp_mul.
    pose proof (bp_big 300 ltac:(lia)). pose proof (bp_ge1 100 ltac:(lia)).
    assert (1024 * bp 100 <= bp 100 * bp 300) by nra. lra. }
  split; lra.
Qed.

End Budget.

(* ---------------------------------------------------------------------- *)
(* Limbs and the forward transforms                                       *)
(* ---------------------------------------------------------------------- *)

Definition KZ : Z := 34905131040%Z.

Definition limbZ (c : Z) (i : nat) : Z := (((c + KZ) / 64 ^ Z.of_nat i) mod 64 - 32)%Z.

Definition Alimb (a : list Z) (i : nat) : vec :=
  fun t => if (t <? List.length a)%nat then (IZR (limbZ (nth t a 0%Z) i), 0%R) else C0.

Lemma limbZ_range : forall c i, (-32 <= limbZ c i <= 31)%Z.
Proof. intros c i. unfold limbZ. pose proof (Z.mod_pos_bound ((c + KZ) / 64 ^ Z.of_nat i) 64 ltac:(lia)). lia. Qed.

Lemma repr_sint_get : forall (x : array sint) (a : list Z), repr x a ->
  forall k, (k < List.length a)%nat -> Sint63.to_Z x.[of_nat k] = nth k a 0%Z.
Proof.
  intros x a [Hl Hc] k Hk. destruct (Hc k Hk) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr. rewrite Hr. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_sint_length : forall (x : array sint) (a : list Z), repr x a ->
  to_Z (PArray.length x) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma limb_repr : forall (c : int) (i : nat), (-2147483648 <= Sint63.to_Z c < 2147483648)%Z -> (i < 6)%nat ->
  repr (limb c (of_nat i)) (IZR (limbZ (Sint63.to_Z c) i)).
Proof.
  intros c i Hc Hi.
  assert (Hiz : to_Z (of_nat i) = Z.of_nat i) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  assert (H6 : to_Z (6 * of_nat i) = (6 * Z.of_nat i)%Z).
  { rewrite Uint63.mul_spec, Hiz. change (to_Z 6) with 6%Z. apply Z.mod_small. change wB with (2^63)%Z. lia. }
  assert (HK : to_Z (c + KOFF) = (Sint63.to_Z c + KZ)%Z).
  { rewrite Uint63.add_spec. rewrite <- (Sint63.to_Z_mod_Uint63to_Z c). change (to_Z KOFF) with KZ.
    rewrite Zplus_mod_idemp_l. apply Z.mod_small. unfold KZ. change wB with (2^63)%Z. lia. }
  set (d := (((Sint63.to_Z c + KZ) / 64 ^ Z.of_nat i) mod 64)%Z).
  assert (Hd : to_Z (((c + KOFF) >> (6 * of_nat i)) land 63) = d).
  { rewrite land_spec', lsr_val, H6, HK. change (to_Z 63) with (Z.ones 6). rewrite Z.land_ones by lia.
    unfold d. rewrite Z.pow_mul_r by lia. reflexivity. }
  assert (Hdr : (0 <= d < 64)%Z) by (unfold d; apply Z.mod_pos_bound; lia).
  unfold limb. pose proof (repr_of_uint63_exact (((c + KOFF) >> (6 * of_nat i)) land 63)
                             ltac:(rewrite Hd; lia)) as R1. rewrite Hd in R1.
  destruct (rsub_ok _ _ _ _ 64 32 R1 repr_lit_32 ltac:(rewrite Rabs_pos_eq by (apply IZR_le; lia); apply IZR_le; lia)
              ltac:(rewrite Rabs_pos_eq; lra) ltac:(pose proof (bp_big 900 ltac:(lia)); lra)) as [R2 _].
  replace (IZR d - 32)%R with (IZR (d - 32)) in R2 by (rewrite minus_IZR; reflexivity).
  rewrite rnd_IZR in R2 by lia. unfold limbZ. fold d. exact R2.
Qed.

Section Forward.
Local Open Scope R_scope.

Lemma repr_conv : forall (f g : float) (r : R), f = g -> repr g r -> repr f r.
Proof. intros f g r -> H. exact H. Qed.

Lemma nrm_const_bound : forall n x c, 0 <= c -> (forall i, (i < n)%nat -> Cmod (x i) <= c) ->
  nrm n x <= c * sqrt (INR n).
Proof.
  intros n x c Hc H. pose proof (nrm_pointwise n x (fun _ => 0) 0 c ltac:(lra) Hc ltac:(intros; lra)
    ltac:(intros i Hi; rewrite Rmult_0_l, Rplus_0_l; apply H; exact Hi)). lra.
Qed.

Lemma Cmod_real : forall r, Cmod (r, 0) = Rabs r.
Proof. intros r. unfold Cmod, Cmod2; simpl. rewrite Rmult_0_l, Rplus_0_r. apply sqrt_Rsqr_abs. Qed.

Lemma Cmod_C0 : Cmod C0 = 0.
Proof. unfold Cmod, Cmod2, C0; simpl. rewrite Rmult_0_l, Rplus_0_r. apply sqrt_0. Qed.

Lemma Alimb_cmod : forall a i t, Cmod (Alimb a i t) <= 32.
Proof.
  intros a i t. unfold Alimb. destruct (t <? List.length a)%nat.
  - rewrite Cmod_real. destruct (limbZ_range (nth t a 0%Z) i) as [A B].
    apply IZR_le in A, B. apply Rabs_le. split; lra.
  - rewrite Cmod_C0. lra.
Qed.

Lemma Alimb_nrm : forall a i lg, (lg <= 18)%nat -> nrm (2 ^ lg) (Alimb a i) <= 32 * sq2 ^ lg.
Proof.
  intros a i lg Hlg. eapply Rle_trans; [apply (nrm_const_bound _ _ 32); [lra | intros; apply Alimb_cmod]|].
  right. f_equal. rewrite <- sq2_pow_lg. apply sqrt_square. apply pow_le. pose proof sq2_bounds. lra.
Qed.

Lemma Alimb_nrm100 : forall a i lg, (lg <= 18)%nat -> nrm (2 ^ lg) (Alimb a i) <= bp 100.
Proof.
  intros. eapply Rle_trans; [apply Alimb_nrm; exact H|]. pose proof (sq2_pow_le lg H).
  pose proof (bp_big 100 ltac:(lia)). unfold bp in *.
  assert (Raux.bpow Zaux.radix2 20 <= Raux.bpow Zaux.radix2 100) by (apply Raux.bpow_le; lia).
  change (Raux.bpow Zaux.radix2 20) with 1048576 in H2. lra.
Qed.

Lemma load_spec : forall (x : array sint) (a : list Z) (n Ni : int) (i : nat) (lg : nat),
  repr x a -> to_Z n = Z.of_nat (List.length a) -> (List.length a <= 2 ^ lg)%nat ->
  to_Z Ni = Z.of_nat (2 ^ lg) -> (lg <= 18)%nat -> (i < 6)%nat ->
  Forall (fun c => -2 ^ 31 <= c < 2 ^ 31)%Z a ->
  PArray.length (load x n Ni (of_nat i)) = Ni /\
  crep (load x n Ni (of_nat i)) (PArray.make Ni 0%float) (2 ^ lg) (Alimb a i).
Proof.
  intros x a n Ni i lg Hx Hn Hla HN Hlg Hi Hc.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (OK : forall k, (k < 2 ^ lg)%nat -> to_Z (of_nat k) = Z.of_nat k).
  { intros k Hk. apply of_nat_to_Z. change wB with (2^63)%Z. lia. }
  assert (L0 : PArray.length (PArray.make Ni 0%float) = Ni) by (apply flength_make; lia).
  unfold load.
  set (P := fun (t : int) (A : array float) => PArray.length A = Ni /\
    forall k, (k < 2 ^ lg)%nat -> (k < Z.to_nat (to_Z t) -> repr A.[of_nat k] (fst (Alimb a i k)))%nat /\
                                  (Z.to_nat (to_Z t) <= k -> A.[of_nat k] = 0%float)%nat).
  assert (HL : P n (loop n (fun t A => A.[t <- limb x.[t] (of_nat i)]) 0 (PArray.make Ni 0%float))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. lia.
    - split; [exact L0|]. intros k Hk. change (Z.to_nat (to_Z 0)) with 0%nat. split; [lia|]. intros _. apply fget_make.
    - intros t A Ht [LA HA]. change (to_Z 0) with 0%Z in Ht. split; [rewrite flength_set; exact LA|].
      set (tn := Z.to_nat (to_Z t)).
      assert (Htn : (tn < List.length a)%nat) by (unfold tn; lia).
      assert (Hto : t = of_nat tn) by (apply of_nat_eq; unfold tn; lia).
      rewrite to_nat_succ by lia. fold tn. intros k Hk.
      destruct (Nat.eq_dec k tn) as [->|Ne].
      + split; [|lia]. intros _. rewrite <- Hto. rewrite fget_set_same by (rewrite LA; apply ltb_true; lia).
        unfold Alimb. destruct (Nat.ltb_spec tn (List.length a)) as [_|]; [|lia]. simpl.
        rewrite Hto. pose proof (repr_sint_get x a Hx tn Htn) as E.
        rewrite <- E. apply limb_repr; [|exact Hi].
        rewrite E. rewrite Forall_forall in Hc. apply Hc. apply nth_In. exact Htn.
      + assert (D : t <> of_nat k) by (rewrite Hto; apply int_neq; rewrite !OK by lia; lia).
        rewrite fget_set_other by exact D. destruct (HA k Hk) as [H1 H2]. split; intros; [apply H1 | apply H2]; lia. }
  destruct HL as [LA HA]. split; [exact LA|].
  intros k Hk. destruct (HA k Hk) as [H1 H2]. rewrite Hn, Nat2Z.id in H1, H2. split.
  - destruct (Nat.lt_ge_cases k (List.length a)) as [Hka|Hka].
    + apply H1. exact Hka.
    + apply (repr_conv _ _ _ (H2 Hka)). unfold Alimb. destruct (Nat.ltb_spec k (List.length a)); [lia|]. exact repr_lit_zero.
  - rewrite fget_make. unfold Alimb. destruct (k <? List.length a)%nat; exact repr_lit_zero.
Qed.

End Forward.

Section Forward2.
Local Open Scope R_scope.

Lemma block_disj : forall i j N k, i <> j -> (k < N)%nat -> ~ (j * N <= i * N + k < j * N + N)%nat.
Proof.
  intros i j N k Hij Hk. destruct (Nat.lt_ge_cases i j) as [H|H].
  - assert (A : ((i + 1) * N <= j * N)%nat) by (apply Nat.mul_le_mono_r; lia).
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l in A. lia.
  - assert (A : ((j + 1) * N <= i * N)%nat) by (apply Nat.mul_le_mono_r; lia).
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l in A. lia.
Qed.

Lemma block_lt : forall i N k M, (i < M)%nat -> (k < N)%nat -> (i * N + k < M * N)%nat.
Proof.
  intros i N k M Hi Hk. assert (A : ((i + 1) * N <= M * N)%nat) by (apply Nat.mul_le_mono_r; lia).
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l in A. lia.
Qed.

Lemma copy_spec : forall (Ni M off : int) (yr yi BR BI : array float) (lg i : nat),
  to_Z Ni = Z.of_nat (2 ^ lg) -> (lg <= 18)%nat -> (i < 6)%nat ->
  to_Z M = (6 * Z.of_nat (2 ^ lg))%Z -> to_Z off = (Z.of_nat i * Z.of_nat (2 ^ lg))%Z ->
  PArray.length BR = M -> PArray.length BI = M ->
  match copy_out Ni off yr yi (BR, BI) with
  | (BR', BI') => PArray.length BR' = M /\ PArray.length BI' = M /\
      forall p, (p < 6 * 2 ^ lg)%nat ->
        (i * 2 ^ lg <= p < i * 2 ^ lg + 2 ^ lg -> BR'.[of_nat p] = yr.[of_nat (p - i * 2 ^ lg)] /\
                                                  BI'.[of_nat p] = yi.[of_nat (p - i * 2 ^ lg)])%nat /\
        (~ (i * 2 ^ lg <= p < i * 2 ^ lg + 2 ^ lg) -> BR'.[of_nat p] = BR.[of_nat p] /\ BI'.[of_nat p] = BI.[of_nat p])%nat
  end.
Proof.
  intros Ni M off yr yi BR BI lg i HN Hlg Hi HM Hoff LR LI.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (OK : forall p, (p < 6 * 2 ^ lg)%nat -> to_Z (of_nat p) = Z.of_nat p).
  { intros p Hp. apply of_nat_to_Z. change wB with (2^63)%Z. lia. }
  unfold copy_out.
  set (P := fun (k : int) (st : array float * array float) =>
    PArray.length (fst st) = M /\ PArray.length (snd st) = M /\
    forall p, (p < 6 * 2 ^ lg)%nat ->
      (i * 2 ^ lg <= p < i * 2 ^ lg + Z.to_nat (to_Z k) -> (fst st).[of_nat p] = yr.[of_nat (p - i * 2 ^ lg)] /\
                                                 (snd st).[of_nat p] = yi.[of_nat (p - i * 2 ^ lg)])%nat /\
      (~ (i * 2 ^ lg <= p < i * 2 ^ lg + Z.to_nat (to_Z k)) -> (fst st).[of_nat p] = BR.[of_nat p] /\ (snd st).[of_nat p] = BI.[of_nat p])%nat).
  assert (HL : P Ni (loop Ni (fun k st => let '(BR, BI) := st in (BR.[off + k <- yr.[k]], BI.[off + k <- yi.[k]])) 0 (BR, BI))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. lia.
    - split; [exact LR|]. split; [exact LI|]. intros p Hp. change (Z.to_nat (to_Z 0)) with 0%nat.
      split; [lia | intros _; split; reflexivity].
    - intros k [A B] Hk [LA [LB HA]]. simpl in LA, LB, HA. change (to_Z 0) with 0%Z in Hk.
      set (kn := Z.to_nat (to_Z k)).
      assert (Hko : k = of_nat kn) by (apply of_nat_eq; unfold kn; lia).
      assert (Hpos : (off + k)%uint63 = of_nat (i * 2 ^ lg + kn)).
      { apply of_nat_eq. rewrite Uint63.add_spec, Hoff. unfold kn. rewrite Z.mod_small by (change wB with (2^63)%Z; nia). nia. }
      assert (Hlt : (of_nat (i * 2 ^ lg + kn) <? M) = true).
      { apply ltb_true. rewrite OK by (unfold kn; nia). rewrite HM. unfold kn. nia. }
      unfold P; simpl. rewrite Hpos. split; [rewrite flength_set; exact LA|]. split; [rewrite flength_set; exact LB|].
      rewrite to_nat_succ by lia. fold kn. intros p Hp.
      destruct (Nat.eq_dec p (i * 2 ^ lg + kn)) as [->|Ne].
      + split; [|intros F; exfalso; apply F; lia]. intros _.
        rewrite (fget_set_same A) by (rewrite LA; exact Hlt). rewrite (fget_set_same B) by (rewrite LB; exact Hlt).
        replace (i * 2 ^ lg + kn - i * 2 ^ lg)%nat with kn by lia. rewrite <- Hko. split; reflexivity.
      + assert (D : of_nat (i * 2 ^ lg + kn) <> of_nat p).
        { apply int_neq. rewrite !OK by (unfold kn in *; nia). lia. }
        rewrite (fget_set_other A) by exact D. rewrite (fget_set_other B) by exact D.
        destruct (HA p Hp) as [H1 H2]. split; intros; [apply H1 | apply H2]; lia. }
  destruct (loop Ni _ 0 (BR, BI)) as [A B]. destruct HL as [LA [LB HA]]. simpl in LA, LB, HA.
  rewrite HN, Nat2Z.id in HA. split; [exact LA|]. split; [exact LB | exact HA].
Qed.

Definition Ahat (a : list Z) (lg i : nat) : vec := cfft lg (twc false) lg (Alimb a i).

Lemma fwd_all_spec : forall (x : array sint) (a : list Z) (n hi : int) (tre tim : array float) (lg : nat),
  repr x a -> to_Z n = Z.of_nat (List.length a) -> (List.length a <= 2 ^ lg)%nat ->
  (2 <= lg <= 18)%nat -> to_Z hi = Z.of_nat (hlf lg) -> TWrep tre tim lg ->
  Forall (fun c => -2 ^ 31 <= c < 2 ^ 31)%Z a ->
  match fwd_all x n (of_nat lg) hi tre tim with
  | (BR, BI) => to_Z (PArray.length BR) = (6 * Z.of_nat (2 ^ lg))%Z /\ to_Z (PArray.length BI) = (6 * Z.of_nat (2 ^ lg))%Z /\
      forall i k, (i < 6)%nat -> (k < 2 ^ lg)%nat ->
        repr BR.[of_nat (i * 2 ^ lg + k)] (fst (Ahat a lg i k)) /\ repr BI.[of_nat (i * 2 ^ lg + k)] (snd (Ahat a lg i k))
  end.
Proof.
  intros x a n hi tre tim lg Hx Hn Hla Hlg Hh Htw Hc.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (HNh : (2 ^ lg = 2 * hlf lg)%nat).
  { unfold hlf. replace lg with (S (lg - 1)) at 1 by lia. reflexivity. }
  set (Ni := (hi + hi)%uint63).
  assert (HN : to_Z Ni = Z.of_nat (2 ^ lg)).
  { unfold Ni. rewrite Uint63.add_spec, Hh. rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
  set (M := (NL * Ni)%uint63).
  assert (HM : to_Z M = (6 * Z.of_nat (2 ^ lg))%Z).
  { unfold M. rewrite Uint63.mul_spec, HN. change (to_Z NL) with 6%Z. apply Z.mod_small. change wB with (2^63)%Z. lia. }
  assert (L0 : PArray.length (PArray.make M 0%float) = M) by (apply flength_make; lia).
  unfold fwd_all. fold Ni. fold M.
  set (P := fun (i : int) (st : array float * array float) =>
    PArray.length (fst st) = M /\ PArray.length (snd st) = M /\
    forall i' k, (i' < Z.to_nat (to_Z i))%nat -> (k < 2 ^ lg)%nat ->
      repr (fst st).[of_nat (i' * 2 ^ lg + k)] (fst (Ahat a lg i' k)) /\
      repr (snd st).[of_nat (i' * 2 ^ lg + k)] (snd (Ahat a lg i' k))).
  assert (HL : P NL (loop NL (fun i st =>
      let '(yr, yi) := fft (of_nat lg) hi false tre tim (load x n Ni i) (PArray.make Ni 0%float) in
      copy_out Ni (i * Ni) yr yi st) 0 (PArray.make M 0%float, PArray.make M 0%float))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. change (to_Z NL) with 6%Z. lia.
    - split; [exact L0|]. split; [exact L0|]. intros i' k Hi'. change (Z.to_nat (to_Z 0)) with 0%nat in Hi'. lia.
    - intros j [A B] Hj [LA [LB HA]]. simpl in LA, LB, HA. change (to_Z 0) with 0%Z in Hj. change (to_Z NL) with 6%Z in Hj.
      set (jn := Z.to_nat (to_Z j)).
      assert (Hjo : j = of_nat jn) by (apply of_nat_eq; unfold jn; lia).
      destruct (load_spec x a n Ni jn lg Hx Hn Hla HN ltac:(lia) ltac:(unfold jn; lia) Hc) as [Ll Hl].
      rewrite <- Hjo in Ll, Hl.
      assert (L1 : PArray.length (PArray.make Ni 0%float) = Ni) by (apply flength_make; lia).
      pose proof (fft_spec lg Ni hi false tre tim (load x n Ni j) (PArray.make Ni 0%float) (Alimb a jn)
                    Hlg HN Hh Ll L1 Htw Hl (cfft_bound false lg (Alimb a jn) Hlg (Alimb_nrm100 a jn lg ltac:(lia)))) as Hf.
      destruct (fft (of_nat lg) hi false tre tim (load x n Ni j) (PArray.make Ni 0%float)) as [yr yi].
      destruct Hf as [Lyr [Lyi Hy]].
      pose proof (copy_spec Ni M (j * Ni) yr yi A B lg jn HN ltac:(lia) ltac:(unfold jn; lia) HM
                    ltac:(rewrite Uint63.mul_spec, HN; unfold jn; rewrite Z2Nat.id by lia; apply Z.mod_small; change wB with (2^63)%Z; nia)
                    LA LB) as Hcp.
      destruct (copy_out Ni (j * Ni) yr yi (A, B)) as [A' B'].
      destruct Hcp as [LA' [LB' Hcp]]. simpl.
      split; [exact LA'|]. split; [exact LB'|].
      rewrite to_nat_succ by lia. fold jn. intros i' k Hi' Hk.
      assert (Hpk : (i' * 2 ^ lg + k < 6 * 2 ^ lg)%nat) by (apply block_lt; lia).
      destruct (Hcp _ Hpk) as [C1 C2].
      destruct (Nat.eq_dec i' jn) as [->|Ne].
      + destruct (C1 ltac:(lia)) as [E1 E2]. replace (jn * 2 ^ lg + k - jn * 2 ^ lg)%nat with k in E1, E2 by lia.
        destruct (Hy k Hk) as [R1 R2]. split; [apply (repr_conv _ _ _ E1) | apply (repr_conv _ _ _ E2)]; assumption.
      + destruct (C2 (block_disj i' jn (2 ^ lg) k Ne Hk)) as [E1 E2]. destruct (HA i' k ltac:(lia) Hk) as [R1 R2].
        split; [apply (repr_conv _ _ _ E1) | apply (repr_conv _ _ _ E2)]; assumption. }
  destruct (loop NL _ 0 _) as [A B]. destruct HL as [LA [LB HA]]. simpl in LA, LB, HA.
  rewrite LA, LB, HM. split; [reflexivity|]. split; [reflexivity|].
  intros i k Hi Hk. apply HA; [change (to_Z NL) with 6%Z; simpl; lia | exact Hk].
Qed.

End Forward2.

(* ---------------------------------------------------------------------- *)
(* The pointwise products                                                 *)
(* ---------------------------------------------------------------------- *)

Section Products.
Local Open Scope R_scope.

Definition cond (w i : nat) : bool := andb (i <=? w)%nat (w - i <? 6)%nat.

Fixpoint pfold (A B : nat -> vec) (w k t : nat) : C :=
  match t with
  | O => C0
  | S t' => if cond w t' then caddr (pfold A B w k t') (cmulr (A t' k) (B (w - t')%nat k))
            else pfold A B w k t'
  end.

Definition pex (A B : nat -> vec) (w k t : nat) : C :=
  csum (fun i => if cond w i then Cmul (A i k) (B (w - i)%nat k) else C0) t.

Definition CI : C := (0, 1).

Definition Pcell (A B : nat -> vec) (g k : nat) : C :=
  let q0 := pfold A B (2 * g) k 6 in
  let q1 := pfold A B (2 * g + 1) k 6 in
  (rnd (fst q0 - snd q1), rnd (snd q0 + fst q1)).

Lemma idx_small : forall a b c : Z, (0 <= a <= 12)%Z -> (0 <= b <= 262144)%Z -> (0 <= c <= 262144)%Z ->
  (0 <= a * b < wB)%Z /\ (0 <= a * b + c < wB)%Z.
Proof. intros a b c Ha Hb Hc. change wB with (2^63)%Z. split; nia. Qed.

Definition BB (t : nat) : R := bp (810 + 2 * Z.of_nat t).

Lemma cond_int : forall (w i : int) (wn in_ : nat), to_Z w = Z.of_nat wn -> to_Z i = Z.of_nat in_ ->
  (wn <= 11)%nat -> (in_ < 6)%nat ->
  andb (i <=? w) (w - i <? NL) = cond wn in_.
Proof.
  intros w i wn in_ Hw Hi Hwn Hin. unfold cond.
  destruct (Nat.leb_spec in_ wn) as [Hle|Hgt].
  - assert (E1 : (i <=? w) = true) by (rewrite Uint63.leb_spec; lia). rewrite E1. simpl.
    assert (Hs : to_Z (w - i) = Z.of_nat (wn - in_)) by (rewrite Uint63.sub_spec, Hw, Hi; rewrite Z.mod_small by (change wB with (2^63)%Z; lia); lia).
    destruct (Nat.ltb_spec (wn - in_) 6) as [Hl|Hl].
    + apply Uint63.ltb_spec. rewrite Hs. change (to_Z NL) with 6%Z. lia.
    + apply Bool.not_true_iff_false. rewrite Uint63.ltb_spec, Hs. change (to_Z NL) with 6%Z. lia.
  - assert (E1 : (i <=? w) = false) by (apply Bool.not_true_iff_false; rewrite Uint63.leb_spec; lia).
    rewrite E1. reflexivity.
Qed.

Lemma pterm_spec : forall (Ni k w : int) (AR AI BR BI : array float) (A B : nat -> vec) (lg kn wn : nat),
  to_Z Ni = Z.of_nat (2 ^ lg) -> (lg <= 18)%nat -> to_Z k = Z.of_nat kn -> (kn < 2 ^ lg)%nat ->
  to_Z w = Z.of_nat wn -> (wn <= 11)%nat ->
  (forall i, (i < 6)%nat -> repr AR.[of_nat (i * 2 ^ lg + kn)] (fst (A i kn)) /\ repr AI.[of_nat (i * 2 ^ lg + kn)] (snd (A i kn)) /\
                            Rabs (fst (A i kn)) <= Bg /\ Rabs (snd (A i kn)) <= Bg) ->
  (forall i, (i < 6)%nat -> repr BR.[of_nat (i * 2 ^ lg + kn)] (fst (B i kn)) /\ repr BI.[of_nat (i * 2 ^ lg + kn)] (snd (B i kn)) /\
                            Rabs (fst (B i kn)) <= Bg /\ Rabs (snd (B i kn)) <= Bg) ->
  match loop NL (pterm w Ni k AR AI BR BI) 0 (0%float, 0%float) with
  | (qr, qi) => repr qr (fst (pfold A B wn kn 6)) /\ repr qi (snd (pfold A B wn kn 6)) /\
                Rabs (fst (pfold A B wn kn 6)) <= BB 6 /\ Rabs (snd (pfold A B wn kn 6)) <= BB 6
  end.
Proof.
  intros Ni k w AR AI BR BI A B lg kn wn HN Hlg Hk Hkn Hw Hwn HA HB.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  destruct Bg_facts as [G1 [G2 G3]].
  assert (Hbg2 : Bg * Bg = bp 800) by (unfold Bg; rewrite <- bp_mul; reflexivity).
  assert (BBup : forall t, (t < 6)%nat ->
            BB t + (8 * (Bg * Bg) + 5) <= bp 900 /\ 2 * (BB t + (8 * (Bg * Bg) + 5)) + 1 <= BB (S t)).
  { intros t Ht. unfold BB. rewrite Hbg2.
    assert (E : bp (810 + 2 * Z.of_nat (S t)) = 4 * bp (810 + 2 * Z.of_nat t)).
    { replace (810 + 2 * Z.of_nat (S t))%Z with (2 + (810 + 2 * Z.of_nat t))%Z by lia.
      rewrite bp_mul. reflexivity. }
    assert (L1 : bp 800 * 1024 <= bp (810 + 2 * Z.of_nat t)).
    { replace (810 + 2 * Z.of_nat t)%Z with (800 + (10 + 2 * Z.of_nat t))%Z by lia. rewrite bp_mul.
      pose proof (bp_big (10 + 2 * Z.of_nat t) ltac:(lia)). pose proof (bp_ge1 800 ltac:(lia)). nra. }
    assert (L2 : bp (810 + 2 * Z.of_nat t) * 1024 <= bp 900).
    { replace 900%Z with ((810 + 2 * Z.of_nat t) + (90 - 2 * Z.of_nat t))%Z by lia.
      rewrite (bp_mul (810 + 2 * Z.of_nat t) (90 - 2 * Z.of_nat t)).
      apply Rmult_le_compat_l; [unfold bp; apply Raux.bpow_ge_0 | apply bp_big; lia]. }
    rewrite E. pose proof (bp_ge1 800 ltac:(lia)). lra. }
  set (P := fun (t : int) (st : float * float) =>
    repr (fst st) (fst (pfold A B wn kn (Z.to_nat (to_Z t)))) /\ repr (snd st) (snd (pfold A B wn kn (Z.to_nat (to_Z t)))) /\
    Rabs (fst (pfold A B wn kn (Z.to_nat (to_Z t)))) <= BB (Z.to_nat (to_Z t)) /\
    Rabs (snd (pfold A B wn kn (Z.to_nat (to_Z t)))) <= BB (Z.to_nat (to_Z t))).
  assert (HL : P NL (loop NL (pterm w Ni k AR AI BR BI) 0 (0%float, 0%float))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. change (to_Z NL) with 6%Z. lia.
    - unfold P. change (Z.to_nat (to_Z 0)) with 0%nat. simpl. split; [exact repr_lit_zero|]. split; [exact repr_lit_zero|].
      rewrite Rabs_R0. unfold BB, bp. pose proof (Raux.bpow_ge_0 Zaux.radix2 (810 + 2 * Z.of_nat 0)). lra.
    - intros i [qr qi] Hi [R1 [R2 [B1 B2]]]. change (to_Z 0) with 0%Z in Hi. change (to_Z NL) with 6%Z in Hi.
      set (tn := Z.to_nat (to_Z i)) in *.
      assert (Hio : to_Z i = Z.of_nat tn) by (unfold tn; lia).
      unfold P. rewrite to_nat_succ by lia. fold tn. simpl pfold. unfold pterm.
      rewrite (cond_int w i wn tn Hw Hio Hwn ltac:(lia)).
      destruct (cond wn tn) eqn:Ec.
      + unfold cond in Ec. apply andb_prop in Ec. destruct Ec as [Ec1 Ec2].
        apply Nat.leb_le in Ec1. apply Nat.ltb_lt in Ec2.
        assert (Ia : (i * Ni + k)%uint63 = of_nat (tn * 2 ^ lg + kn)).
        { apply of_nat_eq. rewrite Uint63.add_spec, Uint63.mul_spec, Hio, HN, Hk.
          destruct (idx_small (Z.of_nat tn) (Z.of_nat (2 ^ lg)) (Z.of_nat kn) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2].
          rewrite (Z.mod_small (_ * _)) by exact S1. rewrite Z.mod_small by exact S2. lia. }
        assert (Ib : ((w - i) * Ni + k)%uint63 = of_nat ((wn - tn) * 2 ^ lg + kn)).
        { apply of_nat_eq. rewrite Uint63.add_spec, Uint63.mul_spec, Uint63.sub_spec, Hio, HN, Hk, Hw.
          rewrite (Z.mod_small (_ - _)) by (change wB with (2^63)%Z; lia).
          destruct (idx_small (Z.of_nat wn - Z.of_nat tn) (Z.of_nat (2 ^ lg)) (Z.of_nat kn) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2].
          rewrite (Z.mod_small (_ * _)) by exact S1. rewrite Z.mod_small by exact S2.
          rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_sub by lia. reflexivity. }
        rewrite Ia, Ib.
        destruct (HA tn ltac:(lia)) as [Ra1 [Ra2 [Ba1 Ba2]]].
        destruct (HB (wn - tn)%nat ltac:(lia)) as [Rb1 [Rb2 [Bb1 Bb2]]].
        destruct (repr_cmulr _ _ _ _ (A tn kn) (B (wn - tn)%nat kn) Bg Bg Ra1 Ra2 Rb1 Rb2 Ba1 Ba2 Bb1 Bb2
                    ltac:(lra) ltac:(lra) ltac:(rewrite Hbg2; lra)) as [Rm1 [Rm2 [Bm1 Bm2]]].
        destruct (BBup tn ltac:(lia)) as [U1 U2].
        unfold cacc, caddr. cbn [fst snd] in *.
        destruct (radd_ok _ _ _ _ _ _ R1 Rm1 B1 Bm1 U1) as [S1 T1].
        destruct (radd_ok _ _ _ _ _ _ R2 Rm2 B2 Bm2 U1) as [S2 T2].
        split; [exact S1|]. split; [exact S2|]. split; lra.
      + simpl. split; [exact R1|]. split; [exact R2|].
        assert (BB tn <= BB (S tn)) by (unfold BB, bp; apply Raux.bpow_le; lia). split; lra. }
  destruct (loop NL _ 0 _) as [qr qi]. unfold P in HL. change (Z.to_nat (to_Z NL)) with 6%nat in HL. exact HL.
Qed.

Lemma BB6_ok : BB 6 + BB 6 <= bp 900.
Proof.
  unfold BB. simpl Z.of_nat. replace 900%Z with (822 + 78)%Z by lia. rewrite (bp_mul 822 78).
  pose proof (bp_big 78 ltac:(lia)). replace (810 + 2 * 6)%Z with 822%Z by lia.
  assert (0 <= bp 822) by (unfold bp; apply Raux.bpow_ge_0). nra.
Qed.

Lemma products_spec : forall (g : nat) (Ni : int) (AR AI BR BI : array float) (A B : nat -> vec) (lg : nat),
  (g < 6)%nat -> to_Z Ni = Z.of_nat (2 ^ lg) -> (lg <= 18)%nat ->
  (forall i k, (i < 6)%nat -> (k < 2 ^ lg)%nat ->
     repr AR.[of_nat (i * 2 ^ lg + k)] (fst (A i k)) /\ repr AI.[of_nat (i * 2 ^ lg + k)] (snd (A i k)) /\
     Rabs (fst (A i k)) <= Bg /\ Rabs (snd (A i k)) <= Bg) ->
  (forall i k, (i < 6)%nat -> (k < 2 ^ lg)%nat ->
     repr BR.[of_nat (i * 2 ^ lg + k)] (fst (B i k)) /\ repr BI.[of_nat (i * 2 ^ lg + k)] (snd (B i k)) /\
     Rabs (fst (B i k)) <= Bg /\ Rabs (snd (B i k)) <= Bg) ->
  match products (of_nat g) Ni AR AI BR BI with
  | (pr, pim) => PArray.length pr = Ni /\ PArray.length pim = Ni /\ crep pr pim (2 ^ lg) (Pcell A B g)
  end.
Proof.
  intros g Ni AR AI BR BI A B lg Hg HN Hlg HA HB.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (OK : forall k, (k < 2 ^ lg)%nat -> to_Z (of_nat k) = Z.of_nat k).
  { intros k Hk. apply of_nat_to_Z. change wB with (2^63)%Z. lia. }
  assert (Hgz : to_Z (of_nat g) = Z.of_nat g) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  assert (Hw0 : to_Z (of_nat g + of_nat g) = Z.of_nat (2 * g)).
  { rewrite Uint63.add_spec, Hgz. rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
  assert (Hw1 : to_Z (of_nat g + of_nat g + 1) = Z.of_nat (2 * g + 1)).
  { rewrite Uint63.add_spec, Hw0. change (to_Z 1) with 1%Z. rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
  assert (L0 : PArray.length (PArray.make Ni 0%float) = Ni) by (apply flength_make; lia).
  unfold products.
  set (P := fun (k : int) (st : array float * array float) =>
    PArray.length (fst st) = Ni /\ PArray.length (snd st) = Ni /\
    forall k', (k' < Z.to_nat (to_Z k))%nat -> repr (fst st).[of_nat k'] (fst (Pcell A B g k')) /\
                                             repr (snd st).[of_nat k'] (snd (Pcell A B g k'))).
  assert (HL : P Ni (loop Ni (pcell (of_nat g) Ni AR AI BR BI) 0 (PArray.make Ni 0%float, PArray.make Ni 0%float))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. lia.
    - split; [exact L0|]. split; [exact L0|]. intros k' Hk'. change (Z.to_nat (to_Z 0)) with 0%nat in Hk'. lia.
    - intros k [pr pim] Hk [L1 [L2 T]]. cbn [fst snd] in L1, L2, T. change (to_Z 0) with 0%Z in Hk.
      set (kn := Z.to_nat (to_Z k)).
      assert (Hko : to_Z k = Z.of_nat kn) by (unfold kn; lia).
      assert (Hkn : (kn < 2 ^ lg)%nat) by (unfold kn; lia).
      unfold pcell.
      pose proof (pterm_spec Ni k (of_nat g + of_nat g) AR AI BR BI A B lg kn (2 * g) HN Hlg Hko Hkn Hw0 ltac:(lia)
                    (fun i Hi => HA i kn Hi Hkn) (fun i Hi => HB i kn Hi Hkn)) as H0.
      pose proof (pterm_spec Ni k (of_nat g + of_nat g + 1) AR AI BR BI A B lg kn (2 * g + 1) HN Hlg Hko Hkn Hw1 ltac:(lia)
                    (fun i Hi => HA i kn Hi Hkn) (fun i Hi => HB i kn Hi Hkn)) as H1.
      destruct (loop NL (pterm (of_nat g + of_nat g) Ni k AR AI BR BI) 0 (0%float, 0%float)) as [q0r q0i].
      destruct (loop NL (pterm (of_nat g + of_nat g + 1) Ni k AR AI BR BI) 0 (0%float, 0%float)) as [q1r q1i].
      destruct H0 as [R0r [R0i [B0r B0i]]]. destruct H1 as [R1r [R1i [B1r B1i]]].
      pose proof BB6_ok as BB6.
      destruct (rsub_ok _ _ _ _ _ _ R0r R1i B0r B1i BB6) as [S1 _].
      destruct (radd_ok _ _ _ _ _ _ R0i R1r B0i B1r BB6) as [S2 _].
      assert (Hko' : k = of_nat kn) by (apply of_nat_eq; exact Hko).
      assert (Hlt : (k <? Ni) = true) by (apply ltb_true; lia).
      unfold P. cbn [fst snd]. rewrite !flength_set. split; [exact L1|]. split; [exact L2|].
      rewrite to_nat_succ by lia. fold kn. intros k' Hk'.
      destruct (Nat.eq_dec k' kn) as [->|Ne].
      + rewrite <- Hko'. rewrite (fget_set_same pr) by (rewrite L1; exact Hlt).
        rewrite (fget_set_same pim) by (rewrite L2; exact Hlt).
        unfold Pcell; cbn [fst snd]. split; assumption.
      + assert (D : k <> of_nat k') by (rewrite Hko'; apply int_neq; rewrite !OK by lia; lia).
        rewrite (fget_set_other pr) by exact D. rewrite (fget_set_other pim) by exact D. apply T. lia. }
  destruct (loop Ni _ 0 _) as [pr pim]. destruct HL as [L1 [L2 T]]. cbn [fst snd] in L1, L2, T.
  rewrite HN, Nat2Z.id in T. split; [exact L1|]. split; [exact L2|]. intros k Hk. apply T. exact Hk.
Qed.

End Products.

(* ---------------------------------------------------------------------- *)
(* Reading a float back as an integer                                     *)
(* ---------------------------------------------------------------------- *)

Section ToInt.
Local Open Scope R_scope.

Local Instance prec_gt_0_53 : FLX.Prec_gt_0 53 := eq_refl _.
Local Instance prec_lt_emax_53 : BinarySingleNaN.Prec_lt_emax 53 1024 := eq_refl _.
Local Instance fexp64_valid2 : Generic_fmt.Valid_exp fexp64 := FLT.FLT_exp_valid _ _.

Lemma rnd_to_int : forall (K : Z) (x : R), (4503599627370497 <= K <= 9007199254740990)%Z ->
  Rabs (x - IZR K) < / 2 -> rnd x = IZR K.
Proof.
  intros K x HK Hx.
  pose proof (Generic_fmt.round_N_pt Zaux.radix2 fexp64 (fun z => negb (Z.even z)) x) as [Hf Hm].
  change (Generic_fmt.round Zaux.radix2 fexp64 (Generic_fmt.Znearest (fun z => negb (Z.even z))) x) with (rnd x) in Hf, Hm.
  assert (HKf : Generic_fmt.generic_format Zaux.radix2 fexp64 (IZR K)).
  { rewrite <- (rnd_IZR K) by lia. unfold rnd. apply Generic_fmt.generic_format_round; [exact _ | apply Generic_fmt.valid_rnd_N]. }
  specialize (Hm _ HKf).
  set (r := rnd x) in *.
  assert (Hr : Rabs (r - IZR K) < 1).
  { replace (r - IZR K) with ((r - x) + (x - IZR K)) by ring. eapply Rle_lt_trans; [apply Rabs_triang|].
    rewrite (Rabs_minus_sym (IZR K) x) in Hm. lra. }
  apply Rabs_def2 in Hr.
  assert (HK2 : IZR K <= 9007199254740990) by (apply IZR_le; lia).
  assert (HK3 : 4503599627370497 <= IZR K) by (apply IZR_le; lia).
  assert (Hmag : Raux.mag_val Zaux.radix2 r (Raux.mag Zaux.radix2 r) = 53%Z).
  { apply Raux.mag_unique. rewrite Rabs_pos_eq by lra.
    change (Raux.bpow Zaux.radix2 (53 - 1)) with 4503599627370496. change (Raux.bpow Zaux.radix2 53) with 9007199254740992. lra. }
  unfold Generic_fmt.generic_format, Generic_fmt.cexp in Hf. rewrite Hmag in Hf.
  change (fexp64 53) with 0%Z in Hf. unfold Defs.F2R in Hf. simpl in Hf. rewrite Rmult_1_r in Hf.
  set (m := Raux.Ztrunc (Generic_fmt.scaled_mantissa Zaux.radix2 fexp64 r)) in Hf.
  rewrite Hf in Hr |- *. f_equal.
  assert (A : (-1 < m - K)%Z) by (apply lt_IZR; rewrite minus_IZR; lra).
  assert (B : (m - K < 1)%Z) by (apply lt_IZR; rewrite minus_IZR; lra). lia.
Qed.

Lemma toint_spec : forall (z : float) (zr : R) (D : Z), repr z zr -> (Z.abs D <= 2 ^ 40)%Z ->
  Rabs (zr - IZR D) < / 2 -> Sint63.to_Z (toint z) = D.
Proof.
  intros z zr D Hz HD Hzd.
  assert (HD' : (-1099511627776 <= D <= 1099511627776)%Z) by lia.
  assert (Hzr : Rabs zr <= 1099511627777).
  { apply Rabs_def2 in Hzd. destruct HD' as [D1 D2]. apply IZR_le in D1, D2. apply Rabs_le. split; lra. }
  destruct (radd_ok z MAGIC zr 6755399441055744 1099511627777 6755399441055744 Hz repr_lit_magic Hzr
             ltac:(rewrite Rabs_pos_eq; lra) ltac:(pose proof (bp_big 900 ltac:(lia)); unfold bp in *;
                   assert (Raux.bpow Zaux.radix2 60 <= Raux.bpow Zaux.radix2 900) by (apply Raux.bpow_le; lia);
                   change (Raux.bpow Zaux.radix2 60) with 1152921504606846976 in H0; lra)) as [Ry _].
  set (K := (6755399441055744 + D)%Z).
  assert (HKr : rnd (zr + 6755399441055744) = IZR K).
  { apply rnd_to_int; [unfold K; lia|]. unfold K. rewrite plus_IZR.
    replace (zr + 6755399441055744 - (IZR 6755399441055744 + IZR D)) with (zr - IZR D) by (simpl; ring). exact Hzd. }
  rewrite HKr in Ry. apply repr_float_iff in Ry. destruct Ry as [Fy By].
  unfold toint.
  pose proof (Flocq.IEEE754.PrimFloat.frshiftexp_equiv (z + MAGIC)%float) as Hfe.
  destruct (frshiftexp (z + MAGIC)%float) as [f e].
  assert (HK : (4503599627370497 <= K <= 9007199254740990)%Z) by (unfold K; lia).
  assert (HKpos : 4503599627370497 <= IZR K <= 9007199254740990) by (split; apply IZR_le; lia).
  assert (Hfs : BinarySingleNaN.is_finite_strict (Flocq.IEEE754.PrimFloat.Prim2B (z + MAGIC)%float) = true).
  { destruct (Flocq.IEEE754.PrimFloat.Prim2B (z + MAGIC)%float) as [s0|s0| |s0 m0 e0 H0]; simpl in Fy, By |- *;
      try discriminate; try reflexivity. lra. }
  pose proof (BinarySingleNaN.Bfrexp_correct _ _ Flocq.IEEE754.PrimFloat.Hprec _ Hfs) as Hc.
  rewrite <- Hfe in Hc. destruct Hc as [Hc1 Hc2]. specialize (Hc2 eq_refl). destruct Hc2 as [Hc2 Hc3].
  rewrite By in Hc1, Hc3.
  assert (Hmag : Raux.mag_val Zaux.radix2 (IZR K) (Raux.mag Zaux.radix2 (IZR K)) = 53%Z).
  { apply Raux.mag_unique. rewrite Rabs_pos_eq by lra.
    change (Raux.bpow Zaux.radix2 (53 - 1)) with 4503599627370496. change (Raux.bpow Zaux.radix2 53) with 9007199254740992. lra. }
  rewrite Hmag in Hc3. rewrite Hc3 in Hc1. change (Raux.bpow Zaux.radix2 53) with 9007199254740992 in Hc1.
  pose proof (BinarySingleNaN.Bnormfr_mantissa_correct _ _ _ (Flocq.IEEE754.PrimFloat.Prim2B f) Hc2) as Hn.
  pose proof (Flocq.IEEE754.PrimFloat.normfr_mantissa_equiv f) as Hnm.
  destruct (Flocq.IEEE754.PrimFloat.Prim2B f) as [s0|s0| |s0 m0 e0 H0]; try contradiction.
  destruct Hn as [Hn1 [_ Hn3]]. rewrite Hn1 in Hnm. simpl in Hnm. subst e0.
  simpl in Hc1. unfold Defs.F2R in Hc1. simpl in Hc1.
  change (Raux.bpow Zaux.radix2 (- 53)) with (/ 9007199254740992) in Hc1.
  assert (Hm : cond_Zopp s0 (Z.pos m0) = K).
  { apply eq_IZR. change (IZR (Z.pow_pos 2 53)) with 9007199254740992 in Hc1. rewrite Hc1. field. }
  destruct s0; simpl in Hm; [lia|].
  rewrite Sint63.to_Z_cmodwB, Uint63.sub_spec, Hnm, Sint63.cmod_mod.
  change (to_Z MAGICI) with 6755399441055744%Z. rewrite Hm. unfold K.
  replace (6755399441055744 + D - 6755399441055744)%Z with D by ring.
  apply Sint63.cmod_small. change wB with (2 ^ 63)%Z. lia.
Qed.

End ToInt.

(* ---------------------------------------------------------------------- *)
(* The exact pipeline: the products are the DFT of the limb convolutions  *)
(* ---------------------------------------------------------------------- *)

Fixpoint zsum (f : nat -> Z) (n : nat) : Z :=
  match n with O => 0%Z | S k => (zsum f k + f k)%Z end.

Lemma zsum_ext : forall f g n, (forall i, (i < n)%nat -> f i = g i) -> zsum f n = zsum g n.
Proof.
  intros f g n; induction n as [|n IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma IZR_zsum : forall f n, IZR (zsum f n) = rsum (fun i => IZR (f i)) n.
Proof. intros f n; induction n as [|n IH]; simpl; [reflexivity|]. rewrite plus_IZR, IH. reflexivity. Qed.

Definition Al (a : list Z) (i t : nat) : Z :=
  if (t <? List.length a)%nat then limbZ (nth t a 0%Z) i else 0%Z.

Definition Dz (a b : list Z) (w q : nat) : Z :=
  zsum (fun i => if cond w i then zsum (fun t => Al a i t * Al b (w - i) (q - t))%Z (S q) else 0%Z) 6.

Section Exact.
Local Open Scope R_scope.

Definition dsum (a b : list Z) (w q : nat) : C :=
  csum (fun i => if cond w i then conv (Alimb a i) (Alimb b (w - i)%nat) q else C0) 6.

Definition dvec (a b : list Z) (g : nat) : vec :=
  fun q => Cadd (dsum a b (2 * g) q) (Cmul CI (dsum a b (2 * g + 1) q)).

Definition Aex (a : list Z) (lg i : nat) : vec := fft_ex 1 lg lg (Alimb a i).

Definition Pex (a b : list Z) (lg g : nat) : vec :=
  fun k => Cadd (pex (Aex a lg) (Aex b lg) (2 * g) k 6) (Cmul CI (pex (Aex a lg) (Aex b lg) (2 * g + 1) k 6)).

Lemma Alimb_fst : forall a i t, fst (Alimb a i t) = IZR (Al a i t).
Proof. intros. unfold Alimb, Al. destruct (t <? List.length a)%nat; reflexivity. Qed.

Lemma Alimb_snd : forall a i t, snd (Alimb a i t) = 0.
Proof. intros. unfold Alimb. destruct (t <? List.length a)%nat; reflexivity. Qed.

Lemma Alimb_zero : forall a i t, (List.length a <= t)%nat -> Alimb a i t = C0.
Proof. intros a i t H. unfold Alimb. destruct (Nat.ltb_spec t (List.length a)); [lia | reflexivity]. Qed.

Lemma if_csum : forall (c : bool) f n, (if c then csum f n else C0) = csum (fun q => if c then f q else C0) n.
Proof. intros c f n. destruct c; [reflexivity|]. symmetry. apply csum_zero. intros; reflexivity. Qed.

Lemma Pex_dft : forall a b lg g k, (List.length a + List.length b <= S (2 ^ lg))%nat -> (k < 2 ^ lg)%nat ->
  Pex a b lg g k = csum (fun q => Cmul (dvec a b g q) (EN (2 ^ lg) (Z.of_nat q * Z.of_nat k))) (2 ^ lg).
Proof.
  intros a b lg g k Hab Hk.
  assert (HN : (0 < 2 ^ lg)%nat) by apply pow2_pos.
  set (p := fun n : nat => EN (2 ^ lg) (Z.of_nat n * Z.of_nat k)).
  assert (Hp : forall x y, p (x + y)%nat = Cmul (p x) (p y)).
  { intros x y. unfold p. rewrite <- EN_add by exact HN. f_equal. lia. }
  assert (Hdft : forall (a0 : list Z) i, Aex a0 lg i k = csum (fun t => Cmul (Alimb a0 i t) (p t)) (2 ^ lg)).
  { intros a0 i. unfold Aex. rewrite fft_ex_dft by (auto; lia). apply csum_ext. intros t Ht. unfold p. f_equal. f_equal. lia. }
  assert (Hprod : forall w, pex (Aex a lg) (Aex b lg) w k 6 =
            csum (fun q => Cmul (dsum a b w q) (p q)) (2 ^ lg)).
  { intros w. unfold pex, dsum.
    rewrite (csum_ext _ (fun i0 => csum (fun q => if cond w i0 then Cmul (conv (Alimb a i0) (Alimb b (w - i0)%nat) q) (p q) else C0) (2 ^ lg))).
    - rewrite csum_swap. apply csum_ext. intros q Hq. rewrite Cmul_csum_r. apply csum_ext. intros i0 Hi0.
      destruct (cond w i0); [reflexivity|]. apply Ceq; unfold Cmul, C0; simpl; ring.
    - intros i0 Hi0. rewrite <- if_csum. destruct (cond w i0); [|reflexivity].
      rewrite !Hdft. apply (cauchy_product _ _ p (List.length a) (List.length b) (2 ^ lg)).
      + intros n Hn. apply Alimb_zero. exact Hn.
      + intros n Hn. apply Alimb_zero. exact Hn.
      + exact Hab.
      + exact Hp. }
  unfold Pex. rewrite (Hprod (2 * g)%nat), (Hprod (2 * g + 1)%nat).
  rewrite Cmul_csum_l, <- csum_add. apply csum_ext. intros q Hq. unfold dvec.
  apply Ceq; unfold Cadd, Cmul, CI; simpl; ring.
Qed.

Lemma Pex_inv : forall a b lg g q, (List.length a + List.length b <= S (2 ^ lg))%nat -> (q < 2 ^ lg)%nat ->
  fft_ex (-1) lg lg (Pex a b lg g) q = Cscal (INR (2 ^ lg)) (dvec a b g q).
Proof.
  intros a b lg g q Hab Hq.
  assert (HN : (0 < 2 ^ lg)%nat) by apply pow2_pos.
  rewrite fft_ex_dft by (auto; lia).
  rewrite <- (dft_inversion (2 ^ lg) HN (dvec a b g) q Hq).
  apply csum_ext. intros k Hk. rewrite Pex_dft by assumption. f_equal. f_equal. lia.
Qed.

Lemma csum_fst : forall f n, fst (csum f n) = rsum (fun i => fst (f i)) n.
Proof. reflexivity. Qed.

Lemma csum_snd : forall f n, snd (csum f n) = rsum (fun i => snd (f i)) n.
Proof. reflexivity. Qed.

Lemma conv_real : forall f g q, (forall t, snd (f t) = 0) -> (forall t, snd (g t) = 0) ->
  snd (conv f g q) = 0 /\ fst (conv f g q) = rsum (fun t => fst (f t) * fst (g (q - t)%nat)) (S q).
Proof.
  intros f g q Hf Hg. unfold conv. rewrite csum_fst, csum_snd. split.
  - apply rsum_zero. intros t _. unfold Cmul. cbn [fst snd]. rewrite Hf, Hg. ring.
  - apply rsum_ext. intros t _. unfold Cmul. cbn [fst snd]. rewrite Hf, Hg. ring.
Qed.

Lemma dsum_real : forall a b w q, snd (dsum a b w q) = 0 /\ fst (dsum a b w q) = IZR (Dz a b w q).
Proof.
  intros a b w q. unfold dsum, Dz. rewrite csum_fst, csum_snd. split.
  - apply rsum_zero. intros i _. destruct (cond w i); [|reflexivity].
    apply conv_real; intros; apply Alimb_snd.
  - rewrite IZR_zsum. apply rsum_ext. intros i _. destruct (cond w i); [|reflexivity].
    destruct (conv_real (Alimb a i) (Alimb b (w - i)%nat) q ltac:(intros; apply Alimb_snd) ltac:(intros; apply Alimb_snd)) as [_ E].
    rewrite E, IZR_zsum. apply rsum_ext. intros t _. rewrite !Alimb_fst, mult_IZR. reflexivity.
Qed.

Lemma dvec_parts : forall a b g q, fst (dvec a b g q) = IZR (Dz a b (2 * g) q) /\ snd (dvec a b g q) = IZR (Dz a b (2 * g + 1) q).
Proof.
  intros a b g q. destruct (dsum_real a b (2 * g) q) as [S0 F0]. destruct (dsum_real a b (2 * g + 1) q) as [S1 F1].
  unfold dvec, Cadd, Cmul, CI. cbn [fst snd]. rewrite S0, F0, S1, F1. split; ring.
Qed.

End Exact.

Lemma zsum_bound : forall f n m c, (0 <= c)%Z -> (forall t, (m <= t)%nat -> f t = 0%Z) ->
  (forall t, (Z.abs (f t) <= c)%Z) -> (Z.abs (zsum f n) <= Z.of_nat m * c)%Z.
Proof.
  intros f n m c Hc Hz Hb. assert (G : (Z.abs (zsum f n) <= Z.of_nat (Nat.min n m) * c)%Z).
  { induction n as [|n IH]; simpl zsum; [simpl; lia|].
    destruct (Nat.lt_ge_cases n m) as [Hn|Hn].
    - pose proof (Hb n). replace (Nat.min (S n) m) with (S (Nat.min n m)) by lia. rewrite Nat2Z.inj_succ. nia.
    - rewrite (Hz n Hn), Z.add_0_r. replace (Nat.min (S n) m) with (Nat.min n m) by lia. exact IH. }
  eapply Z.le_trans; [exact G|]. apply Z.mul_le_mono_nonneg_r; [exact Hc | lia].
Qed.

Lemma Al_bound : forall a i t, (Z.abs (Al a i t) <= 32)%Z.
Proof. intros. unfold Al. destruct (t <? List.length a)%nat; [pose proof (limbZ_range (nth t a 0%Z) i); lia | simpl; lia]. Qed.

Lemma Dz_bound : forall a b w q, (Z.abs (Dz a b w q) <= 6 * (Z.of_nat (List.length a) * 1024))%Z.
Proof.
  intros a b w q. unfold Dz.
  set (F := fun i => if cond w i then zsum (fun t => Al a i t * Al b (w - i) (q - t))%Z (S q) else 0%Z).
  set (X := (Z.of_nat (List.length a) * 1024)%Z).
  assert (Hi : forall i, (Z.abs (F i) <= X)%Z).
  { intros i. unfold F, X. destruct (cond w i); [| pose proof (Zle_0_nat (List.length a)); simpl; lia].
    apply zsum_bound; [lia | | ].
    - intros t Ht. unfold Al at 1. destruct (Nat.ltb_spec t (List.length a)); [lia | reflexivity].
    - intros t. rewrite Z.abs_mul. pose proof (Al_bound a i t). pose proof (Al_bound b (w - i) (q - t)). nia. }
  assert (G : forall n, (Z.abs (zsum F n) <= Z.of_nat n * X)%Z).
  { intros n. induction n as [|n IH]; simpl zsum; [simpl; lia|]. pose proof (Hi n). rewrite Nat2Z.inj_succ, Z.mul_succ_l. lia. }
  exact (G 6%nat).
Qed.

(* ---------------------------------------------------------------------- *)
(* Error of the products                                                  *)
(* ---------------------------------------------------------------------- *)

Section ErrProducts.
Local Open Scope R_scope.

Definition Sk (A B : nat -> vec) (w k t : nat) : R :=
  rsum (fun i => if cond w i then Cmod (A i k) * Cmod (B (w - i)%nat k) else 0) t.

Lemma Sk_nonneg : forall A B w k t, 0 <= Sk A B w k t.
Proof.
  intros. apply rsum_nonneg. intros i _. destruct (cond w i); [|lra].
  apply Rmult_le_pos; apply Cmod_nonneg.
Qed.

Lemma pex_bound : forall A B w k t, Cmod (pex A B w k t) <= Sk A B w k t.
Proof.
  intros. unfold pex, Sk. eapply Rle_trans; [apply Cmod_csum|]. apply rsum_le. intros i _.
  destruct (cond w i); [rewrite Cmod_mul; lra | rewrite Cmod_C0; lra].
Qed.

Lemma pfold_err : forall A B w k t, (t <= 6)%nat ->
  Cmod (Csub (pfold A B w k t) (pex A B w k t)) <= INR t * (7 * eps * Sk A B w k t + 11 * eta_max).
Proof.
  intros A B w k t. induction t as [|t IH]; intros Ht.
  - simpl. unfold pex. rewrite csum_0. replace (Csub C0 C0) with C0 by (apply Ceq; unfold Csub, C0; simpl; ring).
    rewrite Cmod_C0. lra.
  - specialize (IH ltac:(lia)).
    assert (ET : INR (S t) = INR t + 1) by apply S_INR.
    assert (HT : 0 <= INR t <= 5) by (split; [apply pos_INR | replace 5 with (INR 5) by (simpl; lra); apply le_INR; lia]).
    pose proof (Sk_nonneg A B w k t) as HS. pose proof eta_nonneg as He. pose proof eta_tiny as He2. pose proof eps_val as Ev.
    unfold pex in *. unfold Sk in *. simpl pfold. rewrite csum_S. simpl rsum.
    fold (pex A B w k t) in *. fold (Sk A B w k t) in *.
    destruct (cond w t).
    + set (a := A t k) in *. set (b := B (w - t)%nat k) in *.
      set (p := pfold A B w k t) in *. set (pe := pex A B w k t) in *. set (S := Sk A B w k t) in *.
      set (m := cmulr a b).
      pose proof (caddr_err p m) as H1. pose proof (cmulr_err a b) as H2. fold m in H2.
      pose proof (pex_bound A B w k t) as H3. fold pe S in H3.
      set (AB := Cmod a * Cmod b) in *.
      assert (HAB : 0 <= AB) by (apply Rmult_le_pos; apply Cmod_nonneg).
      assert (Hm : Cmod m <= AB + Cmod (Csub m (Cmul a b))).
      { replace m with (Cadd (Cmul a b) (Csub m (Cmul a b))) at 1 by (apply Ceq; simpl; ring).
        eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_mul. unfold AB; lra. }
      assert (Hp : Cmod p <= S + Cmod (Csub p pe)).
      { replace p with (Cadd pe (Csub p pe)) at 1 by (apply Ceq; simpl; ring).
        eapply Rle_trans; [apply Cmod_triangle|]. lra. }
      assert (Hpm : Cmod (Cadd p m) <= Cmod p + Cmod m) by apply Cmod_triangle.
      assert (Hdec : Cmod (Csub (caddr p m) (Cadd pe (Cmul a b)))
                     <= Cmod (Csub (caddr p m) (Cadd p m)) + Cmod (Csub p pe) + Cmod (Csub m (Cmul a b))).
      { replace (Csub (caddr p m) (Cadd pe (Cmul a b)))
          with (Cadd (Cadd (Csub (caddr p m) (Cadd p m)) (Csub p pe)) (Csub m (Cmul a b))) by (apply Ceq; simpl; ring).
        eapply Rle_trans; [apply Cmod_triangle|]. pose proof (Cmod_triangle (Csub (caddr p m) (Cadd p m)) (Csub p pe)). lra. }
      rewrite ET. pose proof (Cmod_nonneg (Cadd p m)).
      assert (TS : INR t * S <= 5 * S) by nra. assert (TE : INR t * eta_max <= 5 * eta_max) by nra.
      assert (TAB : 0 <= INR t * AB) by nra.
      rewrite Ev in *. nra.
    + rewrite ET. replace (Cadd (pex A B w k t) C0) with (pex A B w k t) by (apply Ceq; unfold Cadd, C0; simpl; ring).
      assert (0 <= 7 * eps * Sk A B w k t + 11 * eta_max) by (rewrite Ev; nra).
      replace (Sk A B w k t + 0) with (Sk A B w k t) by ring. nra.
Qed.

Lemma Cmod_CI : Cmod CI = 1.
Proof. unfold Cmod, Cmod2, CI; simpl. replace (0 * 0 + 1 * 1) with 1 by ring. apply sqrt_1. Qed.

Lemma Pcell_err : forall A B g k,
  Cmod (Csub (Pcell A B g k) (Cadd (pex A B (2 * g) k 6) (Cmul CI (pex A B (2 * g + 1) k 6))))
  <= 45 * eps * (Sk A B (2 * g) k 6 + Sk A B (2 * g + 1) k 6) + 140 * eta_max.
Proof.
  intros A B g k.
  pose proof (pfold_err A B (2 * g) k 6 (le_n _)) as E0. pose proof (pfold_err A B (2 * g + 1) k 6 (le_n _)) as E1.
  set (q0 := pfold A B (2 * g) k 6) in *. set (q1 := pfold A B (2 * g + 1) k 6) in *.
  set (p0 := pex A B (2 * g) k 6) in *. set (p1 := pex A B (2 * g + 1) k 6) in *.
  set (S0 := Sk A B (2 * g) k 6) in *. set (S1 := Sk A B (2 * g + 1) k 6) in *.
  pose proof (pex_bound A B (2 * g) k 6) as B0. pose proof (pex_bound A B (2 * g + 1) k 6) as B1. fold p0 S0 in B0. fold p1 S1 in B1.
  set (v := Cadd q0 (Cmul CI q1)).
  assert (Hv : Cmod v <= Cmod q0 + Cmod q1).
  { unfold v. eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_mul.
    rewrite Cmod_CI. lra. }
  assert (Hr : Cmod (Csub (Pcell A B g k) v) <= eps * (2 * Cmod v) + 2 * eta_max).
  { assert (Fx : fst v = fst q0 - snd q1) by (unfold v, Cadd, Cmul, CI; simpl; ring).
    assert (Fy : snd v = snd q0 + fst q1) by (unfold v, Cadd, Cmul, CI; simpl; ring).
    eapply Rle_trans; [apply Cmod_le_reim|].
    unfold Pcell. fold q0 q1. unfold Csub. cbn [fst snd]. rewrite Fx, Fy.
    pose proof (rnd_e (fst q0 - snd q1)). pose proof (rnd_e (snd q0 + fst q1)).
    pose proof (Cmod_re v) as C1. pose proof (Cmod_im v) as C2. rewrite Fx in C1. rewrite Fy in C2.
    pose proof eps_val. rewrite H1 in *. lra. }
  assert (Hq0 : Cmod q0 <= S0 + Cmod (Csub q0 p0)).
  { replace q0 with (Cadd p0 (Csub q0 p0)) at 1 by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. lra. }
  assert (Hq1 : Cmod q1 <= S1 + Cmod (Csub q1 p1)).
  { replace q1 with (Cadd p1 (Csub q1 p1)) at 1 by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. lra. }
  assert (Hd : Cmod (Csub v (Cadd p0 (Cmul CI p1))) <= Cmod (Csub q0 p0) + Cmod (Csub q1 p1)).
  { replace (Csub v (Cadd p0 (Cmul CI p1))) with (Cadd (Csub q0 p0) (Cmul CI (Csub q1 p1)))
      by (unfold v; apply Ceq; unfold Csub, Cadd, Cmul, CI; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_mul.
    rewrite Cmod_CI. lra. }
  replace (Csub (Pcell A B g k) (Cadd p0 (Cmul CI p1))) with (Cadd (Csub (Pcell A B g k) v) (Csub v (Cadd p0 (Cmul CI p1))))
    by (apply Ceq; simpl; ring).
  eapply Rle_trans; [apply Cmod_triangle|].
  replace (INR 6) with 6 in E0, E1 by (simpl; ring).
  pose proof (Sk_nonneg A B (2 * g) k 6). pose proof (Sk_nonneg A B (2 * g + 1) k 6). fold S0 S1 in H, H0.
  pose proof eta_nonneg. pose proof eta_tiny. pose proof eps_val as Ev.
  rewrite Ev in *. lra.
Qed.

Lemma pex_diff : forall A B A' B' w k t,
  Cmod (Csub (pex A B w k t) (pex A' B' w k t))
  <= rsum (fun i => if cond w i then Cmod (Csub (A i k) (A' i k)) * Cmod (B (w - i)%nat k)
                                     + Cmod (A' i k) * Cmod (Csub (B (w - i)%nat k) (B' (w - i)%nat k)) else 0) t.
Proof.
  intros. unfold pex. rewrite <- csum_sub. eapply Rle_trans; [apply Cmod_csum|]. apply rsum_le. intros i _.
  destruct (cond w i).
  - replace (Csub (Cmul (A i k) (B (w - i)%nat k)) (Cmul (A' i k) (B' (w - i)%nat k)))
      with (Cadd (Cmul (Csub (A i k) (A' i k)) (B (w - i)%nat k)) (Cmul (A' i k) (Csub (B (w - i)%nat k) (B' (w - i)%nat k))))
      by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. rewrite !Cmod_mul. lra.
  - replace (Csub C0 C0) with C0 by (apply Ceq; unfold Csub, C0; simpl; ring). rewrite Cmod_C0. lra.
Qed.

(* sums over k of the per-k bounds *)
Lemma sum_Sk : forall A B w t N M, (forall i, nrm N (A i) <= M) -> (forall i, nrm N (B i) <= M) ->
  rsum (fun k => Sk A B w k t) N <= INR t * (M * M).
Proof.
  intros A B w t N M HA HB. unfold Sk. rewrite rsum_swap.
  rewrite <- (rsum_const (M * M) t). apply rsum_le. intros i _. destruct (cond w i).
  - eapply Rle_trans; [apply cs_vec|]. pose proof (nrm_nonneg N (A i)). apply Rmult_le_compat; auto. apply nrm_nonneg.
  - rewrite rsum_zero by (intros; reflexivity). pose proof (nrm_nonneg N (A 0%nat)). pose proof (HA 0%nat). nra.
Qed.

Lemma sum_diff : forall A B A' B' w t N M E, (forall i, nrm N (A' i) <= M) -> (forall i, nrm N (B i) <= M) ->
  (forall i, nrm N (vsub (A i) (A' i)) <= E) -> (forall i, nrm N (vsub (B i) (B' i)) <= E) ->
  rsum (fun k => rsum (fun i => if cond w i then Cmod (Csub (A i k) (A' i k)) * Cmod (B (w - i)%nat k)
                                     + Cmod (A' i k) * Cmod (Csub (B (w - i)%nat k) (B' (w - i)%nat k)) else 0) t) N
  <= INR t * (2 * (E * M)).
Proof.
  intros A B A' B' w t N M E HA' HB HdA HdB. rewrite rsum_swap.
  rewrite <- (rsum_const (2 * (E * M)) t). apply rsum_le. intros i _. destruct (cond w i).
  - rewrite rsum_plus.
    pose proof (cs_vec N (vsub (A i) (A' i)) (B (w - i)%nat)) as C1.
    pose proof (cs_vec N (A' i) (vsub (B (w - i)%nat) (B' (w - i)%nat))) as C2.
    unfold vsub in C1, C2.
    pose proof (nrm_nonneg N (vsub (A i) (A' i))). pose proof (nrm_nonneg N (B (w - i)%nat)).
    pose proof (nrm_nonneg N (A' i)). pose proof (nrm_nonneg N (vsub (B (w - i)%nat) (B' (w - i)%nat))).
    pose proof (HA' i). pose proof (HB (w - i)%nat). pose proof (HdA i). pose proof (HdB (w - i)%nat).
    unfold vsub in *.
    assert (P1 : nrm N (fun i0 => Csub (A i i0) (A' i i0)) * nrm N (B (w - i)%nat) <= E * M) by (apply Rmult_le_compat; lra).
    assert (P2 : nrm N (A' i) * nrm N (fun i0 => Csub (B (w - i)%nat i0) (B' (w - i)%nat i0)) <= M * E) by (apply Rmult_le_compat; lra).
    lra.
  - rewrite rsum_zero by (intros; reflexivity).
    pose proof (nrm_nonneg N (A' 0%nat)). pose proof (HA' 0%nat). pose proof (nrm_nonneg N (vsub (A 0%nat) (A' 0%nat))).
    pose proof (HdA 0%nat). nra.
Qed.

End ErrProducts.

(* ---------------------------------------------------------------------- *)
(* The final error bound                                                  *)
(* ---------------------------------------------------------------------- *)

Section FinalErr.
Local Open Scope R_scope.

Variables (a b : list Z) (lg g : nat).
Hypothesis Hlg : (2 <= lg <= 18)%nat.
Hypothesis Hab : (List.length a + List.length b <= S (2 ^ lg))%nat.
Hypothesis Hla : (Z.of_nat (List.length a) <= 131072)%Z.

Local Notation N := (2 ^ lg)%nat.
Local Notation RN := (INR (2 ^ lg)%nat).
Local Notation s := (sq2 ^ lg).
Local Notation Gc := (3757.3 * eps).
Definition DM : R := 6 * (131072 * 1024).

Local Notation Ah := (Ahat a lg).
Local Notation Bh := (Ahat b lg).
Local Notation Ae := (Aex a lg).
Local Notation Be := (Aex b lg).
Local Notation Ph := (Pcell (Ahat a lg) (Ahat b lg) g).
Local Notation PE := (Pex a b lg g).

Lemma s_facts : 1 <= s <= 512 /\ RN = s * s /\ s <= RN.
Proof.
  pose proof (sq2_pow_le lg ltac:(lia)) as H. pose proof (sq2_pow_lg lg) as E.
  split; [exact H|]. split; [lra | nra].
Qed.

Lemma B_Ae : forall (c : list Z) i, nrm N (Aex c lg i) <= 32 * RN.
Proof.
  intros c i. unfold Aex. rewrite fft_ex_nrm by lia. destruct s_facts as [S1 [S2 S3]].
  pose proof (Alimb_nrm c i lg ltac:(lia)). rewrite S2. nra.
Qed.

Lemma B_dA : forall (c : list Z) i, nrm N (vsub (Ahat c lg i) (Aex c lg i)) <= 33 * RN * Gc.
Proof.
  intros c i. unfold Ahat, Aex. pose proof (cfft_err_c false lg (Alimb c i) Hlg) as H.
  unfold sgn in H. eapply Rle_trans; [exact H|].
  destruct s_facts as [S1 [S2 S3]]. pose proof (Alimb_nrm c i lg ltac:(lia)).
  assert (0 <= Gc) by (rewrite eps_val; lra).
  apply Rmult_le_compat_r; [exact H1|]. rewrite S2. nra.
Qed.

Lemma B_Ah : forall (c : list Z) i, nrm N (Ahat c lg i) <= 33 * RN.
Proof.
  intros c i. pose proof (B_Ae c i). pose proof (B_dA c i).
  assert (E : nrm N (Ahat c lg i) <= nrm N (Aex c lg i) + nrm N (vsub (Ahat c lg i) (Aex c lg i))).
  { rewrite (nrm_ext _ (Ahat c lg i) (vadd (Aex c lg i) (vsub (Ahat c lg i) (Aex c lg i))))
      by (intros j _; unfold vadd, vsub; apply Ceq; simpl; ring). apply nrm_add. }
  destruct s_facts as [S1 [S2 S3]]. assert (33 * (RN * Gc) <= RN) by (rewrite eps_val; nra). lra.
Qed.

Definition l1 : R := rsum (fun k => Cmod (Csub (Ph k) (PE k))) N.

Lemma B_l1 : l1 <= RN * RN * (540 * 1089 * eps + 24 * 1089 * Gc) + 140 * eta_max * RN.
Proof.
  unfold l1.
  set (Pc := fun k => Cadd (pex Ah Bh (2 * g) k 6) (Cmul CI (pex Ah Bh (2 * g + 1) k 6))).
  assert (Hk : forall k, Cmod (Csub (Ph k) (PE k)) <=
      (45 * eps * (Sk Ah Bh (2 * g) k 6 + Sk Ah Bh (2 * g + 1) k 6) + 140 * eta_max)
      + (Cmod (Csub (pex Ah Bh (2 * g) k 6) (pex Ae Be (2 * g) k 6))
         + Cmod (Csub (pex Ah Bh (2 * g + 1) k 6) (pex Ae Be (2 * g + 1) k 6)))).
  { intros k. replace (Csub (Ph k) (PE k)) with (Cadd (Csub (Ph k) (Pc k)) (Csub (Pc k) (PE k))) by (apply Ceq; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. apply Rplus_le_compat; [apply Pcell_err|].
    unfold Pc, Pex.
    replace (Csub (Cadd (pex Ah Bh (2 * g) k 6) (Cmul CI (pex Ah Bh (2 * g + 1) k 6)))
                  (Cadd (pex Ae Be (2 * g) k 6) (Cmul CI (pex Ae Be (2 * g + 1) k 6))))
      with (Cadd (Csub (pex Ah Bh (2 * g) k 6) (pex Ae Be (2 * g) k 6))
                 (Cmul CI (Csub (pex Ah Bh (2 * g + 1) k 6) (pex Ae Be (2 * g + 1) k 6)))) by (apply Ceq; unfold Cmul, CI; simpl; ring).
    eapply Rle_trans; [apply Cmod_triangle|]. rewrite Cmod_mul, Cmod_CI. lra. }
  eapply Rle_trans; [apply rsum_le; intros k _; apply Hk|].
  rewrite !rsum_plus, rsum_scal, rsum_plus, rsum_const.
  assert (MA : forall i, nrm N (Ah i) <= 33 * RN) by (intros; apply B_Ah).
  assert (MB : forall i, nrm N (Bh i) <= 33 * RN) by (intros; apply B_Ah).
  assert (MAe : forall i, nrm N (Ae i) <= 33 * RN) by (intros; pose proof (B_Ae a i); pose proof (pos_INR N); lra).
  assert (EA : forall i, nrm N (vsub (Ah i) (Ae i)) <= 33 * RN * Gc) by (intros; apply B_dA).
  assert (EB : forall i, nrm N (vsub (Bh i) (Be i)) <= 33 * RN * Gc) by (intros; apply B_dA).
  pose proof (sum_Sk Ah Bh (2 * g) 6 N (33 * RN) MA MB) as T1.
  pose proof (sum_Sk Ah Bh (2 * g + 1) 6 N (33 * RN) MA MB) as T2.
  assert (T3 : rsum (fun k => Cmod (Csub (pex Ah Bh (2 * g) k 6) (pex Ae Be (2 * g) k 6))) N <= INR 6 * (2 * (33 * RN * Gc * (33 * RN)))).
  { eapply Rle_trans; [apply rsum_le; intros k _; apply pex_diff|]. apply sum_diff; assumption. }
  assert (T4 : rsum (fun k => Cmod (Csub (pex Ah Bh (2 * g + 1) k 6) (pex Ae Be (2 * g + 1) k 6))) N <= INR 6 * (2 * (33 * RN * Gc * (33 * RN)))).
  { eapply Rle_trans; [apply rsum_le; intros k _; apply pex_diff|]. apply sum_diff; assumption. }
  replace (INR 6) with 6 in T1, T2, T3, T4 by (simpl; ring).
  pose proof eps_val as Ev. rewrite Ev in *. lra.
Qed.

Lemma B_l1_num : l1 <= RN * 0.0029 /\ l1 <= 800.
Proof.
  pose proof B_l1. destruct s_facts as [S1 [S2 S3]].
  assert (HRN : RN <= 262144).
  { rewrite pow_INR. simpl INR. replace 262144 with (2 ^ 18) by (simpl; lra).
    apply Rle_pow; [lra | lia]. }
  assert (HRN0 : 1 <= RN) by nra.
  pose proof eps_val. pose proof eta_nonneg. pose proof eta_tiny.
  set (K := 540 * 1089 * eps + 24 * 1089 * (3757.3 * eps)) in H.
  assert (HK : 0 <= K <= 1.1e-8) by (unfold K; rewrite H0; lra).
  assert (RN * RN * K <= RN * (262144 * K)) by (assert (RN * K <= 262144 * K) by nra; nra).
  assert (140 * eta_max * RN <= RN * (140 * eta_max)) by lra.
  assert (A : l1 <= RN * (262144 * K + 140 * eta_max)) by lra.
  assert (262144 * K + 140 * eta_max <= 0.0029) by (rewrite H0 in *; lra).
  split; [nra|]. nra.
Qed.

Lemma B_d : nrm N (dvec a b g) <= sq2 * DM * s.
Proof.
  destruct s_facts as [S1 [S2 S3]].
  eapply Rle_trans; [apply (nrm_const_bound _ _ (sq2 * DM)); [pose proof sq2_bounds; unfold DM; lra |]|].
  - intros q _. destruct (dvec_parts a b g q) as [F1 F2].
    pose proof (Dz_bound a b (2 * g) q) as D1. pose proof (Dz_bound a b (2 * g + 1) q) as D2.
    assert (Hl := Hla).
    apply Cmod_le_of_sq; [pose proof sq2_bounds; unfold DM; lra|].
    unfold Cmod2. rewrite F1, F2.
    assert (A1 : Rabs (IZR (Dz a b (2 * g) q)) <= DM).
    { rewrite <- abs_IZR. unfold DM. replace (6 * (131072 * 1024)) with (IZR (6 * (131072 * 1024))) by (simpl; lra).
      apply IZR_le. lia. }
    assert (A2 : Rabs (IZR (Dz a b (2 * g + 1) q)) <= DM).
    { rewrite <- abs_IZR. unfold DM. replace (6 * (131072 * 1024)) with (IZR (6 * (131072 * 1024))) by (simpl; lra).
      apply IZR_le. lia. }
    rewrite <- (Rabs_sq (IZR (Dz a b (2 * g) q))), <- (Rabs_sq (IZR (Dz a b (2 * g + 1) q))).
    pose proof (Rabs_pos (IZR (Dz a b (2 * g) q))). pose proof (Rabs_pos (IZR (Dz a b (2 * g + 1) q))).
    pose proof sq2_sq.
    replace (sq2 * DM * (sq2 * DM)) with (2 * (DM * DM)) by (rewrite <- sq2_sq; ring). nra.
  - right. f_equal. rewrite S2. apply sqrt_square. lra.
Qed.

Lemma B_PE : nrm N PE <= sq2 * DM * RN.
Proof.
  destruct s_facts as [S1 [S2 S3]].
  assert (E : nrm N (fft_ex (-1) lg lg PE) = RN * nrm N (dvec a b g)).
  { rewrite (nrm_ext _ _ (fun q => Cscal RN (dvec a b g q))) by (intros q Hq; apply Pex_inv; assumption).
    apply nrm_scal_sq; [lra|]. unfold nsq. rewrite <- rsum_scal. apply rsum_ext. intros q _.
    unfold Cmod2, Cscal; simpl. ring. }
  rewrite fft_ex_nrm in E by lia. rewrite S2 in E.
  assert (nrm N PE = s * nrm N (dvec a b g)) by (apply Rmult_eq_reg_l with s; [nra | lra]).
  rewrite H. pose proof B_d. rewrite S2. assert (0 <= sq2 * DM) by (pose proof sq2_bounds; unfold DM; lra). nra.
Qed.

Lemma B_Ph : nrm N Ph <= sq2 * DM * RN + l1.
Proof.
  pose proof B_PE.
  assert (E : nrm N Ph <= nrm N PE + nrm N (vsub Ph PE)).
  { rewrite (nrm_ext _ Ph (vadd PE (vsub Ph PE))) by (intros j _; unfold vadd, vsub; apply Ceq; simpl; ring). apply nrm_add. }
  pose proof (nrm_le_l1 N (vsub Ph PE)). unfold l1. unfold vsub in *. lra.
Qed.

Lemma B_Ph100 : nrm N Ph <= bp 100.
Proof.
  pose proof B_Ph. destruct B_l1_num as [_ L]. pose proof sq2_bounds.
  assert (HRN : RN <= 262144).
  { rewrite pow_INR. simpl INR. replace 262144 with (2 ^ 18) by (simpl; lra). apply Rle_pow; [lra | lia]. }
  assert (sq2 * DM * RN <= 1.4143 * DM * 262144) by (unfold DM; pose proof (pos_INR N); nra).
  unfold bp. assert (Hb : Raux.bpow Zaux.radix2 70 <= Raux.bpow Zaux.radix2 100) by (apply Raux.bpow_le; lia).
  change (Raux.bpow Zaux.radix2 70) with 1180591620717411303424 in Hb. unfold DM in *. lra.
Qed.

(* the output of the inverse transform, before scaling *)
Lemma final_cmod : forall q, (q < N)%nat ->
  Cmod (Csub (cfft lg (twc true) lg Ph q) (Cscal RN (dvec a b g q))) <= RN * 0.2465.
Proof.
  intros q Hq. destruct s_facts as [S1 [S2 S3]].
  set (Yh := cfft lg (twc true) lg Ph). set (ITP := fft_ex (-1) lg lg Ph).
  assert (E1 : Cmod (Csub (Yh q) (ITP q)) <= s * (nrm N Ph + 1) * Gc).
  { eapply Rle_trans; [apply (nrm_elem N (vsub Yh ITP) q Hq)|]. apply cfft_err_c. exact Hlg. }
  assert (E2 : Cmod (Csub (ITP q) (Cscal RN (dvec a b g q))) <= l1).
  { rewrite <- (Pex_inv a b lg g q Hab Hq). unfold ITP. rewrite <- fft_ex_sub.
    rewrite fft_ex_dft by (auto; lia). eapply Rle_trans; [apply Cmod_csum|].
    apply rsum_le. intros k _. rewrite Cmod_mul, Cmod_EN by apply pow2_pos. unfold vsub. lra. }
  replace (Csub (Yh q) (Cscal RN (dvec a b g q))) with (Cadd (Csub (Yh q) (ITP q)) (Csub (ITP q) (Cscal RN (dvec a b g q))))
    by (apply Ceq; simpl; ring).
  eapply Rle_trans; [apply Cmod_triangle|].
  pose proof B_Ph. destruct B_l1_num as [L1 L2].
  assert (HG : 0 <= Gc <= 4.172e-13) by (rewrite eps_val; lra).
  assert (Hm : s * (nrm N Ph + 1) * Gc <= s * (sq2 * DM * RN + 801) * Gc).
  { apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_l; lra. }
  assert (Hm2 : s * (sq2 * DM * RN + 801) * Gc = RN * (sq2 * DM * s * Gc) + s * 801 * Gc) by (rewrite S2; ring).
  assert (Hm3 : sq2 * DM * s * Gc <= 1.4143 * DM * 512 * 4.172e-13).
  { pose proof sq2_bounds. unfold DM. apply Rmult_le_compat; try nra. }
  assert (Hm5 : RN * (sq2 * DM * s * Gc) <= RN * (1.4143 * DM * 512 * 4.172e-13)) by (apply Rmult_le_compat_l; nra).
  assert (Hm4 : s * 801 * Gc <= RN * 0.000001) by nra.
  unfold DM in *. lra.
Qed.

End FinalErr.

(* ---------------------------------------------------------------------- *)
(* The integer identity: limbs and convolutions reassemble the product    *)
(* ---------------------------------------------------------------------- *)

Section IntId.
Open Scope Z_scope.

Lemma zsum_plus : forall f g n, zsum (fun i => f i + g i) n = zsum f n + zsum g n.
Proof. intros f g n; induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH. ring. Qed.

Lemma zsum_scal : forall c f n, zsum (fun i => c * f i) n = c * zsum f n.
Proof. intros c f n; induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma zsum_swap : forall (f : nat -> nat -> Z) n m,
  zsum (fun i => zsum (fun j => f i j) m) n = zsum (fun j => zsum (fun i => f i j) n) m.
Proof.
  intros f n; induction n as [|n IH]; intros m; simpl.
  - induction m as [|m IHm]; simpl; [reflexivity|]. rewrite <- IHm. ring.
  - rewrite IH, <- zsum_plus. reflexivity.
Qed.

Lemma zsum_mul : forall f g n m, zsum f n * zsum g m = zsum (fun i => zsum (fun j => f i * g j) m) n.
Proof.
  intros f g n m. induction n as [|n IH]; simpl; [ring|].
  rewrite Z.mul_add_distr_r, IH, <- zsum_scal. reflexivity.
Qed.

Lemma limb_identity : forall c, -2 ^ 31 <= c < 2 ^ 31 -> c = zsum (fun i => limbZ c i * 64 ^ Z.of_nat i) 6.
Proof.
  intros c Hc. unfold limbZ, KZ. simpl zsum. simpl Z.of_nat.
  change (64 ^ 0) with 1. change (64 ^ 1) with 64. change (64 ^ 2) with 4096. change (64 ^ 3) with 262144.
  change (64 ^ 4) with 16777216. change (64 ^ 5) with 1073741824.
  Z.to_euclidean_division_equations. lia.
Qed.

Lemma sum_below_zsum : forall f n, sum_below f n = zsum (fun t => f (N.of_nat t)) n.
Proof. intros f n; induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma coeff_limbs : forall a t, Forall (fun c => -2 ^ 31 <= c < 2 ^ 31) a ->
  coeff a (N.of_nat t) = zsum (fun i => Al a i t * 64 ^ Z.of_nat i) 6.
Proof.
  intros a t Ha. unfold coeff, Al. rewrite Nat2N.id. destruct (Nat.ltb_spec t (List.length a)) as [Ht|Ht].
  - apply limb_identity. rewrite Forall_forall in Ha. apply Ha. apply nth_In. exact Ht.
  - rewrite nth_overflow by exact Ht. simpl. reflexivity.
Qed.

Lemma regroup : forall (F : nat -> nat -> Z),
  zsum (fun w => 64 ^ Z.of_nat w * zsum (fun i => if cond w i then F i (w - i)%nat else 0) 6) 12
  = zsum (fun i => zsum (fun j => 64 ^ Z.of_nat (i + j) * F i j) 6) 6.
Proof. intros F. unfold cond. cbn [zsum andb Nat.leb Nat.ltb Nat.sub Nat.add]. ring. Qed.

Lemma prod_coeff_split : forall a b q,
  Forall (fun c => -2 ^ 31 <= c < 2 ^ 31) a -> Forall (fun c => -2 ^ 31 <= c < 2 ^ 31) b ->
  prod_coeff a b (N.of_nat q) = zsum (fun w => 64 ^ Z.of_nat w * Dz a b w q) 12.
Proof.
  intros a b q Ha Hb. unfold prod_coeff. replace (N.to_nat (N.of_nat q + 1)) with (S q) by lia.
  rewrite sum_below_zsum.
  rewrite (zsum_ext _ (fun t => zsum (fun i => zsum (fun j => 64 ^ Z.of_nat (i + j) * (Al a i t * Al b j (q - t))) 6) 6)).
  2:{ intros t Ht. cbv beta. replace (N.of_nat q - N.of_nat t)%N with (N.of_nat (q - t)) by lia.
      rewrite (coeff_limbs a t Ha), (coeff_limbs b (q - t) Hb), zsum_mul. apply zsum_ext. intros i _.
      apply zsum_ext. intros j _. rewrite Nat2Z.inj_add, Z.pow_add_r by lia. ring. }
  rewrite zsum_swap.
  rewrite (zsum_ext _ (fun i => zsum (fun j => 64 ^ Z.of_nat (i + j) * zsum (fun t => Al a i t * Al b j (q - t)) (S q)) 6) 6).
  2:{ intros i _. rewrite zsum_swap. apply zsum_ext. intros j _. rewrite zsum_scal. reflexivity. }
  rewrite <- (regroup (fun i j => zsum (fun t => Al a i t * Al b j (q - t)) (S q))).
  unfold Dz. reflexivity.
Qed.

End IntId.

(* ---------------------------------------------------------------------- *)
(* Scaling, rounding to the nearest integer, reassembly                   *)
(* ---------------------------------------------------------------------- *)

Section Readout.
Local Open Scope R_scope.

Lemma readout_err : forall RN y (D : Z), 4 <= RN <= 262144 ->
  Rabs (y - RN * IZR D) <= RN * 0.2465 -> (Z.abs D <= 805306368)%Z ->
  Rabs (rnd (y * rnd (1 / RN)) - IZR D) < / 2.
Proof.
  intros RN y D HRN Hy HD.
  pose proof eps_val as Ev. pose proof eta_nonneg as He. pose proof eta_tiny as He2.
  assert (HDr : Rabs (IZR D) <= 805306368).
  { rewrite <- abs_IZR. replace 805306368 with (IZR 805306368) by reflexivity. apply IZR_le. exact HD. }
  set (iv := rnd (1 / RN)).
  pose proof (rnd_e (1 / RN)) as Hiv. fold iv in Hiv.
  rewrite (Rabs_pos_eq (1 / RN)) in Hiv by (unfold Rdiv; rewrite Rmult_1_l; apply Rlt_le, Rinv_0_lt_compat; lra).
  set (e := RN * iv - 1).
  assert (Hev : Rabs e <= eps + RN * eta_max).
  { unfold e. replace (RN * iv - 1) with (RN * (iv - 1 / RN)) by (field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq RN) by lra.
    apply Rle_trans with (RN * (eps * (1 / RN) + eta_max)); [apply Rmult_le_compat_l; lra|].
    right. field. lra. }
  set (u := y / RN).
  assert (Hyu : y = RN * u) by (unfold u; field; lra).
  assert (Hu : Rabs (u - IZR D) <= 0.2465).
  { rewrite Hyu in Hy. replace (RN * u - RN * IZR D) with (RN * (u - IZR D)) in Hy by ring.
    rewrite Rabs_mult, (Rabs_pos_eq RN) in Hy by lra. apply Rmult_le_reg_l with RN; lra. }
  assert (Hyi : y * iv = u * (1 + e)) by (rewrite Hyu; unfold e; ring).
  rewrite Hyi.
  assert (Hua : Rabs u <= 805306368.25).
  { replace u with ((u - IZR D) + IZR D) by ring. eapply Rle_trans; [apply Rabs_triang|]. lra. }
  assert (Hue : Rabs (u * e) <= 805306368.25 * (eps + 262144 * eta_max)).
  { rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hua |]. nra. }
  pose proof (rnd_e (u * (1 + e))) as Hr.
  assert (Hu1 : Rabs (u * (1 + e)) <= 805306368.25 + 805306368.25 * (eps + 262144 * eta_max)).
  { replace (u * (1 + e)) with (u + u * e) by ring. eapply Rle_trans; [apply Rabs_triang|]. lra. }
  replace (rnd (u * (1 + e)) - IZR D) with ((rnd (u * (1 + e)) - u * (1 + e)) + (u * e) + (u - IZR D)) by ring.
  eapply Rle_lt_trans; [apply abs_tri3|].
  rewrite Ev in *. nra.
Qed.

Definition acc (a b : list Z) (g q : nat) : Z :=
  zsum (fun g' => Dz a b (2 * g') q * 64 ^ Z.of_nat (2 * g') + Dz a b (2 * g' + 1) q * 64 ^ Z.of_nat (2 * g' + 1))%Z g.

Lemma acc_6 : forall a b q, acc a b 6 q = zsum (fun w => 64 ^ Z.of_nat w * Dz a b w q)%Z 12.
Proof. intros. unfold acc. cbn [zsum Nat.mul Nat.add]. ring. Qed.

Lemma pow64 : forall g : nat, (2 ^ (12 * Z.of_nat g) = 64 ^ Z.of_nat (2 * g))%Z.
Proof.
  intros g. change (64)%Z with (2 ^ 6)%Z. rewrite <- Z.pow_mul_r by lia. f_equal. lia.
Qed.

Lemma pow64' : forall g : nat, (2 ^ (12 * Z.of_nat g + 6) = 64 ^ Z.of_nat (2 * g + 1))%Z.
Proof.
  intros g. change (64)%Z with (2 ^ 6)%Z. rewrite <- Z.pow_mul_r by lia. f_equal. lia.
Qed.

Lemma acc_arith : forall (A D0 D1 x0 x1 r k0 k1 : Z),
  r = (A mod wB)%Z -> x0 = (D0 mod wB)%Z -> x1 = (D1 mod wB)%Z ->
  (((r + (x0 * k0) mod wB) mod wB + (x1 * k1) mod wB) mod wB = (A + D0 * k0 + D1 * k1) mod wB)%Z.
Proof.
  intros. subst.
  assert (madd : forall x y x' y', (x mod wB = x' mod wB -> y mod wB = y' mod wB -> (x + y) mod wB = (x' + y') mod wB)%Z).
  { intros x y x' y' Hx Hy. rewrite Zplus_mod, Hx, Hy, <- Zplus_mod. reflexivity. }
  apply madd.
  - rewrite Z.mod_mod by discriminate. apply madd.
    + apply Z.mod_mod. discriminate.
    + rewrite Z.mod_mod by discriminate. apply Zmult_mod_idemp_l.
  - rewrite Z.mod_mod by discriminate. apply Zmult_mod_idemp_l.
Qed.

End Readout.

Section Accum.
Local Open Scope R_scope.

Lemma accum_spec : forall (a b : list Z) (g : nat) (L : int) (invN : float) (yr yi : array float)
    (R : array int) (lg : nat) (Y : vec),
  (g < 6)%nat -> (2 <= lg <= 18)%nat -> (to_Z L <= Z.of_nat (2 ^ lg))%Z ->
  repr invN (rnd (1 / INR (2 ^ lg))) ->
  crep yr yi (2 ^ lg) Y -> cbnd (2 ^ lg) Y Bg ->
  (forall q, (q < Z.to_nat (to_Z L))%nat ->
     Rabs (fst (Y q) - INR (2 ^ lg) * IZR (Dz a b (2 * g) q)) <= INR (2 ^ lg) * 0.2465 /\
     Rabs (snd (Y q) - INR (2 ^ lg) * IZR (Dz a b (2 * g + 1) q)) <= INR (2 ^ lg) * 0.2465) ->
  (forall w q, (Z.abs (Dz a b w q) <= 805306368)%Z) ->
  PArray.length R = L ->
  (forall q, (q < Z.to_nat (to_Z L))%nat -> to_Z R.[of_nat q] = (acc a b g q mod wB)%Z) ->
  PArray.length (accum (of_nat g) L invN yr yi R) = L /\
  forall q, (q < Z.to_nat (to_Z L))%nat -> to_Z (accum (of_nat g) L invN yr yi R).[of_nat q] = (acc a b (S g) q mod wB)%Z.
Proof.
  intros a b g L invN yr yi R lg Y Hg Hlg HL Hiv HY BY HE HD LR HR.
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z).
  { rewrite Nat2Z.inj_pow. change 262144%Z with (Z.of_nat 2 ^ 18)%Z. apply Z.pow_le_mono_r; lia. }
  assert (Hp4 : (4 <= Z.of_nat (2 ^ lg))%Z).
  { rewrite Nat2Z.inj_pow. change 4%Z with (Z.of_nat 2 ^ 2)%Z. apply Z.pow_le_mono_r; lia. }
  assert (HRN : 4 <= INR (2 ^ lg) <= 262144).
  { rewrite INR_IZR_INZ. split; [replace 4 with (IZR 4) by reflexivity | replace 262144 with (IZR 262144) by reflexivity];
      apply IZR_le; lia. }
  assert (OK : forall q, (q < 2 ^ lg)%nat -> to_Z (of_nat q) = Z.of_nat q).
  { intros q Hq. apply of_nat_to_Z. change wB with (2^63)%Z. lia. }
  assert (Hgz : to_Z (of_nat g) = Z.of_nat g) by (apply of_nat_to_Z; change wB with (2^63)%Z; lia).
  assert (Hk0 : to_Z (12 * of_nat g) = (12 * Z.of_nat g)%Z).
  { rewrite Uint63.mul_spec, Hgz. change (to_Z 12) with 12%Z. apply Z.mod_small. change wB with (2^63)%Z. lia. }
  assert (Hk1 : to_Z (12 * of_nat g + 6) = (12 * Z.of_nat g + 6)%Z).
  { rewrite Uint63.add_spec, Hk0. change (to_Z 6) with 6%Z. apply Z.mod_small. change wB with (2^63)%Z. lia. }
  assert (Hivb : Rabs (rnd (1 / INR (2 ^ lg))) <= 2).
  { assert (Rabs (1 / INR (2 ^ lg)) <= 1).
    { rewrite Rabs_pos_eq by (unfold Rdiv; rewrite Rmult_1_l; apply Rlt_le, Rinv_0_lt_compat; lra).
      unfold Rdiv. rewrite Rmult_1_l. rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
    pose proof (rnd_bnd _ _ H). pose proof (rnd_e (1 / INR (2 ^ lg))). pose proof eps_val. pose proof eta_tiny. pose proof eta_nonneg.
    apply Rabs_le. apply abs_inv in H1. rewrite Rabs_pos_eq in H1 by (unfold Rdiv; rewrite Rmult_1_l; apply Rlt_le, Rinv_0_lt_compat; lra).
    assert (1 / INR (2 ^ lg) <= 1 / 4) by (unfold Rdiv; rewrite !Rmult_1_l; apply Rinv_le_contravar; lra).
    assert (0 <= 1 / INR (2 ^ lg)) by (unfold Rdiv; rewrite Rmult_1_l; apply Rlt_le, Rinv_0_lt_compat; lra).
    rewrite H2 in *. lra. }
  assert (HB2 : Bg * 2 <= bp 900) by (destruct Bg_facts as [G1 [G2 G3]]; lra).
  set (P := fun (j : int) (R' : array int) => PArray.length R' = L /\
    forall q, (q < Z.to_nat (to_Z L))%nat ->
      to_Z R'.[of_nat q] = ((if (q <? Z.to_nat (to_Z j))%nat then acc a b (S g) q else acc a b g q) mod wB)%Z).
  assert (HLp : P L (accum (of_nat g) L invN yr yi R)).
  { unfold accum. apply for_inv.
    - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded L). lia.
    - split; [exact LR|]. intros q Hq. change (Z.to_nat (to_Z 0)) with 0%nat. simpl. apply HR. exact Hq.
    - intros j R0 Hj [L0 T]. change (to_Z 0) with 0%Z in Hj.
      set (jn := Z.to_nat (to_Z j)).
      assert (Hjo : j = of_nat jn) by (apply of_nat_eq; unfold jn; lia).
      assert (Hjl : (jn < 2 ^ lg)%nat) by (unfold jn; lia).
      destruct (HY jn Hjl) as [Ry1 Ry2]. destruct (BY jn Hjl) as [By1 By2].
      destruct (rmul_ok _ _ _ _ Bg 2 Ry1 Hiv By1 Hivb HB2) as [Rz0 _].
      destruct (rmul_ok _ _ _ _ Bg 2 Ry2 Hiv By2 Hivb HB2) as [Rz1 _].
      destruct (HE jn ltac:(unfold jn; lia)) as [E0 E1].
      pose proof (toint_spec _ _ (Dz a b (2 * g) jn) Rz0 ltac:(pose proof (HD (2 * g)%nat jn); lia)
                    (readout_err _ _ _ HRN E0 (HD _ _))) as D0.
      pose proof (toint_spec _ _ (Dz a b (2 * g + 1) jn) Rz1 ltac:(pose proof (HD (2 * g + 1)%nat jn); lia)
                    (readout_err _ _ _ HRN E1 (HD _ _))) as D1.
      rewrite <- Hjo in D0, D1.
      split; [rewrite ilength_set; exact L0|].
      rewrite to_nat_succ by lia. fold jn. intros q Hq.
      destruct (Nat.eq_dec q jn) as [->|Ne].
      + rewrite <- Hjo. rewrite iget_set_same by (rewrite L0; apply ltb_true; lia).
        destruct (Nat.ltb_spec jn (S jn)) as [_|]; [|lia].
        rewrite !Uint63.add_spec, !lsl_spec, Hk0, Hk1.
        pose proof (T jn Hq) as Tj. rewrite <- Hjo in Tj.
        replace (jn <? Z.to_nat (to_Z j))%nat with false in Tj by (symmetry; apply Nat.ltb_ge; unfold jn; lia).
        assert (X0 : to_Z (toint (yr.[j] * invN)%float) = (Dz a b (2 * g) jn mod wB)%Z)
          by (rewrite <- Sint63.to_Z_mod_Uint63to_Z, D0; reflexivity).
        assert (X1 : to_Z (toint (yi.[j] * invN)%float) = (Dz a b (2 * g + 1) jn mod wB)%Z)
          by (rewrite <- Sint63.to_Z_mod_Uint63to_Z, D1; reflexivity).
        rewrite (acc_arith (acc a b g jn) (Dz a b (2 * g) jn) (Dz a b (2 * g + 1) jn) _ _ _ _ _ Tj X0 X1).
        rewrite pow64, pow64'. unfold acc. cbn [zsum]. f_equal. ring.
      + assert (Dq : j <> of_nat q) by (rewrite Hjo; apply int_neq; rewrite !OK by lia; lia).
        rewrite iget_set_other by exact Dq. rewrite (T q Hq).
        destruct (Nat.ltb_spec q (Z.to_nat (to_Z j))), (Nat.ltb_spec q (S jn)); try reflexivity; unfold jn in *; lia. }
  destruct HLp as [L1 T]. split; [exact L1|].
  intros q Hq. rewrite (T q Hq). destruct (Nat.ltb_spec q (Z.to_nat (to_Z L))); [reflexivity | lia].
Qed.

End Accum.

(* ---------------------------------------------------------------------- *)
(* The contract                                                           *)
(* ---------------------------------------------------------------------- *)

(* The output list and its representation (as in template/polymul1):
   the list of the prod_coeff, which Part 0 identifies with the product. *)
Definition out_list (a b : list Z) : list Z :=
  map (fun n => prod_coeff a b (N.of_nat n)) (seq 0 (List.length a + List.length b - 1)).

Lemma out_list_nth_error : forall a b n, (n < List.length a + List.length b - 1)%nat ->
  nth_error (out_list a b) n = Some (prod_coeff a b (N.of_nat n)).
Proof.
  intros a b n Hn. unfold out_list. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec n (List.length a + List.length b - 1)); [reflexivity | lia].
Qed.

Lemma out_list_conv : forall a b, a <> [] -> b <> [] -> out_list a b = pzconv a b.
Proof.
  intros a b Ha Hb.
  assert (HL : List.length (out_list a b) = (List.length a + List.length b - 1)%nat)
    by (unfold out_list; rewrite length_map, length_seq; reflexivity).
  apply (nth_ext _ _ 0%Z 0%Z).
  - rewrite HL, length_pzconv by assumption. reflexivity.
  - intros n Hn. rewrite HL in Hn. rewrite nth_pzconv.
    apply nth_error_nth. apply out_list_nth_error. exact Hn.
Qed.

Lemma out_list_product : forall a b, a <> [] -> b <> [] -> polymul_spec a b (out_list a b).
Proof.
  intros a b Ha Hb. rewrite out_list_conv by assumption. apply pzconv_is_product; assumption.
Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma out_correct : forall (a b : list Z) (r : array@{Set} sint) (L : int),
  valid_input a b ->
  PArray.length@{Set} r = L ->
  to_Z L = (Z.of_nat (List.length a) + Z.of_nat (List.length b) - 1)%Z ->
  (forall k' : int, (to_Z k' < to_Z L)%Z ->
     to_Z (PArray.get@{Set} r k') = (prod_coeff a b (Z.to_N (to_Z k')) mod wB)%Z) ->
  repr r (out_list a b) /\ polymul_spec a b (out_list a b).
Proof.
  intros a b r L Hv Hrl0 HL Hrc0.
  assert (Hrl : PArray.length@{repr_array.u0} r = L) by exact Hrl0.
  assert (Hrc : forall k' : int, (to_Z k' < to_Z L)%Z ->
     to_Z (PArray.get@{repr_array.u0} r k') = (prod_coeff a b (Z.to_N (to_Z k')) mod wB)%Z)
    by exact Hrc0.
  clear Hrl0 Hrc0.
  destruct Hv as [Hva Hvb _ _ Hvp].
  unfold len in Hva, Hvb.
  assert (Ha : a <> []) by (destruct a; [simpl in Hva; lia | discriminate]).
  assert (Hb : b <> []) by (destruct b; [simpl in Hvb; lia | discriminate]).
  assert (Hprod := out_list_product a b Ha Hb).
  assert (Hbnd := Hvp _ Hprod).
  set (na := List.length a) in *. set (nb := List.length b) in *.
  assert (Hlen_p : List.length (out_list a b) = (na + nb - 1)%nat).
  { unfold out_list. rewrite length_map, length_seq. reflexivity. }
  assert (Hnth : forall n, (n < na + nb - 1)%nat ->
            nth_error (out_list a b) n = Some (prod_coeff a b (N.of_nat n))).
  { intros n Hn. apply out_list_nth_error. exact Hn. }
  split.
  - split.
    + rewrite Hlen_p, Hrl, HL. lia.
    + intros n Hn. rewrite Hlen_p in Hn.
      exists (prod_coeff a b (N.of_nat n)). split; [apply Hnth; exact Hn|].
      unfold repr, repr_sint.
      assert (Hn' : to_Z (of_Z (Z.of_nat n)) = Z.of_nat n).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
      rewrite Sint63.to_Z_cmodwB, Hrc by (rewrite Hn', HL; lia).
      rewrite Sint63.cmod_mod, Hn'.
      replace (Z.to_N (Z.of_nat n)) with (N.of_nat n) by lia.
      apply Sint63.cmod_small.
      assert (Hp : (- 2 ^ 31 <= prod_coeff a b (N.of_nat n) < 2 ^ 31)%Z).
      { rewrite Forall_forall in Hbnd. apply Hbnd.
        eapply nth_error_In. apply Hnth. exact Hn. }
      rewrite wB_val. change (9223372036854775808 / 2)%Z with 4611686018427387904%Z.
      lia.
  - exact Hprod.
Qed.

Section Main.
Local Open Scope R_scope.

Lemma Csub_fst : forall u v, fst (Csub u v) = fst u - fst v.
Proof. reflexivity. Qed.
Lemma Csub_snd : forall u v, snd (Csub u v) = snd u - snd v.
Proof. reflexivity. Qed.

Lemma Cscal_fst : forall r z, fst (Cscal r z) = r * fst z.
Proof. reflexivity. Qed.
Lemma Cscal_snd : forall r z, snd (Cscal r z) = r * snd z.
Proof. reflexivity. Qed.

Theorem polymul_impl_correct : forall (a b : list Z) (x y : array sint),
  valid_input a b -> repr x a -> repr y b ->
  exists p : list Z, repr (polymul_impl x y) p /\ polymul_spec a b p.
Proof.
  intros a b x y Hv Hx Hy. exists (out_list a b).
  pose proof Hv as Hv'. destruct Hv' as [Hva Hvb Hca Hcb Hvp].
  unfold len in Hva, Hvb.
  set (na := List.length a) in *. set (nb := List.length b) in *.
  assert (Hna : (2 <= Z.of_nat na <= 131072)%Z) by lia.
  assert (Hnb : (2 <= Z.of_nat nb <= 131072)%Z) by lia.
  assert (Hna' : (Z.of_nat (List.length a) <= 131072)%Z) by (fold na; lia).
  pose proof (repr_sint_length x a Hx) as Lx0. pose proof (repr_sint_length y b Hy) as Ly0. fold na in Lx0. fold nb in Ly0.
  assert (Lx : to_Z (PArray.length@{Set} x) = Z.of_nat na) by exact Lx0.
  assert (Ly : to_Z (PArray.length@{Set} y) = Z.of_nat nb) by exact Ly0.
  unfold polymul_impl.
  set (Li := (PArray.length x + PArray.length y - 1)%uint63).
  assert (HLi : to_Z Li = (Z.of_nat na + Z.of_nat nb - 1)%Z).
  { unfold Li. rewrite Uint63.sub_spec, Uint63.add_spec, Lx, Ly. change (to_Z 1) with 1%Z.
    rewrite (Z.mod_small (_ + _)) by (change wB with (2^63)%Z; lia). rewrite Z.mod_small by (change wB with (2^63)%Z; lia). lia. }
  destruct (log2up_spec Li ltac:(rewrite HLi; lia)) as [Hlg1 Hlg2].
  set (lgi := log2up Li) in *.
  set (lg := Z.to_nat (to_Z lgi)).
  assert (Hlgz : to_Z lgi = Z.of_nat lg) by (unfold lg; lia).
  assert (Hlg : (2 <= lg <= 18)%nat).
  { split; [|unfold lg; lia]. destruct (Nat.le_gt_cases 2 lg) as [|Hl]; [assumption|].
    assert (lg = 1%nat) by (unfold lg in *; lia). rewrite Hlgz, H in Hlg2. simpl in Hlg2. lia. }
  assert (HNz : Z.of_nat (2 ^ lg) = (2 ^ to_Z lgi)%Z) by (rewrite Hlgz, Nat2Z.inj_pow; reflexivity).
  assert (Hlgo : lgi = of_nat lg) by (apply of_nat_eq; exact Hlgz).
  set (half := 1 << (lgi - 1)).
  assert (Hh : to_Z half = Z.of_nat (hlf lg)).
  { unfold half. rewrite pow2_Z_small; [|rewrite Uint63.sub_spec; change (to_Z 1) with 1%Z; rewrite Z.mod_small by (change wB with (2^63)%Z; lia); lia].
    rewrite Uint63.sub_spec. change (to_Z 1) with 1%Z. rewrite Z.mod_small by (change wB with (2^63)%Z; lia).
    unfold hlf. rewrite Nat2Z.inj_pow, Nat2Z.inj_sub by lia. rewrite <- Hlgz. reflexivity. }
  assert (HNh : (2 ^ lg = 2 * hlf lg)%nat) by (unfold hlf; replace lg with (S (lg - 1)) at 1 by lia; reflexivity).
  set (Ni := (half + half)%uint63).
  assert (HN : to_Z Ni = Z.of_nat (2 ^ lg)).
  { unfold Ni. rewrite Uint63.add_spec, Hh. rewrite Z.mod_small by (change wB with (2^63)%Z;
      assert (Z.of_nat (2 ^ lg) <= 262144)%Z by (rewrite HNz; apply Z.le_trans with (2^18)%Z; [apply Z.pow_le_mono_r; lia | reflexivity]); lia). lia. }
  assert (Hp18 : (Z.of_nat (2 ^ lg) <= 262144)%Z) by (rewrite HNz; apply Z.le_trans with (2^18)%Z; [apply Z.pow_le_mono_r; lia | reflexivity]).
  assert (HLN : (to_Z Li <= Z.of_nat (2 ^ lg))%Z) by (rewrite HNz; lia).
  assert (Hab : (na + nb <= S (2 ^ lg))%nat) by lia.
  (* twiddles *)
  pose proof (build_tw_spec lg Ni Hlg HN) as Htw. rewrite <- Hlgo in Htw.
  destruct (build_tw lgi Ni) as [tre tim].
  (* forward transforms *)
  pose proof (fwd_all_spec x a (PArray.length x) half tre tim lg Hx Lx ltac:(lia) Hlg Hh Htw Hca) as Hfa.
  pose proof (fwd_all_spec y b (PArray.length y) half tre tim lg Hy Ly ltac:(lia) Hlg Hh Htw Hcb) as Hfb.
  rewrite <- Hlgo in Hfa, Hfb.
  destruct (fwd_all x (PArray.length x) lgi half tre tim) as [AR AI].
  destruct (fwd_all y (PArray.length y) lgi half tre tim) as [BR BI].
  destruct Hfa as [_ [_ HA]]. destruct Hfb as [_ [_ HB]].
  assert (HA' : forall i k, (i < 6)%nat -> (k < 2 ^ lg)%nat ->
     repr AR.[of_nat (i * 2 ^ lg + k)] (fst (Ahat a lg i k)) /\ repr AI.[of_nat (i * 2 ^ lg + k)] (snd (Ahat a lg i k)) /\
     Rabs (fst (Ahat a lg i k)) <= Bg /\ Rabs (snd (Ahat a lg i k)) <= Bg).
  { intros i k Hi Hk. destruct (HA i k Hi Hk) as [R1 R2].
    destruct (cfft_bound false lg (Alimb a i) Hlg (Alimb_nrm100 a i lg ltac:(lia)) lg (le_n _) k Hk) as [B1 B2].
    split; [exact R1|]. split; [exact R2|]. split; assumption. }
  assert (HB' : forall i k, (i < 6)%nat -> (k < 2 ^ lg)%nat ->
     repr BR.[of_nat (i * 2 ^ lg + k)] (fst (Ahat b lg i k)) /\ repr BI.[of_nat (i * 2 ^ lg + k)] (snd (Ahat b lg i k)) /\
     Rabs (fst (Ahat b lg i k)) <= Bg /\ Rabs (snd (Ahat b lg i k)) <= Bg).
  { intros i k Hi Hk. destruct (HB i k Hi Hk) as [R1 R2].
    destruct (cfft_bound false lg (Alimb b i) Hlg (Alimb_nrm100 b i lg ltac:(lia)) lg (le_n _) k Hk) as [B1 B2].
    split; [exact R1|]. split; [exact R2|]. split; assumption. }
  (* 1 / N *)
  assert (Hiv : repr (1 / of_uint63 Ni)%float (rnd (1 / INR (2 ^ lg)))).
  { pose proof (repr_of_uint63_exact Ni ltac:(rewrite HN; lia)) as RN.
    rewrite HN, <- INR_IZR_INZ in RN.
    assert (HRN : 4 <= INR (2 ^ lg)).
    { rewrite INR_IZR_INZ. replace 4 with (IZR 4) by reflexivity. apply IZR_le.
      rewrite HNz. change 4%Z with (2^2)%Z. apply Z.pow_le_mono_r; lia. }
    apply repr_div; [exact repr_lit_one | exact RN | lra |]. apply ovf_ok.
    rewrite Rabs_pos_eq by (unfold Rdiv; rewrite Rmult_1_l; apply Rlt_le, Rinv_0_lt_compat; lra).
    pose proof (bp_big 1000 ltac:(lia)). unfold Rdiv. rewrite Rmult_1_l.
    assert (/ INR (2 ^ lg) <= 1) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra). lra. }
  (* the six pairs *)
  set (invN := (1 / of_uint63 Ni)%float) in *.
  assert (HD : forall w q, (Z.abs (Dz a b w q) <= 805306368)%Z).
  { intros w q. pose proof (Dz_bound a b w q). fold na in H. lia. }
  set (P := fun (g : int) (R : array int) => PArray.length R = Li /\
    forall q, (q < Z.to_nat (to_Z Li))%nat -> to_Z R.[of_nat q] = (acc a b (Z.to_nat (to_Z g)) q mod wB)%Z).
  assert (HL : P NL (loop NL (fun g R =>
      let '(pr, pim) := products g Ni AR AI BR BI in
      let '(yr, yi) := fft lgi half true tre tim pr pim in
      accum g Li invN yr yi R) 0 (PArray.make Li 0%uint63))).
  { apply for_inv.
    - change (to_Z 0) with 0%Z. change (to_Z NL) with 6%Z. lia.
    - split; [apply ilength_make; lia|]. intros q Hq. change (Z.to_nat (to_Z 0)) with 0%nat. unfold acc. simpl zsum.
      rewrite Z.mod_0_l by discriminate.
      transitivity (to_Z 0%uint63); [|reflexivity]. f_equal. exact (get_make int 0%uint63 Li (of_nat q)).
    - intros j R Hj [LR TR]. change (to_Z 0) with 0%Z in Hj. change (to_Z NL) with 6%Z in Hj.
      set (gn := Z.to_nat (to_Z j)).
      assert (Hjo : j = of_nat gn) by (apply of_nat_eq; unfold gn; lia).
      assert (Hgn : (gn < 6)%nat) by (unfold gn; lia).
      pose proof (products_spec gn Ni AR AI BR BI (Ahat a lg) (Ahat b lg) lg Hgn HN ltac:(lia) HA' HB') as Hpr.
      rewrite <- Hjo in Hpr.
      cbv beta. destruct (products j Ni AR AI BR BI) as [pr pim].
      destruct Hpr as [Lpr [Lpi Hpc]].
      assert (Hbn := B_Ph100 a b lg gn Hlg Hab Hna').
      pose proof (fft_spec lg Ni half true tre tim pr pim (Pcell (Ahat a lg) (Ahat b lg) gn) Hlg HN Hh Lpr Lpi Htw Hpc
                    (cfft_bound true lg _ Hlg Hbn)) as Hf.
      rewrite <- Hlgo in Hf.
      destruct (fft lgi half true tre tim pr pim) as [yr yi].
      destruct Hf as [_ [_ Hyc]].
      assert (HE : forall q, (q < Z.to_nat (to_Z Li))%nat ->
         Rabs (fst (cfft lg (twc true) lg (Pcell (Ahat a lg) (Ahat b lg) gn) q) - INR (2 ^ lg) * IZR (Dz a b (2 * gn) q)) <= INR (2 ^ lg) * 0.2465 /\
         Rabs (snd (cfft lg (twc true) lg (Pcell (Ahat a lg) (Ahat b lg) gn) q) - INR (2 ^ lg) * IZR (Dz a b (2 * gn + 1) q)) <= INR (2 ^ lg) * 0.2465).
      { intros q Hq. pose proof (final_cmod a b lg gn Hlg Hab Hna' q ltac:(lia)) as Hc.
        destruct (dvec_parts a b gn q) as [F1 F2].
        pose proof (Cmod_re (Csub (cfft lg (twc true) lg (Pcell (Ahat a lg) (Ahat b lg) gn) q) (Cscal (INR (2 ^ lg)) (dvec a b gn q)))) as C1.
        pose proof (Cmod_im (Csub (cfft lg (twc true) lg (Pcell (Ahat a lg) (Ahat b lg) gn) q) (Cscal (INR (2 ^ lg)) (dvec a b gn q)))) as C2.
        rewrite Csub_fst, Cscal_fst, F1 in C1. rewrite Csub_snd, Cscal_snd, F2 in C2.
        split; lra. }
      assert (TR' : forall q, (q < Z.to_nat (to_Z Li))%nat -> to_Z R.[of_nat q] = (acc a b gn q mod wB)%Z) by exact TR.
      pose proof (accum_spec a b gn Li invN yr yi R lg (cfft lg (twc true) lg (Pcell (Ahat a lg) (Ahat b lg) gn))
                    Hgn Hlg HLN Hiv Hyc (cfft_bound true lg _ Hlg Hbn lg (le_n _)) HE HD LR TR') as Hac.
      rewrite <- Hjo in Hac. destruct Hac as [L1 T1].
      split; [exact L1|]. rewrite to_nat_succ by lia. fold gn. exact T1. }
  destruct HL as [LR TR]. change (Z.to_nat (to_Z NL)) with 6%nat in TR.
  apply (out_correct a b _ Li Hv LR ltac:(rewrite HLi; reflexivity)).
  intros k' Hk'. pose proof (to_Z_bounded k').
  assert (E := TR (Z.to_nat (to_Z k')) ltac:(lia)). rewrite of_nat_to_nat in E.
  etransitivity; [exact E|]. rewrite acc_6, <- prod_coeff_split by assumption. f_equal. f_equal. lia.
Qed.

End Main.

(* ---------------------------------------------------------------------- *)
(* The spec's items, at top level                                         *)
(* ---------------------------------------------------------------------- *)

Definition polymul : array sint -> array sint -> array sint := polymul_impl.

Definition polymul_correct : forall (a b : list Z) (x y : array sint),
  valid_input a b -> repr x a -> repr y b ->
  exists p : list Z, repr (polymul x y) p /\ polymul_spec a b p
  := polymul_impl_correct.

(* Cost translations of main's six-limb Stockham FFT implementation. *)
Elpi complexity sumbool.
Elpi complexity bdec.
Elpi complexity wloop.
Elpi complexity loop.
Elpi complexity lg_find.
Elpi complexity log2up.
Elpi complexity tw_cell.
Elpi complexity tw_stage.
Elpi complexity build_tw.
Elpi complexity bfly.
Elpi complexity fft_stage.
Elpi complexity fft.
Elpi complexity KOFF.
Elpi complexity limb.
Elpi complexity load.
Elpi complexity copy_out.
Elpi complexity NL.
Elpi complexity fwd_all.
Elpi complexity cacc.
Elpi complexity andb.
Elpi complexity pterm.
Elpi complexity pcell.
Elpi complexity products.
Elpi complexity MAGIC.
Elpi complexity MAGICI.
Elpi complexity toint.
Elpi complexity accum.
Elpi complexity polymul_impl.
Elpi complexity polymul.

From Stdlib Require Import ssreflect.
Arguments Uint63.to_Z : simpl never.
Arguments wloop : simpl never.
Arguments loop : simpl never.
Arguments wloop_cost : simpl never.
Arguments loop_cost : simpl never.
Arguments Zwf_well_founded : simpl never.
Open Scope nat_scope.
Definition zn (x : int) := Z.to_nat (to_Z x).
Lemma bdec_time b bC : cost (bdec_cost stepsCM b bC) <= 2.
Proof. destruct bC; cost_simpl; lia. Qed.
Ltac bound_bdec :=
  repeat match goal with |- context [@cost ?T (bdec_cost stepsCM ?b ?w)] =>
    let H := fresh "Hbdec" in
    have H := (bdec_time b w : (@cost T (bdec_cost stepsCM b w) <= _)%nat);
    let C := fresh "branch_cost" in
    set (C := @cost T (bdec_cost stepsCM b w)) in *; clearbody C end.

Lemma wloop_time St StC K hi hiC f fC i iC s sC H HC :
  (forall j jC t tC, (j <? hi)%uint63 = true ->
    cost (fC j jC) + cost (extract (fC j jC) t tC) <= K) ->
  cost (extract (extract (extract (extract (extract
    (@wloop_cost stepsCM St StC) hi hiC) f fC) i iC) s sC) H HC)
  <= (K+30) * Z.to_nat (gap hi i)+20.
Proof.
  intro HF. unfold wloop_cost. cbn.
  match goal with |- context [@cost ?A (?G _ _ _ _ _ _ _ _ _ _)] =>
    assert (HG : forall N i ic s sc H hc, Z.to_nat (gap hi i) <= N ->
      cost (G hi hiC f fC i ic s sc H hc) <= (K+30)*N+20) end.
  { induction N as [|N IH]; intros i' ic s' sc [g] hc HN;
      match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end;
      cost_simpl; bound_bdec; cost_destruct (bdec (i' <? hi)%uint63); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in HN. lia.
    - lia.
    - pose proof (dec_step _ _ e) as [D E].
      match goal with |- context [@cost ?A (?G ?hi ?hc ?f ?fc ?i ?ic ?s ?sc ?h ?hc0)] =>
        have HI := (IH i ic s sc h hc0 ltac:(lia)
          : (@cost A (G hi hc f fc i ic s sc h hc0) <= _)%nat) end.
      match goal with |- context [extract (fC ?i ?ic) ?s ?sc] =>
        have Hbody := HF i ic s sc e end.
      match type of HI with (?C <= _)%nat =>
        let c := fresh "recursive_cost" in set (c := C) in *; clearbody c end.
      cbv delta [CostM] in *.
      clear IH HF. destruct (fC i' ic) as [c fc] eqn:Efc.
      cbn [cost extract] in Hbody |- *.
      nia.
    - lia. }
  exact (HG _ _ _ _ _ _ _ (le_n _)).
Qed.

Lemma loop_time St StC K hi hiC f fC i iC s sC :
  (forall j jC t tC, (j <? hi)%uint63 = true ->
    cost (fC j jC)+cost (extract (fC j jC) t tC) <= K) ->
  cost (extract (extract (extract (extract
    (@loop_cost stepsCM St StC) hi hiC) f fC) i iC) s sC)
  <= (K+30)*Z.to_nat(gap hi i)+30.
Proof.
  intro HF. unfold loop_cost. cbn -[wloop_cost].
  have HB := wloop_time St StC K hi hiC f fC i iC s sC
    (Zwf_well_founded 0 (gap hi i)) erased_I HF.
  cost_simpl.
  repeat match goal with |- context [@cost ?T ?c] =>
    change (@cost T c) with 0%nat end.
  lia.
Qed.

Ltac zeros := repeat match goal with |- context [@cost ?T ?c] =>
  change (@cost T c) with 0%nat end.
Ltac set_simpl :=
  repeat match goal with |- context [@cost ?T ?c] =>
    first [change (@cost T c) with 0%nat
          | lazymatch c with
            | extract (extract (extract (set_cost _ _ _) _ _) _ _) _ _ =>
              change (@cost T c) with 1%nat
            | extract (extract (make_cost _ _ _) _ _) _ _ =>
              change (@cost T c) with 1%nat end] end.
Ltac split_pair :=
  once match goal with |- context [match ?t as _ return _ with (_,_) => _ end] =>
    cost_destruct_prep t; let p := fresh "p" in let E := fresh "Epair" in
    remember t as p eqn:E;
    match goal with w : prod_cost _ _ _ _ _ p |- _ => destruct w end;
    cbn [fst snd] in *; cost_simpl end.
Ltac gen_loop K body :=
  zeros;
  match goal with |- context [@cost ?T
    (extract (extract (extract (extract (@loop_cost stepsCM ?St ?StC) ?hi ?hc) ?f ?fc) ?i ?ic) ?s ?sc)] =>
    let HF := fresh "Hbody" in
    assert (HF : forall j jc t tc, (j <? hi)%uint63 = true ->
      cost (fc j jc)+cost (extract (fc j jc) t tc) <= K) by
      (intros; match goal with |- (_ <= ?rhs)%nat =>
         let b := fresh "body_budget" in let E := fresh "Hbodybudget" in
         remember rhs as b eqn:E end; body);
    let HB := fresh "Hloop" in
    pose proof (loop_time St StC K hi hc f fc i ic s sc HF) as HB;
    match type of HB with (?C <= _)%nat =>
      let c := fresh "loop_cost_bound" in set (c := C) in *; clearbody c end;
    clear HF end.

Lemma tw_cell_time m mc hm hmc bc bcc bs bsc k kc st stc :
  cost (extract (extract (extract (extract (extract
    (tw_cell_cost stepsCM m mc) hm hmc) bc bcc) bs bsc) k kc) st stc) <= 100.
Proof.
  destruct stc. unfold tw_cell_cost. cost_simpl.
  rewrite cost_if. lazymatch goal with |- context [if ?b then _ else _] => destruct b end;
    cost_simpl; set_simpl; lia.
Qed.

Ltac cost_head f c := lazymatch c with
  | extract ?g _ _ => cost_head f g
  | f stepsCM _ _ => idtac end.
Ltac instantiate_bound lemma c := lazymatch c with
  | extract ?g ?a ?ac => let p := instantiate_bound lemma g in constr:(p a ac)
  | ?f stepsCM ?a ?ac => constr:(lemma a ac) end.
Ltac bound_named f lemma := zeros;
  repeat match goal with |- context [@cost ?T ?c] => cost_head f c;
    let B := fresh "Hcost" in let q := instantiate_bound lemma c in
    have B := (q : (@cost T c <= _)%nat);
    let C := fresh "helper_cost" in set (C := @cost T c) in *; clearbody C end.
Ltac destruct_pairs := repeat match goal with
  w : prod_cost _ _ _ _ _ _ |- _ => destruct w end.
Arguments tw_cell_cost : simpl never.

Lemma tw_stage_time s sc st stc :
  cost (extract (tw_stage_cost stepsCM s sc) st stc)
  <= 200*zn (1 << s)%uint63+100.
Proof.
  destruct_pairs. unfold tw_stage_cost. cost_simpl.
  gen_loop 100 ltac:(bound_named tw_cell_cost tw_cell_time; lia).
  split_pair. unfold gap, zn in *. change (to_Z 0%uint63) with 0%Z in *.
  repeat match goal with H : context [(?z-0)%Z] |- _ => rewrite Z.sub_0_r in H end.
  lia.
Qed.

Local Notation "f @@ [ a ; ac ]" := (extract f a ac)
  (at level 10, left associativity).
Lemma shift_bound x : zn (1 << x)%uint63 <= 2 ^ zn x.
Proof.
  unfold zn. rewrite lsl_spec. change (to_Z 1%uint63) with 1%Z. rewrite Z.mul_1_l.
  pose proof (Z2Nat.inj_pow 2 (to_Z x) ltac:(lia)
    ltac:(pose proof (to_Z_bounded x); lia)) as E.
  change (Z.to_nat (2 ^ to_Z x) = 2 ^ Z.to_nat (to_Z x))%nat in E. rewrite <- E.
  apply Z2Nat.inj_le.
  - apply Z.mod_pos_bound. rewrite wB_val. lia.
  - apply Z.pow_nonneg. lia.
  - apply Z.mod_le; [apply Z.pow_nonneg; lia|rewrite wB_val; lia].
Qed.
Lemma gap0 x : Z.to_nat (gap x 0%uint63) = zn x.
Proof. unfold gap, zn. change (to_Z 0%uint63) with 0%Z. rewrite Z.sub_0_r. reflexivity. Qed.
Ltac norm_gaps := repeat match goal with
  H : context [Z.to_nat (gap ?x 0%uint63)] |- _ => rewrite gap0 in H end.
Arguments tw_stage_cost : simpl never.
Lemma build_tw_time lg lgc N Nc :
  cost ((build_tw_cost stepsCM lg lgc) @@ [N;Nc])
  <= 500*(2^zn lg+1)*(zn lg+1).
Proof.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold build_tw_cost. cost_simpl; set_simpl.
  gen_loop (200*2^zn lg+100) ltac:(
    bound_named tw_stage_cost tw_stage_time;
    match goal with H : (?j <? lg)%uint63 = true |- _ =>
      have Hj := proj1 (Uint63.ltb_spec _ _) H;
      have Hs := shift_bound j;
      assert (He : 2^zn j <= 2^zn lg) by
        (apply Nat.pow_le_mono_r; unfold zn; lia) end;
    nia).
  split_pair; split_pair; split_pair; set_simpl.
  assert (Hg : Z.to_nat (gap lg 1%uint63) <= zn lg) by
    (unfold gap, zn; change (to_Z 1%uint63) with 1%Z; lia).
  nia.
Qed.

Lemma bfly_time sh shc m mc half halfc neg negc sre srec sim simc tre trec tim timc j jc st stc :
  cost ((bfly_cost stepsCM sh shc) @@ [m;mc] @@ [half;halfc] @@ [neg;negc]
    @@ [sre;srec] @@ [sim;simc] @@ [tre;trec] @@ [tim;timc] @@ [j;jc] @@ [st;stc]) <= 300.
Proof.
  destruct_pairs. destruct negc; unfold bfly_cost; cost_simpl; set_simpl; lia.
Qed.
Arguments bfly_cost : simpl never.
Lemma fft_stage_time lg lgc half halfc neg negc tre trec tim timc s sc st stc :
  cost ((fft_stage_cost stepsCM lg lgc) @@ [half;halfc] @@ [neg;negc]
    @@ [tre;trec] @@ [tim;timc] @@ [s;sc] @@ [st;stc]) <= 400*zn half+100.
Proof.
  destruct_pairs.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold fft_stage_cost. cost_simpl.
  gen_loop 300 ltac:(bound_named bfly_cost bfly_time; lia).
  split_pair. norm_gaps. lia.
Qed.
Arguments fft_stage_cost : simpl never.
Lemma fft_time lg lgc half halfc neg negc tre trec tim timc re rec im imc :
  cost ((fft_cost stepsCM lg lgc) @@ [half;halfc] @@ [neg;negc]
    @@ [tre;trec] @@ [tim;timc] @@ [re;rec] @@ [im;imc])
  <= 600*(zn half+1)*(zn lg+1).
Proof.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold fft_cost. cost_simpl; set_simpl.
  gen_loop (400*zn half+100) ltac:(bound_named fft_stage_cost fft_stage_time; lia).
  split_pair; split_pair; split_pair; set_simpl. norm_gaps. nia.
Qed.

Lemma limb_time c cc i ic : cost ((limb_cost stepsCM c cc) @@ [i;ic]) <= 50.
Proof. unfold limb_cost, KOFF_cost. cost_simpl. lia. Qed.
Arguments limb_cost : simpl never.
Lemma load_time x xc n nc N Nc i ic :
  cost ((load_cost stepsCM x xc) @@ [n;nc] @@ [N;Nc] @@ [i;ic]) <= 200*zn n+100.
Proof.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold load_cost. cost_simpl; set_simpl.
  gen_loop 100 ltac:(cost_simpl; set_simpl; bound_named limb_cost limb_time; lia).
  norm_gaps. lia.
Qed.
Lemma copy_out_time N Nc off offc yr yrc yi yic st stc :
  cost ((copy_out_cost stepsCM N Nc) @@ [off;offc] @@ [yr;yrc] @@ [yi;yic] @@ [st;stc])
  <= 200*zn N+100.
Proof.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold copy_out_cost. cost_simpl.
  gen_loop 100 ltac:(destruct_pairs; cost_simpl; set_simpl; lia).
  norm_gaps. lia.
Qed.
Arguments fft_cost : simpl never.
Arguments load_cost : simpl never.
Arguments copy_out_cost : simpl never.
Lemma add_bound a b : zn (a+b)%uint63 <= zn a+zn b.
Proof.
  unfold zn. rewrite Uint63.add_spec.
  pose proof (Z.mod_le (to_Z a+to_Z b) wB
    ltac:(pose proof(to_Z_bounded a); pose proof(to_Z_bounded b); lia)
    ltac:(rewrite wB_val; lia)) as H.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite <- (Z2Nat.inj_add (to_Z a) (to_Z b) ltac:(lia) ltac:(lia)).
  apply Z2Nat.inj_le; [apply Z.mod_pos_bound; rewrite wB_val; lia|lia|exact H].
Qed.
Lemma fwd_all_time x xc n nc lg lgc half halfc tre trec tim timc :
  cost ((fwd_all_cost stepsCM x xc) @@ [n;nc] @@ [lg;lgc] @@ [half;halfc]
    @@ [tre;trec] @@ [tim;timc])
  <= (10*1000)*(zn n+(zn half+1)*(zn lg+1)+zn half+1).
Proof.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold fwd_all_cost, NL_cost. cost_simpl; set_simpl.
  gen_loop (1000*(zn n+(zn half+1)*(zn lg+1)+zn half+1)) ltac:(
    cost_simpl; set_simpl;
    bound_named load_cost load_time; bound_named fft_cost fft_time;
    split_pair; bound_named copy_out_cost copy_out_time;
    have HA := add_bound half half; nia).
  norm_gaps. change (zn NL) with 6 in *. nia.
Qed.

Lemma cacc_time ar arc ai aic br brc bi bic st stc :
  cost ((cacc_cost stepsCM ar arc) @@ [ai;aic] @@ [br;brc] @@ [bi;bic] @@ [st;stc]) <= 50.
Proof. destruct_pairs. unfold cacc_cost. cost_simpl. lia. Qed.
Arguments cacc_cost : simpl never.
Lemma pterm_time w wc N Nc k kc AR ARc AI AIc BR BRc BI BIc i ic st stc :
  cost ((pterm_cost stepsCM w wc) @@ [N;Nc] @@ [k;kc] @@ [AR;ARc] @@ [AI;AIc]
    @@ [BR;BRc] @@ [BI;BIc] @@ [i;ic] @@ [st;stc]) <= 200.
Proof.
  unfold pterm_cost, andb_cost. cost_simpl.
  repeat (rewrite cost_if;
    lazymatch goal with |- context [if ?b then _ else _] => destruct b end; cost_simpl);
    bound_named cacc_cost cacc_time; lia.
Qed.
Arguments pterm_cost : simpl never.
Lemma pcell_time g gc N Nc AR ARc AI AIc BR BRc BI BIc k kc st stc :
  cost ((pcell_cost stepsCM g gc) @@ [N;Nc] @@ [AR;ARc] @@ [AI;AIc]
    @@ [BR;BRc] @@ [BI;BIc] @@ [k;kc] @@ [st;stc]) <= 4000.
Proof.
  destruct_pairs. unfold pcell_cost, NL_cost. cost_simpl.
  gen_loop 200 ltac:(bound_named pterm_cost pterm_time; lia).
  split_pair.
  gen_loop 200 ltac:(bound_named pterm_cost pterm_time; lia).
  split_pair; set_simpl. norm_gaps. change (zn NL) with 6 in *. lia.
Qed.
Arguments pcell_cost : simpl never.
Lemma products_time g gc N Nc AR ARc AI AIc BR BRc BI BIc :
  cost ((products_cost stepsCM g gc) @@ [N;Nc] @@ [AR;ARc] @@ [AI;AIc]
    @@ [BR;BRc] @@ [BI;BIc]) <= 5000*zn N+100.
Proof.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold products_cost. cost_simpl; set_simpl.
  gen_loop 4000 ltac:(bound_named pcell_cost pcell_time; lia).
  norm_gaps. lia.
Qed.
Lemma toint_time z zc : cost (toint_cost stepsCM z zc) <= 50.
Proof. unfold toint_cost, MAGIC_cost, MAGICI_cost. cost_simpl. split_pair. lia. Qed.
Arguments toint_cost : simpl never.
Lemma accum_time g gc L Lc invN invNc yr yrc yi yic R Rc :
  cost ((accum_cost stepsCM g gc) @@ [L;Lc] @@ [invN;invNc] @@ [yr;yrc]
    @@ [yi;yic] @@ [R;Rc]) <= 300*zn L+100.
Proof.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold accum_cost. cost_simpl.
  gen_loop 200 ltac:(cost_simpl; set_simpl; bound_named toint_cost toint_time; lia).
  norm_gaps. lia.
Qed.

Arguments lg_find : simpl never.
Lemma lg_find_time L Lc k kc H Hc :
  cost ((lg_find_cost stepsCM L Lc) @@ [k;kc] @@ [H;Hc])
  <= 50*Z.to_nat(gap 62%uint63 k)+50.
Proof.
  unfold lg_find_cost. cbn.
  match goal with |- context [@cost ?A (?G _ _ _ _ _ _)] =>
    assert (HG : forall N k kc H hc, Z.to_nat(gap 62%uint63 k)<=N ->
      cost (G L Lc k kc H hc)<=50*N+50) end.
  { induction N as [|N IH]; intros k' kc' [g] hc HN;
      match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end;
      cost_simpl; bound_bdec; cost_destruct (bdec (k' <? 62)%uint63); cost_simpl.
    - exfalso. have D := proj1 (Uint63.ltb_spec _ _) e. unfold gap in HN.
      change (to_Z 62%uint63) with 62%Z in HN.
      change (to_Z 62%uint63) with 62%Z in D. lia.
    - lia.
    - rewrite cost_if. lazymatch goal with |- context [if ?b then _ else _] => destruct b end;
        cost_simpl; [lia|].
      have D := dec_step _ _ e. destruct D as [D E].
      match goal with |- context [@cost ?A (?G ?l ?lc ?k ?kc ?h ?hc)] =>
        have HI := (IH k kc h hc ltac:(lia)
          : (@cost A (G l lc k kc h hc) <= _)%nat) end.
      lia.
    - lia. }
  exact (HG _ _ _ _ _ (le_n _)).
Qed.
Arguments lg_find_cost : simpl never.
Lemma log2up_time L Lc : cost (log2up_cost stepsCM L Lc) <= 4000.
Proof.
  unfold log2up_cost. cost_simpl. bound_named lg_find_cost lg_find_time.
  match goal with H : context [Z.to_nat (gap 62%uint63 0%uint63)] |- _ =>
    change (Z.to_nat (gap 62%uint63 0%uint63)) with 62 in H end. lia.
Qed.
Arguments log2up_cost : simpl never.
Arguments build_tw_cost : simpl never.
Arguments fwd_all_cost : simpl never.
Arguments products_cost : simpl never.
Arguments accum_cost : simpl never.

Lemma polymul_time_raw x y :
  let na := @PArray.length@{Set} int x in
  let nb := @PArray.length@{Set} int y in
  let L := (na+nb-1)%uint63 in
  let lg := log2up L in
  let half := (1 << (lg-1))%uint63 in
  cost2 polymul_cost x y <=
    (1000*1000)*((zn na+zn nb+zn L+zn half+2^zn lg+1)*(zn lg+1))+(20*1000).
Proof.
  cbv zeta.
  match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end.
  unfold cost2, polymul_cost, polymul_impl_cost. cost_simpl; set_simpl.
  bound_named log2up_cost log2up_time.
  bound_named build_tw_cost build_tw_time. split_pair.
  bound_named fwd_all_cost fwd_all_time. split_pair; split_pair.
  gen_loop (1000*100*(
    zn (@PArray.length@{Set} int x+@PArray.length@{Set} int y-1)%uint63+
    (zn (1 << (log2up (@PArray.length@{Set} int x+@PArray.length@{Set} int y-1)%uint63-1))%uint63+1)*
    (zn (log2up (@PArray.length@{Set} int x+@PArray.length@{Set} int y-1)%uint63)+1)+1))
    ltac:(cost_simpl; set_simpl;
      bound_named products_cost products_time; split_pair;
      bound_named fft_cost fft_time; split_pair;
      bound_named accum_cost accum_time;
      match goal with H : context [(?half+?half)%uint63] |- _ =>
        have HA := add_bound half half end;
      cbv delta [sint uint] in *;
      clear - Hcost3 Hcost4 Hcost5 HA Hbodybudget;
      nia).
  set_simpl. norm_gaps. change (zn NL) with 6 in *.
  cbv delta [sint uint] in *.
  assert (Hpow : 1 <= 2^zn (log2up
    (@PArray.length@{Set} int x+@PArray.length@{Set} int y-1)%uint63)) by
    (have H := Nat.pow_nonzero 2 (zn (log2up
      (@PArray.length@{Set} int x+@PArray.length@{Set} int y-1)%uint63)) ltac:(lia); lia).
  clear - Hcost Hcost0 Hcost1 Hcost2 Hloop Hbudget Hpow.
  nia.
Qed.

Theorem polymul_time : exists c1 c2 : nat,
  forall (first_coeffs second_coeffs : list Z)
         (first_coeffs_arr second_coeffs_arr : array sint),
  valid_input first_coeffs second_coeffs ->
  repr first_coeffs_arr first_coeffs ->
  repr second_coeffs_arr second_coeffs ->
  Nat.le (cost2 polymul_cost first_coeffs_arr second_coeffs_arr)
    (Nat.add (Nat.mul c1
      ((Cost.size first_coeffs_arr+Cost.size second_coeffs_arr)*
       (Nat.log2(Cost.size first_coeffs_arr+Cost.size second_coeffs_arr)+1))%nat) c2).
Proof.
  exists (20*1000*1000), (20*1000). intros a b x y Hv Hx Hy.
  have Lx := repr_sint_length x a Hx. have Ly := repr_sint_length y b Hy.
  destruct Hv as [Ha Hb _ _ _]. unfold len in Ha, Hb.
  assert (Lxset : to_Z (@PArray.length@{Set} int x) = Z.of_nat(List.length a)) by exact Lx.
  assert (Lyset : to_Z (@PArray.length@{Set} int y) = Z.of_nat(List.length b)) by exact Ly.
  assert (Hxlen : (2 <= to_Z (@PArray.length@{Set} int x) <= 131072)%Z) by lia.
  assert (Hylen : (2 <= to_Z (@PArray.length@{Set} int y) <= 131072)%Z) by lia.
  have HR := polymul_time_raw x y. cbv zeta in HR.
  cbv delta [sint uint] in *.
  change (Cost.size x) with (zn (@PArray.length@{Set} int x)).
  change (Cost.size y) with (zn (@PArray.length@{Set} int y)).
  set (na := @PArray.length@{Set} int x) in *.
  set (nb := @PArray.length@{Set} int y) in *.
  set (L := (na+nb-1)%uint63) in *.
  assert (HL : to_Z L = (to_Z na+to_Z nb-1)%Z).
  { unfold L. rewrite Uint63.sub_spec Uint63.add_spec.
    change (to_Z 1%uint63) with 1%Z.
    rewrite (Z.mod_small (to_Z na+to_Z nb) wB ltac:(rewrite wB_val; lia)).
    rewrite (Z.mod_small (to_Z na+to_Z nb-1) wB ltac:(rewrite wB_val; lia)). reflexivity. }
  destruct (log2up_spec L ltac:(rewrite HL; lia)) as [HG HP].
  set (lg := log2up L) in *.
  set (half := (1 << (lg-1))%uint63) in *.
  set (Ssum := (zn na+zn nb)%nat).
  assert (HS : (4 <= Ssum)%nat) by (unfold Ssum, zn; lia).
  assert (HLnat : (zn L <= Ssum)%nat) by (unfold Ssum, zn; lia).
  assert (HPnat : (2^zn lg < 2*Ssum)%nat).
  { assert (HE : Z.of_nat (2^zn lg) = (2^to_Z lg)%Z).
    { rewrite Nat2Z.inj_pow. unfold zn. rewrite (Z2Nat.id (to_Z lg) ltac:(lia)). reflexivity. }
    unfold zn in HE. unfold Ssum, zn. lia. }
  assert (Hhalf : (zn half <= 2^zn lg)%nat).
  { unfold half. eapply Nat.le_trans; [apply shift_bound|].
    apply Nat.pow_le_mono_r; [lia|]. unfold zn. rewrite Uint63.sub_spec.
    change (to_Z 1%uint63) with 1%Z.
    rewrite (Z.mod_small (to_Z lg-1) wB ltac:(rewrite wB_val; lia)). lia. }
  set (ell := Nat.log2 Ssum).
  assert (Hlog : (Ssum < 2^(S ell))%nat) by
    (have H := Nat.log2_spec Ssum ltac:(lia); exact (proj2 H)).
  assert (HGnat : (zn lg <= ell+1)%nat).
  { destruct (Nat.le_gt_cases (zn lg) (ell+1)) as [Hle|Hgt]; [exact Hle|].
    assert (Hpow : (2^(S(S ell)) <= 2^zn lg)%nat) by (apply Nat.pow_le_mono_r; lia).
    rewrite !Nat.pow_succ_r' in Hpow. rewrite Nat.pow_succ_r' in Hlog.
    clear - Hpow Hlog HPnat. nia. }
  assert (HW : (zn na+zn nb+zn L+zn half+2^zn lg+1 <= 7*Ssum)%nat) by
    (unfold Ssum in *; lia).
  assert (HB : ((zn na+zn nb+zn L+zn half+2^zn lg+1)*(zn lg+1)
    <= 14*(Ssum*(ell+1)))%nat).
  { eapply Nat.le_trans with (m := ((7*Ssum)*(2*(ell+1)))%nat);
      [apply Nat.mul_le_mono; [exact HW|lia]|]. nia. }
  fold Ssum. fold ell.
  clear - HR HB.
  eapply Nat.le_trans; [exact HR|].
  nia.
Qed.

Print Assumptions polymul_correct.
Print Assumptions polymul_time.
