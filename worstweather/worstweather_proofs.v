(* Correctness proofs for worstweather_implem.v. *)
(* Implementation of worstweather (worstweather.spec): a sparse table
   for range maxima of the rain, two binary searches per query.

   Code.  [worstweather_impl ys rs qy qx] with n = |ys|:
   - L = floor(log2 n) + 1 levels; one flat table T of L*n cells, cell
     k*n + i holding max rs[i .. i + 2^k) (row 0 copied from rs, row k
     built from row k-1, [build]);
   - for each query (Y, X): i, j = the first indices with ys >= Y, X
     (signed binary searches, [lower_bound]); Y is known iff ys[i] = Y,
     X iff ys[j] = X; the known years strictly between are the indices
     [lo, j) with lo = i+1 or i; their maximum rain is one O(1) lookup in
     T ([rmq], k = floor(log2 (j - lo)) by a halving loop); then
       both known:  rx <= ry and max < rx  ->  true if j - i = X - Y
                    (every year in between known) else maybe; else false
       Y only:      max < ry -> maybe, else false
       X only:      max < rx -> maybe, else false
       neither:     maybe;
   - the result array is filled in place, one [set] per query.
   Everything is Uint63 [int]; years are compared through Sint63.ltb.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof (the template's device); no nat, no fuel.

   Proof.  [tbl_ok] (each cell is the maximum of its range) is the table
   invariant; [lb_loop_spec] the binary-search invariant; the Math section
   reduces [answers] to the four cases above ([ans_of_correct]), using the
   assignment [ext g] (the known rain, g elsewhere) as the witness of
   might_be_true, and [count_iff] (strictly increasing integers fill
   [ys_i, ys_j] iff j - i = ys_j - ys_i) for the "true" case. *)

From Worstweather.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Worstweather Require Export worstweather_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ------------------------------------------------------------------ *)
(* Unfolding equations                                                 *)
(* ------------------------------------------------------------------ *)

Lemma lb_loop_eq : forall ys key lo hi H,
  lb_loop ys key lo hi H =
  match bdec (lo <? hi) with
  | left Hlt =>
      let mid := lo + (hi - lo) / 2 in
      if Sint63.ltb ys.[mid] key
      then lb_loop ys key (mid + 1) hi (Acc_inv H (lb_dec_r lo hi Hlt))
      else lb_loop ys key lo mid (Acc_inv H (lb_dec_l lo hi Hlt))
  | right _ => lo
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma lg_loop_eq : forall x k H,
  lg_loop x k H =
  match bdec (1 <? x) with
  | left Hx => lg_loop (x / 2) (k + 1) (Acc_inv H (lg_dec x Hx))
  | right _ => k
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma copy_loop_eq : forall rs n i T H,
  copy_loop rs n i T H =
  match bdec (i <? n) with
  | left Hi => copy_loop rs n (i + 1) T.[i <- rs.[i]] (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma row_loop_eq : forall base prev half lim i T H,
  row_loop base prev half lim i T H =
  match bdec (i <? lim) with
  | left Hi =>
      row_loop base prev half lim (i + 1)
        T.[base + i <- imax T.[prev + i] T.[prev + i + half]]
        (Acc_inv H (dec_step lim i Hi))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rows_loop_eq : forall n L k T H,
  rows_loop n L k T H =
  match bdec (k <? L) with
  | left Hk =>
      rows_loop n L (k + 1)
        (row_loop (k * n) ((k - 1) * n) (1 << (k - 1)) (n - (1 << k) + 1) 0 T
           (Zwf_well_founded 0 (gap (n - (1 << k) + 1) 0)))
        (Acc_inv H (dec_step L k Hk))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma q_loop_eq : forall ys rs T qy qx n m k out H,
  q_loop ys rs T qy qx n m k out H =
  match bdec (k <? m) with
  | left Hk =>
      q_loop ys rs T qy qx n m (k + 1)
        out.[k <- answer_query ys rs T n qy.[k] qx.[k]]
        (Acc_inv H (dec_step m k Hk))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma qget_set_same : forall (t : array answer) (i : int) (b : answer),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same answer t i b H). Qed.

Lemma qget_set_other : forall (t : array answer) (i j : int) (b : answer),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other answer t i j b H). Qed.

Lemma qlength_set : forall (t : array answer) (i : int) (b : answer),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set answer t i b). Qed.

Lemma qlength_make : forall (n : int) (b : answer),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make answer n b). Qed.

Definition uget (a : array int) (p : Z) : Z := (φ (a.[of_Z p])).
Definition sget (a : array int) (p : Z) : Z := Sint63.to_Z (a.[of_Z p]).

Lemma uget_int : forall (T : array int) (x : int), (φ (T.[x])) = uget T (φ x).
Proof. intros. unfold uget. rewrite of_to_Z. reflexivity. Qed.

Lemma sget_int : forall (T : array int) (x : int), Sint63.to_Z (T.[x]) = sget T (φ x).
Proof. intros. unfold sget. rewrite of_to_Z. reflexivity. Qed.

Lemma of_Z_phi : forall p, (0 <= p < wB)%Z -> (φ (of_Z p)) = p.
Proof. intros p Hp. rewrite of_Z_spec. apply Z.mod_small. exact Hp. Qed.

Lemma uget_set : forall (T : array int) (i v : int) (p : Z),
  (0 <= p < wB)%Z -> (i <? PArray.length T) = true ->
  uget T.[i <- v] p = if Z.eqb p (φ i) then (φ v) else uget T p.
Proof.
  intros T i v p Hp Hi. unfold uget.
  destruct (Z.eqb_spec p (φ i)) as [E | E].
  - subst p. rewrite of_to_Z. rewrite aget_set_same by exact Hi. reflexivity.
  - rewrite aget_set_other; [reflexivity|].
    intro F. apply E. rewrite F. rewrite of_Z_phi by exact Hp. reflexivity.
Qed.

Lemma pow2_pos : forall k, (0 <= k)%Z -> (0 < 2 ^ k)%Z.
Proof. intros k Hk. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_succ : forall k, (0 <= k)%Z -> (2 ^ (k + 1) = 2 * 2 ^ k)%Z.
Proof. intros k Hk. rewrite Z.pow_add_r by lia. lia. Qed.

Lemma pow2_le_62 : forall k, (0 <= k <= 62)%Z -> (2 ^ k <= 2 ^ 62)%Z.
Proof. intros k Hk. apply Z.pow_le_mono_r; lia. Qed.

Lemma shl1 : forall k : int, ((φ k) <= 62)%Z -> (φ (1 << k)) = (2 ^ (φ k))%Z.
Proof.
  intros k Hk. rewrite lsl_spec. change (φ 1) with 1%Z. rewrite Z.mul_1_l.
  pose proof (to_Z_bounded k) as Bk.
  pose proof (pow2_le_62 (φ k) ltac:(lia)) as P.
  pose proof (pow2_pos (φ k) ltac:(lia)) as P0.
  apply Z.mod_small. rewrite wB_val. change (2 ^ 62)%Z with 4611686018427387904%Z in P.
  lia.
Qed.

Lemma imax_spec : forall a b : int, (φ (imax a b)) = Z.max (φ a) (φ b).
Proof.
  intros a b. unfold imax. destruct (a <? b) eqn:E.
  - rewrite ltb_spec in E. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Binary search                                                       *)
(* ------------------------------------------------------------------ *)

Lemma lb_loop_spec : forall (ys : array int) (N : Z) (key : int),
  (forall p q, (0 <= p <= q)%Z -> (q < N)%Z -> (sget ys p <= sget ys q)%Z) ->
  forall z lo hi H, gap hi lo = z ->
  (0 <= (φ lo) <= (φ hi))%Z -> ((φ hi) <= N)%Z ->
  (forall p, (0 <= p < (φ lo))%Z -> (sget ys p < Sint63.to_Z key)%Z) ->
  (forall p, ((φ hi) <= p < N)%Z -> (Sint63.to_Z key <= sget ys p)%Z) ->
  ((φ lo) <= (φ (lb_loop ys key lo hi H)) <= (φ hi))%Z /\
  (forall p, (0 <= p < (φ (lb_loop ys key lo hi H)))%Z -> (sget ys p < Sint63.to_Z key)%Z) /\
  (forall p, ((φ (lb_loop ys key lo hi H)) <= p < N)%Z -> (Sint63.to_Z key <= sget ys p)%Z).
Proof.
  intros ys N key Hmono z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi H Hz Hlh HhN Hlo Hhi.
  rewrite lb_loop_eq.
  destruct (bdec (lo <? hi)) as [Hlt | Hlt]; cbv zeta.
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hm : (φ (lo + (hi - lo) / 2)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z) by sia.
    assert (Hm1 : (φ (lo + (hi - lo) / 2 + 1)) = ((φ lo) + ((φ hi) - (φ lo)) / 2 + 1)%Z) by sia.
    assert (Hmr : ((φ lo) <= (φ lo) + ((φ hi) - (φ lo)) / 2 < (φ hi))%Z) by sia.
    destruct (Sint63.ltb (ys.[lo + (hi - lo) / 2]) key) eqn:E.
    + rewrite Sint63.ltb_spec, Z.compare_lt_iff, sget_int, Hm in E.
      destruct (IH _ (ltac:(rewrite <- Hz; apply lb_dec_r; exact Hlt))
                  (lo + (hi - lo) / 2 + 1) hi
                  (Acc_inv H (lb_dec_r lo hi Hlt)) eq_refl
                  ltac:(lia) HhN) as (A & B & C).
      * intros p Hp. rewrite Hm1 in Hp.
        destruct (Z.eq_dec p ((φ lo) + ((φ hi) - (φ lo)) / 2)) as [-> | Ne]; [exact E|].
        pose proof (Hmono p ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z ltac:(lia) ltac:(lia)). lia.
      * exact Hhi.
      * split; [lia|]. split; assumption.
    + rewrite <- Bool.not_true_iff_false, Sint63.ltb_spec, Z.compare_lt_iff,
        sget_int, Hm in E.
      destruct (IH _ (ltac:(rewrite <- Hz; apply lb_dec_l; exact Hlt))
                  lo (lo + (hi - lo) / 2)
                  (Acc_inv H (lb_dec_l lo hi Hlt)) eq_refl
                  ltac:(lia) ltac:(lia) Hlo) as (A & B & C).
      * intros p Hp. rewrite Hm in Hp.
        pose proof (Hmono ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z p ltac:(lia) ltac:(lia)). lia.
      * split; [lia|]. split; assumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [lia|]. split; [exact Hlo|].
    intros p Hp. apply Hhi. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* floor(log2)                                                         *)
(* ------------------------------------------------------------------ *)

Lemma lg_loop_spec : forall z (x k : int) H, (φ x) = z ->
  (1 <= (φ x))%Z -> ((φ k) + (φ x) < wB)%Z ->
  exists d, (φ (lg_loop x k H)) = ((φ k) + d)%Z /\ (0 <= d)%Z /\
            (2 ^ d <= (φ x) < 2 ^ (d + 1))%Z.
Proof.
  intro z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x k H Hz Hx Hk.
  rewrite lg_loop_eq.
  destruct (bdec (1 <? x)) as [Hx1 | Hx1].
  - pose proof Hx1 as Hx1'. rewrite ltb_spec in Hx1'. change (φ 1) with 1%Z in Hx1'.
    assert (Hd : (φ (x / 2)) = ((φ x) / 2)%Z) by sia.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    destruct (IH _ (ltac:(rewrite <- Hz; apply lg_dec; exact Hx1)) (x / 2) (k + 1)
                (Acc_inv H (lg_dec x Hx1)) eq_refl ltac:(lia) ltac:(lia))
      as (d & E & Hd0 & Hb).
    exists (d + 1)%Z. rewrite E, Hk1. split; [lia|]. split; [lia|].
    rewrite (pow2_succ (d + 1)) by lia. rewrite (pow2_succ d) in * by lia.
    rewrite Hd in Hb. sia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hx1. change (φ 1) with 1%Z in Hx1.
    exists 0%Z. split; [lia|]. split; [lia|]. simpl. lia.
Qed.

Lemma lg_spec : forall x : int, (1 <= (φ x))%Z ->
  (0 <= (φ (lg x)))%Z /\ (2 ^ (φ (lg x)) <= (φ x) < 2 ^ ((φ (lg x)) + 1))%Z.
Proof.
  intros x Hx. unfold lg.
  pose proof (to_Z_bounded x) as Bx.
  destruct (lg_loop_spec _ x 0 (Zwf_well_founded 0 (φ x)) eq_refl Hx
              ltac:(change (φ 0) with 0%Z; lia)) as (d & E & Hd & Hb).
  change (φ 0) with 0%Z in E. rewrite E. simpl. split; [lia|]. exact Hb.
Qed.

Lemma lg_le_62 : forall x : int, (1 <= (φ x))%Z -> ((φ (lg x)) <= 62)%Z.
Proof.
  intros x Hx. destruct (lg_spec x Hx) as [H0 [H1 _]].
  pose proof (to_Z_bounded x) as Bx.
  destruct (Z.le_gt_cases (φ (lg x)) 62) as [|G]; [assumption|].
  assert (2 ^ 63 <= 2 ^ (φ (lg x)))%Z by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 63)%Z with 9223372036854775808%Z in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The sparse table                                                    *)
(* ------------------------------------------------------------------ *)

Lemma mul_small : forall a b : int, ((φ a) * (φ b) < wB)%Z -> (φ (a * b)) = ((φ a) * (φ b))%Z.
Proof.
  intros a b H. rewrite mul_spec. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  apply Z.mod_small. nia.
Qed.

Lemma mul_add_small : forall a b c : int, ((φ a) * (φ b) + (φ c) < wB)%Z ->
  (φ (a * b + c)) = ((φ a) * (φ b) + (φ c))%Z.
Proof.
  intros a b c H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  pose proof (to_Z_bounded c).
  rewrite add_spec, mul_small by nia. apply Z.mod_small. nia.
Qed.

(* v is the maximum of R over [l, r) (a nonempty range). *)
Definition isMax (R : Z -> Z) (v l r : Z) : Prop :=
  (forall p, (l <= p < r)%Z -> (R p <= v)%Z) /\ (exists p, (l <= p < r)%Z /\ R p = v).

Lemma isMax_union : forall R a b l m1 m2 r,
  isMax R a l m1 -> isMax R b m2 r -> (l <= m2 /\ m2 <= m1 /\ m1 <= r)%Z ->
  isMax R (Z.max a b) l r.
Proof.
  intros R a b l m1 m2 r [Ua [pa [Pa Ea]]] [Ub [pb [Pb Eb]]] Hm. split.
  - intros p Hp. destruct (Z.lt_ge_cases p m1).
    + pose proof (Ua p ltac:(lia)). lia.
    + pose proof (Ub p ltac:(lia)). lia.
  - destruct (Z.le_ge_cases a b).
    + exists pb. split; [lia|]. lia.
    + exists pa. split; [lia|]. lia.
Qed.

(* Rows 0 .. K-1 of the table: cell (k, i) is the max of R over [i, i + 2^k). *)
Definition tbl_ok (R : Z -> Z) (n K : Z) (T : array int) : Prop :=
  forall k i, (0 <= k < K)%Z -> (0 <= i)%Z -> (i + 2 ^ k <= n)%Z ->
    isMax R (uget T (k * n + i)) i (i + 2 ^ k).

Lemma copy_loop_spec : forall (rs : array int) (n : int) (Ltot : int),
  ((φ n) <= (φ Ltot))%Z ->
  forall z i T H, gap n i = z -> PArray.length T = Ltot -> (0 <= (φ i) <= (φ n))%Z ->
  (forall p, (0 <= p < (φ i))%Z -> uget T p = uget rs p) ->
  PArray.length (copy_loop rs n i T H) = Ltot /\
  forall p, (0 <= p < (φ n))%Z -> uget (copy_loop rs n i T H) p = uget rs p.
Proof.
  intros rs n Ltot HnL z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T H Hz Hlen Hi Hinv.
  rewrite copy_loop_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (HiT : (i <? PArray.length T) = true) by (rewrite Hlen, ltb_spec; lia).
    pose proof (to_Z_bounded n).
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + rewrite alength_set. exact Hlen.
    + lia.
    + intros p Hp. rewrite Hi1 in Hp.
      rewrite uget_set; [ | lia | exact HiT].
      destruct (Z.eqb_spec p (φ i)) as [-> | Ne].
      * apply uget_int.
      * apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact Hlen|]. intros p Hp. apply Hinv. lia.
Qed.

Lemma row_loop_spec : forall (R : Z -> Z) (n Ltot : int) (k : Z) (base prev half lim : int),
  (1 <= k)%Z -> (φ base) = (k * (φ n))%Z -> (φ prev) = ((k - 1) * (φ n))%Z ->
  (φ half) = (2 ^ (k - 1))%Z -> (φ lim) = ((φ n) - 2 ^ k + 1)%Z -> (2 ^ k <= (φ n))%Z ->
  ((k + 1) * (φ n) <= (φ Ltot))%Z ->
  forall z i T H, gap lim i = z -> PArray.length T = Ltot -> (0 <= (φ i) <= (φ lim))%Z ->
  tbl_ok R (φ n) k T ->
  (forall j, (0 <= j < (φ i))%Z -> isMax R (uget T (k * (φ n) + j)) j (j + 2 ^ k)) ->
  PArray.length (row_loop base prev half lim i T H) = Ltot /\
  tbl_ok R (φ n) (k + 1) (row_loop base prev half lim i T H).
Proof.
  intros R n Ltot k base prev half lim Hk Hbase Hprev Hhalf Hlim Hpk HL z.
  pose proof (pow2_pos (k - 1) ltac:(lia)) as Pp.
  assert (Pk : (2 ^ k = 2 * 2 ^ (k - 1))%Z)
    by (replace k with ((k - 1) + 1)%Z at 1 by lia; apply pow2_succ; lia).
  pose proof (to_Z_bounded Ltot) as BL. pose proof (to_Z_bounded n) as Bn.
  assert (Hkn : (k * (φ n) = (k - 1) * (φ n) + (φ n))%Z) by ring.
  assert (Hk1n : ((k + 1) * (φ n) = k * (φ n) + (φ n))%Z) by ring.
  assert (Hpos : (0 <= (k - 1) * (φ n))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T H Hz Hlen Hi Hok Hrow.
  rewrite row_loop_eq.
  destruct (bdec (i <? lim)) as [Hil | Hil].
  - pose proof Hil as Hil'. rewrite ltb_spec in Hil'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Ebi : (φ (base + i)) = (k * (φ n) + (φ i))%Z) by sia.
    assert (Epi : (φ (prev + i)) = ((k - 1) * (φ n) + (φ i))%Z) by sia.
    assert (Epih : (φ (prev + i + half)) = ((k - 1) * (φ n) + ((φ i) + 2 ^ (k - 1)))%Z) by sia.
    assert (HiT : (base + i <? PArray.length T) = true) by (rewrite Hlen, ltb_spec; lia).
    assert (Hold : forall p, (0 <= p < k * (φ n) + (φ i))%Z ->
              uget T.[base + i <- imax T.[prev + i] T.[prev + i + half]] p = uget T p).
    { intros p Hp. rewrite uget_set; [ | lia | exact HiT].
      destruct (Z.eqb_spec p (φ (base + i))); [lia | reflexivity]. }
    eapply IH; [ | reflexivity | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hil.
    + rewrite alength_set. exact Hlen.
    + lia.
    + intros k' i' Hk' Hi' Hn'.
      pose proof (pow2_pos k' ltac:(lia)).
      assert (k' * (φ n) + (φ n) <= k * (φ n))%Z
        by (replace (k' * (φ n) + (φ n))%Z with ((k' + 1) * (φ n))%Z by ring;
            apply Z.mul_le_mono_nonneg_r; lia).
      assert (0 <= k' * (φ n))%Z by (apply Z.mul_nonneg_nonneg; lia).
      rewrite Hold by lia. apply Hok; lia.
    + intros j Hj. rewrite Hi1 in Hj.
      destruct (Z.eq_dec j (φ i)) as [-> | Ne].
      * rewrite uget_set; [ | lia | exact HiT].
        rewrite Ebi, Z.eqb_refl, imax_spec, !uget_int, Epi, Epih.
        apply (isMax_union R _ _ (φ i) ((φ i) + 2 ^ (k - 1)) ((φ i) + 2 ^ (k - 1))).
        -- apply Hok; lia.
        -- replace ((φ i) + 2 ^ k)%Z with ((φ i) + 2 ^ (k - 1) + 2 ^ (k - 1))%Z by lia.
           apply Hok; lia.
        -- lia.
      * rewrite Hold by lia. apply Hrow. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hil.
    split; [exact Hlen|].
    intros k' i' Hk' Hi' Hn'.
    destruct (Z.eq_dec k' k) as [-> | Ne].
    + apply Hrow. lia.
    + apply Hok; lia.
Qed.

Lemma rows_loop_spec : forall (R : Z -> Z) (n L Ltot : int),
  (1 <= (φ n))%Z -> ((φ L) <= 62)%Z -> (2 ^ ((φ L) - 1) <= (φ n))%Z ->
  ((φ L) * (φ n) <= (φ Ltot))%Z -> ((φ Ltot) <= 4194303)%Z ->
  forall z k T H, gap L k = z -> PArray.length T = Ltot -> (1 <= (φ k) <= (φ L))%Z ->
  tbl_ok R (φ n) (φ k) T ->
  tbl_ok R (φ n) (φ L) (rows_loop n L k T H).
Proof.
  intros R n L Ltot Hn HL62 HLn HLt HLt' z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k T H Hz Hlen Hk Hok.
  rewrite rows_loop_eq.
  destruct (bdec (k <? L)) as [HkL | HkL].
  - pose proof HkL as HkL'. rewrite ltb_spec in HkL'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hkm : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
    assert (Hpk : (2 ^ (φ k) <= (φ n))%Z).
    { assert (2 ^ (φ k) <= 2 ^ ((φ L) - 1))%Z by (apply Z.pow_le_mono_r; lia). lia. }
    pose proof (pow2_pos (φ k) ltac:(lia)) as Pk.
    assert (E1 : (φ (1 << k)) = (2 ^ (φ k))%Z) by (apply shl1; lia).
    assert (E2 : (φ (1 << (k - 1))) = (2 ^ ((φ k) - 1))%Z)
      by (rewrite shl1; [rewrite Hkm; reflexivity | lia]).
    assert (Hkn1 : ((φ k) * (φ n) + (φ n) <= (φ L) * (φ n))%Z)
      by (replace ((φ k) * (φ n) + (φ n))%Z with (((φ k) + 1) * (φ n))%Z by ring;
          apply Z.mul_le_mono_nonneg_r; lia).
    assert (Hk1n : (((φ k) + 1) * (φ n) <= (φ Ltot))%Z)
      by (replace (((φ k) + 1) * (φ n))%Z with ((φ k) * (φ n) + (φ n))%Z by ring; lia).
    assert (Hkn0 : (0 <= (φ k) * (φ n))%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Eb : (φ (k * n)) = ((φ k) * (φ n))%Z) by (apply mul_small; rewrite wB_val; lia).
    assert (Ep' : (((φ k) - 1) * (φ n) = (φ k) * (φ n) - (φ n))%Z) by ring.
    assert (Ep : (φ ((k - 1) * n)) = (((φ k) - 1) * (φ n))%Z)
      by (rewrite mul_small, Hkm; [reflexivity | rewrite Hkm, wB_val; lia]).
    assert (El : (φ (n - (1 << k) + 1)) = ((φ n) - 2 ^ (φ k) + 1)%Z) by sia.
    destruct (row_loop_spec R n Ltot (φ k) (k * n) ((k - 1) * n)
                (1 << (k - 1)) (n - (1 << k) + 1) ltac:(lia) Eb Ep E2 El Hpk
                Hk1n _ 0 T
                (Zwf_well_founded 0 (gap (n - (1 << k) + 1) 0)) eq_refl Hlen
                ltac:(change (φ 0) with 0%Z; lia) Hok
                ltac:(change (φ 0) with 0%Z; intros; lia)) as [A B].
    apply (IH _ (ltac:(rewrite <- Hz; apply dec_step; exact HkL)) (k + 1)
             _ (Acc_inv H (dec_step L k HkL)) eq_refl A); [lia|].
    rewrite Hk1. exact B.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in HkL.
    replace (φ L) with (φ k) by lia. exact Hok.
Qed.

Lemma build_spec : forall (rs : array int) (n L : int),
  (1 <= (φ n))%Z -> (1 <= (φ L) <= 62)%Z -> (2 ^ ((φ L) - 1) <= (φ n))%Z ->
  ((φ L) * (φ n) <= 4194303)%Z ->
  tbl_ok (uget rs) (φ n) (φ L) (build rs n L).
Proof.
  intros rs n L Hn HL HLn HLt.
  unfold build.
  assert (Et : (φ (L * n)) = ((φ L) * (φ n))%Z) by (apply mul_small; rewrite wB_val; lia).
  assert (Hm : PArray.length (PArray.make (L * n) 0) = L * n).
  { rewrite alength_make.
    replace (L * n <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (HnLn : ((φ n) <= (φ L) * (φ n))%Z)
    by (rewrite <- (Z.mul_1_l (φ n)) at 1; apply Z.mul_le_mono_nonneg_r; lia).
  destruct (copy_loop_spec rs n (L * n) ltac:(lia) _ 0 (PArray.make (L * n) 0)
              (Zwf_well_founded 0 (gap n 0)) eq_refl Hm
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(change (φ 0) with 0%Z; intros; lia)) as [A B].
  apply (rows_loop_spec (uget rs) n L (L * n) Hn ltac:(lia) HLn ltac:(lia) ltac:(lia)
           _ 1 _ _ eq_refl A ltac:(change (φ 1) with 1%Z; lia)).
  change (φ 1) with 1%Z.
  intros k i Hk Hi Hin. replace k with 0%Z in * by lia.
  change (2 ^ 0)%Z with 1%Z in *. rewrite Z.mul_0_l, Z.add_0_l.
  rewrite B by lia. split.
  - intros p Hp. replace p with i by lia. lia.
  - exists i. split; [lia | reflexivity].
Qed.

Lemma rmq_spec : forall R (T : array int) (n L l r : int),
  tbl_ok R (φ n) (φ L) T -> ((φ n) < 2 ^ (φ L))%Z -> ((φ L) * (φ n) <= 4194303)%Z ->
  (0 <= (φ L))%Z -> ((φ l) < (φ r) <= (φ n))%Z ->
  isMax R (φ (rmq T n l r)) (φ l) (φ r).
Proof.
  intros R T n L l r Hok HnL HLt HL0 Hlr.
  unfold rmq. cbv zeta.
  assert (Erl : (φ (r - l)) = ((φ r) - (φ l))%Z) by sia.
  destruct (lg_spec (r - l) ltac:(lia)) as [Hk0 [Hk1 Hk2]].
  pose proof (lg_le_62 (r - l) ltac:(lia)) as Hk62.
  set (k := lg (r - l)) in *.
  rewrite Erl in Hk1, Hk2.
  assert (HkL : ((φ k) < (φ L))%Z).
  { apply (Z.pow_lt_mono_r_iff 2); lia. }
  rewrite (pow2_succ (φ k) Hk0) in Hk2.
  pose proof (pow2_pos (φ k) Hk0) as Pk.
  assert (Hkn : ((φ k) * (φ n) + (φ n) <= (φ L) * (φ n))%Z)
    by (replace ((φ k) * (φ n) + (φ n))%Z with (((φ k) + 1) * (φ n))%Z by ring;
        apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hkn0 : (0 <= (φ k) * (φ n))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (E1 : (φ (1 << k)) = (2 ^ (φ k))%Z) by (apply shl1; lia).
  assert (Ea : (φ (k * n + l)) = ((φ k) * (φ n) + (φ l))%Z)
    by (apply mul_add_small; rewrite wB_val; lia).
  assert (Erk : (φ (r - (1 << k))) = ((φ r) - 2 ^ (φ k))%Z) by sia.
  assert (Eb : (φ (k * n + (r - (1 << k)))) = ((φ k) * (φ n) + ((φ r) - 2 ^ (φ k)))%Z)
    by (rewrite mul_add_small, Erk; [reflexivity | rewrite Erk, wB_val; lia]).
  rewrite imax_spec, !uget_int, Ea, Eb.
  apply (isMax_union R _ _ (φ l) ((φ l) + 2 ^ (φ k)) ((φ r) - 2 ^ (φ k))).
  - apply Hok; lia.
  - pose proof (Hok (φ k) ((φ r) - 2 ^ (φ k))%Z ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
    replace ((φ r) - 2 ^ (φ k) + 2 ^ (φ k))%Z with (φ r) in Hb by ring. exact Hb.
  - lia.
Qed.

Lemma below_spec : forall R (T : array int) (n L lo j v : int),
  tbl_ok R (φ n) (φ L) T -> ((φ n) < 2 ^ (φ L))%Z -> ((φ L) * (φ n) <= 4194303)%Z ->
  (0 <= (φ L))%Z -> ((φ j) <= (φ n))%Z ->
  below T n lo j v = true <-> (forall p, ((φ lo) <= p < (φ j))%Z -> (R p < (φ v))%Z).
Proof.
  intros R T n L lo j v Hok HnL HLt HL0 Hj.
  unfold below. destruct (lo <? j) eqn:E.
  - rewrite ltb_spec in E.
    destruct (rmq_spec R T n L lo j Hok HnL HLt HL0 ltac:(lia)) as [U [p0 [P0 E0]]].
    rewrite ltb_spec. split.
    + intros Hv p Hp. pose proof (U p Hp). lia.
    + intros Hall. pose proof (Hall p0 P0). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
    split; [intros _ p Hp; lia | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: the three answers, decided from two binary searches      *)
(* ------------------------------------------------------------------ *)

Definition nz {A} (l : list A) : Z := Z.of_nat (List.length l).
Definition yv (ys : list Z) (p : Z) : Z := nth (Z.to_nat p) ys 0%Z.
Definition rv (rs : list N) (p : Z) : N := nth (Z.to_nat p) rs 0%N.
(* index k is in range and holds year K *)
Definition atk (ys : list Z) (k K : Z) : Prop := (0 <= k < nz ys)%Z /\ yv ys k = K.
(* the rain of indices lo .. j-1 is below v *)
Definition cv (rs : list N) (lo j : Z) (v : N) : Prop :=
  forall p, (lo <= p < j)%Z -> (rv rs p < v)%N.

(* The rain of year z, if known (a Prop-side helper, never extracted). *)
Fixpoint lookup (ys : list Z) (rs : list N) (z : Z) : option N :=
  match ys, rs with
  | y :: ys', r :: rs' => if Z.eqb y z then Some r else lookup ys' rs' z
  | _, _ => None
  end.

Lemma lookup_some : forall ys rs z v, lookup ys rs z = Some v ->
  exists k, (k < List.length ys)%nat /\ nth k ys 0%Z = z /\ nth k rs 0%N = v.
Proof.
  induction ys as [|a ys IH]; intros rs z v H; [discriminate|].
  destruct rs as [|b rs]; [discriminate|]. simpl in H.
  destruct (Z.eqb_spec a z) as [E|E].
  - injection H as <-. exists 0%nat. simpl. split; [lia|]. split; [exact E | reflexivity].
  - destruct (IH rs z v H) as (k & Hk & E1 & E2). exists (S k). simpl.
    split; [lia|]. split; assumption.
Qed.

Lemma lookup_in : forall ys rs z, List.length rs = List.length ys -> In z ys ->
  exists v, lookup ys rs z = Some v.
Proof.
  induction ys as [|a ys IH]; intros rs z Hl Hin; [destruct Hin|].
  destruct rs as [|b rs]; [simpl in Hl; discriminate|]. simpl.
  destruct (Z.eqb_spec a z) as [E|E]; [eauto|].
  destruct Hin as [Hin|Hin]; [contradiction|].
  apply IH; [simpl in Hl; lia | exact Hin].
Qed.

Lemma ans_T : forall ys rs Y X,
  is_true ys rs Y X -> might_be_true ys rs Y X -> answers ys rs Y X Ans_true.
Proof.
  intros ys rs Y X H1 H2. unfold answers.
  split; [split; [intros _; exact H1 | intros _; reflexivity]|].
  split; split; [discriminate | intros [A _]; contradiction
                | discriminate | intros A; contradiction].
Qed.

Lemma ans_M : forall ys rs Y X,
  ~ is_true ys rs Y X -> might_be_true ys rs Y X -> answers ys rs Y X Ans_maybe.
Proof.
  intros ys rs Y X H1 H2. unfold answers.
  split; [split; [discriminate | intros A; contradiction]|].
  split; [split; [intros _; split; assumption | intros _; reflexivity]
         | split; [discriminate | intros A; contradiction]].
Qed.

Lemma ans_F : forall ys rs Y X,
  ~ might_be_true ys rs Y X -> ~ is_true ys rs Y X -> answers ys rs Y X Ans_false.
Proof.
  intros ys rs Y X H2 H1. unfold answers.
  split; [split; [discriminate | intros A; contradiction]|].
  split; [split; [discriminate | intros [_ A]; contradiction]
         | split; [intros _; exact H2 | intros _; reflexivity]].
Qed.

Definition ans_of (yk xk cmp cA eq cB : bool) : answer :=
  if yk then
    if xk then
      if cmp then
        if cA then (if eq then Ans_true else Ans_maybe)
        else Ans_false
      else Ans_false
    else if cB then Ans_maybe else Ans_false
  else if xk then (if cA then Ans_maybe else Ans_false)
  else Ans_maybe.

Section Math.
Variables (ys : list Z) (rs : list N).
Hypothesis Hrs : List.length rs = List.length ys.
Hypothesis Hinc : forall p, (0 <= p)%Z -> (p + 1 < nz ys)%Z -> (yv ys p < yv ys (p + 1))%Z.
Hypothesis Hrain : forall p, (0 <= p < nz ys)%Z -> (1 <= rv rs p <= 10 ^ 9)%N.

Lemma ygap : forall p q, (0 <= p <= q)%Z -> (q < nz ys)%Z ->
  (q - p <= yv ys q - yv ys p)%Z.
Proof.
  intros p q Hpq Hq.
  assert (G : forall d : nat, (p + Z.of_nat d < nz ys)%Z ->
            (Z.of_nat d <= yv ys (p + Z.of_nat d) - yv ys p)%Z).
  { induction d as [|d IH]; intros Hd.
    - rewrite Z.add_0_r. lia.
    - pose proof (IH ltac:(lia)).
      pose proof (Hinc (p + Z.of_nat d) ltac:(lia) ltac:(lia)).
      replace (p + Z.of_nat (S d))%Z with (p + Z.of_nat d + 1)%Z by lia. lia. }
  pose proof (G (Z.to_nat (q - p)) ltac:(lia)) as Gq.
  replace (p + Z.of_nat (Z.to_nat (q - p)))%Z with q in Gq by lia. lia.
Qed.

Lemma yinj : forall p q, (0 <= p < nz ys)%Z -> (0 <= q < nz ys)%Z ->
  yv ys p = yv ys q -> p = q.
Proof.
  intros p q Hp Hq E. destruct (Z.lt_trichotomy p q) as [L|[L|L]].
  - pose proof (ygap p q ltac:(lia) ltac:(lia)). lia.
  - exact L.
  - pose proof (ygap q p ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma known_iff : forall z,
  known ys z <-> exists p, (0 <= p < nz ys)%Z /\ yv ys p = z.
Proof.
  intros z. unfold known, yv, nz. split.
  - intros Hin. destruct (In_nth ys z 0%Z Hin) as (k & Hk & E).
    exists (Z.of_nat k). rewrite Nat2Z.id. split; [lia | exact E].
  - intros (p & Hp & E). rewrite <- E. apply nth_In. lia.
Qed.

Lemma assign_iff : forall f, assignment ys rs f <->
  forall p, (0 <= p < nz ys)%Z -> f (yv ys p) = rv rs p.
Proof.
  intros f. unfold assignment, at_, len, yv, rv, nz. split.
  - intros H p Hp. pose proof (H (Z.to_N p) ltac:(lia)) as E.
    replace (N.to_nat (Z.to_N p)) with (Z.to_nat p) in E by lia. exact E.
  - intros H i Hi. pose proof (H (Z.of_N i) ltac:(lia)) as E.
    replace (Z.to_nat (Z.of_N i)) with (N.to_nat i) in E by lia. exact E.
Qed.

Lemma lookup_some_Z : forall z v, lookup ys rs z = Some v ->
  exists p, (0 <= p < nz ys)%Z /\ yv ys p = z /\ v = rv rs p.
Proof.
  intros z v H. destruct (lookup_some ys rs z v H) as (k & Hk & E1 & E2).
  exists (Z.of_nat k). unfold yv, rv, nz. rewrite Nat2Z.id.
  split; [lia|]. split; [exact E1 | symmetry; exact E2].
Qed.

Lemma lookup_none : forall z, ~ known ys z -> lookup ys rs z = None.
Proof.
  intros z Hk. destruct (lookup ys rs z) eqn:E; [|reflexivity].
  exfalso. apply Hk. destruct (lookup_some_Z z n E) as (p & Hp & Ey & _).
  apply known_iff. eauto.
Qed.

(* an assignment: the known rain, g elsewhere *)
Definition ext (g : Z -> N) (z : Z) : N :=
  match lookup ys rs z with Some v => v | None => g z end.

Lemma ext_known : forall g p, (0 <= p < nz ys)%Z -> ext g (yv ys p) = rv rs p.
Proof.
  intros g p Hp. unfold ext.
  assert (Hin : known ys (yv ys p)) by (apply known_iff; eauto).
  destruct (lookup_in ys rs (yv ys p) Hrs Hin) as [v Ev]. rewrite Ev.
  destruct (lookup_some_Z _ _ Ev) as (q & Hq & Eq & ->).
  f_equal. apply yinj; assumption.
Qed.

Lemma ext_assign : forall g, assignment ys rs (ext g).
Proof. intros g. apply assign_iff. intros p Hp. apply ext_known. exact Hp. Qed.

Lemma lb_known : forall K k0, (0 <= k0 <= nz ys)%Z ->
  (forall p, (0 <= p < k0)%Z -> (yv ys p < K)%Z) ->
  (forall p, (k0 <= p < nz ys)%Z -> (K <= yv ys p)%Z) ->
  (known ys K <-> atk ys k0 K).
Proof.
  intros K k0 Hk Hb Ha. unfold atk. rewrite known_iff. split.
  - intros (p & Hp & E).
    destruct (Z.lt_trichotomy p k0) as [L|[L|L]].
    + pose proof (Hb p ltac:(lia)). lia.
    + subst p. split; [lia|]. exact E.
    + pose proof (Ha k0 ltac:(lia)). pose proof (ygap k0 p ltac:(lia) ltac:(lia)). lia.
  - intros [Hk0 E]. exists k0. split; assumption.
Qed.

Lemma atk_dec : forall k K, {atk ys k K} + {~ atk ys k K}.
Proof.
  intros k K. unfold atk.
  destruct (Z_le_dec 0 k) as [H0|H0]; [|right; intros [A B]; lia].
  destruct (Z_lt_le_dec k (nz ys)) as [H1|H1]; [|right; intros [A B]; lia].
  destruct (Z.eq_dec (yv ys k) K) as [H2|H2]; [left; split; [lia | exact H2]|].
  right. intros [A B]. contradiction.
Qed.

Lemma is_true_might : forall Y X, is_true ys rs Y X -> might_be_true ys rs Y X.
Proof.
  intros Y X [_ H]. exists (ext (fun _ => 0%N)).
  split; [apply ext_assign | apply H, ext_assign].
Qed.

Lemma count_iff : forall i j, (0 <= i <= j)%Z -> (j < nz ys)%Z ->
  ((forall z, (yv ys i <= z <= yv ys j)%Z -> known ys z) <->
   (j - i = yv ys j - yv ys i)%Z).
Proof.
  intros i j Hij Hj. split.
  - intros Hall.
    pose proof (ygap i j Hij Hj) as Gij.
    assert (G : forall d : nat, (Z.of_nat d <= yv ys j - yv ys i)%Z ->
              (i + Z.of_nat d <= j)%Z /\
              yv ys (i + Z.of_nat d) = (yv ys i + Z.of_nat d)%Z).
    { induction d as [|d IH]; intros Hd.
      - rewrite Z.add_0_r. split; lia.
      - destruct (IH ltac:(lia)) as [A B].
        destruct (proj1 (known_iff _) (Hall (yv ys i + Z.of_nat d + 1)%Z ltac:(lia)))
          as (q & Hq & Eq).
        assert (Hq1 : (i + Z.of_nat d < q)%Z).
        { destruct (Z.lt_ge_cases (i + Z.of_nat d) q) as [|G]; [assumption|].
          pose proof (ygap q (i + Z.of_nat d) ltac:(lia) ltac:(lia)). lia. }
        assert (Hqj : (q <= j)%Z).
        { destruct (Z.le_gt_cases q j) as [|G]; [assumption|].
          pose proof (ygap j q ltac:(lia) ltac:(lia)). lia. }
        assert (Hq2 : (q <= i + Z.of_nat d + 1)%Z).
        { destruct (Z.le_gt_cases q (i + Z.of_nat d + 1)) as [|G]; [assumption|].
          pose proof (ygap (i + Z.of_nat d + 1) q ltac:(lia) ltac:(lia)).
          pose proof (Hinc (i + Z.of_nat d) ltac:(lia) ltac:(lia)). lia. }
        replace (i + Z.of_nat (S d))%Z with q by lia. split; lia. }
    destruct (G (Z.to_nat (yv ys j - yv ys i)) ltac:(lia)) as [A B].
    assert (E : (i + Z.of_nat (Z.to_nat (yv ys j - yv ys i)))%Z = j)
      by (apply yinj; [lia | lia | rewrite B; lia]).
    lia.
  - intros E z Hz. apply known_iff. exists (i + (z - yv ys i))%Z.
    pose proof (ygap i (i + (z - yv ys i)) ltac:(lia) ltac:(lia)).
    pose proof (ygap (i + (z - yv ys i)) j ltac:(lia) ltac:(lia)).
    split; lia.
Qed.

Section Query.
Variables (Y X i j lo : Z).
Hypothesis HYX : (Y < X)%Z.
Hypothesis Hi : (0 <= i <= nz ys)%Z.
Hypothesis Hib : forall p, (0 <= p < i)%Z -> (yv ys p < Y)%Z.
Hypothesis Hia : forall p, (i <= p < nz ys)%Z -> (Y <= yv ys p)%Z.
Hypothesis Hj : (0 <= j <= nz ys)%Z.
Hypothesis Hjb : forall p, (0 <= p < j)%Z -> (yv ys p < X)%Z.
Hypothesis Hja : forall p, (j <= p < nz ys)%Z -> (X <= yv ys p)%Z.
Hypothesis Hlo1 : atk ys i Y -> lo = (i + 1)%Z.
Hypothesis Hlo2 : ~ atk ys i Y -> lo = i.

Lemma kY : known ys Y <-> atk ys i Y.
Proof. apply lb_known; assumption. Qed.

Lemma kX : known ys X <-> atk ys j X.
Proof. apply lb_known; assumption. Qed.

Lemma btw_fwd : forall p, (lo <= p < j)%Z ->
  (0 <= p < nz ys)%Z /\ (Y < yv ys p < X)%Z.
Proof.
  intros p Hp.
  destruct (atk_dec i Y) as [K|K].
  - rewrite (Hlo1 K) in Hp. destruct K as [K1 K2].
    pose proof (Hjb p ltac:(lia)).
    pose proof (ygap i p ltac:(lia) ltac:(lia)). split; [lia|]. split; lia.
  - rewrite (Hlo2 K) in Hp.
    pose proof (Hjb p ltac:(lia)). pose proof (Hia p ltac:(lia)).
    split; [lia|]. split; [|lia].
    destruct (Z.eq_dec (yv ys p) Y) as [E|E]; [|lia].
    exfalso. apply K. apply kY. apply known_iff. exists p. split; [lia | exact E].
Qed.

Lemma btw_bwd : forall p, (0 <= p < nz ys)%Z -> (Y < yv ys p < X)%Z -> (lo <= p < j)%Z.
Proof.
  intros p Hp Hy.
  assert (Hip : (i <= p)%Z)
    by (destruct (Z.lt_ge_cases p i) as [L|L];
        [pose proof (Hib p ltac:(lia)); lia | exact L]).
  assert (Hpj : (p < j)%Z)
    by (destruct (Z.lt_ge_cases p j) as [L|L];
        [exact L | pose proof (Hja p ltac:(lia)); lia]).
  destruct (atk_dec i Y) as [K|K].
  - rewrite (Hlo1 K). destruct K as [K1 K2].
    destruct (Z.eq_dec p i) as [->|Ne]; lia.
  - rewrite (Hlo2 K). lia.
Qed.

Lemma cv_of_mrs : forall f v, assignment ys rs f ->
  (forall z, (Y < z < X)%Z -> (f z < v)%N) -> cv rs lo j v.
Proof.
  intros f v Ha H p Hp. destruct (btw_fwd p Hp) as [Hp1 Hp2].
  rewrite assign_iff in Ha. rewrite <- (Ha p Hp1). apply H. exact Hp2.
Qed.

Lemma ext_btw : forall g v, cv rs lo j v ->
  (forall z, (Y < z < X)%Z -> lookup ys rs z = None -> (g z < v)%N) ->
  forall z, (Y < z < X)%Z -> (ext g z < v)%N.
Proof.
  intros g v Hc Hg z Hz. unfold ext. destruct (lookup ys rs z) eqn:E.
  - destruct (lookup_some_Z z n E) as (p & Hp & Ey & ->).
    apply Hc. apply btw_bwd; [exact Hp | rewrite Ey; exact Hz].
  - apply Hg; assumption.
Qed.

Lemma might_A : atk ys i Y -> atk ys j X ->
  (might_be_true ys rs Y X <->
   (rv rs j <= rv rs i)%N /\ cv rs lo j (rv rs j)).
Proof.
  intros [Hi1 Ei] [Hj1 Ej]. split.
  - intros (f & Ha & H1 & H2). pose proof Ha as Ha'. rewrite assign_iff in Ha'.
    assert (FY : f Y = rv rs i) by (rewrite <- Ei; apply Ha'; lia).
    assert (FX : f X = rv rs j) by (rewrite <- Ej; apply Ha'; lia).
    split; [lia|].
    apply (cv_of_mrs f _ Ha). intros z Hz. pose proof (H2 z Hz). lia.
  - intros [C1 C2]. exists (ext (fun _ => 0%N)). split; [apply ext_assign|].
    assert (EY : ext (fun _ => 0%N) Y = rv rs i) by (rewrite <- Ei; apply ext_known; lia).
    assert (EX : ext (fun _ => 0%N) X = rv rs j) by (rewrite <- Ej; apply ext_known; lia).
    unfold most_rain_since. rewrite EY, EX. split; [exact C1|].
    apply (ext_btw _ _ C2). intros z0 _ _. pose proof (Hrain j ltac:(lia)). cbv beta. lia.
Qed.

Lemma true_A : atk ys i Y -> atk ys j X ->
  (is_true ys rs Y X <->
   (j - i = X - Y)%Z /\ (rv rs j <= rv rs i)%N /\ cv rs lo j (rv rs j)).
Proof.
  intros KY KX. pose proof KY as [Hi1 Ei]. pose proof KX as [Hj1 Ej].
  assert (Hij : (i < j)%Z)
    by (destruct (Z.lt_ge_cases i j) as [|G];
        [assumption | pose proof (ygap j i ltac:(lia) ltac:(lia)); lia]).
  pose proof (count_iff i j ltac:(lia) ltac:(lia)) as Cnt. rewrite Ei, Ej in Cnt.
  split.
  - intros Ht. split; [apply Cnt; exact (proj1 Ht)|].
    apply (might_A KY KX). apply is_true_might. exact Ht.
  - intros (E & C1 & C2). split; [apply Cnt; exact E|].
    intros f Ha. pose proof Ha as Ha'. rewrite assign_iff in Ha'.
    assert (FY : f Y = rv rs i) by (rewrite <- Ei; apply Ha'; lia).
    assert (FX : f X = rv rs j) by (rewrite <- Ej; apply Ha'; lia).
    unfold most_rain_since. rewrite FY, FX. split; [exact C1|].
    intros z Hz.
    destruct (proj1 (known_iff z) (proj2 Cnt E z ltac:(lia))) as (p & Hp & Ey).
    rewrite <- Ey, Ha' by exact Hp. apply C2.
    apply btw_bwd; [exact Hp | rewrite Ey; exact Hz].
Qed.

Lemma not_true_X : ~ atk ys j X -> ~ is_true ys rs Y X.
Proof. intros KX [Hall _]. apply KX. apply kX. apply Hall. lia. Qed.

Lemma not_true_Y : ~ atk ys i Y -> ~ is_true ys rs Y X.
Proof. intros KY [Hall _]. apply KY. apply kY. apply Hall. lia. Qed.

Lemma might_B : atk ys i Y -> ~ atk ys j X ->
  (might_be_true ys rs Y X <-> cv rs lo j (rv rs i)).
Proof.
  intros [Hi1 Ei] KX. split.
  - intros (f & Ha & H1 & H2). pose proof Ha as Ha'. rewrite assign_iff in Ha'.
    assert (FY : f Y = rv rs i) by (rewrite <- Ei; apply Ha'; lia).
    apply (cv_of_mrs f _ Ha). intros z Hz. pose proof (H2 z Hz). lia.
  - intros C. set (g := fun z => if Z.eqb z X then rv rs i else 0%N).
    exists (ext g). split; [apply ext_assign|].
    assert (EY : ext g Y = rv rs i) by (rewrite <- Ei; apply ext_known; lia).
    assert (EX : ext g X = rv rs i).
    { unfold ext. rewrite lookup_none.
      - unfold g. rewrite Z.eqb_refl. reflexivity.
      - intro K. apply KX. apply kX. exact K. }
    unfold most_rain_since. rewrite EY, EX. split; [lia|].
    apply (ext_btw _ _ C). intros z Hz _. unfold g.
    destruct (Z.eqb_spec z X); [lia|]. pose proof (Hrain i ltac:(lia)). lia.
Qed.

Lemma might_C : ~ atk ys i Y -> atk ys j X ->
  (might_be_true ys rs Y X <-> cv rs lo j (rv rs j)).
Proof.
  intros KY [Hj1 Ej]. split.
  - intros (f & Ha & H1 & H2). pose proof Ha as Ha'. rewrite assign_iff in Ha'.
    assert (FX : f X = rv rs j) by (rewrite <- Ej; apply Ha'; lia).
    apply (cv_of_mrs f _ Ha). intros z Hz. pose proof (H2 z Hz). lia.
  - intros C. set (g := fun z => if Z.eqb z Y then rv rs j else 0%N).
    exists (ext g). split; [apply ext_assign|].
    assert (EX : ext g X = rv rs j) by (rewrite <- Ej; apply ext_known; lia).
    assert (EY : ext g Y = rv rs j).
    { unfold ext. rewrite lookup_none.
      - unfold g. rewrite Z.eqb_refl. reflexivity.
      - intro K. apply KY. apply kY. exact K. }
    unfold most_rain_since. rewrite EY, EX. split; [lia|].
    apply (ext_btw _ _ C). intros z Hz _. unfold g.
    destruct (Z.eqb_spec z Y); [lia|]. pose proof (Hrain j ltac:(lia)). lia.
Qed.

Lemma might_D : ~ atk ys i Y -> ~ atk ys j X -> might_be_true ys rs Y X.
Proof.
  intros KY KX.
  set (g := fun z => if Z.eqb z X then (10 ^ 9 + 1)%N
                     else if Z.eqb z Y then (10 ^ 9 + 1)%N else 0%N).
  exists (ext g). split; [apply ext_assign|].
  assert (EX : ext g X = (10 ^ 9 + 1)%N).
  { unfold ext. rewrite lookup_none.
    - unfold g. rewrite Z.eqb_refl. reflexivity.
    - intro H. apply KX. apply kX. exact H. }
  assert (EY : ext g Y = (10 ^ 9 + 1)%N).
  { unfold ext. rewrite lookup_none.
    - unfold g. destruct (Z.eqb_spec Y X); [lia|]. rewrite Z.eqb_refl. reflexivity.
    - intro H. apply KY. apply kY. exact H. }
  unfold most_rain_since. rewrite EY, EX. split; [lia|].
  intros z Hz. unfold ext. destruct (lookup ys rs z) eqn:E.
  - destruct (lookup_some_Z z n E) as (p & Hp & _ & ->). pose proof (Hrain p Hp). lia.
  - unfold g. destruct (Z.eqb_spec z X); [lia|]. destruct (Z.eqb_spec z Y); [lia|]. lia.
Qed.

Lemma ans_of_correct : forall yk xk cmp cA eq cB : bool,
  (yk = true <-> atk ys i Y) -> (xk = true <-> atk ys j X) ->
  (atk ys i Y -> atk ys j X -> (cmp = true <-> (rv rs j <= rv rs i)%N)) ->
  (atk ys j X -> (cA = true <-> cv rs lo j (rv rs j))) ->
  (atk ys i Y -> (cB = true <-> cv rs lo j (rv rs i))) ->
  (atk ys i Y -> atk ys j X -> (eq = true <-> (j - i = X - Y)%Z)) ->
  answers ys rs Y X (ans_of yk xk cmp cA eq cB).
Proof.
  intros yk xk cmp cA eq cB Hyk Hxk Hcmp HcA HcB Heq. unfold ans_of.
  destruct yk.
  - assert (KY : atk ys i Y) by (apply Hyk; reflexivity).
    destruct xk.
    + assert (KX : atk ys j X) by (apply Hxk; reflexivity).
      pose proof (might_A KY KX) as MA. pose proof (true_A KY KX) as TA.
      specialize (Hcmp KY KX). specialize (HcA KX). specialize (Heq KY KX).
      destruct cmp.
      * destruct cA.
        -- destruct eq.
           ++ assert (Ht : is_true ys rs Y X).
              { apply TA. split; [apply Heq; reflexivity|].
                split; [apply Hcmp | apply HcA]; reflexivity. }
              apply ans_T; [exact Ht | apply is_true_might; exact Ht].
           ++ apply ans_M.
              ** intros Ht. apply TA in Ht. destruct Ht as [E _].
                 apply Heq in E. discriminate.
              ** apply MA. split; [apply Hcmp | apply HcA]; reflexivity.
        -- apply ans_F; [|intros Ht; apply is_true_might in Ht; revert Ht].
           all: intros Hm; apply MA in Hm; destruct Hm as [_ C];
                apply HcA in C; discriminate.
      * apply ans_F; [|intros Ht; apply is_true_might in Ht; revert Ht].
        all: intros Hm; apply MA in Hm; destruct Hm as [C _];
             apply Hcmp in C; discriminate.
    + assert (KX : ~ atk ys j X) by (intro K; apply Hxk in K; discriminate).
      pose proof (might_B KY KX) as MB. specialize (HcB KY).
      destruct cB.
      * apply ans_M; [apply not_true_X; exact KX | apply MB, HcB; reflexivity].
      * apply ans_F; [|apply not_true_X; exact KX].
        intros Hm. apply MB in Hm. apply HcB in Hm. discriminate.
  - assert (KY : ~ atk ys i Y) by (intro K; apply Hyk in K; discriminate).
    destruct xk.
    + assert (KX : atk ys j X) by (apply Hxk; reflexivity).
      pose proof (might_C KY KX) as MC. specialize (HcA KX).
      destruct cA.
      * apply ans_M; [apply not_true_Y; exact KY | apply MC, HcA; reflexivity].
      * apply ans_F; [|apply not_true_Y; exact KY].
        intros Hm. apply MC in Hm. apply HcA in Hm. discriminate.
    + assert (KX : ~ atk ys j X) by (intro K; apply Hxk in K; discriminate).
      apply ans_M; [apply not_true_Y; exact KY | apply might_D; assumption].
Qed.

End Query.
End Math.

(* ------------------------------------------------------------------ *)
(* One query, on the machine                                           *)
(* ------------------------------------------------------------------ *)

Lemma answer_query_spec : forall (ys : list Z) (rs : list N) (ys' rs' T : array int) (n L : int),
  List.length rs = List.length ys ->
  (forall p, (0 <= p)%Z -> (p + 1 < nz ys)%Z -> (yv ys p < yv ys (p + 1))%Z) ->
  (forall p, (0 <= p < nz ys)%Z -> (1 <= rv rs p <= 10 ^ 9)%N) ->
  (φ n) = nz ys ->
  (forall p, (0 <= p < nz ys)%Z -> sget ys' p = yv ys p) ->
  (forall p, (0 <= p < nz ys)%Z -> uget rs' p = Z.of_N (rv rs p)) ->
  tbl_ok (uget rs') (φ n) (φ L) T -> ((φ n) < 2 ^ (φ L))%Z ->
  ((φ L) * (φ n) <= 4194303)%Z -> (0 <= (φ L))%Z ->
  forall Yq Xq : int,
  (- 10 ^ 9 <= Sint63.to_Z Yq)%Z -> (Sint63.to_Z Yq < Sint63.to_Z Xq)%Z ->
  (Sint63.to_Z Xq <= 10 ^ 9)%Z ->
  answers ys rs (Sint63.to_Z Yq) (Sint63.to_Z Xq) (answer_query ys' rs' T n Yq Xq).
Proof.
  intros ys rs ys' rs' T n L Hrs Hinc Hrain Hn Hys Hrs' Hok HnL HLt HL0 Yq Xq HY HYX HX.
  assert (Hmono : forall p q, (0 <= p <= q)%Z -> (q < (φ n))%Z ->
                  (sget ys' p <= sget ys' q)%Z).
  { intros p q Hpq Hq. rewrite !Hys by lia.
    pose proof (ygap ys rs Hrs Hinc p q Hpq ltac:(lia)). lia. }
  pose proof (to_Z_bounded n) as Bn.
  destruct (lb_loop_spec ys' (φ n) Yq Hmono _ 0 n (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(lia)
              ltac:(change (φ 0) with 0%Z; intros; lia) ltac:(intros; lia)) as (Ai & Bi & Ci).
  destruct (lb_loop_spec ys' (φ n) Xq Hmono _ 0 n (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(lia)
              ltac:(change (φ 0) with 0%Z; intros; lia) ltac:(intros; lia)) as (Aj & Bj & Cj).
  change (φ 0) with 0%Z in Ai, Aj.
  unfold answer_query, lower_bound. cbv zeta.
  set (i := lb_loop ys' Yq 0 n (Zwf_well_founded 0 (gap n 0))) in *.
  set (j := lb_loop ys' Xq 0 n (Zwf_well_founded 0 (gap n 0))) in *.
  assert (Hib : forall p, (0 <= p < (φ i))%Z -> (yv ys p < Sint63.to_Z Yq)%Z)
    by (intros p Hp; rewrite <- Hys by lia; apply Bi; lia).
  assert (Hia : forall p, ((φ i) <= p < nz ys)%Z -> (Sint63.to_Z Yq <= yv ys p)%Z)
    by (intros p Hp; rewrite <- Hys by lia; apply Ci; lia).
  assert (Hjb : forall p, (0 <= p < (φ j))%Z -> (yv ys p < Sint63.to_Z Xq)%Z)
    by (intros p Hp; rewrite <- Hys by lia; apply Bj; lia).
  assert (Hja : forall p, ((φ j) <= p < nz ys)%Z -> (Sint63.to_Z Xq <= yv ys p)%Z)
    by (intros p Hp; rewrite <- Hys by lia; apply Cj; lia).
  assert (Hij : ((φ i) <= (φ j))%Z).
  { destruct (Z.le_gt_cases (φ i) (φ j)) as [|G]; [assumption|].
    pose proof (Hib (φ j) ltac:(lia)). pose proof (Hja (φ j) ltac:(lia)). lia. }
  assert (Hyk : (if i <? n then ys'.[i] =? Yq else false) = true
                <-> atk ys (φ i) (Sint63.to_Z Yq)).
  { unfold atk. destruct (i <? n) eqn:E.
    - rewrite ltb_spec in E. rewrite eqb_spec. split.
      + intros Ee. split; [lia|]. rewrite <- Hys by lia. rewrite <- sget_int, Ee.
        reflexivity.
      + intros [_ Ee]. apply Sint63.to_Z_inj. rewrite sget_int, Hys by lia. exact Ee.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
      split; [discriminate | intros [A _]; lia]. }
  assert (Hxk : (if j <? n then ys'.[j] =? Xq else false) = true
                <-> atk ys (φ j) (Sint63.to_Z Xq)).
  { unfold atk. destruct (j <? n) eqn:E.
    - rewrite ltb_spec in E. rewrite eqb_spec. split.
      + intros Ee. split; [lia|]. rewrite <- Hys by lia. rewrite <- sget_int, Ee.
        reflexivity.
      + intros [_ Ee]. apply Sint63.to_Z_inj. rewrite sget_int, Hys by lia. exact Ee.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
      split; [discriminate | intros [A _]; lia]. }
  set (yk := if i <? n then ys'.[i] =? Yq else false) in *.
  set (xk := if j <? n then ys'.[j] =? Xq else false) in *.
  set (lo := if yk then i + 1 else i).
  assert (Hlo1 : atk ys (φ i) (Sint63.to_Z Yq) -> (φ lo) = ((φ i) + 1)%Z).
  { intros K. pose proof K as [K1 _]. apply Hyk in K. unfold lo. rewrite K.
    rewrite add_spec. change (φ 1) with 1%Z. apply Z.mod_small. lia. }
  assert (Hlo2 : ~ atk ys (φ i) (Sint63.to_Z Yq) -> (φ lo) = (φ i)).
  { intros K. unfold lo. destruct yk; [exfalso; apply K, Hyk; reflexivity | reflexivity]. }
  assert (Hlo0 : (0 <= (φ lo))%Z) by (pose proof (to_Z_bounded lo); lia).
  assert (Hbelow : forall (k : int), (0 <= (φ k) < nz ys)%Z ->
            below T n lo j rs'.[k] = true <-> cv rs (φ lo) (φ j) (rv rs (φ k))).
  { intros k Hk. rewrite (below_spec (uget rs') T n L lo j _ Hok HnL HLt HL0 ltac:(lia)).
    unfold cv. rewrite uget_int, (Hrs' (φ k) Hk). split.
    - intros H p Hp. specialize (H p Hp). rewrite Hrs' in H by lia. lia.
    - intros H p Hp. specialize (H p Hp). rewrite Hrs' by lia. lia. }
  assert (EXY : (φ (Xq - Yq)) = (Sint63.to_Z Xq - Sint63.to_Z Yq)%Z).
  { rewrite sub_spec, <- (Sint63.to_Z_mod_Uint63to_Z Xq),
      <- (Sint63.to_Z_mod_Uint63to_Z Yq), <- Zminus_mod.
    apply Z.mod_small. rewrite wB_val. lia. }
  assert (Eji : (φ (j - i)) = ((φ j) - (φ i))%Z)
    by (rewrite sub_spec; apply Z.mod_small; lia).
  change (answers ys rs (Sint63.to_Z Yq) (Sint63.to_Z Xq)
            (ans_of yk xk (rs'.[j] <=? rs'.[i]) (below T n lo j rs'.[j])
               (j - i =? Xq - Yq) (below T n lo j rs'.[i]))).
  apply (ans_of_correct ys rs Hrs Hinc Hrain (Sint63.to_Z Yq) (Sint63.to_Z Xq)
           (φ i) (φ j) (φ lo) HYX ltac:(lia) Hib Hia ltac:(lia) Hjb Hja Hlo1 Hlo2
           _ _ _ _ _ _ Hyk Hxk).
  - intros [Ki _] [Kj _]. rewrite leb_spec, !uget_int, !Hrs' by lia. lia.
  - intros [Kj _]. apply Hbelow. lia.
  - intros [Ki _]. apply Hbelow. lia.
  - intros _ _. rewrite eqb_spec. split.
    + intros E. rewrite <- Eji, <- EXY, E. reflexivity.
    + intros E. apply to_Z_inj. rewrite Eji, EXY. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* The query loop                                                      *)
(* ------------------------------------------------------------------ *)

Lemma q_loop_spec : forall (ys : list Z) (rs : list N) (ys' rs' T qy' qx' : array int)
    (n : int) (qy qx : list Z) (m : int),
  (forall Yq Xq : int,
     (- 10 ^ 9 <= Sint63.to_Z Yq)%Z -> (Sint63.to_Z Yq < Sint63.to_Z Xq)%Z ->
     (Sint63.to_Z Xq <= 10 ^ 9)%Z ->
     answers ys rs (Sint63.to_Z Yq) (Sint63.to_Z Xq) (answer_query ys' rs' T n Yq Xq)) ->
  (φ m) = nz qy ->
  (forall p, (0 <= p < nz qy)%Z -> sget qy' p = yv qy p) ->
  (forall p, (0 <= p < nz qy)%Z -> sget qx' p = yv qx p) ->
  (forall p, (0 <= p < nz qy)%Z ->
     (- 10 ^ 9 <= yv qy p)%Z /\ (yv qy p < yv qx p)%Z /\ (yv qx p <= 10 ^ 9)%Z) ->
  forall z k out H, gap m k = z -> PArray.length out = m -> (0 <= (φ k) <= (φ m))%Z ->
  (forall p, (0 <= p < (φ k))%Z -> answers ys rs (yv qy p) (yv qx p) out.[of_Z p]) ->
  PArray.length (q_loop ys' rs' T qy' qx' n m k out H) = m /\
  forall p, (0 <= p < (φ m))%Z ->
    answers ys rs (yv qy p) (yv qx p) (q_loop ys' rs' T qy' qx' n m k out H).[of_Z p].
Proof.
  intros ys rs ys' rs' T qy' qx' n qy qx m HQ Hm Hqy Hqx Hb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k out H Hz Hlen Hk Hinv.
  rewrite q_loop_eq.
  destruct (bdec (k <? m)) as [Hkm | Hkm].
  - pose proof Hkm as Hkm'. rewrite ltb_spec in Hkm'.
    pose proof (to_Z_bounded m) as Bm.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z)
      by (rewrite add_spec; change (φ 1) with 1%Z; apply Z.mod_small; lia).
    assert (HkT : (k <? PArray.length out) = true) by (rewrite Hlen; exact Hkm).
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hkm.
    + rewrite qlength_set. exact Hlen.
    + lia.
    + intros p Hp. rewrite Hk1 in Hp.
      destruct (Z.eq_dec p (φ k)) as [-> | Ne].
      * rewrite of_to_Z, qget_set_same by exact HkT.
        rewrite <- (Hqy (φ k)) by lia. rewrite <- (Hqx (φ k)) by lia.
        rewrite <- !sget_int.
        destruct (Hb (φ k) ltac:(lia)) as (B1 & B2 & B3).
        assert (Eq1 : Sint63.to_Z qy'.[k] = yv qy (φ k))
          by (rewrite sget_int; apply Hqy; lia).
        assert (Eq2 : Sint63.to_Z qx'.[k] = yv qx (φ k))
          by (rewrite sget_int; apply Hqx; lia).
        apply HQ; [rewrite Eq1 | rewrite Eq1, Eq2 | rewrite Eq2]; assumption.
      * rewrite qget_set_other.
        -- apply Hinv. lia.
        -- intro F. apply Ne. rewrite F. rewrite of_Z_phi; [reflexivity|].
           rewrite wB_val. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkm.
    split; [exact Hlen|]. intros p Hp. apply Hinv. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* repr bridges                                                        *)
(* ------------------------------------------------------------------ *)

Lemma repr_sint_arr : forall (x : array sint) (l : list Z), repr x l ->
  (φ (@PArray.length int x)) = nz l /\
  forall p, (0 <= p < nz l)%Z -> sget x p = yv l p.
Proof.
  intros x l [Hl Hc]. split; [symmetry; exact Hl|].
  intros p Hp. unfold nz in Hp.
  destruct (Hc (Z.to_nat p) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_sint in Hr.
  unfold sget, yv. rewrite (nth_error_nth l (Z.to_nat p) 0%Z Hv).
  rewrite <- Hr. f_equal. f_equal. unfold Uint63.of_nat.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma repr_uint_arr : forall (x : array uint) (l : list N), repr x l ->
  (φ (@PArray.length int x)) = nz l /\
  forall p, (0 <= p < nz l)%Z -> uget x p = Z.of_N (rv l p).
Proof.
  intros x l [Hl Hc]. split; [symmetry; exact Hl|].
  intros p Hp. unfold nz in Hp.
  destruct (Hc (Z.to_nat p) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr.
  unfold uget, rv. rewrite (nth_error_nth l (Z.to_nat p) 0%N Hv).
  rewrite <- Hr. unfold Uint63.of_nat. rewrite Z2Nat.id by lia.
  rewrite Z2N.id; [reflexivity|]. apply to_Z_bounded.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma worstweather_impl_correct : forall (ys : list Z) (rs : list N) (qy qx : list Z)
    (ys' : array sint) (rs' : array uint) (qy' qx' : array sint),
  valid_input ys rs qy qx ->
  repr ys' ys -> repr rs' rs -> repr qy' qy -> repr qx' qx ->
  exists o : list answer,
    repr (worstweather_impl ys' rs' qy' qx') o /\ worstweather_spec ys rs qy qx o.
Proof.
  intros ys rs qy qx ys' rs' qy' qx' Hv Rys Rrs Rqy Rqx.
  destruct Hv as [Vn Vrs Vy Vr Vinc Vm Vqx Vq].
  unfold len in *.
  destruct (repr_sint_arr ys' ys Rys) as [Lys Gys].
  destruct (repr_uint_arr rs' rs Rrs) as [Lrs Grs].
  destruct (repr_sint_arr qy' qy Rqy) as [Lqy Gqy].
  destruct (repr_sint_arr qx' qx Rqx) as [Lqx Gqx].
  assert (Hrs : List.length rs = List.length ys) by lia.
  assert (Hnz : nz rs = nz ys) by (unfold nz; rewrite Hrs; reflexivity).
  assert (Hqz : nz qx = nz qy) by (unfold nz; lia).
  assert (Hinc : forall p, (0 <= p)%Z -> (p + 1 < nz ys)%Z -> (yv ys p < yv ys (p + 1))%Z).
  { intros p Hp Hp1. pose proof (Vinc (Z.to_N p) ltac:(unfold nz in Hp1; lia)) as E.
    unfold at_ in E. unfold yv.
    replace (N.to_nat (Z.to_N p)) with (Z.to_nat p) in E by lia.
    replace (N.to_nat (Z.to_N p + 1)) with (Z.to_nat (p + 1)) in E by lia. exact E. }
  assert (Hrain : forall p, (0 <= p < nz ys)%Z -> (1 <= rv rs p <= 10 ^ 9)%N).
  { intros p Hp. unfold rv. rewrite Forall_nth in Vr.
    exact (Vr (Z.to_nat p) 0%N ltac:(unfold nz in Hp; lia)). }
  assert (Hq : forall p, (0 <= p < nz qy)%Z ->
     (- 10 ^ 9 <= yv qy p)%Z /\ (yv qy p < yv qx p)%Z /\ (yv qx p <= 10 ^ 9)%Z).
  { intros p Hp. pose proof (Vq (Z.to_N p) ltac:(unfold nz in Hp; lia)) as E.
    unfold at_ in E. unfold yv.
    replace (N.to_nat (Z.to_N p)) with (Z.to_nat p) in E by lia. lia. }
  unfold worstweather_impl. cbv zeta.
  set (n := @PArray.length int ys') in *.
  set (m := @PArray.length int qy') in *.
  assert (Hn1 : (1 <= (φ n) <= 50000)%Z) by (rewrite Lys; unfold nz; lia).
  assert (Hm1 : (1 <= (φ m) <= 10000)%Z) by (rewrite Lqy; unfold nz; lia).
  pose proof (lg_spec n ltac:(lia)) as [Hl0 [Hl1 Hl2]].
  assert (Hl15 : ((φ (lg n)) <= 15)%Z).
  { destruct (Z.le_gt_cases (φ (lg n)) 15) as [|G]; [assumption|].
    assert (P : (2 ^ 16 <= 2 ^ (φ (lg n)))%Z) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 16)%Z with 65536%Z in P. lia. }
  assert (HL : (φ (lg n + 1)) = ((φ (lg n)) + 1)%Z)
    by (rewrite add_spec; change (φ 1) with 1%Z; apply Z.mod_small; rewrite wB_val; lia).
  set (L := lg n + 1) in *.
  assert (HLn : ((φ L) * (φ n) <= 4194303)%Z).
  { assert ((φ L) * (φ n) <= 16 * 50000)%Z by (apply Z.mul_le_mono_nonneg; lia). lia. }
  assert (Hbuild := build_spec rs' n L ltac:(lia) ltac:(lia)
                      ltac:(rewrite HL; replace ((φ (lg n)) + 1 - 1)%Z with (φ (lg n)) by ring;
                            exact Hl1) HLn).
  assert (HQ := answer_query_spec ys rs ys' rs' (build rs' n L) n L Hrs Hinc Hrain Lys Gys
                  ltac:(intros p Hp; apply Grs; rewrite Hnz; exact Hp) Hbuild
                  ltac:(rewrite HL; exact Hl2) HLn ltac:(lia)).
  assert (Hmk : PArray.length (PArray.make m Ans_false) = m).
  { rewrite qlength_make. replace (m <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (q_loop_spec ys rs ys' rs' (build rs' n L) qy' qx' n qy qx m HQ Lqy Gqy
              ltac:(intros p Hp; apply Gqx; rewrite Hqz; exact Hp) Hq
              _ 0 (PArray.make m Ans_false) (Zwf_well_founded 0 (gap m 0)) eq_refl Hmk
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(change (φ 0) with 0%Z; intros; lia)) as [Ho1 Ho2].
  set (out := q_loop ys' rs' (build rs' n L) qy' qx' n m 0 (PArray.make m Ans_false)
                (Zwf_well_founded 0 (gap m 0))) in *.
  exists (map (fun k => out.[of_nat k]) (seq 0 (List.length qy))).
  split.
  - split.
    + rewrite length_map, length_seq.
      transitivity (φ m); [rewrite Lqy; reflexivity | f_equal; symmetry; exact Ho1].
    + intros k Hk. rewrite length_map, length_seq in Hk.
      exists (out.[of_nat k]). split.
      * rewrite nth_error_map, nth_error_seq.
        destruct (Nat.ltb_spec k (List.length qy)); [reflexivity | lia].
      * reflexivity.
  - split.
    + unfold len. rewrite length_map, length_seq. reflexivity.
    + intros k Hk. unfold len in Hk. unfold at_.
      assert (E : nth (N.to_nat k) (map (fun k => out.[of_nat k]) (seq 0 (List.length qy)))
                    Ans_false = out.[of_nat (N.to_nat k)]).
      { apply nth_error_nth. rewrite nth_error_map, nth_error_seq.
        destruct (Nat.ltb_spec (N.to_nat k) (List.length qy)); [reflexivity | lia]. }
      rewrite E.
      replace (nth (N.to_nat k) qy 0%Z) with (yv qy (Z.of_N k)) by (unfold yv; f_equal; lia).
      replace (nth (N.to_nat k) qx 0%Z) with (yv qx (Z.of_N k)) by (unfold yv; f_equal; lia).
      rewrite N_nat_Z.
      exact (Ho2 (Z.of_N k) ltac:(rewrite Lqy; unfold nz; lia)).
Qed.

Definition worstweather_correct :
  forall (ys : list Z) (rs : list N) (qy qx : list Z)
         (ys' : array sint) (rs' : array uint) (qy' qx' : array sint),
  valid_input ys rs qy qx ->
  repr ys' ys -> repr rs' rs -> repr qy' qy -> repr qx' qx ->
  exists o : list answer,
    repr (worstweather ys' rs' qy' qx') o /\ worstweather_spec ys rs qy qx o
  := worstweather_impl_correct.
