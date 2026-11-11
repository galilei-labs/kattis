(* Implementation of cudak (cudak.spec): digit DP.

   Code.  [cudak a b s] computes D, the number of decimal digits of b
   (b < 10^D, D <= 15), and one flat table T of D rows of s+1 cells,
   T[k*(s+1) + u] = g k u = #{ y < 10^k : digit sum of y = u }, built row
   by row from g 0 u = [u = 0] and g (k+1) u = sum_{c <= 9, c <= u}
   g k (u - c).  The count is f(b) - f(a-1), f(X) = #{ y <= X : digit sum
   s }, computed by a top-down walk over the D digits of X.  The smallest
   qualifying integer is the (f(a-1)+1)-th integer of digit sum s, built
   greedily digit by digit from the top, each digit chosen by subtracting
   the table counts of the smaller digits from the remaining rank.  All
   values are Uint63 words (no value exceeds 10^15 + 1).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (the template's device). *)

From Cudak.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import FinFun.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ================================================================== *)
(* Math side: digit sums and counts                                    *)
(* ================================================================== *)

Section MathSide.
Local Open Scope N_scope.

Fixpoint ds_f (f : nat) (n : N) : N :=
  match f with
  | O => 0
  | S f => if n =? 0 then 0 else n mod 10 + ds_f f (n / 10)
  end.

(* the digit sum, as a function *)
Definition ds (n : N) : N := ds_f (S (N.to_nat n)) n.

Lemma ds_f_indep : forall f g n,
  (N.to_nat n < f)%nat -> (N.to_nat n < g)%nat -> ds_f f n = ds_f g n.
Proof.
  induction f as [| f IH]; intros g n Hf Hg; [lia|].
  destruct g as [| g]; [lia|]. simpl.
  destruct (N.eqb_spec n 0) as [E | E]; [reflexivity|].
  f_equal. apply IH.
  - assert (n / 10 < n) by (apply N.div_lt; lia). lia.
  - assert (n / 10 < n) by (apply N.div_lt; lia). lia.
Qed.

Lemma ds_0 : ds 0 = 0.
Proof. reflexivity. Qed.

Lemma ds_eq : forall n, ds n = n mod 10 + ds (n / 10).
Proof.
  intros n. destruct (N.eqb_spec n 0) as [E | E].
  - subst n. reflexivity.
  - unfold ds at 1. simpl.
    replace (n =? 0) with false by (symmetry; apply N.eqb_neq; exact E).
    f_equal. unfold ds. apply ds_f_indep.
    + assert (n / 10 < n) by (apply N.div_lt; lia). lia.
    + lia.
Qed.

Lemma digit_sum_ds : forall n t, digit_sum n t <-> ds n = t.
Proof.
  intros n t. split.
  - intros H. induction H as [| n t Hn _ IH].
    + reflexivity.
    + rewrite ds_eq, IH. reflexivity.
  - intros <-.
    assert (Hf : forall f n, (N.to_nat n < f)%nat -> digit_sum n (ds n)).
    { induction f as [| f IH]; intros m Hm; [lia|].
      destruct (N.eqb_spec m 0) as [E | E].
      - subst m. rewrite ds_0. constructor.
      - rewrite ds_eq. constructor; [lia|]. apply IH.
        assert (m / 10 < m) by (apply N.div_lt; lia). lia. }
    apply (Hf (S (N.to_nat n))). lia.
Qed.

Lemma ds_small : forall c, c < 10 -> ds c = c.
Proof.
  intros c Hc. rewrite ds_eq, N.mod_small, N.div_small by exact Hc.
  rewrite ds_0. lia.
Qed.

Lemma ds_split : forall k c y, y < 10 ^ k -> ds (c * 10 ^ k + y) = ds c + ds y.
Proof.
  induction k as [| k IH] using N.peano_ind; intros c y Hy.
  - rewrite N.pow_0_r in *. assert (y = 0) by lia. subst y.
    rewrite N.mul_1_r, N.add_0_r, ds_0. lia.
  - rewrite N.pow_succ_r' in *.
    set (P := 10 ^ k) in *.
    assert (Hx : c * (10 * P) + y = y + (c * P) * 10) by lia.
    rewrite Hx, ds_eq, N.mod_add, N.div_add by lia.
    rewrite (ds_eq y).
    rewrite (N.add_comm (y / 10) (c * P)), IH.
    + lia.
    + apply N.div_lt_upper_bound; lia.
Qed.

(* counts over [0, n) *)
Fixpoint cntn (P : N -> bool) (n : nat) : N :=
  match n with
  | O => 0
  | S n => cntn P n + (if P (N.of_nat n) then 1 else 0)
  end.

Definition cnt (P : N -> bool) (X : N) : N := cntn P (N.to_nat X).

Lemma cntn_add : forall P n m,
  cntn P (n + m) = cntn P n + cntn (fun y => P (N.of_nat n + y)) m.
Proof.
  intros P n m. induction m as [| m IH]; simpl.
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. simpl. rewrite IH, Nat2N.inj_add. lia.
Qed.

Lemma cnt_add : forall P X Y,
  cnt P (X + Y) = cnt P X + cnt (fun y => P (X + y)) Y.
Proof.
  intros P X Y. unfold cnt. rewrite N2Nat.inj_add, cntn_add, N2Nat.id.
  reflexivity.
Qed.

Lemma cnt_ext : forall P Q Y, (forall y, y < Y -> P y = Q y) -> cnt P Y = cnt Q Y.
Proof.
  intros P Q Y H. unfold cnt.
  assert (G : forall m, (m <= N.to_nat Y)%nat -> cntn P m = cntn Q m).
  { induction m as [| m IH]; intros Hm; simpl; [reflexivity|].
    rewrite IH by lia. rewrite H by lia. reflexivity. }
  apply G. lia.
Qed.

Lemma cnt_succ : forall P X, cnt P (X + 1) = cnt P X + (if P X then 1 else 0).
Proof.
  intros P X. unfold cnt. rewrite N2Nat.inj_add.
  change (N.to_nat 1) with 1%nat. rewrite Nat.add_1_r. simpl.
  rewrite N2Nat.id. reflexivity.
Qed.

Lemma cnt_0 : forall P, cnt P 0 = 0.
Proof. reflexivity. Qed.

Lemma cnt_le : forall P X, cnt P X <= X.
Proof.
  intros P X. unfold cnt.
  assert (G : forall m, cntn P m <= N.of_nat m).
  { induction m as [| m IH]; simpl; [lia|]. destruct (P (N.of_nat m)); lia. }
  specialize (G (N.to_nat X)). lia.
Qed.

Lemma cnt_mono : forall P X Y, X <= Y -> cnt P X <= cnt P Y.
Proof.
  intros P X Y H. replace Y with (X + (Y - X)) by lia.
  rewrite cnt_add. lia.
Qed.

Lemma cnt_false : forall P Y, (forall y, y < Y -> P y = false) -> cnt P Y = 0.
Proof.
  intros P Y H. rewrite (cnt_ext P (fun _ => false)) by exact H.
  unfold cnt. induction (N.to_nat Y) as [| m IH]; simpl; lia.
Qed.

Lemma cnt_strict : forall P z X Y,
  P z = true -> X <= z -> z < Y -> cnt P X < cnt P Y.
Proof.
  intros P z X Y Hz HX HY.
  pose proof (cnt_mono P X z HX).
  pose proof (cnt_mono P (z + 1) Y ltac:(lia)).
  rewrite cnt_succ, Hz in *. lia.
Qed.

(* y has digit sum t once o is added to it *)
Definition Pd (o t : N) (y : N) : bool := o + ds y =? t.

(* the table: integers below 10^k with digit sum u *)
Definition g (k u : N) : N := cnt (Pd 0 u) (10 ^ k).

Definition term (k t d : N) : N := if d <=? t then g k (t - d) else 0.

Fixpoint bsum (k t : N) (c : nat) : N :=
  match c with
  | O => 0
  | S c => bsum k t c + term k t (N.of_nat c)
  end.

Lemma cnt_Pd_off : forall o t Y,
  cnt (Pd o t) Y = if o <=? t then cnt (Pd 0 (t - o)) Y else 0.
Proof.
  intros o t Y. destruct (N.leb_spec o t) as [H | H].
  - apply cnt_ext. intros y _. unfold Pd.
    destruct (N.eqb_spec (o + ds y) t), (N.eqb_spec (0 + ds y) (t - o)); lia.
  - apply cnt_false. intros y _. unfold Pd. apply N.eqb_neq. lia.
Qed.

Lemma g_0 : forall u, g 0 u = if u =? 0 then 1 else 0.
Proof.
  intros u. unfold g. rewrite N.pow_0_r.
  change 1 with (0 + 1). rewrite cnt_succ, cnt_0. unfold Pd. rewrite ds_0.
  destruct (N.eqb_spec (0 + 0) u), (N.eqb_spec u 0); lia.
Qed.

Lemma g_le : forall k u, g k u <= 10 ^ k.
Proof. intros k u. apply cnt_le. Qed.

Lemma term_le : forall k t d, term k t d <= 10 ^ k.
Proof. intros k t d. unfold term. destruct (d <=? t); [apply g_le | lia]. Qed.

Lemma bsum_le : forall k t c, bsum k t c <= N.of_nat c * 10 ^ k.
Proof.
  intros k t c. induction c as [| c IH]; [simpl; lia|].
  change (bsum k t (S c)) with (bsum k t c + term k t (N.of_nat c)).
  rewrite Nat2N.inj_succ, N.mul_succ_l.
  pose proof (term_le k t (N.of_nat c)). lia.
Qed.

Lemma bsum_mono : forall k t c c', (c <= c')%nat -> bsum k t c <= bsum k t c'.
Proof.
  intros k t c c' H. induction H as [| c' H IH]; [lia|]. simpl. lia.
Qed.

(* c whole blocks of 10^k, after an offset o <= t *)
Lemma cnt_blocks : forall k o t c, (c <= 10)%nat -> o <= t ->
  cnt (Pd o t) (N.of_nat c * 10 ^ k) = bsum k (t - o) c.
Proof.
  intros k o t c. induction c as [| c IH]; intros Hc Ho.
  - reflexivity.
  - rewrite Nat2N.inj_succ, N.mul_succ_l, cnt_add, IH by lia. simpl.
    f_equal.
    rewrite (cnt_ext _ (Pd (o + N.of_nat c) t)).
    + rewrite cnt_Pd_off. unfold term.
      destruct (N.leb_spec (o + N.of_nat c) t), (N.leb_spec (N.of_nat c) (t - o));
        try lia.
      unfold g. f_equal. f_equal. lia.
    + intros y Hy. unfold Pd. rewrite ds_split by exact Hy.
      rewrite ds_small by lia. f_equal. lia.
Qed.

Lemma g_succ : forall k t, g (k + 1) t = bsum k t 10.
Proof.
  intros k t. unfold g at 1.
  rewrite N.pow_add_r, N.pow_1_r, N.mul_comm.
  change 10 with (N.of_nat 10) at 1.
  rewrite cnt_blocks by lia. f_equal. lia.
Qed.

(* one step of the counting walk: X + 1 = c * 10^k + R' + 1 *)
Lemma walk_block : forall k t c R', c < 10 -> R' < 10 ^ k ->
  cnt (Pd 0 t) (c * 10 ^ k + R' + 1)
  = bsum k t (N.to_nat c) + (if c <=? t then cnt (Pd 0 (t - c)) (R' + 1) else 0).
Proof.
  intros k t c R' Hc HR.
  rewrite <- N.add_assoc, cnt_add.
  rewrite <- (N2Nat.id c) at 1.
  rewrite cnt_blocks by lia. rewrite N.sub_0_r. f_equal.
  rewrite (cnt_ext _ (Pd c t)).
  - rewrite cnt_Pd_off. reflexivity.
  - intros y Hy. unfold Pd. rewrite ds_split by lia.
    rewrite ds_small by exact Hc. f_equal; lia.
Qed.

(* one step of the greedy walk: prefix x, then digit c *)
Lemma min_block : forall x k c s, ds x <= s -> c < 10 ->
  cnt (Pd 0 s) ((x * 10 + c) * 10 ^ k)
  = cnt (Pd 0 s) (x * 10 ^ (k + 1)) + bsum k (s - ds x) (N.to_nat c).
Proof.
  intros x k c s Hx Hc.
  replace ((x * 10 + c) * 10 ^ k) with (x * 10 ^ (k + 1) + c * 10 ^ k)
    by (rewrite N.pow_add_r, N.pow_1_r; lia).
  rewrite cnt_add. f_equal.
  rewrite (cnt_ext _ (Pd (ds x) s)).
  - rewrite <- (N2Nat.id c) at 1. apply cnt_blocks; lia.
  - intros y Hy. unfold Pd. rewrite ds_split.
    + f_equal.
    + rewrite N.pow_add_r, N.pow_1_r. nia.
Qed.

(* the list of the integers of [a, a + m) satisfying P *)
Lemma len_filter_seq : forall (P : N -> bool) (a : N) m,
  N.of_nat (List.length (List.filter P (List.map N.of_nat (seq (N.to_nat a) m))))
  = cntn (fun y => P (a + y)) m.
Proof.
  intros P a m. induction m as [| m IH]; [reflexivity|].
  rewrite seq_S, map_app, filter_app, length_app. simpl.
  rewrite <- IH.
  replace (N.of_nat (N.to_nat a + m)) with (a + N.of_nat m) by lia.
  destruct (P (a + N.of_nat m)); simpl; lia.
Qed.

End MathSide.

(* ================================================================== *)
(* Uint63 / PArray plumbing                                            *)
(* ================================================================== *)

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

(* ================================================================== *)
(* The termination device                                              *)
(* ================================================================== *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_pred : forall j : int,
  (0 <? j) = true -> Zwf 0 (φ (j - 1)) (φ j).
Proof.
  intros j H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
  unfold Zwf. pose proof (to_Z_bounded (j - 1)). lia.
Qed.

Lemma andb_l : forall a b : bool, a && b = true -> a = true.
Proof. intros a b H. destruct a; [reflexivity | discriminate]. Qed.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

(* the table count of the integers below 10^k (row k, at [base]) whose
   digit sum is t - c, or 0 when c > t *)
Definition vcell (T : array int) (base t c : int) : int :=
  if c <=? t then T.[base + (t - c)] else 0.

(* acc + sum of the vcells for the digits d .. c-1 *)
Fixpoint rowsum (T : array int) (base t c d acc : int)
    (H : Acc (Zwf 0) (gap c d)) {struct H} : int :=
  match bdec (d <? c) with
  | left Hd =>
      rowsum T base t c (d + 1) (acc + vcell T base t d)
        (Acc_inv H (dec_step c d Hd))
  | right _ => acc
  end.

Lemma rowsum_eq : forall T base t c d acc H,
  rowsum T base t c d acc H =
  match bdec (d <? c) with
  | left Hd =>
      rowsum T base t c (d + 1) (acc + vcell T base t d)
        (Acc_inv H (dec_step c d Hd))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* cells idx .. n-1 of the table; idx = k * S1 + u, row k >= 1 computed
   from row k - 1 *)
Fixpoint fill (T : array int) (s S1 n idx k u : int)
    (H : Acc (Zwf 0) (gap n idx)) {struct H} : array int :=
  match bdec (idx <? n) with
  | left Hi =>
      fill T.[idx <- rowsum T ((k - 1) * S1) u 10 0 0
                        (Zwf_well_founded 0 (gap 10 0))]
        s S1 n (idx + 1)
        (if u =? s then k + 1 else k) (if u =? s then 0 else u + 1)
        (Acc_inv H (dec_step n idx Hi))
  | right _ => T
  end.

Lemma fill_eq : forall T s S1 n idx k u H,
  fill T s S1 n idx k u H =
  match bdec (idx <? n) with
  | left Hi =>
      fill T.[idx <- rowsum T ((k - 1) * S1) u 10 0 0
                        (Zwf_well_founded 0 (gap 10 0))]
        s S1 n (idx + 1)
        (if u =? s then k + 1 else k) (if u =? s then 0 else u + 1)
        (Acc_inv H (dec_step n idx Hi))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the number d of decimal digits of b, with q = 10^(d-1) *)
Fixpoint digits (b d q : int) (H : Acc (Zwf 0) (gap 15 d)) {struct H}
    : int * int :=
  match bdec ((d <? 15) && (q * 10 <=? b)) with
  | left Hc => digits b (d + 1) (q * 10) (Acc_inv H (dec_step 15 d (andb_l _ _ Hc)))
  | right _ => (d, q)
  end.

Lemma digits_eq : forall b d q H,
  digits b d q H =
  match bdec ((d <? 15) && (q * 10 <=? b)) with
  | left Hc => digits b (d + 1) (q * 10) (Acc_inv H (dec_step 15 d (andb_l _ _ Hc)))
  | right _ => (d, q)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* acc + #{ y <= R : digit sum t }, R having j digits, p = 10^(j-1) *)
Fixpoint walk (T : array int) (S1 j p R t acc : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : int :=
  match bdec (0 <? j) with
  | left Hj =>
      let c := R / p in
      let acc' := rowsum T ((j - 1) * S1) t c 0 acc
                    (Zwf_well_founded 0 (gap c 0)) in
      if t <? c then acc'
      else walk T S1 (j - 1) (p / 10) (R mod p) (t - c) acc'
             (Acc_inv H (dec_pred j Hj))
  | right _ => if t =? 0 then acc + 1 else acc
  end.

Lemma walk_eq : forall T S1 j p R t acc H,
  walk T S1 j p R t acc H =
  match bdec (0 <? j) with
  | left Hj =>
      let c := R / p in
      let acc' := rowsum T ((j - 1) * S1) t c 0 acc
                    (Zwf_well_founded 0 (gap c 0)) in
      if t <? c then acc'
      else walk T S1 (j - 1) (p / 10) (R mod p) (t - c) acc'
             (Acc_inv H (dec_pred j Hj))
  | right _ => if t =? 0 then acc + 1 else acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the digit c (from c on) at which the rank r falls, and the rank left *)
Fixpoint pick (T : array int) (base t c r : int)
    (H : Acc (Zwf 0) (gap 9 c)) {struct H} : int * int :=
  match bdec ((c <? 9) && (vcell T base t c <? r)) with
  | left Hc =>
      pick T base t (c + 1) (r - vcell T base t c)
        (Acc_inv H (dec_step 9 c (andb_l _ _ Hc)))
  | right _ => (c, r)
  end.

Lemma pick_eq : forall T base t c r H,
  pick T base t c r H =
  match bdec ((c <? 9) && (vcell T base t c <? r)) with
  | left Hc =>
      pick T base t (c + 1) (r - vcell T base t c)
        (Acc_inv H (dec_step 9 c (andb_l _ _ Hc)))
  | right _ => (c, r)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the greedy construction: prefix x, j digits left, sum t left, rank r *)
Fixpoint minwalk (T : array int) (S1 j t r x : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : int :=
  match bdec (0 <? j) with
  | left Hj =>
      let cr := pick T ((j - 1) * S1) t 0 r (Zwf_well_founded 0 (gap 9 0)) in
      minwalk T S1 (j - 1) (t - fst cr) (snd cr) (x * 10 + fst cr)
        (Acc_inv H (dec_pred j Hj))
  | right _ => x
  end.

Lemma minwalk_eq : forall T S1 j t r x H,
  minwalk T S1 j t r x H =
  match bdec (0 <? j) with
  | left Hj =>
      let cr := pick T ((j - 1) * S1) t 0 r (Zwf_well_founded 0 (gap 9 0)) in
      minwalk T S1 (j - 1) (t - fst cr) (snd cr) (x * 10 + fst cr)
        (Acc_inv H (dec_pred j Hj))
  | right _ => x
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition cudak_impl (a b s : uint) : uint * uint :=
  let S1 := s + 1 in
  let dq := digits b 1 1 (Zwf_well_founded 0 (gap 15 1)) in
  let D := fst dq in
  let q := snd dq in
  let n := D * S1 in
  let T := fill (PArray.make n 0).[0 <- 1] s S1 n S1 1 0
             (Zwf_well_founded 0 (gap n S1)) in
  let cb := walk T S1 D q b s 0 (Zwf_well_founded 0 (φ D)) in
  let ca := walk T S1 D q (a - 1) s 0 (Zwf_well_founded 0 (φ D)) in
  (cb - ca, minwalk T S1 D s (ca + 1) 0 (Zwf_well_founded 0 (φ D))).

(* ================================================================== *)
(* Prop side: the final math lemma                                     *)
(* ================================================================== *)

Lemma Pd_true : forall s y, Pd 0 s y = true <-> ds y = s.
Proof.
  intros s y. unfold Pd. rewrite N.eqb_eq. lia.
Qed.

(* from the two counts and the greedy result to the spec *)
Lemma spec_from_counts : forall (a b s m : N), valid_input a b s ->
  ds m = s -> cnt (Pd 0 s) m = cnt (Pd 0 s) a ->
  cudak_spec a b s ((cnt (Pd 0 s) (b + 1) - cnt (Pd 0 s) a)%N, m).
Proof.
  intros a b s m Hv Hm Hc.
  destruct Hv as [Hab Hb Hs [m0 [Hm0 Hd0]]].
  rewrite digit_sum_ds in Hd0.
  assert (Hq : forall y, qualifies a b s y <-> (a <= y <= b)%N /\ ds y = s).
  { intros y. unfold qualifies. rewrite digit_sum_ds. reflexivity. }
  assert (Hmin : forall y, qualifies a b s y -> (m <= y)%N).
  { intros y Hy. apply Hq in Hy. destruct Hy as [Hy1 Hy2].
    destruct (N.le_gt_cases m y) as [Hle | Hlt]; [exact Hle|].
    exfalso. assert (cnt (Pd 0 s) a < cnt (Pd 0 s) m)%N.
    { apply (cnt_strict _ y); [apply Pd_true; exact Hy2 | lia | lia]. }
    lia. }
  assert (Ham : (a <= m)%N).
  { destruct (N.le_gt_cases a m) as [Hle | Hlt]; [exact Hle|].
    exfalso. assert (cnt (Pd 0 s) m < cnt (Pd 0 s) a)%N.
    { apply (cnt_strict _ m); [apply Pd_true; exact Hm | lia | lia]. }
    lia. }
  assert (Hmm0 : (m <= m0)%N) by (apply Hmin; apply Hq; split; [lia | exact Hd0]).
  unfold cudak_spec. split; [| split].
  - set (L := N.to_nat (b + 1 - a)).
    exists (List.filter (Pd 0 s) (List.map N.of_nat (seq (N.to_nat a) L))).
    split; [| split].
    + apply NoDup_filter. apply Injective_map_NoDup.
      * intros u v E. apply Nat2N.inj. exact E.
      * apply seq_NoDup.
    + intros y. rewrite filter_In, in_map_iff, Hq, Pd_true. split.
      * intros [[n [<- Hn]] Hy]. apply in_seq in Hn. unfold L in Hn. lia.
      * intros [Hy1 Hy2]. split; [| exact Hy2].
        exists (N.to_nat y). split; [lia|]. apply in_seq. unfold L. lia.
    + unfold len. rewrite len_filter_seq.
      replace (b + 1)%N with (a + (b + 1 - a))%N by lia.
      rewrite cnt_add. unfold cnt at 2. fold L. lia.
  - apply Hq. split; [lia | exact Hm].
  - exact Hmin.
Qed.

(* ================================================================== *)
(* Prop side: machine arithmetic                                       *)
(* ================================================================== *)

Lemma add_small : forall x y : int, ((φ x) + (φ y) < wB)%Z -> (φ (x + y)) = ((φ x) + (φ y))%Z.
Proof.
  intros x y H. rewrite add_spec. apply Z.mod_small.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia.
Qed.

Lemma sub_small : forall x y : int, ((φ y) <= (φ x))%Z -> (φ (x - y)) = ((φ x) - (φ y))%Z.
Proof.
  intros x y H. rewrite sub_spec. apply Z.mod_small.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia.
Qed.

Lemma mul_small : forall x y : int, ((φ x) * (φ y) < wB)%Z -> (φ (x * y)) = ((φ x) * (φ y))%Z.
Proof.
  intros x y H. rewrite mul_spec. apply Z.mod_small.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). nia.
Qed.

Lemma decomp_unique : forall S k u k' u' : Z,
  (0 <= u < S)%Z -> (0 <= u' < S)%Z -> (k * S + u = k' * S + u')%Z ->
  k = k' /\ u = u'.
Proof.
  intros S k u k' u' Hu Hu' E.
  assert (Hk : k = k').
  { destruct (Z.lt_trichotomy k k') as [H | [H | H]]; [| exact H |]; exfalso.
    - assert ((k + 1) * S <= k' * S)%Z by (apply Z.mul_le_mono_nonneg_r; lia). lia.
    - assert ((k' + 1) * S <= k * S)%Z by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  subst k'. split; [reflexivity | lia].
Qed.

Lemma pow10_le : forall e e' : Z, (0 <= e <= e')%Z -> (10 ^ e <= 10 ^ e')%Z.
Proof. intros e e' H. apply Z.pow_le_mono_r; lia. Qed.

Lemma pow10_pos : forall e : Z, (0 <= e)%Z -> (0 < 10 ^ e)%Z.
Proof. intros e H. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow10_15 : (10 ^ 15 < wB)%Z.
Proof. rewrite wB_val. reflexivity. Qed.

Lemma Npow10_Z : forall e : Z, (0 <= e)%Z -> Z.of_N (10 ^ Z.to_N e) = (10 ^ e)%Z.
Proof. intros e H. rewrite N2Z.inj_pow, Z2N.id by exact H. reflexivity. Qed.

Lemma Z2N_phi : forall x : int, Z.of_N (Z.to_N (φ x)) = (φ x).
Proof. intros x. apply Z2N.id. apply to_Z_bounded. Qed.

(* lia, after replacing each Z.to_N (φ x) by an N variable (zify would
   otherwise split on every Z.to_N) *)
Ltac nlia :=
  repeat match goal with
  | |- context [Z.to_N (to_Z ?x)] =>
      let E := fresh "EN" in pose proof (Z2N_phi x) as E;
      let n := fresh "nN" in set (n := Z.to_N (to_Z x)) in *; clearbody n
  | H : context [Z.to_N (to_Z ?x)] |- _ =>
      let E := fresh "EN" in pose proof (Z2N_phi x) as E;
      let n := fresh "nN" in set (n := Z.to_N (to_Z x)) in *; clearbody n
  end; lia.

Lemma base_eq : forall j S1 : int, (1 <= (φ j) <= 15)%Z -> ((φ S1) <= 136)%Z ->
  (φ ((j - 1) * S1)) = (((φ j) - 1) * (φ S1))%Z.
Proof.
  intros j S1 Hj HS.
  pose proof (to_Z_bounded S1).
  assert (E : (φ (j - 1)) = ((φ j) - 1)%Z)
    by (rewrite sub_small; change (φ 1) with 1%Z; lia).
  rewrite mul_small; rewrite E; [reflexivity|]. rewrite wB_val. nia.
Qed.

(* ================================================================== *)
(* Prop side: the table                                                *)
(* ================================================================== *)

Definition tab_ok (T : array int) (S1 lim : Z) : Prop :=
  forall kk uu : Z, (0 <= kk)%Z -> (0 <= uu < S1)%Z -> (kk * S1 + uu < lim)%Z ->
  (φ (T.[of_Z (kk * S1 + uu)])) = Z.of_N (g (Z.to_N kk) (Z.to_N uu)).

Lemma read_cell : forall T S1 lim, tab_ok T S1 lim ->
  forall (i : int) (kk uu : Z), (φ i) = (kk * S1 + uu)%Z ->
  (0 <= kk)%Z -> (0 <= uu < S1)%Z -> (kk * S1 + uu < lim)%Z ->
  (φ (T.[i])) = Z.of_N (g (Z.to_N kk) (Z.to_N uu)).
Proof.
  intros T S1 lim Ht i kk uu Hi Hk Hu Hl.
  rewrite <- (of_to_Z i), Hi. apply Ht; assumption.
Qed.

Lemma vcell_spec : forall T S1 lim (base t c : int) kk,
  tab_ok T S1 lim -> (0 <= kk)%Z -> (φ base) = (kk * S1)%Z ->
  ((φ t) < S1)%Z -> (kk * S1 + (φ t) < lim)%Z -> (lim < wB)%Z ->
  (φ (vcell T base t c)) = Z.of_N (term (Z.to_N kk) (Z.to_N (φ t)) (Z.to_N (φ c))).
Proof.
  intros T S1 lim base t c kk Ht Hk Hb Hts Hl HlwB.
  pose proof (to_Z_bounded t). pose proof (to_Z_bounded c).
  unfold vcell, term.
  destruct (c <=? t) eqn:E.
  - rewrite leb_spec in E.
    replace (Z.to_N (φ c) <=? Z.to_N (φ t))%N with true by (symmetry; apply N.leb_le; lia).
    rewrite (read_cell T S1 lim Ht (base + (t - c)) kk ((φ t) - (φ c))%Z).
    + f_equal. f_equal. lia.
    + rewrite add_small; rewrite sub_small; lia.
    + exact Hk.
    + lia.
    + lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec in E.
    replace (Z.to_N (φ c) <=? Z.to_N (φ t))%N with false by (symmetry; apply N.leb_gt; lia).
    reflexivity.
Qed.

Lemma rowsum_spec : forall T S1 lim (base t c : int) kk,
  tab_ok T S1 lim -> (0 <= kk)%Z -> (φ base) = (kk * S1)%Z ->
  ((φ t) < S1)%Z -> (kk * S1 + (φ t) < lim)%Z -> (lim < wB)%Z -> ((φ c) <= 10)%Z ->
  forall (A0 z : Z) (d acc : int) (H : Acc (Zwf 0) (gap c d)),
  gap c d = z -> ((φ d) <= (φ c))%Z -> (0 <= A0)%Z ->
  (φ acc) = (A0 + Z.of_N (bsum (Z.to_N kk) (Z.to_N (φ t)) (Z.to_nat (φ d))))%Z ->
  (A0 + Z.of_N (bsum (Z.to_N kk) (Z.to_N (φ t)) (Z.to_nat (φ c))) < wB)%Z ->
  (φ (rowsum T base t c d acc H))
  = (A0 + Z.of_N (bsum (Z.to_N kk) (Z.to_N (φ t)) (Z.to_nat (φ c))))%Z.
Proof.
  intros T S1 lim base t c kk Ht Hk Hb Hts Hl HlwB Hc10 A0 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d acc H Hz Hdc HA Hacc Hbd.
  rewrite rowsum_eq.
  destruct (bdec (d <? c)) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded d).
    assert (Hd1 : (φ (d + 1)) = ((φ d) + 1)%Z) by sia.
    assert (Hn1 : Z.to_nat ((φ d) + 1) = S (Z.to_nat (φ d))) by lia.
    assert (Hm := bsum_mono (Z.to_N kk) (Z.to_N (φ t)) (S (Z.to_nat (φ d)))
                    (Z.to_nat (φ c)) ltac:(lia)).
    cbn [bsum] in Hm.
    replace (N.of_nat (Z.to_nat (φ d))) with (Z.to_N (φ d)) in Hm by lia.
    pose proof (vcell_spec T S1 lim base t d kk Ht Hk Hb Hts Hl HlwB) as Hv.
    eapply IH; [ | reflexivity | lia | exact HA | | exact Hbd].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite Hd1, Hn1. cbn [bsum].
      replace (N.of_nat (Z.to_nat (φ d))) with (Z.to_N (φ d)) by lia.
      rewrite add_small; rewrite Hacc, Hv; [lia|].
      lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    replace (Z.to_nat (φ c)) with (Z.to_nat (φ d)) by lia. exact Hacc.
Qed.

Lemma tab_init : forall (n S1 : int),
  (1 <= (φ S1))%Z -> ((φ S1) <= (φ n))%Z -> ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n 0).[0 <- 1] = n /\
  tab_ok (PArray.make n 0).[0 <- 1] (φ S1) (φ S1).
Proof.
  intros n S1 H1 H2 H3.
  assert (Hl : PArray.length (PArray.make n 0) = n).
  { rewrite alength_make.
    replace (n <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  split; [rewrite alength_set; exact Hl|].
  intros kk uu Hk Hu Hlt.
  assert (kk = 0%Z) by nia. subst kk.
  rewrite Z.mul_0_l, Z.add_0_l. rewrite g_0.
  destruct (Z.eq_dec uu 0) as [E | E].
  - subst uu. change (of_Z 0) with 0. rewrite aget_set_same.
    + reflexivity.
    + rewrite Hl, ltb_spec. change (φ 0) with 0%Z. lia.
  - rewrite aget_set_other, aget_make.
    + replace (Z.to_N uu =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      reflexivity.
    + intro F. apply E.
      assert (Hf : (φ (of_Z uu)) = uu).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
      rewrite <- F in Hf. change (φ 0) with 0%Z in Hf. lia.
Qed.

Lemma fill_spec : forall (s S1 n : int) (Dz : Z),
  (φ S1) = ((φ s) + 1)%Z -> ((φ S1) <= 136)%Z -> (1 <= Dz <= 15)%Z ->
  (φ n) = (Dz * (φ S1))%Z ->
  forall (z : Z) (idx k u : int) (T : array int) (H : Acc (Zwf 0) (gap n idx)),
  gap n idx = z -> PArray.length T = n ->
  (φ idx) = ((φ k) * (φ S1) + (φ u))%Z -> (1 <= (φ k))%Z -> ((φ u) < (φ S1))%Z ->
  ((φ idx) <= (φ n))%Z -> tab_ok T (φ S1) (φ idx) ->
  PArray.length (fill T s S1 n idx k u H) = n /\
  tab_ok (fill T s S1 n idx k u H) (φ S1) (φ n).
Proof.
  intros s S1 n Dz HS1 HS1b HD Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros idx k u T H Hz Hlen Hidx Hk Hu Hin Ht.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded u).
  pose proof (to_Z_bounded k). pose proof (to_Z_bounded idx).
  rewrite fill_eq.
  destruct (bdec (idx <? n)) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (HkD : ((φ k) < Dz)%Z) by nia.
    assert (Hbase : (φ ((k - 1) * S1)) = (((φ k) - 1) * (φ S1))%Z).
    { apply base_eq; clear - Hk HkD HD HS1b; lia. }
    assert (Hpow : (10 ^ Z.to_N ((φ k) - 1) <= 10 ^ 13)%N).
    { apply N.pow_le_mono_r; lia. }
    assert (Hbs := bsum_le (Z.to_N ((φ k) - 1)) (Z.to_N (φ u)) 10).
    assert (Hv : (φ (rowsum T ((k - 1) * S1) u 10 0 0 (Zwf_well_founded 0 (gap 10 0))))
                 = Z.of_N (g (Z.to_N (φ k)) (Z.to_N (φ u)))).
    { rewrite (rowsum_spec T (φ S1) (φ idx) ((k - 1) * S1) u 10 ((φ k) - 1) Ht
                 ltac:(lia) Hbase Hu ltac:(nia) ltac:(rewrite wB_val; lia)
                 ltac:(change (φ 10) with 10%Z; lia)
                 0 _ 0 0 _ eq_refl ltac:(change (φ 0) with 0%Z; change (φ 10) with 10%Z; lia)
                 ltac:(lia) ltac:(reflexivity)).
      - change (Z.to_nat (φ 10)) with 10%nat. rewrite <- g_succ, Z.add_0_l.
        f_equal. f_equal. lia.
      - change (Z.to_nat (φ 10)) with 10%nat. rewrite wB_val.
        change (N.of_nat 10) with 10%N in Hbs. lia. }
    set (v := rowsum T ((k - 1) * S1) u 10 0 0 (Zwf_well_founded 0 (gap 10 0))) in *.
    assert (Hi1 : (φ (idx + 1)) = ((φ idx) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | rewrite alength_set; exact Hlen | | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + destruct (u =? s) eqn:E.
      * rewrite eqb_spec in E. subst u.
        assert ((φ (k + 1)) = ((φ k) + 1)%Z) by sia. change (φ 0) with 0%Z. nia.
      * assert ((φ (u + 1)) = ((φ u) + 1)%Z) by sia. lia.
    + destruct (u =? s) eqn:E; [| lia].
      assert ((φ (k + 1)) = ((φ k) + 1)%Z) by sia. lia.
    + destruct (u =? s) eqn:E.
      * change (φ 0) with 0%Z. lia.
      * rewrite <- Bool.not_true_iff_false, eqb_spec in E.
        assert ((φ u) <> (φ s)) by (intro F; apply E; apply to_Z_inj; exact F).
        assert ((φ (u + 1)) = ((φ u) + 1)%Z) by sia. lia.
    + lia.
    + intros kk uu Hkk Huu Hl.
      destruct (Z.eq_dec (kk * (φ S1) + uu) (φ idx)) as [E | E].
      * rewrite Hidx in E.
        destruct (decomp_unique (φ S1) kk uu (φ k) (φ u) Huu ltac:(lia) E) as [-> ->].
        rewrite <- Hidx, of_to_Z, aget_set_same; [exact Hv|].
        rewrite Hlen. exact Hlt.
      * rewrite aget_set_other.
        -- apply Ht; [exact Hkk | exact Huu | lia].
        -- intro F. apply E. rewrite F, of_Z_spec. symmetry. apply Z.mod_small.
           pose proof (Z.mul_nonneg_nonneg kk (φ S1) Hkk ltac:(lia)).
           rewrite wB_val. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hlen|].
    replace (φ n) with (φ idx) by lia. exact Ht.
Qed.

(* ================================================================== *)
(* Prop side: the number of digits                                     *)
(* ================================================================== *)

Lemma digits_spec : forall b : int, ((φ b) < 10 ^ 15)%Z ->
  forall (z : Z) (d q : int) (H : Acc (Zwf 0) (gap 15 d)),
  gap 15 d = z -> (1 <= (φ d) <= 15)%Z -> (φ q) = (10 ^ ((φ d) - 1))%Z ->
  (1 <= (φ (fst (digits b d q H))) <= 15)%Z /\
  (φ (snd (digits b d q H))) = (10 ^ ((φ (fst (digits b d q H))) - 1))%Z /\
  ((φ b) < 10 ^ (φ (fst (digits b d q H))))%Z.
Proof.
  intros b Hb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d q H Hz Hd Hq.
  pose proof (to_Z_bounded b). pose proof (to_Z_bounded q).
  pose proof pow10_15.
  rewrite digits_eq.
  destruct (bdec ((d <? 15) && (q * 10 <=? b))) as [Hc | Hc].
  - destruct (andb_prop _ _ Hc) as [Hc1 Hc2].
    pose proof Hc1 as H1'. rewrite ltb_spec in H1'. change (φ 15) with 15%Z in H1'.
    rewrite leb_spec in Hc2.
    assert (Hq13 : (10 ^ ((φ d) - 1) <= 10 ^ 13)%Z) by (apply pow10_le; lia).
    assert (Hq10 : (φ (q * 10)) = ((φ q) * 10)%Z)
      by (apply mul_small; change (φ 10) with 10%Z; rewrite wB_val; lia).
    assert (Hd1 : (φ (d + 1)) = ((φ d) + 1)%Z) by sia.
    apply (IH (gap 15 (d + 1))).
    + rewrite <- Hz. apply dec_step. exact Hc1.
    + reflexivity.
    + lia.
    + rewrite Hq10, Hd1, Hq.
      replace ((φ d) + 1 - 1)%Z with (Z.succ ((φ d) - 1)) by lia.
      rewrite Z.pow_succ_r by lia. lia.
  - cbn [fst snd]. split; [lia|]. split; [exact Hq|].
    destruct (d <? 15) eqn:E1; cbn in Hc.
    + rewrite <- Bool.not_true_iff_false, leb_spec in Hc.
      rewrite ltb_spec in E1. change (φ 15) with 15%Z in E1.
      assert (Hq13 : (10 ^ ((φ d) - 1) <= 10 ^ 13)%Z) by (apply pow10_le; lia).
      assert (Hq10 : (φ (q * 10)) = ((φ q) * 10)%Z)
        by (apply mul_small; change (φ 10) with 10%Z; rewrite wB_val; lia).
      replace (φ d) with (Z.succ ((φ d) - 1)) by lia.
      rewrite Z.pow_succ_r by lia. lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
      change (φ 15) with 15%Z in E1.
      replace (φ d) with 15%Z by lia. exact Hb.
Qed.

(* ================================================================== *)
(* Prop side: the counting walk                                        *)
(* ================================================================== *)

Lemma walk_blockN : forall k t X, (X < 10 ^ (k + 1))%N ->
  cnt (Pd 0 t) (X + 1)
  = (bsum k t (N.to_nat (X / 10 ^ k))
     + (if (X / 10 ^ k <=? t)%N then cnt (Pd 0 (t - X / 10 ^ k)) (X mod 10 ^ k + 1)
        else 0))%N.
Proof.
  intros k t X HX.
  assert (Hp : (10 ^ k <> 0)%N) by (apply N.pow_nonzero; lia).
  rewrite (N.div_mod X (10 ^ k)) at 1 by exact Hp.
  rewrite (N.mul_comm (10 ^ k)). apply walk_block.
  - apply N.div_lt_upper_bound; [exact Hp|].
    rewrite N.pow_add_r, N.pow_1_r in HX. lia.
  - apply N.mod_lt. exact Hp.
Qed.

Lemma cnt1 : forall u, cnt (Pd 0 u) 1 = if (u =? 0)%N then 1%N else 0%N.
Proof. exact g_0. Qed.

Lemma walk_spec : forall T (S1 s : int) (Dz : Z),
  tab_ok T (φ S1) (Dz * (φ S1)) -> (φ S1) = ((φ s) + 1)%Z -> ((φ S1) <= 136)%Z ->
  (1 <= Dz <= 15)%Z ->
  forall (z : Z) (j p R t acc : int) (H : Acc (Zwf 0) (φ j)),
  (φ j) = z -> ((φ j) <= Dz)%Z -> (0 < (φ j) -> (φ p) = 10 ^ ((φ j) - 1))%Z ->
  ((φ R) < 10 ^ (φ j))%Z -> ((φ t) <= (φ s))%Z ->
  ((φ acc) + Z.of_N (cnt (Pd 0 (Z.to_N (φ t))) (Z.to_N (φ R) + 1)) < wB)%Z ->
  (φ (walk T S1 j p R t acc H))
  = ((φ acc) + Z.of_N (cnt (Pd 0 (Z.to_N (φ t))) (Z.to_N (φ R) + 1)))%Z.
Proof.
  intros T S1 s Dz Ht HS1 HS1b HD z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j p R t acc H Hz HjD Hp HR Hts Hb.
  pose proof (to_Z_bounded j). pose proof (to_Z_bounded p).
  pose proof (to_Z_bounded R). pose proof (to_Z_bounded t).
  pose proof (to_Z_bounded acc) as Bacc.
  rewrite walk_eq.
  destruct (bdec (0 <? j)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'. change (φ 0) with 0%Z in Hj'.
    specialize (Hp Hj').
    assert (Hpow0 : (0 < 10 ^ ((φ j) - 1))%Z) by (apply pow10_pos; nlia).
    assert (HR' : ((φ R) < 10 ^ ((φ j) - 1) * 10)%Z).
    { replace (φ j) with (Z.succ ((φ j) - 1)) in HR by nlia.
      rewrite Z.pow_succ_r in HR by nlia. nlia. }
    assert (Hc : (φ (R / p)) = ((φ R) / (φ p))%Z) by apply div_spec.
    assert (Hm : (φ (R mod p)) = ((φ R) mod (φ p))%Z) by apply mod_spec.
    assert (Hc9 : ((φ R) / (φ p) < 10)%Z) by (apply Z.div_lt_upper_bound; nlia).
    assert (Hc0 : (0 <= (φ R) / (φ p))%Z) by (apply Z.div_pos; nlia).
    assert (Hm0 : (0 <= (φ R) mod (φ p) < (φ p))%Z) by (apply Z.mod_pos_bound; nlia).
    assert (HcN : Z.to_N (φ (R / p)) = (Z.to_N (φ R) / 10 ^ Z.to_N ((φ j) - 1))%N).
    { rewrite Hc, Hp, Z2N.inj_div, Z2N.inj_pow by nlia. reflexivity. }
    assert (HmN : Z.to_N (φ (R mod p)) = (Z.to_N (φ R) mod 10 ^ Z.to_N ((φ j) - 1))%N).
    { rewrite Hm, Hp, Z2N.inj_mod, Z2N.inj_pow by nlia. reflexivity. }
    assert (HRN : (Z.to_N (φ R) < 10 ^ (Z.to_N ((φ j) - 1) + 1))%N).
    { apply N2Z.inj_lt. rewrite Z2N.id by nlia.
      rewrite N2Z.inj_pow, N2Z.inj_add, Z2N.id by nlia.
      rewrite Z.pow_add_r by nlia. change (Z.of_N 10) with 10%Z.
      change (Z.of_N 1) with 1%Z. nlia. }
    pose proof (walk_blockN (Z.to_N ((φ j) - 1)) (Z.to_N (φ t)) (Z.to_N (φ R)) HRN) as Hblock.
    rewrite <- HcN, <- HmN, Z_N_nat in Hblock.
    assert (Hc10 : ((φ (R / p)) <= 10)%Z) by (clear - Hc Hc9; lia).
    assert (Hc00 : ((φ 0) <= (φ (R / p)))%Z)
      by (change (φ 0) with 0%Z; clear - Hc Hc0; lia).
    assert (HmB : ((φ (R mod p)) < (φ p))%Z) by (clear - Hm Hm0; lia).
    clear HcN HmN HRN Hc Hm Hc9 Hc0 Hm0 HR' HR.
    assert (Hbase : (φ ((j - 1) * S1)) = (((φ j) - 1) * (φ S1))%Z).
    { apply base_eq; clear - Hj' HjD HD HS1b; nlia. }
    rewrite Hblock in Hb.
    pose proof (to_Z_bounded S1) as BS1.
    assert (Hrow : (((φ j) - 1) * (φ S1) + (φ t) < Dz * (φ S1))%Z)
      by (clear - Hj' HjD Hts HS1 BS1; nia).
    assert (Hlim : (Dz * (φ S1) < wB)%Z)
      by (rewrite wB_val; clear - HD HS1b BS1; nia).
    assert (Hbsb : ((φ acc) + Z.of_N (bsum (Z.to_N ((φ j) - 1)) (Z.to_N (φ t))
                                      (Z.to_nat (φ (R / p)))) < wB)%Z)
      by (clear - Hb; destruct (Z.to_N (φ (R / p)) <=? Z.to_N (φ t))%N; nlia).
    assert (Hk0 : (0 <= (φ j) - 1)%Z) by (clear - Hj'; nlia).
    assert (Hts' : ((φ t) < (φ S1))%Z) by (clear - Hts HS1; nlia).
    assert (Hacc0 : (0 <= (φ acc))%Z) by (clear - Bacc; nlia).
    assert (Hacc1 : (φ acc) = ((φ acc) + Z.of_N (bsum (Z.to_N ((φ j) - 1)) (Z.to_N (φ t))
                                               (Z.to_nat (φ 0))))%Z)
      by (change (Z.to_nat (φ 0)) with 0%nat; cbn [bsum]; ring).
    assert (Hrs := rowsum_spec T (φ S1) (Dz * (φ S1)) ((j - 1) * S1) t (R / p) ((φ j) - 1)
                     Ht Hk0 Hbase Hts' Hrow Hlim Hc10
                     (φ acc) _ 0 acc (Zwf_well_founded 0 (gap (R / p) 0)) eq_refl
                     Hc00 Hacc0 Hacc1 Hbsb).
    cbv zeta.
    destruct (t <? R / p) eqn:Etc.
    + rewrite ltb_spec in Etc.
      replace (Z.to_N (φ (R / p)) <=? Z.to_N (φ t))%N with false in Hblock
        by (symmetry; apply N.leb_gt; nlia).
      rewrite Hrs, Hblock. nlia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Etc.
      replace (Z.to_N (φ (R / p)) <=? Z.to_N (φ t))%N with true in Hblock, Hb
        by (symmetry; apply N.leb_le; nlia).
      assert (Hj1 : (φ (j - 1)) = ((φ j) - 1)%Z)
        by (rewrite sub_small; change (φ 1) with 1%Z; nlia).
      assert (Htc : Z.to_N (φ (t - R / p)) = (Z.to_N (φ t) - Z.to_N (φ (R / p)))%N)
        by (rewrite sub_small by nlia; nlia).
      rewrite (IH (φ (j - 1))).
      * rewrite Hrs, Htc, Hblock. nlia.
      * unfold Zwf. nlia.
      * reflexivity.
      * nlia.
      * rewrite Hj1. intros Hpos.
        rewrite div_spec, Hp. change (φ 10) with 10%Z.
        replace ((φ j) - 1)%Z with (Z.succ ((φ j) - 1 - 1)) at 1 by nlia.
        rewrite Z.pow_succ_r by nlia. rewrite Z.mul_comm, Z.div_mul by nlia.
        f_equal; nlia.
      * rewrite Hj1, <- Hp. exact HmB.
      * rewrite sub_small by nlia. nlia.
      * rewrite Hrs, Htc. nlia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj. change (φ 0) with 0%Z in Hj.
    assert (Ej : (φ j) = 0%Z) by nlia. rewrite Ej in HR. change (10 ^ 0)%Z with 1%Z in HR.
    replace (Z.to_N (φ R) + 1)%N with 1%N by nlia.
    rewrite cnt1 in *.
    destruct (t =? 0) eqn:E.
    + rewrite eqb_spec in E. subst t. change (Z.to_N (φ 0)) with 0%N in *.
      change (N.eqb 0 0) with true in *.
      change (Z.of_N (if true then 1 else 0)%N) with 1%Z in *.
      assert (Hc1 : cnt (Pd 0 0) (Z.to_N (φ R) + 1) = 1%N)
        by (replace (Z.to_N (φ R) + 1)%N with 1%N by nlia; reflexivity).
      rewrite Hc1 in Hb.
      rewrite add_small; change (φ 1) with 1%Z; nlia.
    + rewrite <- Bool.not_true_iff_false, eqb_spec in E.
      assert ((φ t) <> 0%Z) by (intro F; apply E; apply to_Z_inj; exact F).
      replace (Z.to_N (φ t) =? 0)%N with false by (symmetry; apply N.eqb_neq; nlia).
      nlia.
Qed.

(* ================================================================== *)
(* Prop side: the greedy construction                                  *)
(* ================================================================== *)

Lemma pick_spec : forall T S1 lim (base t : int) kk,
  tab_ok T S1 lim -> (0 <= kk)%Z -> (φ base) = (kk * S1)%Z ->
  ((φ t) < S1)%Z -> (kk * S1 + (φ t) < lim)%Z -> (lim < wB)%Z ->
  forall (Rl z : Z) (c r : int) (H : Acc (Zwf 0) (gap 9 c)),
  gap 9 c = z -> ((φ c) <= 9)%Z -> (1 <= (φ r))%Z ->
  ((φ r) + Z.of_N (bsum (Z.to_N kk) (Z.to_N (φ t)) (Z.to_nat (φ c))) = Rl)%Z ->
  (Rl <= Z.of_N (bsum (Z.to_N kk) (Z.to_N (φ t)) 10))%Z ->
  ((φ (fst (pick T base t c r H))) <= 9)%Z /\
  (1 <= (φ (snd (pick T base t c r H))))%Z /\
  ((φ (snd (pick T base t c r H)))
   + Z.of_N (bsum (Z.to_N kk) (Z.to_N (φ t)) (Z.to_nat (φ (fst (pick T base t c r H)))))
   = Rl)%Z /\
  ((φ (snd (pick T base t c r H)))
   <= Z.of_N (term (Z.to_N kk) (Z.to_N (φ t)) (Z.to_N (φ (fst (pick T base t c r H))))))%Z.
Proof.
  intros T S1 lim base t kk Ht Hk Hb Hts Hl HlwB Rl z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros c r H Hz Hc9 Hr HRl HRb.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded r).
  pose proof (vcell_spec T S1 lim base t c kk Ht Hk Hb Hts Hl HlwB) as Hv.
  rewrite pick_eq.
  destruct (bdec ((c <? 9) && (vcell T base t c <? r))) as [Hcd | Hcd].
  - destruct (andb_prop _ _ Hcd) as [Hc1 Hc2].
    pose proof Hc1 as H1'. rewrite ltb_spec in H1', Hc2. change (φ 9) with 9%Z in H1'.
    assert (Hcs1 : (φ (c + 1)) = ((φ c) + 1)%Z) by sia.
    assert (Hn1 : Z.to_nat ((φ c) + 1) = S (Z.to_nat (φ c))) by nlia.
    eapply IH; [ | reflexivity | nlia | rewrite sub_small; nlia | | exact HRb].
    + rewrite <- Hz. apply dec_step. exact Hc1.
    + rewrite sub_small by nlia. rewrite Hcs1, Hn1. cbn [bsum].
      replace (N.of_nat (Z.to_nat (φ c))) with (Z.to_N (φ c)) by nlia.
      rewrite N2Z.inj_add. nlia.
  - cbn [fst snd].
    destruct (c <? 9) eqn:E1; cbn in Hcd.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Hcd. nlia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E1. change (φ 9) with 9%Z in E1.
      replace (Z.to_nat (φ c)) with 9%nat in * by nlia.
      replace (Z.to_N (φ c)) with 9%N by nlia.
      change (bsum (Z.to_N kk) (Z.to_N (φ t)) 10)
        with (bsum (Z.to_N kk) (Z.to_N (φ t)) 9 + term (Z.to_N kk) (Z.to_N (φ t)) (N.of_nat 9))%N
        in HRb.
      change (N.of_nat 9) with 9%N in HRb. rewrite N2Z.inj_add in HRb.
      nlia.
Qed.

Lemma ds_shift : forall X C, (C < 10)%N -> ds (X * 10 + C) = (ds X + C)%N.
Proof.
  intros X C HC. pose proof (ds_split 1 X C ltac:(rewrite N.pow_1_r; exact HC)) as E.
  rewrite N.pow_1_r in E. rewrite E, (ds_small C HC). reflexivity.
Qed.

Lemma minwalk_spec : forall T (S1 s : int) (Dz r0 : Z),
  tab_ok T (φ S1) (Dz * (φ S1)) -> (φ S1) = ((φ s) + 1)%Z -> ((φ S1) <= 136)%Z ->
  (1 <= Dz <= 15)%Z ->
  forall (z : Z) (j t r x : int) (H : Acc (Zwf 0) (φ j)),
  (φ j) = z -> ((φ j) <= Dz)%Z -> ((φ t) <= (φ s))%Z ->
  (ds (Z.to_N (φ x)) + Z.to_N (φ t) = Z.to_N (φ s))%N ->
  ((φ x) < 10 ^ (Dz - (φ j)))%Z -> (1 <= (φ r))%Z ->
  ((φ r) <= Z.of_N (g (Z.to_N (φ j)) (Z.to_N (φ t))))%Z ->
  ((φ r) + Z.of_N (cnt (Pd 0 (Z.to_N (φ s))) (Z.to_N (φ x) * 10 ^ Z.to_N (φ j))) = r0)%Z ->
  ds (Z.to_N (φ (minwalk T S1 j t r x H))) = Z.to_N (φ s) /\
  (Z.of_N (cnt (Pd 0 (Z.to_N (φ s))) (Z.to_N (φ (minwalk T S1 j t r x H)))) + 1 = r0)%Z /\
  ((φ (minwalk T S1 j t r x H)) < 10 ^ Dz)%Z.
Proof.
  intros T S1 s Dz r0 Ht HS1 HS1b HD z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j t r x H Hz HjD Hts Hds Hx Hr Hrg Hinv.
  pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded t) as Bt.
  pose proof (to_Z_bounded r) as Br. pose proof (to_Z_bounded x) as Bx.
  pose proof pow10_15 as P15.
  rewrite minwalk_eq.
  destruct (bdec (0 <? j)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'. change (φ 0) with 0%Z in Hj'.
    cbv zeta.
    assert (Hbase : (φ ((j - 1) * S1)) = (((φ j) - 1) * (φ S1))%Z).
    { apply base_eq; clear - Hj' HjD HD HS1b; nlia. }
    assert (Hgj : g (Z.to_N (φ j)) (Z.to_N (φ t)) = bsum (Z.to_N ((φ j) - 1)) (Z.to_N (φ t)) 10).
    { rewrite <- g_succ. f_equal. nlia. }
    pose proof (to_Z_bounded S1) as BS1.
    assert (Hrow : (((φ j) - 1) * (φ S1) + (φ t) < Dz * (φ S1))%Z)
      by (clear - Hj' HjD Hts HS1 BS1; nia).
    assert (Hlim : (Dz * (φ S1) < wB)%Z)
      by (rewrite wB_val; clear - HD HS1b BS1; nia).
    pose proof (pick_spec T (φ S1) (Dz * (φ S1)) ((j - 1) * S1) t ((φ j) - 1)
                  Ht ltac:(nlia) Hbase ltac:(nlia) Hrow Hlim
                  (φ r) _ 0 r (Zwf_well_founded 0 (gap 9 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; nlia) Hr
                  ltac:(change (Z.to_nat (φ 0)) with 0%nat; cbn [bsum]; nlia)
                  ltac:(rewrite <- Hgj; exact Hrg)) as Hpk.
    destruct (pick T ((j - 1) * S1) t 0 r (Zwf_well_founded 0 (gap 9 0))) as [c r'].
    cbn [fst snd] in *.
    destruct Hpk as (Hc9 & Hr1 & Hrl & Hrt).
    pose proof (to_Z_bounded c) as Bc. pose proof (to_Z_bounded r') as Br'.
    unfold term in Hrt.
    destruct (Z.to_N (φ c) <=? Z.to_N (φ t))%N eqn:Ect; [| clear - Hrt Hr1; nlia].
    apply N.leb_le in Ect.
    assert (Hct : ((φ c) <= (φ t))%Z) by (clear - Ect Bc Bt; nlia).
    assert (Hdx : (0 <= Dz - (φ j))%Z) by (clear - HjD; lia).
    assert (HP := pow10_pos (Dz - (φ j)) Hdx).
    assert (HP15 : (10 ^ (Dz - (φ j) + 1) <= 10 ^ 15)%Z)
      by (apply pow10_le; clear - Hdx HD Hj'; lia).
    assert (HPs : (10 ^ (Dz - (φ j) + 1) = 10 ^ (Dz - (φ j)) * 10)%Z)
      by (rewrite Z.pow_add_r by lia; reflexivity).
    assert (Hx10 : (φ (x * 10)) = ((φ x) * 10)%Z).
    { apply mul_small; change (φ 10) with 10%Z.
      clear - Hx HP15 HPs P15 Bx. lia. }
    assert (Hx' : (φ (x * 10 + c)) = ((φ x) * 10 + (φ c))%Z).
    { rewrite add_small; rewrite Hx10; [reflexivity|].
      clear - Hx HP15 HPs P15 Bx Bc Hc9. lia. }
    assert (Hj1 : (φ (j - 1)) = ((φ j) - 1)%Z)
      by (rewrite sub_small; change (φ 1) with 1%Z; clear - Hj'; lia).
    assert (Htc : (φ (t - c)) = ((φ t) - (φ c))%Z) by (rewrite sub_small; [reflexivity | exact Hct]).
    assert (EX : Z.to_N (φ (x * 10 + c)) = (Z.to_N (φ x) * 10 + Z.to_N (φ c))%N)
      by (rewrite Hx'; clear - Bx Bc; lia).
    assert (EJ : Z.to_N (φ (j - 1)) = Z.to_N ((φ j) - 1)) by (rewrite Hj1; reflexivity).
    assert (ET : Z.to_N (φ (t - c)) = (Z.to_N (φ t) - Z.to_N (φ c))%N)
      by (rewrite Htc; clear - Hct Bc Bt; lia).
    apply (IH (φ (j - 1))).
    + unfold Zwf. clear - Hj1 Hz Hj'. lia.
    + reflexivity.
    + clear - Hj1 HjD. lia.
    + clear - Htc Hts Bc. lia.
    + rewrite EX, ET, ds_shift by (clear - Hc9 Bc; lia).
      clear - Hds Ect. lia.
    + rewrite Hx', Hj1. replace (Dz - ((φ j) - 1))%Z with (Dz - (φ j) + 1)%Z by lia.
      clear - Hx HPs Bc Hc9. lia.
    + exact Hr1.
    + rewrite EJ, ET. exact Hrt.
    + rewrite EX, EJ, min_block by (clear - Hds Hc9 Bc; lia).
      replace (Z.to_N ((φ j) - 1) + 1)%N with (Z.to_N (φ j)) by (clear - Hj'; lia).
      replace (Z.to_N (φ s) - ds (Z.to_N (φ x)))%N with (Z.to_N (φ t)) by (clear - Hds; lia).
      rewrite Z_N_nat. rewrite N2Z.inj_add.
      clear - Hrl Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj. change (φ 0) with 0%Z in Hj.
    assert (Ej : (φ j) = 0%Z) by nlia.
    rewrite Ej in Hx, Hrg, Hinv. change (Z.to_N 0) with 0%N in Hrg, Hinv.
    rewrite g_0 in Hrg. rewrite N.pow_0_r, N.mul_1_r in Hinv.
    replace (Dz - 0)%Z with Dz in Hx by nlia.
    destruct (Z.to_N (φ t) =? 0)%N eqn:E; [apply N.eqb_eq in E | nlia].
    split; [nlia | split; nlia].
Qed.

(* ================================================================== *)
(* The contract                                                        *)
(* ================================================================== *)

Lemma cudak_impl_correct : forall (a b s : N) (x y z : uint),
  valid_input a b s -> repr x a -> repr y b -> repr z s ->
  exists o : N * N, repr (cudak_impl x y z) o /\ cudak_spec a b s o.
Proof.
  intros a b s x y z Hv Ha Hb Hs.
  unfold repr, repr_uint in Ha, Hb, Hs. subst a b s.
  pose proof Hv as Hv'. destruct Hv' as [Hab Hbb Hsb [m0 [Hm0 Hd0]]].
  rewrite digit_sum_ds in Hd0.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). pose proof (to_Z_bounded z).
  pose proof pow10_15.
  change (10 ^ 15)%N with 1000000000000000%N in Hbb.
  assert (Hy15 : ((φ y) < 10 ^ 15)%Z)
    by (change (10 ^ 15)%Z with 1000000000000000%Z; nlia).
  assert (HS1 : (φ (z + 1)) = ((φ z) + 1)%Z)
    by (rewrite add_small; change (φ 1) with 1%Z; nlia).
  unfold cudak_impl. cbv zeta.
  destruct (digits_spec y Hy15 _ 1 1 (Zwf_well_founded 0 (gap 15 1)) eq_refl
              ltac:(change (φ 1) with 1%Z; nlia) ltac:(reflexivity)) as (HD & Hq & HbD).
  destruct (digits y 1 1 (Zwf_well_founded 0 (gap 15 1))) as [D q].
  cbn [fst snd] in *.
  assert (Hn : (φ (D * (z + 1))) = ((φ D) * (φ (z + 1)))%Z) by (apply mul_small; nia).
  destruct (tab_init (D * (z + 1)) (z + 1) ltac:(nlia) ltac:(nia) ltac:(nia)) as [Hl0 Ht0].
  destruct (fill_spec z (z + 1) (D * (z + 1)) (φ D) HS1 ltac:(nlia) HD Hn
              _ (z + 1) 1 0 _ (Zwf_well_founded 0 (gap (D * (z + 1)) (z + 1))) eq_refl Hl0
              ltac:(change (φ 1) with 1%Z; change (φ 0) with 0%Z; nlia)
              ltac:(change (φ 1) with 1%Z; nlia)
              ltac:(change (φ 0) with 0%Z; nlia)
              ltac:(nia) Ht0) as [_ Ht].
  rewrite Hn in Ht.
  set (T := fill _ z (z + 1) (D * (z + 1)) (z + 1) 1 0 _) in *.
  (* the count up to b *)
  pose proof (cnt_le (Pd 0 (Z.to_N (φ z))) (Z.to_N (φ y) + 1)) as Hcb_le.
  assert (Hcb := walk_spec T (z + 1) z (φ D) Ht HS1 ltac:(nlia) HD _ D q y z 0
                  (Zwf_well_founded 0 (φ D)) eq_refl ltac:(nlia) ltac:(intros; exact Hq)
                  HbD ltac:(nlia) ltac:(change (φ 0) with 0%Z; rewrite wB_val; nlia)).
  change (φ 0) with 0%Z in Hcb.
  (* the count below a *)
  assert (Hx1 : (φ (x - 1)) = ((φ x) - 1)%Z)
    by (rewrite sub_small; change (φ 1) with 1%Z; nlia).
  assert (Hxa : (Z.to_N (φ (x - 1)) + 1)%N = Z.to_N (φ x)) by (rewrite Hx1; nlia).
  pose proof (cnt_le (Pd 0 (Z.to_N (φ z))) (Z.to_N (φ x))) as Hca_le.
  assert (Hca := walk_spec T (z + 1) z (φ D) Ht HS1 ltac:(nlia) HD _ D q (x - 1) z 0
                  (Zwf_well_founded 0 (φ D)) eq_refl ltac:(nlia) ltac:(intros; exact Hq)
                  ltac:(rewrite Hx1; nlia) ltac:(nlia)
                  ltac:(rewrite Hxa; change (φ 0) with 0%Z; rewrite wB_val; nlia)).
  change (φ 0) with 0%Z in Hca. rewrite Hxa in Hca.
  set (cb := walk T (z + 1) D q y z 0 _) in *.
  set (ca := walk T (z + 1) D q (x - 1) z 0 _) in *.
  (* the rank of the smallest one *)
  assert (Hlt : (cnt (Pd 0 (Z.to_N (φ z))) (Z.to_N (φ x)) < cnt (Pd 0 (Z.to_N (φ z))) (Z.to_N (φ y) + 1))%N).
  { apply (cnt_strict _ m0); [apply Pd_true; exact Hd0 | nlia | nlia]. }
  assert (HbP : (Z.to_N (φ y) + 1 <= 10 ^ Z.to_N (φ D))%N).
  { apply N2Z.inj_le. rewrite N2Z.inj_add, Npow10_Z, Z2N.id by nlia. nlia. }
  pose proof (cnt_mono (Pd 0 (Z.to_N (φ z))) _ _ HbP) as Hmono.
  assert (Hca1 : (φ (ca + 1)) = ((φ ca) + 1)%Z)
    by (rewrite add_small; change (φ 1) with 1%Z; nlia).
  destruct (minwalk_spec T (z + 1) z (φ D) (Z.of_N (cnt (Pd 0 (Z.to_N (φ z))) (Z.to_N (φ x))) + 1)
              Ht HS1 ltac:(nlia) HD _ D z (ca + 1) 0 (Zwf_well_founded 0 (φ D)) eq_refl
              ltac:(nlia) ltac:(nlia)
              ltac:(change (Z.to_N (φ 0)) with 0%N; rewrite ds_0; reflexivity)
              ltac:(change (φ 0) with 0%Z; rewrite Z.sub_diag; reflexivity)
              ltac:(nlia)
              ltac:(unfold g; nlia)
              ltac:(change (Z.to_N (φ 0)) with 0%N; rewrite N.mul_0_l, cnt_0; nlia))
    as (Hmds & Hmcnt & _).
  set (m := minwalk T (z + 1) D z (ca + 1) 0 _) in *.
  assert (Hsub : (φ (cb - ca)) = ((φ cb) - (φ ca))%Z)
    by (rewrite sub_small; [reflexivity | nlia]).
  exists (Z.to_N (φ (cb - ca)), Z.to_N (φ m)). split.
  - split; reflexivity.
  - replace (Z.to_N (φ (cb - ca)))
      with (cnt (Pd 0 (Z.to_N (φ z))) (Z.to_N (φ y) + 1) - cnt (Pd 0 (Z.to_N (φ z))) (Z.to_N (φ x)))%N by nlia.
    apply spec_from_counts; [exact Hv | exact Hmds | nlia].
Qed.

(* ================================================================== *)
(* The spec's items, at top level                                      *)
(* ================================================================== *)

Definition cudak : uint -> uint -> uint -> uint * uint := cudak_impl.

Definition cudak_correct : forall (a b s : N) (x y z : uint),
  valid_input a b s -> repr x a -> repr y b -> repr z s ->
  exists o : N * N, repr (cudak x y z) o /\ cudak_spec a b s o
  := cudak_impl_correct.
