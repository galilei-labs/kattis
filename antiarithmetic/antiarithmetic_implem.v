(* Implementation of antiarithmetic (antiarithmetic.spec):
   bitset scan over positions, the steps of a middle value tested 63 at a
   time (W = 63, every bit of a Uint63 word).

   Code.  n = |x|.  Two flat bitsets S and R of n/63 + 1 words each (bit v
   of a bitset is bit v mod 63 of word v / 63).  Scanning the positions
   left to right, with m = x.[pos] the value there: bit v of S is set iff
   value v was seen at an earlier position, and bit n-1-v of R likewise
   (R is S mirrored).  With L = min(m, n-1-m), a progression with middle m
   exists iff some step e in [1, L] has exactly one of m-e, m+e seen; bit
   S[m+e] is bit e-1 of S read from offset m+1, bit S[m-e] = R[n-1-m+e] is
   bit e-1 of R read from offset n-m.  [inner] reads both 63-bit slices
   from those offsets (offset 63a + r: (w[a] >> r) lor (w[a+1] << (63-r)),
   the r = 0 case giving w[a+1] << 63 = 0), XORs them, masks the last one
   to its rem <= 63 valid steps with (1 << rem) - 1 (= all ones for
   rem = 63), and stops on the first nonzero word.  Otherwise bit m of S
   and bit n-1-m of R are set ([setbit], one read-modify-write each on the
   latest version) and the scan goes on; true after the last position.

   Termination: both loops recurse on an erased [Acc (Zwf 0) _] proof (the
   template's device): [scan] on n - pos, [inner] on rem.  No nat, no Z
   in the code. *)

From Antiarithmetic.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
From KattisLib Require Import Cost.
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

Lemma wB_pow : wB = (2 ^ 63)%Z.
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

Lemma aget_make : forall (n : int) (b i : int), (PArray.make n b).[i] = b.
Proof. intros n b i. exact (get_make int b n i). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

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
Elpi complexity negb.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* The measure of [inner], named and sealed against cbn (the cost proof's
   cost_simpl would otherwise unfold φ of a variable). *)
Definition meas (r : int) : Z := φ r.
Arguments meas : simpl never.

Lemma rem_dec : forall rem : int,
  (rem <=? 63) = false -> Zwf 0 (meas (rem - 63)) (meas rem).
Proof.
  unfold meas.
  intros rem H. rewrite <- not_true_iff_false, leb_spec in H.
  change (φ 63) with 63%Z in H.
  assert (H1 : (φ (rem - 63)) = ((φ rem) - 63)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* true iff some j < rem has bit (63 aS + rS + j) of S different from bit
   (63 aR + rR + j) of R; lS = 63 - rS, lR = 63 - rR. *)
Fixpoint inner (S R : array int) (rS lS rR lR : int) (aS aR rem : int)
    (H : Acc (Zwf 0) (meas rem)) {struct H} : bool :=
  let w := ((S.[aS] >> rS) lor (S.[aS + 1] << lS))
           lxor ((R.[aR] >> rR) lor (R.[aR + 1] << lR)) in
  match bdec (rem <=? 63) with
  | left _ => negb ((w land ((1 << rem) - 1)) =? 0)
  | right Hr =>
      if w =? 0
      then inner S R rS lS rR lR (aS + 1) (aR + 1) (rem - 63)
             (Acc_inv H (rem_dec rem Hr))
      else true
  end.
Elpi complexity inner.
Arguments inner_cost : simpl never.

Lemma inner_eq : forall S R rS lS rR lR aS aR rem H,
  inner S R rS lS rR lR aS aR rem H =
  let w := ((S.[aS] >> rS) lor (S.[aS + 1] << lS))
           lxor ((R.[aR] >> rR) lor (R.[aR + 1] << lR)) in
  match bdec (rem <=? 63) with
  | left _ => negb ((w land ((1 << rem) - 1)) =? 0)
  | right Hr =>
      if w =? 0
      then inner S R rS lS rR lR (aS + 1) (aR + 1) (rem - 63)
             (Acc_inv H (rem_dec rem Hr))
      else true
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Set bit v of the bitset t. *)
Definition setbit (t : array int) (v : int) : array int :=
  let a := v / 63 in t.[a <- t.[a] lor (1 << (v mod 63))].
Elpi complexity setbit.
Arguments setbit_cost : simpl never.

Fixpoint scan (x : array uint) (n : int) (S R : array int) (pos : int)
    (H : Acc (Zwf 0) (gap n pos)) {struct H} : bool :=
  match bdec (pos <? n) with
  | left Hp =>
      let m : int := x.[pos] in
      let c := n - 1 - m in
      let L := if m <? c then m else c in
      let oS := m + 1 in
      let oR := n - m in
      let rS := oS mod 63 in
      let rR := oR mod 63 in
      if inner S R rS (63 - rS) rR (63 - rR) (oS / 63) (oR / 63) L
           (Zwf_well_founded 0 (meas L))
      then false
      else scan x n (setbit S m) (setbit R c) (pos + 1)
             (Acc_inv H (dec_step n pos Hp))
  | right _ => true
  end.
Elpi complexity scan.
Arguments scan_cost : simpl never.

Lemma scan_eq : forall x n S R pos H,
  scan x n S R pos H =
  match bdec (pos <? n) with
  | left Hp =>
      let m : int := x.[pos] in
      let c := n - 1 - m in
      let L := if m <? c then m else c in
      let oS := m + 1 in
      let oR := n - m in
      let rS := oS mod 63 in
      let rR := oR mod 63 in
      if inner S R rS (63 - rS) rR (63 - rR) (oS / 63) (oR / 63) L
           (Zwf_well_founded 0 (meas L))
      then false
      else scan x n (setbit S m) (setbit R c) (pos + 1)
             (Acc_inv H (dec_step n pos Hp))
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition antiarithmetic_impl (x : array uint) : bool :=
  let n := PArray.length x in
  let k := n / 63 + 1 in
  scan x n (PArray.make k 0) (PArray.make k 0) 0 (Zwf_well_founded 0 (gap n 0)).
Elpi complexity antiarithmetic_impl.
Arguments antiarithmetic_impl_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Bit level                                                           *)
(* ------------------------------------------------------------------ *)

(* Bit v of the bitset t. *)
Definition tb (t : array int) (v : Z) : bool :=
  Z.testbit (φ (t.[of_Z (v / 63)])) (v mod 63).

Lemma of_Z_succ : forall z : Z, of_Z (z + 1) = of_Z z + 1.
Proof.
  intros z. apply to_Z_inj. rewrite add_spec, !of_Z_spec.
  change (φ 1) with 1%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma testbit_int_high : forall (w : int) (j : Z), (63 <= j)%Z ->
  Z.testbit (φ w) j = false.
Proof.
  intros w j Hj. pose proof (to_Z_bounded w) as B.
  rewrite <- (Z.mod_small (φ w) (2 ^ 63))
    by (change (2 ^ 63)%Z with 9223372036854775808%Z; lia).
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma slice_bit : forall (t : array int) (o j : Z) (a r l : int),
  (0 <= o)%Z -> (0 <= j < 63)%Z ->
  (φ r) = (o mod 63)%Z -> (φ l) = (63 - o mod 63)%Z -> a = of_Z (o / 63) ->
  Z.testbit (φ ((t.[a] >> r) lor (t.[a + 1] << l))) j = tb t (o + j).
Proof.
  intros t o j a r l Ho Hj Hr Hl Ha.
  assert (Hm : (0 <= o mod 63 < 63)%Z) by (apply Z.mod_pos_bound; lia).
  rewrite lor_spec', Z.lor_spec, lsr_spec, lsl_spec, Hr, Hl, wB_pow.
  rewrite Z.div_pow2_bits by lia.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.mul_pow2_bits by lia.
  unfold tb.
  destruct (Z_lt_le_dec (j + o mod 63) 63) as [Hc | Hc].
  - assert (E1 : ((o + j) / 63 = o / 63)%Z)
      by (Z.to_euclidean_division_equations; lia).
    assert (E2 : ((o + j) mod 63 = j + o mod 63)%Z)
      by (Z.to_euclidean_division_equations; lia).
    rewrite E1, E2, <- Ha.
    rewrite (Z.testbit_neg_r _ (j - (63 - o mod 63))) by lia.
    apply orb_false_r.
  - assert (E1 : ((o + j) / 63 = o / 63 + 1)%Z)
      by (Z.to_euclidean_division_equations; lia).
    assert (E2 : ((o + j) mod 63 = j - (63 - o mod 63))%Z)
      by (Z.to_euclidean_division_equations; lia).
    rewrite E1, E2, of_Z_succ, <- Ha.
    rewrite testbit_int_high by lia. reflexivity.
Qed.

Lemma eqb0_true : forall y : int,
  (y =? 0) = true <-> forall j, (0 <= j < 63)%Z -> Z.testbit (φ y) j = false.
Proof.
  intros y. rewrite Uint63.eqb_spec. split.
  - intros -> j _. change (φ 0) with 0%Z. apply Z.testbit_0_l.
  - intros H. apply to_Z_inj. change (φ 0) with 0%Z. apply Z.bits_inj_0.
    intros j. destruct (Z_lt_le_dec j 0) as [H0 | H0].
    + apply Z.testbit_neg_r. exact H0.
    + destruct (Z_lt_le_dec j 63) as [H1 | H1].
      * apply H. lia.
      * apply testbit_int_high. exact H1.
Qed.

Lemma eqb0_false : forall y : int,
  (y =? 0) = false <-> exists j, (0 <= j < 63)%Z /\ Z.testbit (φ y) j = true.
Proof.
  intros y. split.
  - intros H. rewrite <- not_true_iff_false, Uint63.eqb_spec in H.
    assert (Hy : (φ y) <> 0%Z).
    { intro E. apply H. apply to_Z_inj. exact E. }
    pose proof (to_Z_bounded y) as B.
    assert (Hb : Z.testbit (φ y) (Z.log2 (φ y)) = true) by (apply Z.bit_log2; lia).
    exists (Z.log2 (φ y)). split; [| exact Hb].
    split; [apply Z.log2_nonneg |].
    destruct (Z_lt_le_dec (Z.log2 (φ y)) 63) as [Hl | Hl]; [exact Hl |].
    rewrite testbit_int_high in Hb by exact Hl. discriminate.
  - intros (j & Hj & Hb). rewrite <- not_true_iff_false, eqb0_true.
    intros H. rewrite H in Hb by exact Hj. discriminate.
Qed.

Lemma mask_bits : forall (y rem : int) (j : Z), ((φ rem) <= 63)%Z -> (0 <= j)%Z ->
  Z.testbit (φ (y land ((1 << rem) - 1))) j = Z.testbit (φ y) j && (j <? (φ rem))%Z.
Proof.
  intros y rem j Hr Hj. pose proof (to_Z_bounded rem) as B.
  rewrite land_spec', Z.land_spec. f_equal.
  assert (Hm : (φ ((1 << rem) - 1)) = Z.ones (φ rem)).
  { rewrite sub_spec, lsl_spec. change (φ 1) with 1%Z. rewrite Z.mul_1_l.
    destruct (Z.eq_dec (φ rem) 63) as [E | E].
    - rewrite E. reflexivity.
    - assert (H2 : (1 <= 2 ^ (φ rem) < 2 ^ 63)%Z).
      { split.
        - change 1%Z with (2 ^ 0)%Z. apply Z.pow_le_mono_r; lia.
        - apply Z.pow_lt_mono_r; lia. }
      rewrite wB_pow. rewrite (Z.mod_small (2 ^ (φ rem))) by lia.
      rewrite Z.mod_small by lia. rewrite Z.ones_equiv. lia. }
  rewrite Hm, Z.testbit_ones by lia.
  replace (0 <=? j)%Z with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma xorb_neq : forall a b : bool, xorb a b = true <-> a <> b.
Proof. intros [] []; cbn; split; intro H; congruence. Qed.

(* The inner loop: some step j < rem has its two bits different. *)
Lemma inner_spec : forall (S R : array int) (rS lS rR lR : int),
  (φ lS) = (63 - (φ rS))%Z -> (φ lR) = (63 - (φ rR))%Z ->
  forall (z : Z) (rem : int) (H : Acc (Zwf 0) (φ rem)) (oS oR : Z) (aS aR : int),
  (φ rem) = z ->
  (0 <= oS)%Z -> (0 <= oR)%Z ->
  (oS mod 63)%Z = (φ rS) -> (oR mod 63)%Z = (φ rR) ->
  aS = of_Z (oS / 63) -> aR = of_Z (oR / 63) ->
  (inner S R rS lS rR lR aS aR rem H = true <->
   exists j, (0 <= j < (φ rem))%Z /\ tb S (oS + j) <> tb R (oR + j)).
Proof.
  intros S R rS lS rR lR HlS HlR z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros rem H oS oR aS aR Hz HoS HoR HrS HrR HaS HaR.
  rewrite inner_eq. cbv zeta.
  set (w := ((S.[aS] >> rS) lor (S.[aS + 1] << lS))
            lxor ((R.[aR] >> rR) lor (R.[aR + 1] << lR))).
  assert (Hw : forall j, (0 <= j < 63)%Z ->
            Z.testbit (φ w) j = xorb (tb S (oS + j)) (tb R (oR + j))).
  { intros j Hj. unfold w. rewrite lxor_spec', Z.lxor_spec.
    rewrite (slice_bit S oS j aS rS lS), (slice_bit R oR j aR rR lR); auto; lia. }
  pose proof (to_Z_bounded rem) as Brem.
  destruct (bdec (rem <=? 63)) as [Hr | Hr].
  - rewrite leb_spec in Hr. change (φ 63) with 63%Z in Hr.
    rewrite negb_true_iff, eqb0_false. split.
    + intros (j & Hj & Hb). rewrite mask_bits in Hb by lia.
      apply andb_true_iff in Hb as [Hb1 Hb2]. rewrite Hw in Hb1 by lia.
      apply Z.ltb_lt in Hb2. exists j. split; [lia |]. apply xorb_neq. exact Hb1.
    + intros (j & Hj & Hne). exists j. split; [lia |].
      rewrite mask_bits by lia. rewrite Hw by lia. apply andb_true_iff. split.
      * apply xorb_neq. exact Hne.
      * apply Z.ltb_lt. lia.
  - pose proof Hr as Hr'. rewrite <- not_true_iff_false, leb_spec in Hr'.
    change (φ 63) with 63%Z in Hr'.
    assert (Hrem : (φ (rem - 63)) = ((φ rem) - 63)%Z) by sia.
    destruct (w =? 0) eqn:E0.
    + rewrite eqb0_true in E0.
      rewrite (IH (φ (rem - 63)) ltac:(rewrite <- Hz; apply rem_dec; exact Hr)
                 (rem - 63) _ (oS + 63)%Z (oR + 63)%Z (aS + 1) (aR + 1)).
      2: reflexivity.
      2, 3: lia.
      2: rewrite <- HrS; Z.to_euclidean_division_equations; lia.
      2: rewrite <- HrR; Z.to_euclidean_division_equations; lia.
      2: rewrite HaS, <- of_Z_succ; f_equal;
         Z.to_euclidean_division_equations; lia.
      2: rewrite HaR, <- of_Z_succ; f_equal;
         Z.to_euclidean_division_equations; lia.
      split.
      * intros (j & Hj & Hne). exists (j + 63)%Z. split; [lia |].
        replace (oS + (j + 63))%Z with (oS + 63 + j)%Z by lia.
        replace (oR + (j + 63))%Z with (oR + 63 + j)%Z by lia. exact Hne.
      * intros (j & Hj & Hne).
        destruct (Z_lt_le_dec j 63) as [Hj63 | Hj63].
        -- exfalso. apply xorb_neq in Hne. rewrite <- Hw in Hne by lia.
           rewrite E0 in Hne by lia. discriminate.
        -- exists (j - 63)%Z. split; [lia |].
           replace (oS + 63 + (j - 63))%Z with (oS + j)%Z by lia.
           replace (oR + 63 + (j - 63))%Z with (oR + j)%Z by lia. exact Hne.
    + split; [intros _ | reflexivity].
      apply eqb0_false in E0. destruct E0 as (j & Hj & Hb).
      rewrite Hw in Hb by exact Hj. apply xorb_neq in Hb.
      exists j. split; [lia | exact Hb].
Qed.

Lemma l63 : forall a : int, (φ (63 - a mod 63)) = (63 - (φ (a mod 63)))%Z.
Proof. intros a. sia. Qed.

Lemma setbit_length : forall (t : array int) (v : int),
  PArray.length (setbit t v) = PArray.length t.
Proof. intros t v. unfold setbit. apply alength_set. Qed.

Lemma setbit_tb : forall (t : array int) (v : int) (u : Z),
  ((φ v) / 63 < (φ (PArray.length t)))%Z -> (0 <= u < wB)%Z ->
  tb (setbit t v) u = tb t u || (u =? (φ v))%Z.
Proof.
  intros t v u Hv Hu. unfold setbit, tb. cbv zeta.
  pose proof (to_Z_bounded v) as Bv. rewrite wB_val in Hu.
  assert (Hdv : (φ (v / 63)) = ((φ v) / 63)%Z) by (rewrite div_spec; reflexivity).
  assert (Hmv : (φ (v mod 63)) = ((φ v) mod 63)%Z) by (rewrite mod_spec; reflexivity).
  assert (Hu63 : (0 <= u / 63 < 9223372036854775808)%Z)
    by (Z.to_euclidean_division_equations; lia).
  destruct (Z.eq_dec (u / 63) ((φ v) / 63)) as [E | E].
  - assert (Ei : of_Z (u / 63) = v / 63).
    { apply to_Z_inj. rewrite of_Z_spec, Hdv, E, wB_val.
      apply Z.mod_small. rewrite <- E. exact Hu63. }
    rewrite Ei, aget_set_same by (rewrite ltb_spec, Hdv; exact Hv).
    rewrite lor_spec', Z.lor_spec, lsl_spec, Hmv.
    change (φ 1) with 1%Z. rewrite Z.mul_1_l.
    assert (Hm : (0 <= (φ v) mod 63 < 63)%Z) by (apply Z.mod_pos_bound; lia).
    rewrite (Z.mod_small (2 ^ ((φ v) mod 63))).
    2: { rewrite wB_pow. split; [apply Z.pow_nonneg; lia |].
         apply Z.pow_lt_mono_r; lia. }
    rewrite Z.pow2_bits_eqb by lia. f_equal.
    apply eq_iff_eq_true. rewrite !Z.eqb_eq. split; intro F.
    + Z.to_euclidean_division_equations; lia.
    + subst u. reflexivity.
  - rewrite aget_set_other.
    + replace (u =? (φ v))%Z with false; [rewrite orb_false_r; reflexivity |].
      symmetry. apply Z.eqb_neq. intro F. apply E. rewrite F. reflexivity.
    + intro F. apply E. apply (f_equal to_Z) in F.
      rewrite of_Z_spec, Hdv, wB_val, Z.mod_small in F by exact Hu63.
      symmetry. exact F.
Qed.

Lemma tb_make : forall (k : int) (u : Z), tb (PArray.make k 0) u = false.
Proof.
  intros k u. unfold tb. rewrite aget_make. change (φ 0) with 0%Z.
  apply Z.testbit_0_l.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side                                                           *)
(* ------------------------------------------------------------------ *)

Definition nz (p : list N) : Z := Z.of_nat (List.length p).

(* p_i, read in Z *)
Definition gz (p : list N) (i : Z) : Z :=
  Z.of_N (Prelude.get p (Z.to_N i)).

(* value v sits at a position below pos *)
Definition seen (p : list N) (pos v : Z) : Prop :=
  exists i, (0 <= i < pos)%Z /\ gz p i = v.

(* p_j is the middle of a progression *)
Definition hitp (p : list N) (j : Z) : Prop :=
  exists i k, (0 <= i < j /\ j < k < nz p)%Z /\ (gz p i - gz p j = gz p j - gz p k)%Z.

Section Perm.
  Variable p : list N.
  Hypothesis Hp : valid_input p.

  Lemma gz_range : forall i, (0 <= i < nz p)%Z -> (0 <= gz p i < nz p)%Z.
  Proof.
    intros i Hi. destruct Hp as [_ Hv _]. unfold gz, Prelude.get.
    rewrite Forall_forall in Hv.
    assert (Hin : In (nth (N.to_nat (Z.to_N i)) p 0%N) p).
    { apply nth_In. unfold nz in Hi. lia. }
    specialize (Hv _ Hin). unfold len in Hv. unfold nz. lia.
  Qed.

  Lemma gz_inj : forall i k, (0 <= i < nz p)%Z -> (0 <= k < nz p)%Z ->
    gz p i = gz p k -> i = k.
  Proof.
    intros i k Hi Hk E. destruct Hp as [_ _ Hd]. unfold gz, Prelude.get in E.
    apply N2Z.inj in E. rewrite !Z_N_nat in E.
    rewrite (NoDup_nth p 0%N) in Hd.
    unfold nz in Hi, Hk.
    specialize (Hd (Z.to_nat i) (Z.to_nat k) ltac:(lia) ltac:(lia) E). lia.
  Qed.

  Lemma gz_surj : forall v, (0 <= v < nz p)%Z ->
    exists i, (0 <= i < nz p)%Z /\ gz p i = v.
  Proof.
    intros v Hv'. destruct Hp as [_ Hv Hd].
    assert (Hincl : incl (map N.of_nat (seq 0 (List.length p))) p).
    { apply NoDup_length_incl; [exact Hd | rewrite length_map, length_seq; lia |].
      intros a Ha. rewrite Forall_forall in Hv. apply in_map_iff.
      exists (N.to_nat a). split; [lia |]. apply in_seq.
      specialize (Hv a Ha). unfold len in Hv. lia. }
    assert (Hin : In (Z.to_N v) p).
    { apply Hincl. apply in_map_iff. exists (Z.to_nat v). split; [lia |].
      apply in_seq. unfold nz in Hv'. lia. }
    apply (In_nth p _ 0%N) in Hin. destruct Hin as (k & Hk & Hnth).
    exists (Z.of_nat k). split; [unfold nz; lia |].
    unfold gz, Prelude.get. replace (N.to_nat (Z.to_N (Z.of_nat k))) with k by lia.
    rewrite Hnth. lia.
  Qed.

  (* The middle value m = p_j has a step e in [1, min(m, n-1-m)] with
     exactly one of m+e, m-e seen before j, iff p_j is the middle of a
     progression. *)
  Lemma hit_iff : forall j, (0 <= j < nz p)%Z ->
    ((exists e, (1 <= e <= Z.min (gz p j) (nz p - 1 - gz p j))%Z /\
       ((seen p j (gz p j + e) /\ ~ seen p j (gz p j - e)) \/
        (~ seen p j (gz p j + e) /\ seen p j (gz p j - e))))
     <-> hitp p j).
  Proof.
    intros j Hj.
    pose proof (gz_range j Hj) as Hmj.
    split.
    - intros (e & He & [[(i & Hi & Ei) Hns] | [Hns (i & Hi & Ei)]]).
      + destruct (gz_surj (gz p j - e) ltac:(lia)) as (k & Hk & Ek).
        destruct (Z.lt_trichotomy k j) as [Hkj | [Hkj | Hkj]].
        * exfalso. apply Hns. exists k. split; [lia | exact Ek].
        * subst k. lia.
        * exists i, k. split; [lia |]. lia.
      + destruct (gz_surj (gz p j + e) ltac:(lia)) as (k & Hk & Ek).
        destruct (Z.lt_trichotomy k j) as [Hkj | [Hkj | Hkj]].
        * exfalso. apply Hns. exists k. split; [lia | exact Ek].
        * subst k. lia.
        * exists i, k. split; [lia |]. lia.
    - intros (i & k & Hik & Eq).
      pose proof (gz_range i ltac:(lia)) as Hri.
      pose proof (gz_range k ltac:(lia)) as Hrk.
      assert (Hne : gz p i <> gz p j).
      { intro E. apply gz_inj in E; lia. }
      destruct (Z_lt_le_dec (gz p i) (gz p j)) as [Hl | Hl].
      + exists (gz p j - gz p i)%Z. split; [lia |]. right. split.
        * intros (i' & Hi' & Ei').
          assert (i' = k) by (apply gz_inj; lia). lia.
        * exists i. split; [lia | lia].
      + exists (gz p i - gz p j)%Z. split; [lia |]. left. split.
        * exists i. split; [lia | lia].
        * intros (i' & Hi' & Ei').
          assert (i' = k) by (apply gz_inj; lia). lia.
  Qed.
End Perm.

Lemma seen_succ : forall p pos v, (0 <= pos)%Z ->
  (seen p (pos + 1) v <-> seen p pos v \/ gz p pos = v).
Proof.
  intros p pos v Hpos. split.
  - intros (i & Hi & E). destruct (Z.eq_dec i pos) as [-> | Hn].
    + right. exact E.
    + left. exists i. split; [lia | exact E].
  - intros [(i & Hi & E) | E].
    + exists i. split; [lia | exact E].
    + exists pos. split; [lia | exact E].
Qed.

Lemma neq_bool_iff : forall (b1 b2 : bool) (P Q : Prop),
  (b1 = true <-> P) -> (b2 = true <-> Q) ->
  (b1 <> b2 <-> (P /\ ~ Q) \/ (~ P /\ Q)).
Proof.
  intros [] [] P Q H1 H2; rewrite <- H1, <- H2; intuition congruence.
Qed.

Lemma has_prog_iff : forall p,
  has_progression p <-> exists j, (0 <= j < nz p)%Z /\ hitp p j.
Proof.
  intros p. unfold has_progression, hitp, progression, gz, nz, len. split.
  - intros (i & j & k & Hij & Hjk & Hk & E).
    exists (Z.of_N j). split; [lia |]. exists (Z.of_N i), (Z.of_N k).
    rewrite !N2Z.id. split; [lia | exact E].
  - intros (j & Hj & i & k & Hik & E).
    exists (Z.to_N i), (Z.to_N j), (Z.to_N k).
    split; [lia |]. split; [lia |]. split; [lia | exact E].
Qed.

(* ------------------------------------------------------------------ *)
(* The scan                                                            *)
(* ------------------------------------------------------------------ *)

(* Reading an in-bounds cell of an array representing p. *)
Lemma repr_get : forall (x : array uint) (p : list N), repr x p ->
  forall i : int, ((φ i) < nz p)%Z -> (φ (x.[i])) = gz p (φ i).
Proof.
  intros x p [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(unfold nz in Hi; lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  unfold gz, Prelude.get. rewrite Z_N_nat. erewrite nth_error_nth; [| exact Hm].
  rewrite <- Hr. rewrite Z2N.id by (pose proof (to_Z_bounded x.[i]); lia).
  reflexivity.
Qed.

Lemma repr_length : forall (x : array uint) (p : list N), repr x p ->
  (φ (PArray.length x)) = nz p.
Proof. intros x p [Hl _]. symmetry. exact Hl. Qed.

Lemma scan_spec : forall (p : list N) (x : array uint),
  valid_input p -> repr x p ->
  forall n : int, (φ n) = nz p ->
  forall (z : Z) (pos : int) (S R : array int) (H : Acc (Zwf 0) (gap n pos)),
  gap n pos = z -> ((φ pos) <= (φ n))%Z ->
  ((φ n) / 63 < (φ (PArray.length S)))%Z -> ((φ n) / 63 < (φ (PArray.length R)))%Z ->
  (forall v, (0 <= v < nz p)%Z ->
     (tb S v = true <-> seen p (φ pos) v) /\
     (tb R (nz p - 1 - v) = true <-> seen p (φ pos) v)) ->
  (scan x n S R pos H = false <->
   exists j, ((φ pos) <= j < nz p)%Z /\ hitp p j).
Proof.
  intros p x Hp Hx n Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros pos S R H Hz Hpn HS HR Hinv.
  pose proof Hp as Hp'. destruct Hp' as [Hnb _ _]. unfold len in Hnb.
  assert (Hnb' : (3 <= nz p <= 10000)%Z) by (unfold nz; lia).
  pose proof (to_Z_bounded pos) as Bpos.
  rewrite scan_eq.
  destruct (bdec (pos <? n)) as [Hlt | Hge].
  - cbv zeta.
    pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hm : (φ (x.[pos])) = gz p (φ pos)) by (apply repr_get; [exact Hx | lia]).
    pose proof (gz_range p Hp (φ pos) ltac:(lia)) as Hmr.
    set (m := x.[pos]) in *.
    assert (Hc : (φ (n - 1 - m)) = (nz p - 1 - (φ m))%Z) by sia.
    assert (HL : (φ (if m <? n - 1 - m then m else n - 1 - m))
                 = Z.min (φ m) (nz p - 1 - (φ m))).
    { destruct (m <? n - 1 - m) eqn:E.
      - rewrite ltb_spec, Hc in E. lia.
      - rewrite <- not_true_iff_false, ltb_spec, Hc in E. lia. }
    assert (Hm1 : (φ (m + 1)) = ((φ m) + 1)%Z) by sia.
    assert (Hnm : (φ (n - m)) = (nz p - (φ m))%Z) by sia.
    assert (Hinner :
      inner S R ((m + 1) mod 63) (63 - (m + 1) mod 63)
            ((n - m) mod 63) (63 - (n - m) mod 63)
            ((m + 1) / 63) ((n - m) / 63)
            (if m <? n - 1 - m then m else n - 1 - m)
            (Zwf_well_founded 0 (meas (if m <? n - 1 - m then m else n - 1 - m)))
      = true <-> hitp p (φ pos)).
    { rewrite (inner_spec S R ((m + 1) mod 63) (63 - (m + 1) mod 63)
                 ((n - m) mod 63) (63 - (n - m) mod 63) (l63 _) (l63 _) _ _ _
                 ((φ m) + 1)%Z (nz p - (φ m))%Z _ _ eq_refl).
      2, 3: lia.
      2: rewrite mod_spec, Hm1; reflexivity.
      2: rewrite mod_spec, Hnm; reflexivity.
      2: apply to_Z_inj; rewrite div_spec, Hm1, of_Z_spec, wB_val;
         symmetry; apply Z.mod_small; Z.to_euclidean_division_equations; lia.
      2: apply to_Z_inj; rewrite div_spec, Hnm, of_Z_spec, wB_val;
         symmetry; apply Z.mod_small; Z.to_euclidean_division_equations; lia.
      rewrite HL, <- (hit_iff p Hp (φ pos) ltac:(lia)), <- Hm.
      assert (Hpt : forall j, (0 <= j < Z.min (φ m) (nz p - 1 - (φ m)))%Z ->
        (tb S ((φ m) + 1 + j) <> tb R (nz p - (φ m) + j) <->
         (seen p (φ pos) ((φ m) + (j + 1)) /\ ~ seen p (φ pos) ((φ m) - (j + 1))) \/
         (~ seen p (φ pos) ((φ m) + (j + 1)) /\ seen p (φ pos) ((φ m) - (j + 1))))).
      { intros j Hj. apply neq_bool_iff.
        - replace ((φ m) + 1 + j)%Z with ((φ m) + (j + 1))%Z by lia.
          apply Hinv. lia.
        - replace (nz p - (φ m) + j)%Z with (nz p - 1 - ((φ m) - (j + 1)))%Z by lia.
          apply Hinv. lia. }
      split.
      - intros (j & Hj & Hne). exists (j + 1)%Z. split; [lia |].
        apply Hpt; [lia | exact Hne].
      - intros (e & He & Hor). exists (e - 1)%Z. split; [lia |].
        apply Hpt; [lia |].
        replace (e - 1 + 1)%Z with e by lia. exact Hor. }
    destruct (inner _ _ _ _ _ _ _ _ _ _) eqn:Ei.
    + split; [intros _ | reflexivity].
      exists (φ pos). split; [lia |]. apply Hinner. reflexivity.
    + assert (Hpos1 : (φ (pos + 1)) = ((φ pos) + 1)%Z) by sia.
      rewrite (IH (gap n (pos + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hlt)
                 (pos + 1) (setbit S m) (setbit R (n - 1 - m)) _ eq_refl).
      * split.
        -- intros (j & Hj & Hh). exists j. split; [lia | exact Hh].
        -- intros (j & Hj & Hh). exists j. split; [| exact Hh].
           destruct (Z.eq_dec j (φ pos)) as [-> | Hne]; [| lia].
           exfalso. apply Hinner in Hh. congruence.
      * lia.
      * rewrite setbit_length. exact HS.
      * rewrite setbit_length. exact HR.
      * intros v Hv. rewrite Hpos1, seen_succ by lia.
        rewrite !setbit_tb.
        -- rewrite !orb_true_iff, !Z.eqb_eq, Hc, Hm.
           destruct (Hinv v Hv) as [H1 H2]. rewrite H1, H2.
           split; split; intros [A | A]; first [left; exact A | right; lia].
        -- rewrite Hc. Z.to_euclidean_division_equations; lia.
        -- rewrite wB_val. lia.
        -- Z.to_euclidean_division_equations; lia.
        -- rewrite wB_val. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Hge.
    split; [discriminate |]. intros (j & Hj & _). lia.
Qed.

Lemma impl_false_iff : forall (p : list N) (x : array uint),
  valid_input p -> repr x p ->
  (antiarithmetic_impl x = false <-> has_progression p).
Proof.
  intros p x Hp Hx. pose proof (repr_length x p Hx) as Hn0.
  assert (Hk1 : (φ (PArray.length x / 63 + 1)) = ((φ (PArray.length x)) / 63 + 1)%Z).
  { rewrite add_spec, div_spec. change (φ 63) with 63%Z. change (φ 1) with 1%Z.
    pose proof (to_Z_bounded (PArray.length x)). rewrite Z.mod_small; [reflexivity |].
    Z.to_euclidean_division_equations; lia. }
  assert (Hn : (φ (PArray.length x)) = nz p) by exact Hn0. clear Hn0.
  pose proof Hp as Hp'. destruct Hp' as [Hnb _ _]. unfold len in Hnb.
  assert (Hnb' : (3 <= nz p <= 10000)%Z) by (unfold nz; lia).
  unfold antiarithmetic_impl. cbv zeta.
  set (S0 := PArray.make (PArray.length x / 63 + 1) 0).
  assert (Hk : PArray.length S0 = PArray.length x / 63 + 1).
  { unfold S0. rewrite alength_make.
    replace (PArray.length x / 63 + 1 <=? PArray.max_length) with true; [reflexivity |].
    symmetry. apply leb_spec. rewrite max_length_val.
    eapply Z.le_trans; [apply Z.eq_le_incl; exact Hk1 |].
    rewrite Hn. Z.to_euclidean_division_equations; lia. }
  assert (Hk' : ((φ (PArray.length x)) / 63 < (φ (PArray.length x / 63 + 1)))%Z) by lia.
  assert (H0 : ((φ 0) <= (φ (PArray.length x)))%Z)
    by (change (φ 0) with 0%Z; pose proof (to_Z_bounded (PArray.length x)); lia).
  assert (HS : ((φ (PArray.length x)) / 63 < (φ (PArray.length S0)))%Z)
    by (rewrite Hk; exact Hk').
  assert (Hi0 : forall v, (0 <= v < nz p)%Z ->
     (tb S0 v = true <-> seen p (φ 0) v) /\
     (tb S0 (nz p - 1 - v) = true <-> seen p (φ 0) v)).
  { intros v Hv. unfold S0. rewrite !tb_make. change (φ 0) with 0%Z.
    split; (split; [discriminate | intros (i & Hi & _); lia]). }
  refine (iff_trans (scan_spec p x Hp Hx (PArray.length x) Hn _ 0 S0 S0
            (Zwf_well_founded 0 (gap (PArray.length x) 0)) eq_refl H0 HS HS Hi0) _).
  rewrite has_prog_iff. change (φ 0) with 0%Z. reflexivity.
Qed.

(* The spec's match on the boolean answer, from the two iffs. *)
Lemma bool_match_of_iffs : forall (b : bool) (A B : Prop),
  (b = true <-> A) /\ (b = false <-> B) ->
  match b with true => A | false => B end.
Proof.
  intros [|] A B [H1 H2]; [apply H1 | apply H2]; reflexivity.
Qed.

Lemma antiarithmetic_impl_correct : forall (p : list N) (x : array uint),
  valid_input p -> repr x p ->
  exists b : bool, repr (antiarithmetic_impl x) b /\ antiarithmetic_spec p b.
Proof.
  intros p x Hp Hx. exists (antiarithmetic_impl x). split; [reflexivity |].
  pose proof (impl_false_iff p x Hp Hx) as E.
  unfold antiarithmetic_spec, is_antiarithmetic.
  destruct (antiarithmetic_impl x); split.
  - intros _ Hh. apply E in Hh. discriminate.
  - intros _. reflexivity.
  - discriminate.
  - intros Hn. exfalso. apply Hn. apply E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition antiarithmetic : array uint -> bool := antiarithmetic_impl.
Elpi complexity antiarithmetic.

Definition antiarithmetic_correct : forall (p : list N) (x : array uint),
  valid_input p -> repr x p ->
  exists b : bool, repr (antiarithmetic x) b /\ antiarithmetic_spec p b
  := antiarithmetic_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost bound                                                          *)
(* ------------------------------------------------------------------ *)

(* inner from rem: at most 100 * (rem / 63) + 100 steps (one word of 63
   steps per round); scan from pos: at most (100 * (n / 63) + 300) per
   remaining position, + 10, the middle value m = x.[pos] < n making
   L = min(m, n-1-m) < n; antiarithmetic_impl: (100 (n/63) + 300) n + 50.
   antiarithmetic_time: c1 = 300, c2 = 100. *)

From Stdlib Require Import ssreflect.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma negb_time b (w : bool_cost stepsCM b) : (cost (negb_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Ltac negb_bound := match goal with |- context [cost (negb_cost stepsCM ?b ?w)] => pose proof (negb_time b w) end.

Lemma rem_big (rem : int) : (rem <=? 63) = false ->
  (1 <= Nat.div (Z.to_nat (to_Z rem)) 63)%nat /\
  Nat.div (Z.to_nat (to_Z (rem - 63))) 63 = (Nat.div (Z.to_nat (to_Z rem)) 63 - 1)%nat.
Proof.
  intros H. rewrite <- not_true_iff_false, leb_spec in H. change (φ 63) with 63%Z in H.
  assert (E : φ (rem - 63) = (φ rem - 63)%Z) by (zify; Z.to_euclidean_division_equations; lia).
  rewrite E. pose proof (to_Z_bounded rem).
  rewrite Z2Nat.inj_sub; [lia|]. change (Z.to_nat 63) with 63%nat.
  remember (Z.to_nat (φ rem)) as r. assert (63 < r)%nat by lia.
  split.
  - apply Nat.div_le_lower_bound; lia.
  - replace r with ((r - 63) + 1 * 63)%nat at 2 by lia. rewrite Nat.div_add; lia.
Qed.

Lemma inner_time S SC R RC rS rSC lS lSC rR rRC lR lRC aS aSC aR aRC rem remC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (inner_cost stepsCM S SC) R RC) rS rSC) lS lSC) rR rRC) lR lRC) aS aSC) aR aRC) rem remC) H HC)
    <= 100 * Nat.div (Z.to_nat (to_Z rem)) 63 + 100)%nat.
Proof.
  unfold inner_cost. cbn.
  match goal with |- context [@cost ?T (?G S SC R RC rS rSC lS lSC rR rRC lR lRC aS aSC aR aRC rem remC H HC)] =>
    assert (HG : forall k aS aSC aR aRC rem remC H HC, (Nat.div (Z.to_nat (to_Z rem)) 63 <= k)%nat ->
       (cost (G S SC R RC rS rSC lS lSC rR rRC lR lRC aS aSC aR aRC rem remC H HC) <= 100 * k + 100)%nat) end.
  { induction k as [|k IH]; intros aS' aSC' aR' aRC' rem' remC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (rem' <=? 63) (bool_w (rem' <=? 63))) as HB;
      cost_destruct (bdec (rem' <=? 63)); cost_simpl; try (negb_bound; lia).
    - exfalso. pose proof (rem_big rem' e). lia.
    - pose proof (rem_big rem' e) as [Hb1 Hb2].
      assert (Hk' : (Nat.div (Z.to_nat (to_Z (rem' - 63))) 63 <= k)%nat) by lia.
      cost_destruct (((S.[aS'] >> rS) lor (S.[aS' + 1] << lS)) lxor ((R.[aR'] >> rR) lor (R.[aR' + 1] << lR)) =? 0); cost_simpl; try lia.
      match goal with |- context [@cost ?T (?G' S SC R RC rS rSC lS lSC rR rRC lR lRC (aS' + 1)%uint63 ?w1 (aR' + 1)%uint63 ?w2 (rem' - 63)%uint63 ?w3 ?a ?e)] =>
        have HI := (IH _ w1 _ w2 _ w3 a e Hk' : (@cost T (G' S SC R RC rS rSC lS lSC rR rRC lR lRC (aS' + 1)%uint63 w1 (aR' + 1)%uint63 w2 (rem' - 63)%uint63 w3 a e) <= _)%nat) end.
      lia. }
  match goal with |- context [@cost ?T (?G S SC R RC rS rSC lS lSC rR rRC lR lRC aS aSC aR aRC rem remC H HC)] =>
    exact (HG _ aS aSC aR aRC rem remC H HC (le_n _) : (@cost T (G S SC R RC rS rSC lS lSC rR rRC lR lRC aS aSC aR aRC rem remC H HC) <= _)%nat) end.
Qed.

Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  | |- context [cost (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (set_cost a b c) d e) f g)) with 0%nat
  | |- context [cost (extract (set_cost ?a ?b ?c) ?d ?e)] =>
      change (cost (extract (set_cost a b c) d e)) with 0%nat
  | |- context [cost (set_cost ?a ?b ?c)] =>
      change (cost (set_cost a b c)) with 0%nat
  end.

Lemma setbit_time t tC v vC : (cost (extract (setbit_cost stepsCM t tC) v vC) <= 30)%nat.
Proof. unfold setbit_cost. cost_simpl. set_simpl. lia. Qed.

Ltac gen_inner := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract (inner_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC) ?i ?iC) ?j ?jC =>
    let Hc := fresh "Hinner" in
    have Hc := (inner_time a aC b bC c cC d dC e eC f fC g gC h hC i iC j jC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.
Ltac gen_setbit := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (setbit_cost stepsCM ?a ?aC) ?b ?bC =>
    let Hc := fresh "Hset" in
    have Hc := (setbit_time a aC b bC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Ltac zpart f := repeat match goal with
  | |- context [cost (f stepsCM ?a ?b)] => change (cost (f stepsCM a b)) with 0%nat
  | |- context [cost (extract (f stepsCM ?a ?b) ?c ?d)] =>
      change (cost (extract (f stepsCM a b) c d)) with 0%nat
  | |- context [cost (extract (extract (f stepsCM ?a ?b) ?c ?d) ?c1 ?d1)] =>
      change (cost (extract (extract (f stepsCM a b) c d) c1 d1)) with 0%nat
  | |- context [cost (extract (extract (extract (f stepsCM ?a ?b) ?c ?d) ?c1 ?d1) ?c2 ?d2)] =>
      change (cost (extract (extract (extract (f stepsCM a b) c d) c1 d1) c2 d2)) with 0%nat
  | |- context [cost (extract (extract (extract (extract (f stepsCM ?a ?b) ?c ?d) ?c1 ?d1) ?c2 ?d2) ?c3 ?d3)] =>
      change (cost (extract (extract (extract (extract (f stepsCM a b) c d) c1 d1) c2 d2) c3 d3)) with 0%nat
  | |- context [cost (extract (extract (extract (extract (extract (f stepsCM ?a ?b) ?c ?d) ?c1 ?d1) ?c2 ?d2) ?c3 ?d3) ?c4 ?d4)] =>
      change (cost (extract (extract (extract (extract (extract (f stepsCM a b) c d) c1 d1) c2 d2) c3 d3) c4 d4)) with 0%nat
  | |- context [cost (extract (extract (extract (extract (extract (extract (f stepsCM ?a ?b) ?c ?d) ?c1 ?d1) ?c2 ?d2) ?c3 ?d3) ?c4 ?d4) ?c5 ?d5)] =>
      change (cost (extract (extract (extract (extract (extract (extract (f stepsCM a b) c d) c1 d1) c2 d2) c3 d3) c4 d4) c5 d5)) with 0%nat
  | |- context [cost (extract (extract (extract (extract (extract (extract (extract (f stepsCM ?a ?b) ?c ?d) ?c1 ?d1) ?c2 ?d2) ?c3 ?d3) ?c4 ?d4) ?c5 ?d5) ?c6 ?d6)] =>
      change (cost (extract (extract (extract (extract (extract (extract (extract (f stepsCM a b) c d) c1 d1) c2 d2) c3 d3) c4 d4) c5 d5) c6 d6)) with 0%nat
  | |- context [cost (extract (extract (extract (extract (extract (extract (extract (extract (f stepsCM ?a ?b) ?c ?d) ?c1 ?d1) ?c2 ?d2) ?c3 ?d3) ?c4 ?d4) ?c5 ?d5) ?c6 ?d6) ?c7 ?d7)] =>
      change (cost (extract (extract (extract (extract (extract (extract (extract (extract (f stepsCM a b) c d) c1 d1) c2 d2) c3 d3) c4 d4) c5 d5) c6 d6) c7 d7)) with 0%nat
  end.

Lemma L_le (n m : int) : (φ m < φ n)%Z ->
  (φ (if (m <? n - 1 - m)%uint63 then m else (n - 1 - m)%uint63) < φ n)%Z.
Proof.
  intros Hm. pose proof (to_Z_bounded m).
  assert (Hc : φ (n - 1 - m)%uint63 = (φ n - 1 - φ m)%Z) by (zify; Z.to_euclidean_division_equations; lia).
  destruct (m <? n - 1 - m)%uint63; lia.
Qed.

Lemma div_mono_to_nat (a b : int) : (φ a < φ b)%Z ->
  (Nat.div (Z.to_nat (to_Z a)) 63 <= Nat.div (Z.to_nat (φ b)) 63)%nat.
Proof. intros H. apply Nat.Div0.div_le_mono. lia. Qed.

Lemma scan_time x xC n nC S SC R RC pos posC H HC :
  (forall i : int, (φ i < φ n)%Z -> (φ x.[i] < φ n)%Z) ->
  (cost (extract (extract (extract (extract (extract (scan_cost stepsCM x xC) n nC) S SC) R RC) pos posC) H HC)
     <= (100 * Nat.div (Z.to_nat (φ n)) 63 + 300) * Z.to_nat (gap n pos) + 10)%nat.
Proof.
  intros Hx.
  remember (Nat.div (Z.to_nat (φ n)) 63) as D eqn:ED.
  unfold scan_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC S SC R RC pos posC H HC)] =>
    assert (HG : forall m S SC R RC pos posC H HC, (Z.to_nat (gap n pos) <= m)%nat ->
       (cost (G x xC n nC S SC R RC pos posC H HC) <= (100 * D + 300) * m + 10)%nat) end.
  { induction m as [|m IH]; intros S' SC' R' RC' pos' posC' [g] HC' Hm;
      cost_simpl;
      pose proof (bdec_time (pos' <? n) (bool_w (pos' <? n))) as HB;
      cost_destruct (bdec (pos' <? n)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hm' : (Z.to_nat (gap n (pos' + 1)) <= m)%nat).
      { unfold gap in *. assert (φ (pos' + 1) = φ pos' + 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      zpart inner_cost. gen_inner.
      match type of Hinner with (?c <= 100 * Nat.div (Z.to_nat (to_Z ?L)) 63 + 100)%nat =>
        assert (HD : (Nat.div (Z.to_nat (to_Z L)) 63 <= D)%nat)
          by (rewrite ED; apply div_mono_to_nat; apply L_le; exact (Hx pos' Hlt));
        assert (Hin : (c <= 100 * D + 100)%nat) by lia end.
      clear Hinner HD.
      (match goal with |- context [inner ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j] => cost_destruct (inner a b c d e f g h i j) end).
      all: cost_simpl; zpart setbit_cost; gen_setbit; zpart scan_cost.
      all: match goal with |- context [bool_w ?b] => destruct b end; cbn [cost].
      all: try lia.
      + match goal with |- context [@cost ?T (?G' x xC n nC ?S1 ?SC1 ?R1 ?RC1 (pos' + 1)%uint63 ?w ?a ?e)] =>
          have HI := (IH S1 SC1 R1 RC1 (pos' + 1)%uint63 w a e Hm' : (@cost T (G' x xC n nC S1 SC1 R1 RC1 (pos' + 1)%uint63 w a e) <= _)%nat) end;
        nia.
      + match goal with |- context [@cost ?T (?G' x xC n nC ?S1 ?SC1 ?R1 ?RC1 (pos' + 1)%uint63 ?w ?a ?e)] =>
          have HI := (IH S1 SC1 R1 RC1 (pos' + 1)%uint63 w a e Hm' : (@cost T (G' x xC n nC S1 SC1 R1 RC1 (pos' + 1)%uint63 w a e) <= _)%nat) end;
        nia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC S SC R RC pos posC H HC)] =>
    exact (HG _ S SC R RC pos posC H HC (le_n _) : (@cost T (G x xC n nC S SC R RC pos posC H HC) <= _)%nat) end.
Qed.


Ltac gen_scan Hx := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (scan_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
    let Hc := fresh "Hscan" in
    have Hc := (scan_time a aC b bC c cC d dC e eC f fC Hx : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma impl_time x xC :
  (forall i : int, (φ i < φ (PArray.length x))%Z -> (φ x.[i] < φ (PArray.length x))%Z) ->
  (cost (antiarithmetic_impl_cost stepsCM x xC)
     <= (100 * Nat.div (Z.to_nat (φ (PArray.length x))) 63 + 300) * Z.to_nat (φ (PArray.length x)) + 50)%nat.
Proof.
  intros Hx.
  remember ((100 * Nat.div (Z.to_nat (φ (PArray.length x))) 63 + 300) * Z.to_nat (φ (PArray.length x)) + 50)%nat as RHS eqn:ERHS.
  unfold antiarithmetic_impl_cost. cost_simpl.
  zpart make_cost.
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.
  zpart scan_cost. gen_scan Hx.
  unfold gap in Hscan. change (φ 0) with 0%Z in Hscan. rewrite Z.sub_0_r in Hscan.
  subst RHS.
  match type of Hscan with (_ <= (100 * Nat.div (Z.to_nat (to_Z ?m)) 63 + 300) * Z.to_nat (to_Z ?m) + 10)%nat =>
    assert (E : m = PArray.length x) by reflexivity; rewrite E in Hscan end.
  lia.
Qed.

Lemma perm_bound (p : list N) (x : array uint) : valid_input p -> repr x p ->
  forall i : int, (φ i < φ (PArray.length x))%Z -> (φ x.[i] < φ (PArray.length x))%Z.
Proof.
  intros Hp Hx i Hi. rewrite (repr_length x p Hx) in Hi |- *.
  rewrite (repr_get x p Hx i Hi).
  pose proof (to_Z_bounded i). pose proof (gz_range p Hp (φ i) ltac:(lia)). lia.
Qed.

Theorem antiarithmetic_time : exists c1 c2 : nat,
  forall (permutation : list N)
  (permutation_arr : array uint),
  valid_input permutation
  -> repr permutation_arr permutation ->
  (cost1 antiarithmetic_cost permutation_arr <= c1 * ((size permutation_arr + 1) * (size permutation_arr / 63 + 1)) + c2)%nat.
Proof.
  exists 300%nat, 100%nat. intros p x Hp Hx.
  remember (300 * ((size x + 1) * (size x / 63 + 1)) + 100)%nat as RHS eqn:ERHS.
  pose proof (impl_time x (witness x) (perm_bound p x Hp Hx)) as HI.
  unfold cost1, antiarithmetic_cost. cost_simpl.
  eapply Nat.le_trans; [exact HI|]. subst RHS.
  match goal with |- (_ * Z.to_nat (to_Z ?m) + _ <= _)%nat =>
    assert (E : m = PArray.length x) by reflexivity; rewrite E end.
  change (size x) with (Z.to_nat (φ (PArray.length x))).
  remember (Z.to_nat (φ (PArray.length x))) as N.
  remember (Nat.div N 63) as D.
  nia.
Qed.
