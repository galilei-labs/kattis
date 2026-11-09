(* Correctness proofs for isahasa_implem.v. *)
(* Implementation of isahasa (isahasa.spec): a chained hash table on the
   class names, then one Floyd-Warshall transitive closure on bit-packed
   rows of a layered graph.

   Code.
   - Names.  Every name of the n given lines goes through [intern]: a hash
     table with chaining, in flat arrays.  [hkeys.[i]] is the name of id i,
     [hnxt.[i]] the next id of its chain (encoded i+1, 0 = end of chain),
     [hhead.[b]] the first id of bucket b (encoded).  A new name gets the
     next id and is pushed at the front of its bucket.  The chains point to
     strictly smaller encoded ids, which is the termination measure of the
     chain walk (checked dynamically, [q <? p]).  The ids of the two names of
     line l are stored in [ia.[l]], [ib.[l]].
   - Closure.  k distinct names give a layered graph on N = 2k vertices:
     vertex a (a < k) is "name a, no has-a step yet", vertex a+k is "name
     a, a has-a step used".  A given line "a is-a b" gives the edges
     a -> b and a+k -> b+k, a line "a has-a b" the edges a -> b+k and
     a+k -> b+k.  One flat table of N rows of W = ceil(N/63) Uint63 words
     each, 63 bits per word, bit v of row u at word u*W + v/63, bit v mod 63.
     TRANSITIVE-CLOSURE (Floyd-Warshall, the intermediate vertex w
     outermost): for every row u whose bit w is set, row u |= row w, a
     whole-word [lor] per word.
   - Queries.  Two hash lookups; "x is-a y" is x = y or bit (x, y), "x
     has-a y" is bit (x, y+k).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (the template's device); no nat, no fuel.  Every
   array is threaded linearly. *)

From Isahasa.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
From Stdlib Require Import Relations String Ascii.
From Stdlib Require PrimString PrimStringAxioms PString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Isahasa Require Export isahasa_implem.
Open Scope uint63_scope.
Open Scope array_scope.


Lemma add_small : forall a b : int, ((φ a) + (φ b) < 9223372036854775808)%Z ->
  (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof.
  intros a b H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite add_spec. apply Z.mod_small. lia.
Qed.

(* PROOFS *)

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

Lemma to_Z_neq : forall x y : int, (φ x) <> (φ y) -> x <> y.
Proof. intros x y H E. apply H. rewrite E. reflexivity. Qed.

Lemma eqb_Z : forall x y : int, (x =? y) = ((φ x) =? (φ y))%Z.
Proof.
  intros x y. destruct (x =? y) eqn:E.
  - apply Uint63.eqb_spec in E. subst. symmetry. apply Z.eqb_refl.
  - symmetry. apply Z.eqb_neq. intro F. apply to_Z_inj in F.
    subst. rewrite Uint63.eqb_refl in E. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Bits                                                                *)
(* ------------------------------------------------------------------ *)

Lemma getbit_spec : forall T W u v,
  getbit T W u v = Z.testbit (φ (T.[u * W + v / 63])) ((φ v) mod 63).
Proof.
  intros T W u v. unfold getbit.
  set (x := T.[u * W + v / 63]).
  assert (Hs : (φ (v mod 63)) = ((φ v) mod 63)%Z) by (rewrite mod_spec; reflexivity).
  assert (Hs0 : (0 <= (φ v) mod 63)%Z) by (apply Z.mod_pos_bound; lia).
  pose proof (Z.testbit_spec' (φ x) ((φ v) mod 63) Hs0) as Hb.
  assert (Hy : (φ ((x >> (v mod 63)) land 1)) = (((φ x) / 2 ^ ((φ v) mod 63)) mod 2)%Z).
  { rewrite land_spec', lsr_spec, Hs. change (φ 1) with (Z.ones 1).
    rewrite Z.land_ones by lia. reflexivity. }
  rewrite eqb_Z, Hy, <- Hb. destruct (Z.testbit _ _); reflexivity.
Qed.

Lemma testbit_lor : forall (x y : int) i,
  Z.testbit (φ (x lor y)) i = (Z.testbit (φ x) i || Z.testbit (φ y) i)%bool.
Proof. intros x y i. rewrite lor_spec'. apply Z.lor_spec. Qed.

Lemma testbit_pow : forall (s : int) i, ((φ s) < 63)%Z -> (0 <= i)%Z ->
  Z.testbit (φ (1 << s)) i = ((φ s) =? i)%Z.
Proof.
  intros s i Hs Hi. rewrite lsl_spec. change (φ 1) with 1%Z. rewrite Z.mul_1_l.
  pose proof (to_Z_bounded s) as Bs.
  assert (H2 : (2 ^ (φ s) < 2 ^ 63)%Z) by (apply Z.pow_lt_mono_r; lia).
  rewrite Z.mod_small.
  - apply Z.pow2_bits_eqb. lia.
  - split; [apply Z.pow_nonneg; lia|]. rewrite wB_val.
    change (2 ^ 63)%Z with 9223372036854775808%Z in H2. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Geometry of the packed table                                        *)
(* ------------------------------------------------------------------ *)

(* N rows of W words, W = ceil(N / 63), N*W cells *)
Definition geom (N W : int) : Prop :=
  (φ W) = (((φ N) + 62) / 63)%Z /\ ((φ N) * (φ W) <= 4194303)%Z.

Lemma word_lt : forall N W v, geom N W -> ((φ v) < (φ N))%Z -> ((φ v) / 63 < (φ W))%Z.
Proof. intros N W v [HW _] Hv. rewrite HW. pose proof (to_Z_bounded v). lia. Qed.

Lemma cell_lt : forall N W u j, geom N W -> ((φ u) < (φ N))%Z -> (0 <= j < (φ W))%Z ->
  (0 <= (φ u) * (φ W) + j < (φ N) * (φ W))%Z.
Proof.
  intros N W u j [_ HB] Hu Hj. pose proof (to_Z_bounded u). nia.
Qed.

Lemma cell_spec : forall N W u j, geom N W -> ((φ u) < (φ N))%Z -> ((φ j) < (φ W))%Z ->
  (φ (u * W + j)) = ((φ u) * (φ W) + (φ j))%Z.
Proof.
  intros N W u j G Hu Hj. pose proof (to_Z_bounded j).
  pose proof (cell_lt N W u (φ j) G Hu ltac:(lia)) as Hc.
  destruct G as [_ HB].
  pose proof (to_Z_bounded u). pose proof (to_Z_bounded W).
  rewrite add_spec, mul_spec.
  rewrite (Z.mod_small ((φ u) * (φ W))) by (rewrite wB_val; nia).
  apply Z.mod_small. rewrite wB_val. lia.
Qed.

Lemma div63_spec : forall v : int, (φ (v / 63)) = ((φ v) / 63)%Z.
Proof. intros v. rewrite div_spec. reflexivity. Qed.

Lemma row_unique : forall (W u w j j' : Z), (0 < W)%Z -> (0 <= j < W)%Z -> (0 <= j' < W)%Z ->
  (u * W + j = w * W + j')%Z -> u = w /\ j = j'.
Proof.
  intros W u w j j' HW Hj Hj' E.
  assert (Hu : ((u * W + j) / W)%Z = u).
  { rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (Hw : ((w * W + j') / W)%Z = w).
  { rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  rewrite E in Hu. split; [lia|]. subst. lia.
Qed.

(* reading bit v of row u: the cell and the bit position *)
Lemma getbit_cell : forall N W u v, geom N W -> ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
  (φ (u * W + v / 63)) = ((φ u) * (φ W) + (φ v) / 63)%Z.
Proof.
  intros N W u v G Hu Hv. rewrite (cell_spec N W) by (auto; rewrite div63_spec; eapply word_lt; eauto).
  rewrite div63_spec. reflexivity.
Qed.

(* setting a bit *)
Lemma getbit_setbit : forall N W T a b u v, geom N W ->
  (φ (PArray.length T)) = ((φ N) * (φ W))%Z ->
  ((φ a) < (φ N))%Z -> ((φ b) < (φ N))%Z -> ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
  (getbit (setbit T W a b) W u v = true <->
   getbit T W u v = true \/ ((φ u) = (φ a) /\ (φ v) = (φ b))).
Proof.
  intros N W T a b u v G HL Ha Hb Hu Hv.
  unfold setbit. rewrite !getbit_spec.
  pose proof (getbit_cell N W u v G Hu Hv) as Cuv.
  pose proof (getbit_cell N W a b G Ha Hb) as Cab.
  pose proof (word_lt N W v G Hv). pose proof (word_lt N W b G Hb).
  pose proof (to_Z_bounded v). pose proof (to_Z_bounded b).
  pose proof (to_Z_bounded u). pose proof (to_Z_bounded a).
  assert (HW : (0 < (φ W))%Z) by lia.
  destruct (Z.eq_dec ((φ u) * (φ W) + (φ v) / 63) ((φ a) * (φ W) + (φ b) / 63)) as [E | E].
  - assert (Ei : u * W + v / 63 = a * W + b / 63) by (apply to_Z_inj; lia).
    rewrite Ei. rewrite aget_set_same.
    2:{ rewrite ltb_spec, HL, Cab. pose proof (cell_lt N W a ((φ b) / 63) G Ha ltac:(lia)). lia. }
    rewrite testbit_lor.
    assert (Hm : (φ (b mod 63)) = ((φ b) mod 63)%Z) by (rewrite mod_spec; reflexivity).
    pose proof (Z.mod_pos_bound (φ v) 63 ltac:(lia)).
    pose proof (Z.mod_pos_bound (φ b) 63 ltac:(lia)).
    rewrite testbit_pow by (rewrite ?Hm; lia).
    rewrite Hm.
    destruct (row_unique (φ W) (φ u) (φ a) ((φ v) / 63) ((φ b) / 63) HW ltac:(lia) ltac:(lia) E)
      as [Eu Ej].
    rewrite <- Ei.
    rewrite orb_true_iff, Z.eqb_eq.
    split; intros [K | K]; auto.
    + right. split; [lia|].
      rewrite (Z.div_mod (φ v) 63), (Z.div_mod (φ b) 63) by lia. lia.
    + right. destruct K as [_ K]. rewrite K. reflexivity.
  - rewrite aget_set_other by (apply to_Z_neq; lia).
    split; [intros K; left; exact K | intros [K | K]; auto].
    destruct K as [K1 K2]. exfalso. apply E. rewrite K1, K2. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Unfolding equations of the loops                                    *)
(* ------------------------------------------------------------------ *)

Lemma rowor_eq : forall T W u w j H,
  rowor T W u w j H =
  match bdec (j <? W) with
  | left Hj =>
      rowor T.[u * W + j <- T.[u * W + j] lor T.[w * W + j]] W u w (j + 1)
        (Acc_inv H (dec_step W j Hj))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fw_inner_eq : forall T N W w u H,
  fw_inner T N W w u H =
  match bdec (u <? N) with
  | left Hu =>
      fw_inner (if getbit T W u w
                then rowor T W u w 0 (Zwf_well_founded 0 (gap W 0)) else T)
        N W w (u + 1) (Acc_inv H (dec_step N u Hu))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fw_outer_eq : forall T N W w H,
  fw_outer T N W w H =
  match bdec (w <? N) with
  | left Hw =>
      fw_outer (fw_inner T N W w 0 (Zwf_well_founded 0 (gap N 0))) N W (w + 1)
        (Acc_inv H (dec_step N w Hw))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma eloop_eq : forall xrs ia ib k W n l T H,
  eloop xrs ia ib k W n l T H =
  match bdec (l <? n) with
  | left Hl =>
      let a := ia.[l] in
      let b := ib.[l] in
      let T' := match xrs.[l] with
                | IsA => setbit (setbit T W a b) W (a + k) (b + k)
                | HasA => setbit (setbit T W a (b + k)) W (a + k) (b + k)
                end in
      eloop xrs ia ib k W n (l + 1) T' (Acc_inv H (dec_step n l Hl))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_eq : forall f m j out H,
  fill f m j out H =
  match bdec (j <? m) with
  | left Hj => fill f m (j + 1) out.[j <- f j] (Acc_inv H (dec_step m j Hj))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma walk_eq : forall s keys nxt p H,
  walk s keys nxt p H =
  match bdec (p =? 0) with
  | left _ => 0
  | right _ =>
      match PrimString.compare keys.[p - 1] s with
      | Eq => p
      | _ =>
          let q := nxt.[p - 1] in
          match bdec (q <? p) with
          | left Hq => walk s keys nxt q (Acc_inv H (dec_lt q p Hq))
          | right _ => 0
          end
      end
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma iloop_eq : forall xsrc xdst n i st ia ib H,
  iloop xsrc xdst n i st ia ib H =
  match bdec (i <? n) with
  | left Hi =>
      let (st1, a) := intern st xsrc.[i] in
      let (st2, b) := intern st1 xdst.[i] in
      iloop xsrc xdst n (i + 1) st2 ia.[i <- a] ib.[i <- b]
        (Acc_inv H (dec_step n i Hi))
  | right _ => (st, ia, ib)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ltb_false : forall x y : int, (x <? y) = false -> ((φ y) <= (φ x))%Z.
Proof. intros x y H. rewrite <- Bool.not_true_iff_false, ltb_spec in H. lia. Qed.

(* ------------------------------------------------------------------ *)
(* One row |= another                                                  *)
(* ------------------------------------------------------------------ *)

Lemma rowor_spec : forall N W u w (T0 : array int), geom N W ->
  ((φ u) < (φ N))%Z -> ((φ w) < (φ N))%Z ->
  forall z j T H, gap W j = z -> ((φ j) <= (φ W))%Z ->
  (φ (PArray.length T)) = ((φ N) * (φ W))%Z ->
  (forall j', ((φ j') < (φ j))%Z -> T.[u * W + j'] = T0.[u * W + j'] lor T0.[w * W + j']) ->
  (forall c, (forall j', ((φ j') < (φ j))%Z -> c <> u * W + j') -> T.[c] = T0.[c]) ->
  (φ (PArray.length (rowor T W u w j H))) = ((φ N) * (φ W))%Z /\
  (forall j', ((φ j') < (φ W))%Z ->
     (rowor T W u w j H).[u * W + j'] = T0.[u * W + j'] lor T0.[w * W + j']) /\
  (forall c, (forall j', ((φ j') < (φ W))%Z -> c <> u * W + j') ->
     (rowor T W u w j H).[c] = T0.[c]).
Proof.
  intros N W u w T0 G Hu Hw z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j T H Hz Hj HL R1 R2.
  rewrite rowor_eq.
  destruct (bdec (j <? W)) as [Hjw | Hjw].
  - pose proof Hjw as Hjw'. rewrite ltb_spec in Hjw'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded u). pose proof (to_Z_bounded w).
    assert (HW : (0 < (φ W))%Z) by lia.
    assert (C0 : (φ (u * W + j)) = ((φ u) * (φ W) + (φ j))%Z) by (apply (cell_spec N); auto).
    assert (Cw : (φ (w * W + j)) = ((φ w) * (φ W) + (φ j))%Z) by (apply (cell_spec N); auto).
    assert (Cj : forall j', ((φ j') < (φ W))%Z -> (φ (u * W + j')) = ((φ u) * (φ W) + (φ j'))%Z)
      by (intros; apply (cell_spec N); auto).
    assert (E1 : T.[u * W + j] = T0.[u * W + j]).
    { apply R2. intros j' Hj'. apply to_Z_neq. rewrite C0, Cj by lia. lia. }
    assert (E2 : T.[w * W + j] = T0.[w * W + j]).
    { apply R2. intros j' Hj'. apply to_Z_neq. rewrite Cw, Cj by lia. intro E.
      pose proof (to_Z_bounded j').
      destruct (row_unique (φ W) (φ w) (φ u) (φ j) (φ j') HW ltac:(lia) ltac:(lia) E). lia. }
    assert (Hin : (u * W + j <? PArray.length T) = true).
    { rewrite ltb_spec, HL, C0. pose proof (cell_lt N W u (φ j) G Hu ltac:(lia)). lia. }
    eapply IH; [ | reflexivity | lia | | | ].
    + rewrite <- Hz. apply dec_step. exact Hjw.
    + rewrite alength_set. exact HL.
    + intros j' Hj'. rewrite Hj1 in Hj'.
      destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
      * assert (j' = j) by (apply to_Z_inj; exact E). subst j'.
        rewrite aget_set_same by exact Hin. rewrite E1, E2. reflexivity.
      * rewrite aget_set_other.
        -- apply R1. lia.
        -- apply to_Z_neq. rewrite C0, Cj by lia. lia.
    + intros c Hc. rewrite aget_set_other.
      * apply R2. intros j' Hj'. apply Hc. rewrite Hj1. lia.
      * intro E. apply (Hc j). rewrite Hj1. lia. symmetry. exact E.
  - apply ltb_false in Hjw.
    split; [exact HL|]. split.
    + intros j' Hj'. apply R1. lia.
    + intros c Hc. apply R2. intros j' Hj'. apply Hc. lia.
Qed.

Lemma rowor_bits : forall N W u w (T0 : array int), geom N W ->
  ((φ u) < (φ N))%Z -> ((φ w) < (φ N))%Z ->
  (φ (PArray.length T0)) = ((φ N) * (φ W))%Z ->
  let R := rowor T0 W u w 0 (Zwf_well_founded 0 (gap W 0)) in
  (φ (PArray.length R)) = ((φ N) * (φ W))%Z /\
  forall u' v, ((φ u') < (φ N))%Z -> ((φ v) < (φ N))%Z ->
    getbit R W u' v =
    if ((φ u') =? (φ u))%Z then (getbit T0 W u v || getbit T0 W w v)%bool
    else getbit T0 W u' v.
Proof.
  intros N W u w T0 G Hu Hw HL R.
  destruct (rowor_spec N W u w T0 G Hu Hw _ 0 T0 (Zwf_well_founded 0 (gap W 0))
              eq_refl ltac:(pose proof (to_Z_bounded W); change (φ 0) with 0%Z; lia) HL
              ltac:(intros j' Hj'; change (φ 0) with 0%Z in Hj'; pose proof (to_Z_bounded j'); lia)
              ltac:(intros; reflexivity)) as [RL [R1 R2]].
  fold R in RL, R1, R2.
  split; [exact RL|].
  intros u' v Hu' Hv.
  pose proof (word_lt N W v G Hv) as Hwv.
  rewrite !getbit_spec.
  destruct (Z.eqb_spec (φ u') (φ u)) as [E | E].
  - assert (u' = u) by (apply to_Z_inj; exact E). subst u'.
    rewrite R1 by (rewrite div63_spec; exact Hwv).
    apply testbit_lor.
  - rewrite R2; [reflexivity|].
    intros j' Hj'. apply to_Z_neq.
    rewrite (getbit_cell N W u' v G Hu' Hv), (cell_spec N W u j' G Hu Hj').
    intro F. pose proof (to_Z_bounded j'). pose proof (to_Z_bounded v).
    destruct (row_unique (φ W) (φ u') (φ u) ((φ v) / 63) (φ j')
                ltac:(lia) ltac:(split; [apply Z.div_pos; lia | lia]) ltac:(lia) F).
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Floyd-Warshall on relations: paths whose intermediates are below t  *)
(* ------------------------------------------------------------------ *)

Inductive Q (E : Z -> Z -> Prop) (t : Z) : Z -> Z -> Prop :=
| Qe : forall u v, E u v -> Q E t u v
| Qc : forall u w v, (0 <= w < t)%Z -> Q E t u w -> Q E t w v -> Q E t u v.

Lemma Q_mono : forall E t t' u v, (t <= t')%Z -> Q E t u v -> Q E t' u v.
Proof.
  intros E t t' u v Ht HQ. induction HQ.
  - apply Qe. assumption.
  - eapply Qc; eauto. lia.
Qed.

Lemma Q_split : forall E t u v, (0 <= t)%Z -> Q E (t + 1) u v ->
  Q E t u v \/ (Q E t u t /\ Q E t t v).
Proof.
  intros E t u v Ht HQ. induction HQ as [u v He | u w v Hw H1 IH1 H2 IH2].
  - left. apply Qe. exact He.
  - destruct (Z.eq_dec w t) as [-> | Hne].
    + right. split.
      * destruct IH1 as [A | [A _]]; exact A.
      * destruct IH2 as [A | [_ A]]; exact A.
    + assert (Hw' : (0 <= w < t)%Z) by lia.
      destruct IH1 as [A | [A B]], IH2 as [C | [C D]].
      * left. eapply Qc; eauto.
      * right. split; [eapply Qc; eauto | exact D].
      * right. split; [exact A | eapply Qc; eauto].
      * right. split; [exact A | exact D].
Qed.

Lemma Q_step : forall E t u v, (0 <= t)%Z ->
  (Q E (t + 1) u v <-> Q E t u v \/ (Q E t u t /\ Q E t t v)).
Proof.
  intros E t u v Ht. split.
  - apply Q_split. exact Ht.
  - intros [A | [A B]].
    + eapply Q_mono; [ | exact A]. lia.
    + apply Qc with t; [lia | |]; (eapply Q_mono; [ | eassumption]); lia.
Qed.

Lemma Q_zero : forall E u v, Q E 0 u v <-> E u v.
Proof.
  intros E u v. split.
  - intros HQ. induction HQ; [assumption | lia].
  - apply Qe.
Qed.

Lemma Q_tc : forall E t u v, Q E t u v -> clos_trans Z E u v.
Proof.
  intros E t u v HQ. induction HQ.
  - apply t_step. assumption.
  - eapply t_trans; eauto.
Qed.

Lemma tc_bound : forall (E : Z -> Z -> Prop) N,
  (forall u v, E u v -> (0 <= v < N)%Z) ->
  forall u v, clos_trans Z E u v -> (0 <= v < N)%Z.
Proof. intros E N HE u v H. induction H; eauto. Qed.

Lemma tc_Q : forall (E : Z -> Z -> Prop) N,
  (forall u v, E u v -> (0 <= v < N)%Z) ->
  forall u v, clos_trans Z E u v -> Q E N u v.
Proof.
  intros E N HE u v H. induction H as [x y Hxy | x y z H1 IH1 H2 IH2].
  - apply Qe. exact Hxy.
  - apply Qc with y; auto. exact (tc_bound E N HE x y H1).
Qed.

(* ------------------------------------------------------------------ *)
(* The closure loops on the packed table                               *)
(* ------------------------------------------------------------------ *)

Lemma fw_inner_spec : forall N W w (T0 : array int), geom N W -> ((φ w) < (φ N))%Z ->
  (φ (PArray.length T0)) = ((φ N) * (φ W))%Z ->
  forall z u T H, gap N u = z -> ((φ u) <= (φ N))%Z ->
  (φ (PArray.length T)) = ((φ N) * (φ W))%Z ->
  (forall u' v, ((φ u') < (φ N))%Z -> ((φ v) < (φ N))%Z ->
     getbit T W u' v =
     if ((φ u') <? (φ u))%Z
     then (getbit T0 W u' v || (getbit T0 W u' w && getbit T0 W w v))%bool
     else getbit T0 W u' v) ->
  (φ (PArray.length (fw_inner T N W w u H))) = ((φ N) * (φ W))%Z /\
  (forall u' v, ((φ u') < (φ N))%Z -> ((φ v) < (φ N))%Z ->
     getbit (fw_inner T N W w u H) W u' v =
     (getbit T0 W u' v || (getbit T0 W u' w && getbit T0 W w v))%bool).
Proof.
  intros N W w T0 G Hw HL0 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u T H Hz Hu HL Inv.
  rewrite fw_inner_eq.
  destruct (bdec (u <? N)) as [Hun | Hun].
  - pose proof Hun as Hun'. rewrite ltb_spec in Hun'.
    assert (Hu1 : (φ (u + 1)) = ((φ u) + 1)%Z) by sia.
    assert (Huw : getbit T W u w = getbit T0 W u w).
    { rewrite Inv by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hun.
    + destruct (getbit T W u w); [ | exact HL].
      exact (proj1 (rowor_bits N W u w T G Hun' Hw HL)).
    + intros u' v Hu' Hv. rewrite Hu1.
      destruct (getbit T W u w) eqn:Eb.
      * rewrite (proj2 (rowor_bits N W u w T G Hun' Hw HL)) by assumption.
        destruct (Z.eqb_spec (φ u') (φ u)) as [E | E].
        -- assert (u' = u) by (apply to_Z_inj; exact E). subst u'.
           rewrite (proj2 (Z.ltb_lt _ _)) by lia.
           rewrite Inv by lia. rewrite (proj2 (Z.ltb_ge (φ u) (φ u))) by lia.
           rewrite Inv by lia. rewrite <- Huw.
           destruct ((φ w) <? (φ u))%Z;
             destruct (getbit T0 W u v), (getbit T0 W w v), (getbit T0 W w w); reflexivity.
        -- rewrite Inv by lia.
           destruct (Z.ltb_spec (φ u') (φ u)), (Z.ltb_spec (φ u') ((φ u) + 1)); try lia;
             reflexivity.
      * rewrite Inv by lia.
        destruct (Z.eqb_spec (φ u') (φ u)) as [E | E].
        -- assert (u' = u) by (apply to_Z_inj; exact E). subst u'.
           rewrite (proj2 (Z.ltb_ge (φ u) (φ u))) by lia.
           rewrite (proj2 (Z.ltb_lt (φ u) ((φ u) + 1))) by lia.
           rewrite <- Huw. destruct (getbit T0 W u v); reflexivity.
        -- destruct (Z.ltb_spec (φ u') (φ u)), (Z.ltb_spec (φ u') ((φ u) + 1)); try lia;
             reflexivity.
  - apply ltb_false in Hun.
    split; [exact HL|].
    intros u' v Hu' Hv. rewrite Inv by assumption.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma fw_outer_spec : forall (E : Z -> Z -> Prop) N W, geom N W ->
  forall z w T H, gap N w = z -> ((φ w) <= (φ N))%Z ->
  (φ (PArray.length T)) = ((φ N) * (φ W))%Z ->
  (forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
     (getbit T W u v = true <-> Q E (φ w) (φ u) (φ v))) ->
  (φ (PArray.length (fw_outer T N W w H))) = ((φ N) * (φ W))%Z /\
  (forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
     (getbit (fw_outer T N W w H) W u v = true <-> Q E (φ N) (φ u) (φ v))).
Proof.
  intros E N W G z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros w T H Hz Hw HL Inv.
  rewrite fw_outer_eq.
  destruct (bdec (w <? N)) as [Hwn | Hwn].
  - pose proof Hwn as Hwn'. rewrite ltb_spec in Hwn'.
    assert (Hw1 : (φ (w + 1)) = ((φ w) + 1)%Z) by sia.
    destruct (fw_inner_spec N W w T G Hwn' HL _ 0 T (Zwf_well_founded 0 (gap N 0))
                eq_refl ltac:(pose proof (to_Z_bounded N); change (φ 0) with 0%Z; lia) HL
                ltac:(intros u' v _ _; change (φ 0) with 0%Z;
                      rewrite (proj2 (Z.ltb_ge _ _)) by (pose proof (to_Z_bounded u'); lia);
                      reflexivity))
      as [L1 B1].
    eapply IH; [ | reflexivity | lia | exact L1 | ].
    + rewrite <- Hz. apply dec_step. exact Hwn.
    + intros u v Hu Hv. rewrite B1 by assumption. rewrite Hw1.
      rewrite Q_step by (pose proof (to_Z_bounded w); lia).
      rewrite orb_true_iff, andb_true_iff, !Inv by assumption. tauto.
  - apply ltb_false in Hwn.
    assert (Ew : (φ N) = (φ w)) by lia.
    split; [exact HL|]. intros u v Hu Hv. rewrite Ew. apply Inv; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The layered graph: is-a / has-a as reachability                     *)
(* ------------------------------------------------------------------ *)

Section Layered.
  Local Open Scope Z_scope.

  (* k ids; ei a b / eh a b: a given is-a / has-a line from id a to id b *)
  Variable k : Z.
  Variables ei eh : Z -> Z -> Prop.
  Hypothesis Hei : forall a b, ei a b -> (0 <= a < k /\ 0 <= b < k)%Z.
  Hypothesis Heh : forall a b, eh a b -> (0 <= a < k /\ 0 <= b < k)%Z.

  Definition ea (a b : Z) : Prop := ei a b \/ eh a b.

  (* vertex a: no has-a step yet; vertex a + k: a has-a step used *)
  Definition Elay (u v : Z) : Prop :=
    ei u v \/ eh u (v - k) \/ ea (u - k) (v - k).

  Definition Hrel (x z : Z) : Prop :=
    exists y y', clos_refl_trans Z ei x y /\ eh y y' /\ clos_refl_trans Z ea y' z.

  Definition Mlay (u v : Z) : Prop :=
    (0 <= u < k /\ 0 <= v < k /\ clos_refl_trans Z ei u v)%Z \/
    (0 <= u < k /\ k <= v < k + k /\ Hrel u (v - k))%Z \/
    (k <= u < k + k /\ k <= v < k + k /\ clos_refl_trans Z ea (u - k) (v - k))%Z.

  Lemma Hea : forall a b, ea a b -> (0 <= a < k /\ 0 <= b < k)%Z.
  Proof. intros a b [H | H]; auto. Qed.

  Lemma Elay_bound : forall u v, Elay u v -> (0 <= v < k + k)%Z.
  Proof.
    intros u v [H | [H | H]].
    - apply Hei in H. lia.
    - apply Heh in H. lia.
    - apply Hea in H. lia.
  Qed.

  Lemma Elay_M : forall u v, Elay u v -> Mlay u v.
  Proof.
    intros u v [H | [H | H]].
    - left. pose proof (Hei _ _ H). repeat split; try lia. apply rt_step. exact H.
    - right; left. pose proof (Heh _ _ H). repeat split; try lia.
      exists u, (v - k)%Z. split; [apply rt_refl|]. split; [exact H | apply rt_refl].
    - right; right. pose proof (Hea _ _ H). repeat split; try lia. apply rt_step. exact H.
  Qed.

  Lemma ei_ea : forall x y, clos_refl_trans Z ei x y -> clos_refl_trans Z ea x y.
  Proof.
    intros x y H. induction H.
    - apply rt_step. left. assumption.
    - apply rt_refl.
    - eapply rt_trans; eauto.
  Qed.

  Lemma Mlay_trans : forall u w v, Mlay u w -> Mlay w v -> Mlay u v.
  Proof.
    intros u w v [A | [A | A]] [B | [B | B]];
      destruct A as (A1 & A2 & A), B as (B1 & B2 & B); try lia.
    - left. repeat split; try lia. eapply rt_trans; eauto.
    - right; left. repeat split; try lia.
      destruct B as (y & y' & C1 & C2 & C3). exists y, y'.
      split; [eapply rt_trans; eauto | split; assumption].
    - right; left. repeat split; try lia.
      destruct A as (y & y' & C1 & C2 & C3). exists y, y'.
      split; [assumption | split; [assumption | eapply rt_trans; eauto]].
    - right; right. repeat split; try lia. eapply rt_trans; eauto.
  Qed.

  Lemma tc_M : forall u v, clos_trans Z Elay u v -> Mlay u v.
  Proof.
    intros u v H. induction H.
    - apply Elay_M. assumption.
    - eapply Mlay_trans; eauto.
  Qed.

  Lemma isa_tc : forall x y, clos_refl_trans Z ei x y -> x = y \/ clos_trans Z Elay x y.
  Proof.
    intros x y H. induction H as [x y H | x | x y z H1 IH1 H2 IH2].
    - right. apply t_step. left. exact H.
    - left. reflexivity.
    - destruct IH1 as [-> | A], IH2 as [-> | B]; auto.
      right. eapply t_trans; eauto.
  Qed.

  Lemma any_tc : forall x y, clos_refl_trans Z ea x y ->
    x = y \/ clos_trans Z Elay (x + k) (y + k).
  Proof.
    intros x y H. induction H as [x y H | x | x y z H1 IH1 H2 IH2].
    - right. apply t_step. right; right.
      replace (x + k - k)%Z with x by lia. replace (y + k - k)%Z with y by lia. exact H.
    - left. reflexivity.
    - destruct IH1 as [-> | A], IH2 as [-> | B]; auto.
      right. eapply t_trans; eauto.
  Qed.

  Lemma H_tc : forall x z, Hrel x z -> clos_trans Z Elay x (z + k).
  Proof.
    intros x z (y & y' & A & B & C).
    assert (Ey : clos_trans Z Elay y (y' + k)).
    { apply t_step. right; left. replace (y' + k - k)%Z with y' by lia. exact B. }
    destruct (isa_tc x y A) as [-> | A'], (any_tc y' z C) as [-> | C'].
    - exact Ey.
    - eapply t_trans; eauto.
    - eapply t_trans; eauto.
    - eapply t_trans; [exact A' | eapply t_trans; eauto].
  Qed.

  Lemma first_has : forall x y, clos_refl_trans Z ea x y ->
    clos_refl_trans Z ei x y \/
    exists a a', clos_refl_trans Z ei x a /\ eh a a' /\ clos_refl_trans Z ea a' y.
  Proof.
    intros x y H. apply clos_rt_rt1n_iff in H.
    induction H as [x | x w y H1 H2 IH].
    - left. apply rt_refl.
    - destruct H1 as [H1 | H1].
      + destruct IH as [A | (a & a' & A & B & C)].
        * left. eapply rt_trans; [apply rt_step; exact H1 | exact A].
        * right. exists a, a'. split; [eapply rt_trans; [apply rt_step; exact H1 | exact A] |].
          split; assumption.
      + right. exists x, w. split; [apply rt_refl|]. split; [exact H1|].
        apply clos_rt_rt1n_iff. exact H2.
  Qed.

  Lemma Hrel_iff : forall x z, Hrel x z <->
    exists y y', clos_refl_trans Z ea x y /\ eh y y' /\ clos_refl_trans Z ea y' z.
  Proof.
    intros x z. split.
    - intros (y & y' & A & B & C). exists y, y'. split; [apply ei_ea; exact A|]. auto.
    - intros (y & y' & A & B & C).
      destruct (first_has x y A) as [A' | (a & a' & A1 & A2 & A3)].
      + exists y, y'. auto.
      + exists a, a'. split; [exact A1|]. split; [exact A2|].
        eapply rt_trans; [exact A3|]. eapply rt_trans; [apply rt_step; right; exact B | exact C].
  Qed.

  Lemma isa_iff : forall x y, (0 <= x < k)%Z -> (0 <= y < k)%Z ->
    (x = y \/ clos_trans Z Elay x y <-> clos_refl_trans Z ei x y).
  Proof.
    intros x y Hx Hy. split.
    - intros [-> | H]; [apply rt_refl|].
      destruct (tc_M x y H) as [(_ & _ & A) | [(_ & A & _) | (A & _ & _)]]; auto; lia.
    - apply isa_tc.
  Qed.

  Lemma has_iff : forall x z, (0 <= x < k)%Z -> (0 <= z < k)%Z ->
    (clos_trans Z Elay x (z + k) <-> Hrel x z).
  Proof.
    intros x z Hx Hz. split.
    - intros H.
      destruct (tc_M x (z + k) H) as [(_ & A & _) | [(_ & _ & A) | (A & _ & _)]];
        try lia.
      replace (z + k - k)%Z with z in A by lia. exact A.
    - apply H_tc.
  Qed.

End Layered.

(* ------------------------------------------------------------------ *)
(* Primitive strings and the math strings they represent               *)
(* ------------------------------------------------------------------ *)

Fixpoint smk (l : list int) : String.string :=
  match l with
  | nil => EmptyString
  | c :: r => String.String (ascii_of_N (Z.to_N (φ c))) (smk r)
  end.

(* the math string a primitive string represents *)
Definition to_math (x : pstr) : String.string := smk (PrimStringAxioms.to_list x).

Lemma smk_get : forall l k,
  String.get k (smk l) = option_map (fun c => ascii_of_N (Z.to_N (φ c))) (nth_error l k).
Proof. induction l as [| c l IH]; intros [| k]; simpl; auto. Qed.

Lemma str_get_none : forall s k, (String.length s <= k)%nat -> String.get k s = None.
Proof.
  induction s as [| c s IH]; intros [| k] Hk; simpl in *; auto; try lia.
  apply IH. lia.
Qed.

Lemma str_ext : forall s1 s2 : String.string,
  (forall k, String.get k s1 = String.get k s2) -> s1 = s2.
Proof.
  induction s1 as [| c1 s1 IH]; intros [| c2 s2] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. simpl in H0. injection H0 as ->.
    f_equal. apply IH. intros k. exact (H (S k)).
Qed.

Lemma repr_to_math : forall (x : pstr) (X : String.string), repr x X -> X = to_math x.
Proof.
  intros x X [Hl Hc]. apply str_ext. intros k. unfold to_math. rewrite smk_get.
  pose proof (PrimStringAxioms.length_spec x) as Hls.
  pose proof (to_Z_bounded (PrimString.length x)) as Bl.
  destruct (Nat.lt_ge_cases k (String.length X)) as [Hk | Hk].
  - destruct (Hc k Hk) as (c & Hg & Hr). rewrite Hg.
    assert (Hk' : (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
    { rewrite of_Z_spec. apply Z.mod_small. lia. }
    destruct (PString.get_spec_in_bounds x (of_Z (Z.of_nat k)) ltac:(lia)) as [_ Hn].
    rewrite Hk', Nat2Z.id in Hn.
    assert (Hn' : @nth_error int (PrimStringAxioms.to_list x) k
                  = Some (PrimString.get x (of_Z (Z.of_nat k)))) by exact Hn.
    rewrite Hn'. simpl. f_equal.
    unfold repr, repr_uint in Hr. rewrite Hr. symmetry. apply ascii_N_embedding.
  - rewrite str_get_none by exact Hk.
    assert (Hn : @nth_error int (PrimStringAxioms.to_list x) k = None)
      by (apply nth_error_None;
          change (@List.length PrimString.char63 (PrimStringAxioms.to_list x) <= k)%nat; lia).
    rewrite Hn. reflexivity.
Qed.

Lemma char_valid_bound : forall c : int, PrimStringAxioms.char63_valid c -> ((φ c) < 256)%Z.
Proof.
  intros c H. unfold PrimStringAxioms.char63_valid in H.
  assert (E : (φ (PrimInt63.land c 255)) = (φ c)) by (rewrite H; reflexivity).
  change (PrimInt63.land c 255) with (c land 255) in E.
  rewrite land_spec' in E. change (φ 255) with (Z.ones 8) in E.
  rewrite Z.land_ones in E by lia.
  pose proof (Z.mod_pos_bound (φ c) (2 ^ 8) ltac:(lia)). rewrite E in *. lia.
Qed.

Lemma smk_inj : forall l1 l2,
  Forall PrimStringAxioms.char63_valid l1 -> Forall PrimStringAxioms.char63_valid l2 ->
  smk l1 = smk l2 -> l1 = l2.
Proof.
  induction l1 as [| c1 l1 IH]; intros [| c2 l2] V1 V2 H; simpl in H; try discriminate.
  - reflexivity.
  - inversion V1 as [| ? ? V1c V1r]; subst. inversion V2 as [| ? ? V2c V2r]; subst.
    injection H as Hc Hr.
    apply char_valid_bound in V1c. apply char_valid_bound in V2c.
    pose proof (to_Z_bounded c1). pose proof (to_Z_bounded c2).
    assert (E : Z.to_N (φ c1) = Z.to_N (φ c2)).
    { rewrite <- (N_ascii_embedding (Z.to_N (φ c1))) by lia.
      rewrite <- (N_ascii_embedding (Z.to_N (φ c2))) by lia.
      rewrite Hc. reflexivity. }
    f_equal.
    + apply to_Z_inj. lia.
    + apply IH; assumption.
Qed.

Lemma to_math_inj : forall x y : pstr, to_math x = to_math y -> x = y.
Proof.
  intros x y H. apply PString.to_list_inj. apply smk_inj; try apply PrimStringAxioms.to_list_char63_valid.
  exact H.
Qed.

(* reading the input arrays *)
Lemma repr_arr_str : forall (xa : array pstr) (la : list String.string), repr xa la ->
  (φ (PArray.length xa)) = Z.of_nat (List.length la) /\
  forall l : nat, (l < List.length la)%nat ->
    nth_error la l = Some (to_math xa.[of_Z (Z.of_nat l)]).
Proof.
  intros xa la [Hl Hc]. split; [symmetry; exact Hl|].
  intros l Hlt. destruct (Hc l Hlt) as (m & Hm & Hr).
  rewrite Hm. f_equal. apply repr_to_math. exact Hr.
Qed.

Lemma repr_arr_rel : forall (xa : array relkind) (la : list relkind), repr xa la ->
  (φ (PArray.length xa)) = Z.of_nat (List.length la) /\
  forall l : nat, (l < List.length la)%nat ->
    nth_error la l = Some xa.[of_Z (Z.of_nat l)].
Proof.
  intros xa la [Hl Hc]. split; [symmetry; exact Hl|].
  intros l Hlt. destruct (Hc l Hlt) as (m & Hm & Hr).
  rewrite Hm. f_equal. symmetry. exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* The hash table                                                      *)
(* ------------------------------------------------------------------ *)

Lemma plength_set : forall (t : array pstr) (i : int) (b : pstr),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set pstr t i b). Qed.

Lemma pget_set_same : forall (t : array pstr) (i : int) (b : pstr),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same pstr t i b H). Qed.

Lemma pget_set_other : forall (t : array pstr) (i j : int) (b : pstr),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other pstr t i j b H). Qed.

Lemma pred_spec : forall p : int, p <> 0 -> (φ (p - 1)) = ((φ p) - 1)%Z.
Proof.
  intros p Hp. assert ((φ p) <> 0%Z) by (intro E; apply Hp; apply to_Z_inj; exact E).
  pose proof (to_Z_bounded p). rewrite sub_spec. change (φ 1) with 1%Z.
  apply Z.mod_small. lia.
Qed.

Lemma succ_spec : forall c : int, ((φ c) < 4194303)%Z -> (φ (c + 1)) = ((φ c) + 1)%Z.
Proof.
  intros c Hc. pose proof (to_Z_bounded c). rewrite add_spec. change (φ 1) with 1%Z.
  apply Z.mod_small. rewrite wB_val. lia.
Qed.

Lemma hash_bound : forall s, ((φ (hash s)) < 1024)%Z.
Proof.
  intros s. unfold hash. rewrite land_spec'. change (φ 1023) with (Z.ones 10).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

(* id j is on the chain starting at encoded id p *)
Inductive inS (nxt : array int) : int -> int -> Prop :=
| inS_here : forall p, p <> 0 -> inS nxt p (p - 1)
| inS_next : forall p j, p <> 0 -> inS nxt (nxt.[p - 1]) j -> inS nxt p j.

Lemma inS_lt : forall nxt c p j, inS nxt p j ->
  (forall j', ((φ j') < c)%Z -> ((φ (nxt.[j'])) <= (φ j'))%Z) ->
  ((φ p) <= c)%Z -> ((φ j) < (φ p))%Z.
Proof.
  intros nxt c p j H Hn. induction H as [p Hp | p j Hp H IH]; intros Hpc.
  - rewrite pred_spec by exact Hp. lia.
  - pose proof (pred_spec p Hp) as E.
    assert ((φ p) <> 0%Z) by (intro F; apply Hp; apply to_Z_inj; exact F).
    pose proof (to_Z_bounded p).
    pose proof (Hn (p - 1) ltac:(lia)) as Hle.
    pose proof (IH ltac:(lia)). lia.
Qed.

Lemma inS_lift : forall nxt nxt' c p j, inS nxt p j ->
  (forall j', ((φ j') < c)%Z -> ((φ (nxt.[j'])) <= (φ j'))%Z) ->
  (forall j', ((φ j') < c)%Z -> nxt'.[j'] = nxt.[j']) ->
  ((φ p) <= c)%Z -> inS nxt' p j.
Proof.
  intros nxt nxt' c p j H Hn Heq. induction H as [p Hp | p j Hp H IH]; intros Hpc.
  - apply inS_here. exact Hp.
  - pose proof (pred_spec p Hp) as E.
    assert ((φ p) <> 0%Z) by (intro F; apply Hp; apply to_Z_inj; exact F).
    pose proof (to_Z_bounded p).
    apply inS_next; [exact Hp|].
    rewrite Heq by lia. apply IH.
    pose proof (Hn (p - 1) ltac:(lia)). lia.
Qed.

Lemma walk_spec : forall s keys nxt c,
  (forall j', ((φ j') < c)%Z -> ((φ (nxt.[j'])) <= (φ j'))%Z) ->
  forall z p H, (φ p) = z -> ((φ p) <= c)%Z ->
  (walk s keys nxt p H = 0 /\ forall j, inS nxt p j -> keys.[j] <> s) \/
  (walk s keys nxt p H <> 0 /\ inS nxt p (walk s keys nxt p H - 1) /\
   keys.[walk s keys nxt p H - 1] = s).
Proof.
  intros s keys nxt c Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p H Hz Hpc. rewrite walk_eq.
  destruct (bdec (p =? 0)) as [Hp | Hp].
  - apply Uint63.eqb_spec in Hp. subst p. left. split; [reflexivity|].
    intros j Hj. inversion Hj; contradiction.
  - assert (Hp' : p <> 0) by (intro E; subst; rewrite Uint63.eqb_refl in Hp; discriminate).
    pose proof (pred_spec p Hp') as E.
    assert ((φ p) <> 0%Z) by (intro F; apply Hp'; apply to_Z_inj; exact F).
    pose proof (to_Z_bounded p).
    destruct (PrimString.compare keys.[p - 1] s) eqn:C; cbv zeta.
    + right. split; [exact Hp'|]. split.
      * apply inS_here. exact Hp'.
      * apply PString.compare_eq. exact C.
    + assert (Hne : keys.[p - 1] <> s)
        by (intro F; rewrite F, PString.compare_refl in C; discriminate).
      pose proof (Hn (p - 1) ltac:(lia)) as Hq.
      destruct (bdec (nxt.[p - 1] <? p)) as [Hlt | Hlt].
      * destruct (IH (φ (nxt.[p - 1])) ltac:(rewrite <- Hz; apply dec_lt; exact Hlt)
                    (nxt.[p - 1]) (Acc_inv H (dec_lt (nxt.[p - 1]) p Hlt)) eq_refl
                    ltac:(lia)) as [[A B] | [A [B D]]].
        -- left. split; [exact A|]. intros j Hj. inversion Hj; subst.
           ++ exact Hne.
           ++ apply B. assumption.
        -- right. split; [exact A|]. split; [apply inS_next; assumption | exact D].
      * apply ltb_false in Hlt. lia.
    + assert (Hne : keys.[p - 1] <> s)
        by (intro F; rewrite F, PString.compare_refl in C; discriminate).
      pose proof (Hn (p - 1) ltac:(lia)) as Hq.
      destruct (bdec (nxt.[p - 1] <? p)) as [Hlt | Hlt].
      * destruct (IH (φ (nxt.[p - 1])) ltac:(rewrite <- Hz; apply dec_lt; exact Hlt)
                    (nxt.[p - 1]) (Acc_inv H (dec_lt (nxt.[p - 1]) p Hlt)) eq_refl
                    ltac:(lia)) as [[A B] | [A [B D]]].
        -- left. split; [exact A|]. intros j Hj. inversion Hj; subst.
           ++ exact Hne.
           ++ apply B. assumption.
        -- right. split; [exact A|]. split; [apply inS_next; assumption | exact D].
      * apply ltb_false in Hlt. lia.
Qed.

Record HTinv (st : ht) (cap : int) : Prop := {
  hi_cap : ((φ cap) <= 4194303)%Z;
  hi_lk : (φ (PArray.length (hkeys st))) = (φ cap);
  hi_ln : (φ (PArray.length (hnxt st))) = (φ cap);
  hi_lh : (φ (PArray.length (hhead st))) = 1024%Z;
  hi_cnt : ((φ (hcnt st)) <= (φ cap))%Z;
  hi_nxt : forall j, ((φ j) < (φ (hcnt st)))%Z -> ((φ ((hnxt st).[j])) <= (φ j))%Z;
  hi_head : forall b, ((φ b) < 1024)%Z -> ((φ ((hhead st).[b])) <= (φ (hcnt st)))%Z;
  hi_chain : forall j, ((φ j) < (φ (hcnt st)))%Z ->
               inS (hnxt st) ((hhead st).[hash ((hkeys st).[j])]) j;
  hi_inj : forall j1 j2, ((φ j1) < (φ (hcnt st)))%Z -> ((φ j2) < (φ (hcnt st)))%Z ->
             (hkeys st).[j1] = (hkeys st).[j2] -> j1 = j2 }.

Lemma lookup_spec : forall st cap s, HTinv st cap ->
  (lookup st s <> 0 -> ((φ (lookup st s - 1)) < (φ (hcnt st)))%Z /\
                       (hkeys st).[lookup st s - 1] = s) /\
  ((exists j, ((φ j) < (φ (hcnt st)))%Z /\ (hkeys st).[j] = s) -> lookup st s <> 0).
Proof.
  intros st cap s I. unfold lookup.
  set (p := (hhead st).[hash s]).
  assert (Hp : ((φ p) <= (φ (hcnt st)))%Z) by (apply (hi_head _ _ I); apply hash_bound).
  destruct (walk_spec s (hkeys st) (hnxt st) (φ (hcnt st)) (hi_nxt _ _ I) _ p
              (Zwf_well_founded 0 (φ p)) eq_refl Hp) as [[A B] | [A [B D]]].
  - split; [intro F; contradiction|].
    intros (j & Hj & Hk). exfalso.
    pose proof (hi_chain _ _ I j Hj) as Hc. rewrite Hk in Hc. fold p in Hc.
    exact (B j Hc Hk).
  - split; [|intros _; exact A].
    intros _. split; [|exact D].
    pose proof (inS_lt _ _ _ _ B (hi_nxt _ _ I) Hp). lia.
Qed.

Lemma intern_spec : forall st cap s st' id, HTinv st cap ->
  ((φ (hcnt st)) < (φ cap))%Z -> intern st s = (st', id) ->
  HTinv st' cap /\ ((φ id) < (φ (hcnt st')))%Z /\ (hkeys st').[id] = s /\
  ((φ (hcnt st)) <= (φ (hcnt st')) <= (φ (hcnt st)) + 1)%Z /\
  (forall j, ((φ j) < (φ (hcnt st)))%Z -> (hkeys st').[j] = (hkeys st).[j]) /\
  (forall j, ((φ j) < (φ (hcnt st')))%Z -> ((φ j) < (φ (hcnt st)))%Z \/ (hkeys st').[j] = s).
Proof.
  intros st cap s st' id I Hroom Hint.
  pose proof I as I'.
  destruct I' as [Icap Ilk Iln Ilh Icnt Inxt Ihead Ichain Iinj].
  destruct st as [keys nxt head c]. simpl in *.
  unfold intern in Hint. simpl in Hint.
  set (b := hash s) in *. set (hb := head.[b]) in *.
  assert (Hb : ((φ b) < 1024)%Z) by apply hash_bound.
  assert (Hhb : ((φ hb) <= (φ c))%Z) by (apply Ihead; exact Hb).
  destruct (walk_spec s keys nxt (φ c) Inxt _ hb (Zwf_well_founded 0 (φ hb)) eq_refl Hhb)
    as [[A B] | [A [B D]]].
  - rewrite A in Hint. simpl in Hint. injection Hint as <- <-.
    pose proof (to_Z_bounded c) as Bc.
    assert (Hc1 : (φ (c + 1)) = ((φ c) + 1)%Z) by (apply succ_spec; lia).
    assert (Hck : (c <? PArray.length keys) = true) by (rewrite ltb_spec; lia).
    assert (Hcn : (c <? PArray.length nxt) = true) by (rewrite ltb_spec; lia).
    assert (Hbh : (b <? PArray.length head) = true) by (rewrite ltb_spec; lia).
    (* the old ids keep their key and their next pointer *)
    assert (Kold : forall j, ((φ j) < (φ c))%Z -> keys.[c <- s].[j] = keys.[j])
      by (intros j Hj; apply pget_set_other; apply to_Z_neq; lia).
    assert (Nold : forall j, ((φ j) < (φ c))%Z -> nxt.[c <- hb].[j] = nxt.[j])
      by (intros j Hj; apply aget_set_other; apply to_Z_neq; lia).
    (* s is new *)
    assert (Snew : forall j, ((φ j) < (φ c))%Z -> keys.[j] <> s).
    { intros j Hj Hk. apply (B j); [|exact Hk].
      pose proof (Ichain j Hj) as Hc. rewrite Hk in Hc. exact Hc. }
    assert (Hsplit : forall j, ((φ j) < (φ (c + 1)))%Z -> ((φ j) < (φ c))%Z \/ j = c).
    { intros j Hj. rewrite Hc1 in Hj. destruct (Z.eq_dec (φ j) (φ c)) as [E | E].
      - right. apply to_Z_inj. exact E.
      - left. lia. }
    split; [ | split; [ | split; [ | split; [ | split]]]]; simpl.
    + constructor; simpl.
      * exact Icap.
      * rewrite plength_set. exact Ilk.
      * rewrite alength_set. exact Iln.
      * rewrite alength_set. exact Ilh.
      * lia.
      * intros j Hj. destruct (Hsplit j Hj) as [Hj' | ->].
        -- rewrite Nold by exact Hj'. pose proof (Inxt j Hj'). lia.
        -- rewrite aget_set_same by exact Hcn. lia.
      * intros b' Hb'. destruct (Z.eq_dec (φ b') (φ b)) as [E | E].
        -- assert (b' = b) by (apply to_Z_inj; exact E). subst b'.
           rewrite aget_set_same by exact Hbh. lia.
        -- rewrite aget_set_other by (apply to_Z_neq; lia). pose proof (Ihead b' Hb'). lia.
      * intros j Hj. destruct (Hsplit j Hj) as [Hj' | ->].
        -- rewrite Kold by exact Hj'.
           assert (Lift : forall p, ((φ p) <= (φ c))%Z -> inS nxt p j -> inS nxt.[c <- hb] p j)
             by (intros p Hp HS; apply (inS_lift nxt _ (φ c) p j HS Inxt Nold Hp)).
           destruct (Z.eq_dec (φ (hash keys.[j])) (φ b)) as [E | E].
           ++ assert (Eh : hash keys.[j] = b) by (apply to_Z_inj; exact E).
              rewrite Eh, aget_set_same by exact Hbh.
              apply inS_next; [apply to_Z_neq; lia|].
              replace (c + 1 - 1) with c by (apply to_Z_inj; rewrite pred_spec by (apply to_Z_neq; lia); lia).
              rewrite aget_set_same by exact Hcn.
              apply Lift; [exact Hhb|]. pose proof (Ichain j Hj') as Hc. rewrite Eh in Hc. exact Hc.
           ++ rewrite aget_set_other by (apply to_Z_neq; lia).
              apply Lift; [apply Ihead; apply hash_bound | apply Ichain; exact Hj'].
        -- rewrite pget_set_same by exact Hck. fold b. rewrite aget_set_same by exact Hbh.
           assert (Ec : c + 1 - 1 = c)
             by (apply to_Z_inj; rewrite pred_spec by (apply to_Z_neq; lia); lia).
           pose proof (inS_here nxt.[c <- hb] (c + 1) ltac:(apply to_Z_neq; lia)) as Hh.
           rewrite Ec in Hh. exact Hh.
      * intros j1 j2 Hj1 Hj2 Hk.
        destruct (Hsplit j1 Hj1) as [H1 | ->], (Hsplit j2 Hj2) as [H2 | ->].
        -- rewrite !Kold in Hk by assumption. apply Iinj; assumption.
        -- rewrite (Kold j1 H1) in Hk. rewrite pget_set_same in Hk by exact Hck.
           exfalso. exact (Snew j1 H1 Hk).
        -- rewrite (Kold j2 H2) in Hk. rewrite pget_set_same in Hk by exact Hck.
           exfalso. exact (Snew j2 H2 (eq_sym Hk)).
        -- reflexivity.
    + lia.
    + apply pget_set_same. exact Hck.
    + lia.
    + exact Kold.
    + intros j Hj. destruct (Hsplit j Hj) as [Hj' | ->]; [left; exact Hj'|].
      right. apply pget_set_same. exact Hck.
  - assert (Hw : (walk s keys nxt hb (Zwf_well_founded 0 (φ hb)) =? 0) = false).
    { destruct (walk s keys nxt hb (Zwf_well_founded 0 (φ hb)) =? 0) eqn:E; [|reflexivity].
      apply Uint63.eqb_spec in E. contradiction. }
    rewrite Hw in Hint. injection Hint as <- <-. simpl.
    pose proof (inS_lt _ _ _ _ B Inxt Hhb).
    split; [exact I|]. split; [lia|]. split; [exact D|]. split; [lia|].
    split; [reflexivity|]. intros j Hj. left. exact Hj.
Qed.

(* ------------------------------------------------------------------ *)
(* Interning every name                                                *)
(* ------------------------------------------------------------------ *)

Definition LineInv (xsrc xdst : array pstr) (i : int) (st : ht) (ia ib : array int) : Prop :=
  forall l, ((φ l) < (φ i))%Z ->
    ((φ (ia.[l])) < (φ (hcnt st)))%Z /\ (hkeys st).[ia.[l]] = xsrc.[l] /\
    ((φ (ib.[l])) < (φ (hcnt st)))%Z /\ (hkeys st).[ib.[l]] = xdst.[l].

Definition NameInv (xsrc xdst : array pstr) (i : int) (st : ht) : Prop :=
  forall j, ((φ j) < (φ (hcnt st)))%Z ->
    exists l, ((φ l) < (φ i))%Z /\ ((hkeys st).[j] = xsrc.[l] \/ (hkeys st).[j] = xdst.[l]).

Lemma iloop_spec : forall xsrc xdst n cap,
  ((φ n) <= 10000)%Z -> (φ cap) = ((φ n) + (φ n))%Z ->
  forall z i st ia ib H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  (φ (PArray.length ia)) = (φ n) -> (φ (PArray.length ib)) = (φ n) ->
  HTinv st cap -> ((φ (hcnt st)) <= (φ i) + (φ i))%Z ->
  LineInv xsrc xdst i st ia ib -> NameInv xsrc xdst i st ->
  forall st' ia' ib', iloop xsrc xdst n i st ia ib H = (st', ia', ib') ->
  HTinv st' cap /\ ((φ (hcnt st')) <= (φ n) + (φ n))%Z /\
  LineInv xsrc xdst n st' ia' ib' /\ NameInv xsrc xdst n st'.
Proof.
  intros xsrc xdst n cap Hn Hcap z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i st ia ib H Hz Hi Hla Hlb I Hc LI NI st' ia' ib' Hres.
  rewrite iloop_eq in Hres.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply succ_spec; lia).
    destruct (intern st xsrc.[i]) as [st1 a] eqn:E1.
    destruct (intern st1 xdst.[i]) as [st2 b] eqn:E2.
    cbv beta iota in Hres.
    destruct (intern_spec st cap _ st1 a I ltac:(lia) E1)
      as (I1 & Ha & Ka & Hc1 & Old1 & New1).
    destruct (intern_spec st1 cap _ st2 b I1 ltac:(lia) E2)
      as (I2 & Hb & Kb & Hc2 & Old2 & New2).
    assert (Hia : (i <? PArray.length ia) = true) by (rewrite ltb_spec; lia).
    assert (Hib : (i <? PArray.length ib) = true) by (rewrite ltb_spec; lia).
    refine (IH (gap n (i + 1)) _ (i + 1) st2 ia.[i <- a] ib.[i <- b]
              (Acc_inv H (dec_step n i Hin)) eq_refl _ _ _ I2 _ _ _ st' ia' ib' Hres);
      [ | lia | | | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + rewrite alength_set. exact Hla.
    + rewrite alength_set. exact Hlb.
    + intros l Hl. rewrite Hi1 in Hl.
      destruct (Z.eq_dec (φ l) (φ i)) as [E | E].
      * assert (l = i) by (apply to_Z_inj; exact E). subst l.
        rewrite !aget_set_same by assumption.
        split; [lia|]. split; [rewrite Old2 by lia; exact Ka|].
        split; [lia | exact Kb].
      * rewrite !aget_set_other by (apply to_Z_neq; lia).
        destruct (LI l ltac:(lia)) as (A1 & A2 & A3 & A4).
        split; [lia|]. split; [rewrite Old2, Old1 by lia; exact A2|].
        split; [lia | rewrite Old2, Old1 by lia; exact A4].
    + intros j Hj. rewrite Hi1.
      destruct (New2 j Hj) as [Hj1 | Kj].
      * destruct (New1 j Hj1) as [Hj0 | Kj].
        -- destruct (NI j Hj0) as (l & Hl & Kl).
           exists l. split; [lia|]. rewrite Old2, Old1 by lia. exact Kl.
        -- exists i. split; [lia|]. left. rewrite Old2 by lia. exact Kj.
      * exists i. split; [lia|]. right. exact Kj.
  - apply ltb_false in Hin. injection Hres as <- <- <-.
    assert (Ei : (φ i) = (φ n)) by lia.
    split; [exact I|]. split; [lia|]. split.
    + intros l Hl. apply LI. lia.
    + intros j Hj. destruct (NI j Hj) as (l & Hl & Kl). exists l. split; [lia | exact Kl].
Qed.

(* ------------------------------------------------------------------ *)
(* The edges                                                           *)
(* ------------------------------------------------------------------ *)

Definition edge_of (xrs : array relkind) (ia ib : array int) (k : Z) (l : int) (u v : Z) : Prop :=
  match xrs.[l] with
  | IsA => (u = (φ (ia.[l])) /\ v = (φ (ib.[l]))) \/ (u = (φ (ia.[l])) + k /\ v = (φ (ib.[l])) + k)
  | HasA => (u = (φ (ia.[l])) /\ v = (φ (ib.[l])) + k) \/ (u = (φ (ia.[l])) + k /\ v = (φ (ib.[l])) + k)
  end%Z.

Lemma eloop_spec : forall xrs ia ib k W n N, geom N W ->
  (φ N) = ((φ k) + (φ k))%Z -> ((φ k) <= 500)%Z ->
  (forall l, ((φ l) < (φ n))%Z -> ((φ (ia.[l])) < (φ k) /\ (φ (ib.[l])) < (φ k))%Z) ->
  forall z l T H, gap n l = z -> ((φ l) <= (φ n))%Z ->
  (φ (PArray.length T)) = ((φ N) * (φ W))%Z ->
  (forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
     (getbit T W u v = true <->
      exists l', ((φ l') < (φ l))%Z /\ edge_of xrs ia ib (φ k) l' (φ u) (φ v))) ->
  (φ (PArray.length (eloop xrs ia ib k W n l T H))) = ((φ N) * (φ W))%Z /\
  (forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
     (getbit (eloop xrs ia ib k W n l T H) W u v = true <->
      exists l', ((φ l') < (φ n))%Z /\ edge_of xrs ia ib (φ k) l' (φ u) (φ v))).
Proof.
  intros xrs ia ib k W n N G HN Hk Hid z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros l T H Hz Hl HL Inv.
  rewrite eloop_eq.
  destruct (bdec (l <? n)) as [Hln | Hln].
  - pose proof Hln as Hln'. rewrite ltb_spec in Hln'.
    assert (Hl1 : (φ (l + 1)) = ((φ l) + 1)%Z) by sia.
    cbv zeta.
    destruct (Hid l Hln') as [Ha Hb].
    set (a := ia.[l]) in *. set (b := ib.[l]) in *.
    pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded k).
    assert (Hak : (φ (a + k)) = ((φ a) + (φ k))%Z) by (apply add_small; lia).
    assert (Hbk : (φ (b + k)) = ((φ b) + (φ k))%Z) by (apply add_small; lia).
    assert (SL : forall T' x y, PArray.length (setbit T' W x y) = PArray.length T')
      by (intros; unfold setbit; apply alength_set).
    assert (Step : forall T1, (φ (PArray.length T1)) = ((φ N) * (φ W))%Z ->
      (forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
        (getbit T1 W u v = true <->
         (exists l', ((φ l') < (φ l))%Z /\ edge_of xrs ia ib (φ k) l' (φ u) (φ v)) \/
         edge_of xrs ia ib (φ k) l (φ u) (φ v))) ->
      (φ (PArray.length (eloop xrs ia ib k W n (l + 1) T1 (Acc_inv H (dec_step n l Hln)))))
        = ((φ N) * (φ W))%Z /\
      (forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
        (getbit (eloop xrs ia ib k W n (l + 1) T1 (Acc_inv H (dec_step n l Hln))) W u v = true <->
         exists l', ((φ l') < (φ n))%Z /\ edge_of xrs ia ib (φ k) l' (φ u) (φ v)))).
    { intros T1 HL1 Inv1.
      eapply IH; [ | reflexivity | lia | exact HL1 | ].
      - rewrite <- Hz. apply dec_step. exact Hln.
      - intros u v Hu Hv. rewrite Inv1 by assumption. rewrite Hl1. split.
        + intros [(l' & Hl' & Ed) | Ed].
          * exists l'. split; [lia | exact Ed].
          * exists l. split; [lia | exact Ed].
        + intros (l' & Hl' & Ed). destruct (Z.eq_dec (φ l') (φ l)) as [E | E].
          * right. assert (l' = l) by (apply to_Z_inj; exact E). subst l'. exact Ed.
          * left. exists l'. split; [lia | exact Ed]. }
    unfold edge_of in Step at 2. fold a b in Step.
    destruct (xrs.[l]) eqn:Er; apply Step.
    + rewrite !SL. exact HL.
    + intros u v Hu Hv.
      rewrite (getbit_setbit N W) by (try rewrite SL; first [exact G | exact HL | lia]).
      rewrite (getbit_setbit N W) by (first [exact G | exact HL | lia]).
      rewrite Inv by assumption. rewrite Hak, Hbk. tauto.
    + rewrite !SL. exact HL.
    + intros u v Hu Hv.
      rewrite (getbit_setbit N W) by (try rewrite SL; first [exact G | exact HL | lia]).
      rewrite (getbit_setbit N W) by (first [exact G | exact HL | lia]).
      rewrite Inv by assumption. rewrite Hak, Hbk. tauto.
  - apply ltb_false in Hln.
    split; [exact HL|]. intros u v Hu Hv. rewrite Inv by assumption.
    split; intros (l' & Hl' & Ed); exists l'; split; auto; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The answers                                                         *)
(* ------------------------------------------------------------------ *)

Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.

Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.

Lemma fill_spec : forall f m z j out H, gap m j = z -> ((φ j) <= (φ m))%Z ->
  (φ (PArray.length out)) = (φ m) ->
  (forall j', ((φ j') < (φ j))%Z -> out.[j'] = f j') ->
  (φ (PArray.length (fill f m j out H))) = (φ m) /\
  (forall j', ((φ j') < (φ m))%Z -> (fill f m j out H).[j'] = f j').
Proof.
  intros f m z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j out H Hz Hj HL Inv.
  rewrite fill_eq.
  destruct (bdec (j <? m)) as [Hjm | Hjm].
  - pose proof Hjm as Hjm'. rewrite ltb_spec in Hjm'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hjm.
    + rewrite blength_set. exact HL.
    + intros j' Hj'. rewrite Hj1 in Hj'.
      destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
      * assert (j' = j) by (apply to_Z_inj; exact E). subst j'.
        apply bget_set_same. rewrite ltb_spec. lia.
      * rewrite bget_set_other by (apply to_Z_neq; lia). apply Inv. lia.
  - apply ltb_false in Hjm. split; [exact HL|]. intros j' Hj'. apply Inv. lia.
Qed.

(* moving a reflexive-transitive closure along an injective naming *)
Section Transfer.
  Local Open Scope Z_scope.
  Variables (k : Z) (key : Z -> String.string).
  Variables (R : String.string -> String.string -> Prop) (r : Z -> Z -> Prop).
  Hypothesis Hinj : forall a b, 0 <= a < k -> 0 <= b < k -> key a = key b -> a = b.
  Hypothesis Hr : forall a b, r a b -> 0 <= a < k /\ 0 <= b < k.
  Hypothesis HR : forall x y, R x y <-> exists a b, r a b /\ key a = x /\ key b = y.

  Lemma crt_key_r : forall X Y, clos_refl_trans String.string R X Y ->
    forall a, 0 <= a < k -> key a = X ->
    exists b, 0 <= b < k /\ key b = Y /\ clos_refl_trans Z r a b.
  Proof.
    intros X Y H. induction H as [X Y H | X | X Y Z' H1 IH1 H2 IH2]; intros a Ha Ka.
    - apply HR in H. destruct H as (a' & b' & Hab & Ka' & Kb').
      destruct (Hr a' b' Hab) as [Ba Bb].
      assert (a' = a) by (apply Hinj; auto; congruence). subst a'.
      exists b'. split; [exact Bb|]. split; [exact Kb'|]. apply rt_step. exact Hab.
    - exists a. split; [exact Ha|]. split; [exact Ka | apply rt_refl].
    - destruct (IH1 a Ha Ka) as (b1 & Hb1 & Kb1 & C1).
      destruct (IH2 b1 Hb1 Kb1) as (b2 & Hb2 & Kb2 & C2).
      exists b2. split; [exact Hb2|]. split; [exact Kb2|]. eapply rt_trans; eauto.
  Qed.

  Lemma crt_key : forall a b, 0 <= a < k -> 0 <= b < k ->
    (clos_refl_trans String.string R (key a) (key b) <-> clos_refl_trans Z r a b).
  Proof.
    intros a b Ha Hb. split.
    - intros H. destruct (crt_key_r _ _ H a Ha eq_refl) as (b' & Hb' & Kb' & C).
      assert (b' = b) by (apply Hinj; auto). subst b'. exact C.
    - intros H.
      assert (G : forall a b, clos_refl_trans Z r a b -> 0 <= a < k ->
                  0 <= b < k /\ clos_refl_trans String.string R (key a) (key b)).
      { clear a b Ha Hb H. intros a b H.
        induction H as [a b H | a | a b c H1 IH1 H2 IH2]; intros Ha0.
        - split; [exact (proj2 (Hr a b H))|].
          apply rt_step. apply HR. exists a, b. auto.
        - split; [exact Ha0 | apply rt_refl].
        - destruct (IH1 Ha0) as [Hb1 C1]. destruct (IH2 Hb1) as [Hc1 C2].
          split; [exact Hc1 | eapply rt_trans; eauto]. }
      exact (proj2 (G a b H Ha)).
  Qed.
End Transfer.

Lemma of_to_nat : forall l : int, of_Z (Z.of_nat (Z.to_nat (φ l))) = l.
Proof.
  intros l. pose proof (to_Z_bounded l). rewrite Z2Nat.id by lia. apply of_to_Z.
Qed.

Lemma to_of_small : forall z : Z, (0 <= z < 9223372036854775808)%Z -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. exact Hz. Qed.

Lemma repr_str_int : forall (xa : array pstr) (la : list String.string), repr xa la ->
  forall l : int, ((φ l) < Z.of_nat (List.length la))%Z ->
    nth_error la (Z.to_nat (φ l)) = Some (to_math xa.[l]).
Proof.
  intros xa la H l Hl. destruct (repr_arr_str xa la H) as [Hlen Hc].
  pose proof (to_Z_bounded l).
  rewrite Hc by lia. rewrite of_to_nat. reflexivity.
Qed.

Lemma repr_rel_int : forall (xa : array relkind) (la : list relkind), repr xa la ->
  forall l : int, ((φ l) < Z.of_nat (List.length la))%Z ->
    nth_error la (Z.to_nat (φ l)) = Some xa.[l].
Proof.
  intros xa la H l Hl. destruct (repr_arr_rel xa la H) as [Hlen Hc].
  pose proof (to_Z_bounded l).
  rewrite Hc by lia. rewrite of_to_nat. reflexivity.
Qed.

Lemma count_bound : forall (keys : array pstr) (c : int) (names : list String.string),
  (forall j1 j2, ((φ j1) < (φ c))%Z -> ((φ j2) < (φ c))%Z -> keys.[j1] = keys.[j2] -> j1 = j2) ->
  (forall j, ((φ j) < (φ c))%Z -> In (to_math keys.[j]) names) ->
  ((φ c) <= Z.of_nat (List.length names))%Z.
Proof.
  intros keys c names Hinj Hin.
  pose proof (to_Z_bounded c) as Bc.
  set (L := map (fun x : nat => to_math keys.[of_Z (Z.of_nat x)]) (seq 0 (Z.to_nat (φ c)))).
  assert (Hlen : List.length L = Z.to_nat (φ c)) by (unfold L; rewrite length_map, length_seq; reflexivity).
  assert (Hnd : NoDup L).
  { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
    intros x y Hx Hy E. apply in_seq in Hx, Hy.
    apply to_math_inj in E. apply Hinj in E;
      [| rewrite to_of_small by lia; lia | rewrite to_of_small by lia; lia].
    apply (f_equal to_Z) in E. rewrite !to_of_small in E by lia. lia. }
  assert (Hincl : incl L names).
  { intros s Hs. unfold L in Hs. apply in_map_iff in Hs. destruct Hs as (x & <- & Hx).
    apply in_seq in Hx. apply Hin. rewrite to_of_small by lia. lia. }
  pose proof (NoDup_incl_length Hnd Hincl). lia.
Qed.

Lemma glength_make : forall (A : Set) (n : int) (d : A), ((φ n) <= 4194303)%Z ->
  (φ (PArray.length@{Set} (PArray.make@{Set} n d))) = (φ n).
Proof.
  intros A n d Hn.
  assert (E0 : PArray.length@{Set} (PArray.make@{Set} n d)
               = if n <=? PArray.max_length then n else PArray.max_length)
    by exact (length_make A n d).
  rewrite E0.
  destruct (n <=? PArray.max_length) eqn:E; [reflexivity|].
  exfalso. rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E. lia.
Qed.

Lemma getbit_make : forall n W u v, getbit (PArray.make n 0) W u v = false.
Proof.
  intros n W u v. rewrite getbit_spec, aget_make. change (φ 0) with 0%Z.
  apply Z.testbit_0_l.
Qed.

(* ------------------------------------------------------------------ *)
(* Correctness                                                         *)
(* ------------------------------------------------------------------ *)

Section Correct.

  Variables (src : list string) (rs : list relkind) (dst qsrc : list string)
            (qrs : list relkind) (qdst : list string).
  Variables (xsrc : array pstr) (xrs : array relkind) (xdst xqsrc : array pstr)
            (xqrs : array relkind) (xqdst : array pstr).
  Hypothesis Hv : valid_input src rs dst qsrc qrs qdst.
  Hypothesis Rsrc : repr xsrc src.
  Hypothesis Rrs : repr xrs rs.
  Hypothesis Rdst : repr xdst dst.
  Hypothesis Rqsrc : repr xqsrc qsrc.
  Hypothesis Rqrs : repr xqrs qrs.
  Hypothesis Rqdst : repr xqdst qdst.

  Definition nn : int := PArray.length xsrc.

  (* a given line of kind r from id a to id b *)
  Definition eir (ia ib : array int) (r : relkind) (a b : Z) : Prop :=
    exists l, ((φ l) < (φ nn))%Z /\ xrs.[l] = r /\ (φ (ia.[l])) = a /\ (φ (ib.[l])) = b.

  (* the name of id a *)
  Definition keyz (st : ht) (a : Z) : string := to_math (hkeys st).[of_Z a].

  Lemma Ln : (φ nn) = Z.of_nat (List.length src).
  Proof. exact (proj1 (repr_arr_str _ _ Rsrc)). Qed.

  Lemma Lrs : (φ nn) = Z.of_nat (List.length rs).
  Proof.
    rewrite Ln. destruct Hv as [_ H _ _ _ _ _ _ _ _]. unfold len in H. lia.
  Qed.

  Lemma Ldst : (φ nn) = Z.of_nat (List.length dst).
  Proof.
    rewrite Ln. destruct Hv as [_ _ H _ _ _ _ _ _ _]. unfold len in H. lia.
  Qed.

  Lemma given_iff : forall st ia ib, LineInv xsrc xdst nn st ia ib ->
    forall r X Y, given src rs dst r X Y <->
      exists a b, eir ia ib r a b /\ keyz st a = X /\ keyz st b = Y.
  Proof.
    intros st ia ib LI r X Y. pose proof Ln as L1. pose proof Lrs as L2. pose proof Ldst as L3.
    split.
    - intros (i & H1 & H2 & H3).
      assert (Hi : (i < List.length src)%nat)
        by (apply nth_error_Some; rewrite H1; discriminate).
      set (l := of_Z (Z.of_nat i)).
      assert (El : (φ l) = Z.of_nat i) by (apply to_of_small; lia).
      assert (Ei : Z.to_nat (φ l) = i) by lia.
      rewrite <- Ei, (repr_str_int _ _ Rsrc l ltac:(lia)) in H1.
      rewrite <- Ei, (repr_rel_int _ _ Rrs l ltac:(lia)) in H2.
      rewrite <- Ei, (repr_str_int _ _ Rdst l ltac:(lia)) in H3.
      injection H1 as <-. injection H2 as <-. injection H3 as <-.
      destruct (LI l ltac:(lia)) as (A1 & A2 & A3 & A4).
      exists (φ (ia.[l])), (φ (ib.[l])). split; [exists l; repeat split; lia|].
      unfold keyz. rewrite !of_to_Z, A2, A4. split; reflexivity.
    - intros (a & b & (l & Hl & Hr & Ha & Hb) & Ka & Kb).
      destruct (LI l Hl) as (A1 & A2 & A3 & A4).
      exists (Z.to_nat (φ l)).
      rewrite (repr_str_int _ _ Rsrc l ltac:(lia)), (repr_rel_int _ _ Rrs l ltac:(lia)),
              (repr_str_int _ _ Rdst l ltac:(lia)).
      unfold keyz in Ka, Kb. rewrite <- Ha, of_to_Z, A2 in Ka. rewrite <- Hb, of_to_Z, A4 in Kb.
      refine (conj (f_equal Some Ka) (conj (f_equal Some Hr) (f_equal Some Kb))).
  Qed.

  Lemma eir_bound : forall st ia ib, LineInv xsrc xdst nn st ia ib ->
    forall r a b, eir ia ib r a b ->
      (0 <= a < (φ (hcnt st)) /\ 0 <= b < (φ (hcnt st)))%Z.
  Proof.
    intros st ia ib LI r a b (l & Hl & _ & <- & <-).
    destruct (LI l Hl) as (A1 & _ & A3 & _).
    pose proof (to_Z_bounded (ia.[l])). pose proof (to_Z_bounded (ib.[l])). lia.
  Qed.

  Lemma keyz_inj : forall st cap, HTinv st cap ->
    forall a b, (0 <= a < (φ (hcnt st)))%Z -> (0 <= b < (φ (hcnt st)))%Z ->
    keyz st a = keyz st b -> a = b.
  Proof.
    intros st cap I a b Ha Hb E. unfold keyz in E. apply to_math_inj in E.
    pose proof (to_Z_bounded (hcnt st)).
    apply (hi_inj _ _ I) in E; [| rewrite to_of_small; lia | rewrite to_of_small; lia].
    apply (f_equal to_Z) in E. rewrite !to_of_small in E by lia. exact E.
  Qed.

  Lemma any_iff : forall st ia ib, LineInv xsrc xdst nn st ia ib ->
    forall X Y, any_given src rs dst X Y <->
      exists a b, ea (eir ia ib IsA) (eir ia ib HasA) a b /\ keyz st a = X /\ keyz st b = Y.
  Proof.
    intros st ia ib LI X Y. unfold any_given, ea.
    rewrite !(given_iff st ia ib LI). split.
    - intros [(a & b & A & B & C) | (a & b & A & B & C)]; exists a, b; auto.
    - intros (a & b & [A | A] & B & C); [left | right]; exists a, b; auto.
  Qed.

  Lemma name_found : forall st ia ib, LineInv xsrc xdst nn st ia ib ->
    forall s, In (to_math s) (src ++ dst) ->
    exists j, ((φ j) < (φ (hcnt st)))%Z /\ (hkeys st).[j] = s.
  Proof.
    intros st ia ib LI s Hin. pose proof Ln as L1. pose proof Ldst as L3.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin];
      apply In_nth_error in Hin; destruct Hin as (i & Hi).
    - assert (Hil : (i < List.length src)%nat)
        by (apply nth_error_Some; rewrite Hi; discriminate).
      set (l := of_Z (Z.of_nat i)).
      assert (El : (φ l) = Z.of_nat i) by (apply to_of_small; lia).
      replace i with (Z.to_nat (φ l)) in Hi by lia.
      rewrite (repr_str_int _ _ Rsrc l ltac:(lia)) in Hi. injection Hi as Hi.
      apply to_math_inj in Hi.
      destruct (LI l ltac:(lia)) as (A1 & A2 & _ & _).
      exists (ia.[l]). split; [exact A1 | rewrite A2; exact Hi].
    - assert (Hil : (i < List.length dst)%nat)
        by (apply nth_error_Some; rewrite Hi; discriminate).
      set (l := of_Z (Z.of_nat i)).
      assert (El : (φ l) = Z.of_nat i) by (apply to_of_small; lia).
      replace i with (Z.to_nat (φ l)) in Hi by lia.
      rewrite (repr_str_int _ _ Rdst l ltac:(lia)) in Hi. injection Hi as Hi.
      apply to_math_inj in Hi.
      destruct (LI l ltac:(lia)) as (_ & _ & A3 & A4).
      exists (ib.[l]). split; [exact A3 | rewrite A4; exact Hi].
  Qed.

  Lemma lookup_key : forall st cap ia ib, HTinv st cap -> LineInv xsrc xdst nn st ia ib ->
    forall s, In (to_math s) (src ++ dst) ->
    lookup st s <> 0 /\ (0 <= (φ (lookup st s - 1)) < (φ (hcnt st)))%Z /\
    keyz st (φ (lookup st s - 1)) = to_math s.
  Proof.
    intros st cap ia ib I LI s Hin.
    destruct (lookup_spec st cap s I) as [A B].
    pose proof (B (name_found st ia ib LI s Hin)) as Hne.
    destruct (A Hne) as [C D].
    split; [exact Hne|]. split; [pose proof (to_Z_bounded (lookup st s - 1)); lia|].
    unfold keyz. rewrite of_to_Z, D. reflexivity.
  Qed.

  Lemma edge_Elay : forall (ia ib : array int) (c : Z),
    (forall l, ((φ l) < (φ nn))%Z -> ((φ (ia.[l])) < c /\ (φ (ib.[l])) < c)%Z) ->
    forall u v, (exists l, ((φ l) < (φ nn))%Z /\ edge_of xrs ia ib c l u v) <->
      Elay c (eir ia ib IsA) (eir ia ib HasA) u v.
  Proof.
    intros ia ib c Hid u v. unfold Elay, ea. split.
    - intros (l & Hl & Ed). unfold edge_of in Ed.
      destruct (xrs.[l]) eqn:Er; destruct Ed as [[-> ->] | [-> ->]].
      + left. exists l. auto.
      + right; right; left. exists l. repeat split; auto; lia.
      + right; left. exists l. repeat split; auto; lia.
      + right; right; right. exists l. repeat split; auto; lia.
    - intros [(l & Hl & Er & Ha & Hb) | [(l & Hl & Er & Ha & Hb) |
              [(l & Hl & Er & Ha & Hb) | (l & Hl & Er & Ha & Hb)]]];
        exists l; split; auto; unfold edge_of; rewrite Er; lia.
  Qed.

  Lemma answer_ok : forall st cap ia ib T W N,
    HTinv st cap -> LineInv xsrc xdst nn st ia ib -> geom N W ->
    (φ N) = ((φ (hcnt st)) + (φ (hcnt st)))%Z ->
    (forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
       (getbit T W u v = true <->
        clos_trans Z (Elay (φ (hcnt st)) (eir ia ib IsA) (eir ia ib HasA)) (φ u) (φ v))) ->
    forall s1 s2 r, In (to_math s1) (src ++ dst) -> In (to_math s2) (src ++ dst) ->
    (answer st T W (hcnt st) s1 s2 r = true <-> follows src rs dst r (to_math s1) (to_math s2)).
  Proof.
    intros st cap ia ib T W N I LI G HN HT s1 s2 r In1 In2.
    destruct (lookup_key st cap ia ib I LI s1 In1) as (A1 & B1 & K1).
    destruct (lookup_key st cap ia ib I LI s2 In2) as (A2 & B2 & K2).
    set (c := (φ (hcnt st))) in *.
    pose proof (eir_bound st ia ib LI IsA) as BI.
    pose proof (eir_bound st ia ib LI HasA) as BH.
    unfold answer. cbv zeta.
    set (a := lookup st s1) in *. set (b := lookup st s2) in *.
    rewrite (proj2 (Uint63.eqb_false_spec a 0) A1), (proj2 (Uint63.eqb_false_spec b 0) A2).
    rewrite <- K1, <- K2.
    set (x := (φ (a - 1))) in *. set (y := (φ (b - 1))) in *.
    assert (Hx : x = (φ (a - 1))) by reflexivity. assert (Hy : y = (φ (b - 1))) by reflexivity.
    clearbody x y a b.
    destruct r; simpl.
    - unfold is_a.
      rewrite (crt_key c (keyz st) (given src rs dst IsA) (eir ia ib IsA)
                 (keyz_inj st cap I) (BI) (given_iff st ia ib LI IsA) x y B1 B2).
      rewrite <- (isa_iff c (eir ia ib IsA) (eir ia ib HasA) BI BH x y B1 B2).
      pose proof (HT (a - 1) (b - 1) ltac:(lia) ltac:(lia)) as HTab. rewrite <- Hx, <- Hy in HTab.
      rewrite <- HTab.
      assert (Eab : (a =? b) = (x =? y)%Z).
      { assert (Ha' : (φ a) = (x + 1)%Z) by (rewrite Hx, pred_spec by assumption; lia).
        assert (Hb' : (φ b) = (y + 1)%Z) by (rewrite Hy, pred_spec by assumption; lia).
        rewrite eqb_Z, Ha', Hb'.
        destruct (Z.eqb_spec (x + 1) (y + 1)), (Z.eqb_spec x y); try reflexivity; lia. }
      rewrite Eab. destruct (Z.eqb_spec x y) as [E | E].
      + split; [intros _; left; exact E | intros _; reflexivity].
      + split; [intros H; right; exact H | intros [H | H]; [contradiction | exact H]].
    - unfold has_a.
      assert (Ebk : (φ (b - 1 + hcnt st)) = (y + c)%Z)
        by (rewrite Hy; unfold c; apply add_small; pose proof (to_Z_bounded (hcnt st)); lia).
      rewrite (HT (a - 1) (b - 1 + hcnt st)) by lia. rewrite Ebk, <- Hx.
      rewrite (has_iff c (eir ia ib IsA) (eir ia ib HasA) BI BH x y B1 B2), Hrel_iff.
      assert (BA : forall p q, ea (eir ia ib IsA) (eir ia ib HasA) p q ->
                     (0 <= p < c /\ 0 <= q < c)%Z)
        by (intros p q [E | E]; [apply (BI p q E) | apply (BH p q E)]).
      pose proof (crt_key c (keyz st) (any_given src rs dst)
                    (ea (eir ia ib IsA) (eir ia ib HasA))
                    (keyz_inj st cap I) BA (any_iff st ia ib LI)) as CK.
      split.
      + intros (y1 & y1' & C1 & C2 & C3).
        destruct (BH y1 y1' C2) as [By1 By1'].
        exists (keyz st y1), (keyz st y1').
        rewrite CK by assumption. split; [exact C1|].
        split; [apply (given_iff st ia ib LI); exists y1, y1'; auto|].
        rewrite CK by assumption. exact C3.
      + intros (Y1 & Y1' & C1 & C2 & C3).
        apply (given_iff st ia ib LI) in C2. destruct C2 as (y1 & y1' & C2 & <- & <-).
        destruct (BH y1 y1' C2) as [By1 By1'].
        exists y1, y1'. rewrite CK in C1, C3 by assumption. auto.
  Qed.

  Theorem impl_correct : exists o : list bool,
    repr (isahasa_impl xsrc xrs xdst xqsrc xqrs xqdst) o /\
    isahasa_spec src rs dst qsrc qrs qdst o.
  Proof.
    pose proof Hv as [Vn Vrs Vdst Vm Vqrs Vqdst Vw Vdist Vq Vac].
    unfold len in Vn, Vrs, Vdst, Vm, Vqrs, Vqdst.
    pose proof Ln as L1.
    unfold isahasa_impl. cbv zeta.
    set (n := PArray.length xsrc).
    assert (Hn : (φ n) = Z.of_nat (List.length src)) by exact L1.
    assert (Hn2 : (φ (n + n)) = ((φ n) + (φ n))%Z) by (apply add_small; lia).
    destruct (iloop xsrc xdst n 0 _ _ _ _) as [[st ia] ib] eqn:Eil.
    cbv beta iota.
    (* the empty table *)
    assert (I0 : HTinv (mkht (PArray.make@{Set} (n + n) (PrimString.make 0 0)) (PArray.make@{Set} (n + n) 0)
                             (PArray.make@{Set} 1024 0) 0) (n + n)).
    { constructor; cbn [hkeys hnxt hhead hcnt].
      - lia.
      - apply glength_make. lia.
      - apply glength_make. lia.
      - reflexivity.
      - change (φ 0) with 0%Z. lia.
      - intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia.
      - intros b _.
        replace ((PArray.make@{Set} 1024 0).[b]) with 0 by (symmetry; exact (get_make int 0 1024 b)).
        change (φ 0) with 0%Z. lia.
      - intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia.
      - intros j1 j2 Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j1). lia. }
    destruct (iloop_spec xsrc xdst n (n + n) ltac:(lia) Hn2 _ 0 _
                (PArray.make@{Set} n 0) (PArray.make@{Set} n 0) (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(apply glength_make; lia) ltac:(apply glength_make; lia) I0
                ltac:(simpl; change (φ 0) with 0%Z; lia)
                ltac:(intros l Hl; change (φ 0) with 0%Z in Hl; pose proof (to_Z_bounded l); lia)
                ltac:(intros j Hj; simpl in Hj; change (φ 0) with 0%Z in Hj;
                      pose proof (to_Z_bounded j); lia)
                st ia ib Eil) as (I & Hcnt & LI & NI).
    assert (LI' : LineInv xsrc xdst nn st ia ib) by exact LI.
    set (k := hcnt st) in *.
    pose proof (to_Z_bounded k) as Bk.
    (* at most 500 names *)
    assert (Hk : ((φ k) <= 500)%Z).
    { destruct Vdist as (names & Hlen & Hnames). unfold len in Hlen.
      enough ((φ k) <= Z.of_nat (List.length names))%Z by lia.
      apply (count_bound (hkeys st)); [exact (hi_inj _ _ I)|].
      intros j Hj. apply Hnames. destruct (NI j Hj) as (l & Hl & [E | E]); rewrite E.
      - apply in_or_app. left. apply (nth_error_In _ (Z.to_nat (φ l))).
        exact (repr_str_int _ _ Rsrc l ltac:(lia)).
      - apply in_or_app. right. apply in_or_app. left.
        apply (nth_error_In _ (Z.to_nat (φ l))).
        pose proof Ldst as L3. exact (repr_str_int _ _ Rdst l ltac:(unfold nn in *; lia)). }
    (* the table geometry *)
    assert (HN : (φ (k + k)) = ((φ k) + (φ k))%Z) by (apply add_small; lia).
    set (N := k + k) in *.
    assert (HW : (φ ((N + 62) / 63)) = (((φ N) + 62) / 63)%Z)
      by (rewrite div_spec, add_small; [reflexivity | change (φ 62) with 62%Z; lia]).
    set (W := (N + 62) / 63) in *.
    assert (HW16 : ((φ W) < 17)%Z) by (rewrite HW; apply Z.div_lt_upper_bound; lia).
    pose proof (to_Z_bounded W) as BW.
    assert (HNW : ((φ N) * (φ W) <= 1000 * 16)%Z) by (apply Z.mul_le_mono_nonneg; lia).
    assert (G : geom N W) by (split; [exact HW | lia]).
    assert (HNW' : (φ (N * W)) = ((φ N) * (φ W))%Z).
    { rewrite mul_spec. apply Z.mod_small. pose proof (to_Z_bounded N). rewrite wB_val. nia. }
    (* the edges *)
    assert (Hid : forall l, ((φ l) < (φ n))%Z -> ((φ (ia.[l])) < (φ k) /\ (φ (ib.[l])) < (φ k))%Z)
      by (intros l Hl; destruct (LI l Hl) as (A1 & _ & A3 & _); split; assumption).
    destruct (eloop_spec xrs ia ib k W n N G HN Hk Hid _ 0 (PArray.make@{Set} (N * W) 0)
                (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(rewrite glength_make; lia)
                ltac:(intros u v _ _; rewrite getbit_make; split; [discriminate|];
                      intros (l' & Hl' & _); change (φ 0) with 0%Z in Hl';
                      pose proof (to_Z_bounded l'); lia))
      as [HL1 HB1].
    set (T1 := eloop xrs ia ib k W n 0 _ _) in *.
    set (E := Elay (φ k) (eir ia ib IsA) (eir ia ib HasA)).
    assert (HidZ : forall l, ((φ l) < (φ nn))%Z -> ((φ (ia.[l])) < (φ k) /\ (φ (ib.[l])) < (φ k))%Z)
      by exact Hid.
    (* the closure *)
    destruct (fw_outer_spec E N W G _ 0 T1 (Zwf_well_founded 0 (gap N 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded N); lia) HL1
                ltac:(intros u v Hu Hv'; change (φ 0) with 0%Z; rewrite Q_zero, HB1 by assumption;
                      exact (edge_Elay ia ib (φ k) HidZ (φ u) (φ v))))
      as [HL2 HB2].
    set (T := fw_outer T1 N W 0 _) in *.
    assert (HT : forall u v, ((φ u) < (φ N))%Z -> ((φ v) < (φ N))%Z ->
              (getbit T W u v = true <-> clos_trans Z E (φ u) (φ v))).
    { intros u v Hu Hv'. rewrite HB2 by assumption. split.
      - apply Q_tc.
      - apply tc_Q. intros p q Hpq.
        pose proof (Elay_bound (φ k) (eir ia ib IsA) (eir ia ib HasA)
                      (eir_bound st ia ib LI' IsA) (eir_bound st ia ib LI' HasA) p q Hpq).
        lia. }
    (* the queries *)
    destruct (repr_arr_str _ _ Rqsrc) as [Lq Cq].
    destruct (repr_arr_str _ _ Rqdst) as [_ Cqd].
    destruct (repr_arr_rel _ _ Rqrs) as [_ Cqr].
    set (m := PArray.length xqsrc).
    assert (Hm : (φ m) = Z.of_nat (List.length qsrc)) by exact Lq.
    set (f := fun j => answer st T W k xqsrc.[j] xqdst.[j] xqrs.[j]).
    destruct (fill_spec f m _ 0 (PArray.make@{Set} m false) (Zwf_well_founded 0 (gap m 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(apply glength_make; lia)
                ltac:(intros j' Hj'; change (φ 0) with 0%Z in Hj'; pose proof (to_Z_bounded j'); lia))
      as [HLo Ho].
    set (out := fill f m 0 (PArray.make@{Set} m false) _).
    exists (map (fun j : nat => out.[of_Z (Z.of_nat j)]) (seq 0 (List.length qsrc))).
    assert (Hlen : List.length (map (fun j : nat => out.[of_Z (Z.of_nat j)])
                                    (seq 0 (List.length qsrc))) = List.length qsrc)
      by (rewrite length_map, length_seq; reflexivity).
    assert (Hnth : forall j, (j < List.length qsrc)%nat ->
              nth j (map (fun j : nat => out.[of_Z (Z.of_nat j)]) (seq 0 (List.length qsrc))) false
              = f (of_Z (Z.of_nat j))).
    { intros j Hj.
      rewrite (nth_indep _ false (out.[of_Z (Z.of_nat 0)])) by (rewrite Hlen; exact Hj).
      rewrite (map_nth (fun j : nat => out.[of_Z (Z.of_nat j)])).
      rewrite seq_nth by exact Hj. simpl.
      apply Ho. rewrite to_of_small by lia. lia. }
    split.
    - split.
      + rewrite Hlen. refine (eq_trans _ (eq_sym HLo)). exact (eq_sym Hm).
      + intros j Hj. rewrite Hlen in Hj.
        exists (out.[of_Z (Z.of_nat j)]). split.
        * rewrite nth_error_map, nth_error_seq.
          destruct (Nat.ltb_spec j (List.length qsrc)); [reflexivity | lia].
        * reflexivity.
    - split.
      + unfold len. rewrite Hlen. reflexivity.
      + intros j Hj. rewrite Hnth by exact Hj.
        pose proof (Vqrs) as Lqr. pose proof (Vqdst) as Lqd.
        rewrite (nth_error_nth qsrc j EmptyString (Cq j Hj)).
        rewrite (nth_error_nth qdst j EmptyString (Cqd j ltac:(lia))).
        rewrite (nth_error_nth qrs j IsA (Cqr j ltac:(lia))).
        unfold f.
        apply (answer_ok st (n + n) ia ib T W N I LI' G HN HT).
        * apply Vq. apply in_or_app. left. rewrite <- (nth_error_nth qsrc j EmptyString (Cq j Hj)).
          apply nth_In. exact Hj.
        * apply Vq. apply in_or_app. right.
          rewrite <- (nth_error_nth qdst j EmptyString (Cqd j ltac:(lia))).
          apply nth_In. lia.
  Qed.

End Correct.

Lemma isahasa_correct :
  forall (src : list string) (rs : list relkind) (dst : list string)
         (qsrc : list string) (qrs : list relkind) (qdst : list string)
         (xsrc : array PrimString.string) (xrs : array relkind)
         (xdst : array PrimString.string) (xqsrc : array PrimString.string)
         (xqrs : array relkind) (xqdst : array PrimString.string),
  valid_input src rs dst qsrc qrs qdst ->
  repr xsrc src -> repr xrs rs -> repr xdst dst ->
  repr xqsrc qsrc -> repr xqrs qrs -> repr xqdst qdst ->
  exists o : list bool,
    repr (isahasa xsrc xrs xdst xqsrc xqrs xqdst) o /\
    isahasa_spec src rs dst qsrc qrs qdst o.
Proof. intros. eapply impl_correct; eassumption. Qed.
