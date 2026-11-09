(* Correctness proofs for knapsack2_implem.v. *)
(* Implementation of knapsack2 (knapsack2.spec). *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export knapsack2_implem.
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

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

(* Unfolding equations. *)
Lemma min_loop_eq : forall g n i best H,
  min_loop g n i best H =
  match bdec (i <? n) with
  | left Hi =>
      min_loop g n (i + 1) (if g.[i] <? best then g.[i] else best)
        (Acc_inv H (dec_step n i Hi))
  | right _ => best
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma gcd_loop_eq : forall u v H,
  gcd_loop u v H =
  match bdec (v =? 0) with
  | left _ => u
  | right Hv => gcd_loop v (u mod v) (Acc_inv H (gcd_dec u v Hv))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_eq : forall A m a' L j x p H,
  scan A m a' L j x p H =
  match bdec (j <? L) with
  | left Hj =>
      scan A m a' L (j + 1) (nxt m a' x) (if A.[x] <? A.[p] then x else p)
        (Acc_inv H (dec_step L j Hj))
  | right _ => p
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma relax_eq : forall m a a' L1 j x cur A H,
  relax m a a' L1 j x cur A H =
  match bdec (j <? L1) with
  | left Hj =>
      let y := nxt m a' x in
      let c := cur + a in
      let v := A.[y] in
      if c <? v then relax m a a' L1 (j + 1) y c A.[y <- c]
                       (Acc_inv H (dec_step L1 j Hj))
      else relax m a a' L1 (j + 1) y v A (Acc_inv H (dec_step L1 j Hj))
  | right _ => A
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma classes_eq : forall m a a' d L c A H,
  classes m a a' d L c A H =
  match bdec (c <? d) with
  | left Hc =>
      let p := scan A m a' L 0 c c (Zwf_well_founded 0 (gap L 0)) in
      let v := A.[p] in
      classes m a a' d L (c + 1)
        (if v =? inf then A
         else relax m a a' (L - 1) 0 p v A (Zwf_well_founded 0 (gap (L - 1) 0)))
        (Acc_inv H (dec_step d c Hc))
  | right _ => A
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma items_eq : forall g n m i A H,
  items g n m i A H =
  match bdec (i <? n) with
  | left Hi => items g n m (i + 1) (item m g.[i] A) (Acc_inv H (dec_step n i Hi))
  | right _ => A
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Number theory of the cycles of +a modulo M                          *)
(* ------------------------------------------------------------------ *)

Section Cycles.
  Open Scope Z_scope.
  Variables (M a : Z).
  Hypothesis HM : 0 < M.
  Hypothesis Ha : 0 <= a.

  Let D := Z.gcd M a.
  Let L := M / D.

  Lemma D_pos : 0 < D.
  Proof.
    unfold D. pose proof (Z.gcd_nonneg M a).
    destruct (Z.eq_dec (Z.gcd M a) 0) as [E|E]; [|lia].
    apply Z.gcd_eq_0_l in E. lia.
  Qed.

  Lemma DL : M = D * L.
  Proof.
    unfold L. pose proof D_pos. destruct (Z.gcd_divide_l M a) as [q Hq].
    fold D in Hq. rewrite Hq at 2. rewrite Z.div_mul by lia. lia.
  Qed.

  Lemma L_pos : 0 < L.
  Proof. pose proof DL. pose proof D_pos. nia. Qed.

  Lemma L_le : L <= M.
  Proof. pose proof DL. pose proof D_pos. pose proof L_pos. nia. Qed.

  Lemma a_split : a = D * (a / D).
  Proof.
    pose proof D_pos. destruct (Z.gcd_divide_r M a) as [q Hq].
    fold D in Hq. rewrite Hq at 2. rewrite Z.div_mul by lia. lia.
  Qed.

  Lemma coprime : Z.gcd L (a / D) = 1.
  Proof. unfold L, D. apply Z.gcd_div_gcd; [pose proof D_pos; unfold D in *; lia | reflexivity]. Qed.

  Lemma cyc_wrap : forall p, (p + L * a) mod M = p mod M.
  Proof.
    intros p. rewrite a_split.
    replace (L * (D * (a / D))) with ((a / D) * M) by (rewrite DL; ring).
    apply Z.mod_add. lia.
  Qed.

  Lemma cyc_inj : forall p j j', 0 <= j < L -> 0 <= j' < L ->
    (p + j * a) mod M = (p + j' * a) mod M -> j = j'.
  Proof.
    intros p j j' Hj Hj' E.
    assert (Hdiv : (M | (j - j') * a)).
    { apply Z.mod_divide; [lia|].
      replace ((j - j') * a) with ((p + j * a) - (p + j' * a)) by ring.
      rewrite Zminus_mod, E, Z.sub_diag. reflexivity. }
    rewrite DL, a_split in Hdiv.
    replace ((j - j') * (D * (a / D))) with (D * ((a / D) * (j - j'))) in Hdiv by ring.
    apply Z.mul_divide_cancel_l in Hdiv; [|pose proof D_pos; lia].
    apply Z.gauss in Hdiv; [|exact coprime].
    destruct Hdiv as [w Hw]. pose proof L_pos.
    destruct (Z.lt_total w 0) as [Hw0|[Hw0|Hw0]]; [nia| |nia]. subst w. lia.
  Qed.

  Lemma cyc_class : forall p j, ((p + j * a) mod M) mod D = p mod D.
  Proof.
    intros p j. pose proof D_pos. pose proof L_pos.
    rewrite Z.mod_mod_divide by (exists L; rewrite DL; ring).
    rewrite a_split. replace (j * (D * (a / D))) with ((j * (a / D)) * D) by ring.
    apply Z.mod_add. lia.
  Qed.

  Lemma cyc_cover : forall p q, 0 <= q < M -> q mod D = p mod D ->
    exists j, 0 <= j < L /\ (p + j * a) mod M = q.
  Proof.
    intros p q Hq E. pose proof D_pos. pose proof L_pos.
    assert (Hw : (D | q - p)).
    { apply Z.mod_divide; [lia|]. rewrite Zminus_mod, E, Z.sub_diag. reflexivity. }
    destruct Hw as [w Hw].
    destruct (Z.gcd_bezout (a / D) L 1) as [u [v Huv]].
    { rewrite Z.gcd_comm. exact coprime. }
    exists ((u * w) mod L). split; [apply Z.mod_pos_bound; lia|].
    rewrite (Z.mod_eq (u * w) L) by lia.
    assert (Ea : a = D * (a / D)) by exact a_split.
    set (al := a / D) in *.
    replace (p + (u * w - L * (u * w / L)) * a)
      with (q + (- (w * v) - (u * w / L) * al) * M).
    - rewrite Z.mod_add by lia. apply Z.mod_small. exact Hq.
    - rewrite DL, Ea. assert (q = p + w * D) by lia. subst q.
      assert (Huv' : u * al = 1 - v * L) by lia.
      transitivity (p + w * D * (u * al) - (u * w / L) * al * (D * L));
        [rewrite Huv'; ring | ring].
  Qed.

End Cycles.

Lemma gcd_spec : forall (zm : Z) (u v : int) (H : Acc (Zwf 0) (φ v)), (φ v) = zm ->
  (φ (gcd_loop u v H)) = Z.gcd (φ u) (φ v).
Proof.
  intros zm.
  induction zm as [zm IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u v H Hz. rewrite gcd_loop_eq.
  destruct (bdec (v =? 0)) as [Hv | Hv].
  - rewrite eqb_spec in Hv. subst v. change (φ 0) with 0%Z. rewrite Z.gcd_0_r.
    symmetry. apply Z.abs_eq. pose proof (to_Z_bounded u). lia.
  - rewrite (IH (φ (u mod v))); [| rewrite <- Hz; apply gcd_dec; exact Hv | reflexivity].
    assert ((φ v) <> 0%Z).
    { rewrite eqb_false_spec in Hv. intro E. apply Hv. apply to_Z_inj. exact E. }
    rewrite mod_spec, (Z.gcd_comm (φ v)), Z.gcd_mod, Z.gcd_comm by exact H0.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Tables as functions of Z                                            *)
(* ------------------------------------------------------------------ *)

Definition INF : Z := 9223372036854775807%Z.

(* Cell z of A, as a Z. *)
Definition W (A : array int) (z : Z) : Z := (φ (A.[of_Z z])).

Lemma phi_inf : (φ inf) = INF.
Proof. reflexivity. Qed.

Lemma W_bound : forall A z, (0 <= W A z <= INF)%Z.
Proof.
  intros A z. unfold W, INF. pose proof (to_Z_bounded (A.[of_Z z])) as H.
  lia.
Qed.

Lemma W_get : forall A x, (φ (A.[x])) = W A (φ x).
Proof. intros A x. unfold W. rewrite of_to_Z. reflexivity. Qed.

Lemma phi_of_Z : forall z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z H. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

Lemma W_set_same : forall A x v, ((φ x) < (φ (PArray.length A)))%Z ->
  W (A.[x <- v]) (φ x) = (φ v).
Proof.
  intros A x v H. rewrite <- W_get. rewrite aget_set_same; [reflexivity|].
  rewrite ltb_spec. exact H.
Qed.

Lemma W_set_other : forall A x v z, (0 <= z < wB)%Z -> z <> (φ x) ->
  W (A.[x <- v]) z = W A z.
Proof.
  intros A x v z Hz Hn. unfold W. rewrite aget_set_other; [reflexivity|].
  intro E. apply Hn. rewrite E, phi_of_Z by exact Hz. reflexivity.
Qed.

Lemma nxt_spec : forall m a a' x, (0 < (φ m) <= 4194303)%Z -> ((φ x) < (φ m))%Z ->
  (φ a') = ((φ a) mod (φ m))%Z ->
  (φ (nxt m a' x)) = (((φ x) + (φ a)) mod (φ m))%Z.
Proof.
  intros m a a' x Hm Hx Ha'. unfold nxt.
  pose proof (Z.mod_pos_bound (φ a) (φ m) ltac:(lia)).
  pose proof (to_Z_bounded x).
  assert (Hy : (φ (x + a')) = ((φ x) + (φ a'))%Z)
    by (rewrite add_spec; apply Z.mod_small; rewrite wB_val; lia).
  rewrite <- Zplus_mod_idemp_r, <- Ha'.
  destruct (x + a' <? m) eqn:E.
  - rewrite ltb_spec in E. rewrite Hy in *. rewrite Z.mod_small; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. rewrite Hy in E.
    rewrite sub_spec, Hy. rewrite Z.mod_small by (rewrite wB_val; lia).
    apply (Z.mod_unique _ _ 1); lia.
Qed.

Lemma pos_succ : forall M a p j, (0 < M)%Z ->
  (((p + j * a) mod M + a) mod M = (p + (j + 1) * a) mod M)%Z.
Proof.
  intros M a p j HM. rewrite Zplus_mod_idemp_l. f_equal. ring.
Qed.

(* v, the value of a cell z, is a cell s of E0 plus t items of size Aa,
   t <= tb, landing in class z. *)
Definition form (E0 : array int) (M Aa v z tb : Z) : Prop :=
  exists s t, (0 <= s < M /\ 0 <= t <= tb /\ W E0 s < INF /\
               v = W E0 s + t * Aa /\ (s + t * Aa) mod M = z)%Z.

Lemma form_mono : forall E0 M Aa v z tb tb',
  form E0 M Aa v z tb -> (tb <= tb')%Z -> form E0 M Aa v z tb'.
Proof.
  intros E0 M Aa v z tb tb' (s & t & H1 & H2 & H3 & H4 & H5) Hle.
  exists s, t. repeat split; try lia; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* One item: closing the table under +a                               *)
(* ------------------------------------------------------------------ *)

Section Item.
  Variables (m a : int) (E0 : array int) (B : Z).
  Let M := (φ m).
  Let Aa := (φ a).
  Hypothesis Hm : (1 <= M <= 4194303)%Z.
  Hypothesis Hlen : PArray.length E0 = m.
  Hypothesis HB : (0 <= B /\ B + M * Aa < 4611686018427387904)%Z.
  Hypothesis HE0 : forall z, (0 <= z < M)%Z -> (W E0 z < INF)%Z -> (W E0 z <= B)%Z.
  Let D := Z.gcd M Aa.
  Let Lz := (M / D)%Z.

  Lemma HM0 : (0 < M)%Z.
  Proof. lia. Qed.
  Lemma Ha0 : (0 <= Aa)%Z.
  Proof. unfold Aa. pose proof (to_Z_bounded a). lia. Qed.

  Lemma inM : forall z, (0 <= z < M)%Z -> (0 <= z < wB)%Z.
  Proof. intros z H. rewrite wB_val. lia. Qed.

  Lemma D_pos' : (0 < D)%Z.
  Proof. intros; eapply D_pos; eauto using HM0, Ha0. Qed.
  Lemma DL' : M = (D * Lz)%Z.
  Proof. intros; eapply DL; eauto using HM0, Ha0. Qed.
  Lemma L_pos' : (0 < Lz)%Z.
  Proof. intros; eapply L_pos; eauto using HM0, Ha0. Qed.
  Lemma L_le' : (Lz <= M)%Z.
  Proof. intros; eapply L_le; eauto using HM0, Ha0. Qed.
  Lemma D_le' : (D <= M)%Z.
  Proof. pose proof DL'. pose proof D_pos'. pose proof L_pos'. nia. Qed.

  Lemma inj' : forall p j j', (0 <= j < Lz)%Z -> (0 <= j' < Lz)%Z ->
    ((p + j * Aa) mod M = (p + j' * Aa) mod M)%Z -> j = j'.
  Proof. intros; eapply cyc_inj; eauto using HM0, Ha0. Qed.

  Lemma class' : forall p j, (((p + j * Aa) mod M) mod D = p mod D)%Z.
  Proof. intros; eapply cyc_class; eauto using HM0, Ha0. Qed.

  Lemma cover' : forall p q, (0 <= q < M)%Z -> (q mod D = p mod D)%Z ->
    exists j, (0 <= j < Lz)%Z /\ ((p + j * Aa) mod M = q)%Z.
  Proof. intros; eapply cyc_cover; eauto using HM0, Ha0. Qed.

  Lemma wrap' : forall p, ((p + Lz * Aa) mod M = p mod M)%Z.
  Proof. intros; eapply cyc_wrap; eauto using HM0, Ha0. Qed.

  Lemma form_bound : forall v z tb, form E0 M Aa v z tb -> (v <= B + tb * Aa)%Z.
  Proof.
    intros v z tb (s & t & H1 & H2 & H3 & H4 & H5).
    pose proof (HE0 s H1 H3). pose proof Ha0. nia.
  Qed.

  Lemma relax_spec : forall (As : array int) (p : Z) (L1 a' : int),
    PArray.length As = m ->
    (φ a') = (Aa mod M)%Z ->
    (φ L1) = (Lz - 1)%Z ->
    (0 <= p < M)%Z ->
    (forall z, (0 <= z < M)%Z -> (z mod D = p mod D)%Z -> W As z = W E0 z) ->
    (forall z, (0 <= z < M)%Z -> (z mod D = p mod D)%Z -> W As p <= W As z)%Z ->
    (forall z, (0 <= z < M)%Z -> (W As z < INF)%Z -> form E0 M Aa (W As z) z (Lz - 1)) ->
    forall (zm : Z) (j x cur : int) (A : array int) (H : Acc (Zwf 0) (gap L1 j)),
    gap L1 j = zm ->
    PArray.length A = m ->
    (0 <= (φ j) <= Lz - 1)%Z ->
    (φ x) = ((p + (φ j) * Aa) mod M)%Z ->
    (φ cur) = W A (φ x) ->
    (forall z, (0 <= z < M)%Z -> W A z <= W As z)%Z ->
    (forall z, (0 <= z < M)%Z ->
       (forall j', (1 <= j' <= (φ j))%Z -> z <> ((p + j' * Aa) mod M)%Z) ->
       W A z = W As z) ->
    form E0 M Aa (φ cur) (φ x) (φ j) ->
    (forall z, (0 <= z < M)%Z -> (W A z < INF)%Z -> form E0 M Aa (W A z) z (Lz - 1)) ->
    (forall j', (0 <= j' < (φ j))%Z ->
       W A ((p + (j' + 1) * Aa) mod M) <= W A ((p + j' * Aa) mod M) + Aa)%Z ->
    (W As p <= (φ cur))%Z ->
    let R := relax m a a' L1 j x cur A H in
    PArray.length R = m /\
    (forall z, (0 <= z < M)%Z -> W R z <= W As z)%Z /\
    (forall z, (0 <= z < M)%Z -> (z mod D <> p mod D)%Z -> W R z = W As z) /\
    (forall z, (0 <= z < M)%Z -> (W R z < INF)%Z -> form E0 M Aa (W R z) z (Lz - 1)) /\
    (forall z, (0 <= z < M)%Z -> (z mod D = p mod D)%Z ->
       W R ((z + Aa) mod M) <= W R z + Aa)%Z.
  Proof.
    intros As p L1 a' HAs Ha' HL1 Hp HAsE Hmin HAsF zm.
    clearbody Lz D.
    pose proof HM0 as HM0. pose proof Ha0 as Ha0. pose proof L_pos' as HLp.
    pose proof L_le' as HLle.
    induction zm as [zm IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros j x cur A H Hz HA Hj Hx Hcur HAle HAun Hcf HAf Hcl Hcmin.
    rewrite relax_eq.
    destruct (bdec (j <? L1)) as [Hj1 | Hj1].
    - cbv zeta.
      pose proof Hj1 as Hj1'. rewrite ltb_spec, HL1 in Hj1'.
      assert (HJ : (φ (j + 1)) = ((φ j) + 1)%Z) by (rewrite add_spec; apply Z.mod_small;
        change (φ 1) with 1%Z; rewrite wB_val; lia).
      assert (Hxb : (0 <= (φ x) < M)%Z) by (rewrite Hx; apply Z.mod_pos_bound; lia).
      assert (Hy' : (φ (nxt m a' x)) = (((φ x) + Aa) mod M)%Z)
        by (apply nxt_spec; unfold M, Aa in *; lia).
      assert (Hy : (φ (nxt m a' x)) = ((p + ((φ j) + 1) * Aa) mod M)%Z)
        by (rewrite Hy', Hx; apply pos_succ; lia).
      set (y := nxt m a' x) in *.
      assert (Hyb : (0 <= (φ y) < M)%Z) by (rewrite Hy; apply Z.mod_pos_bound; lia).
      assert (Hyun : W A (φ y) = W As (φ y)).
      { apply HAun; [exact Hyb|]. intros j' Hj' E. rewrite Hy in E.
        apply inj' in E; lia. }
      assert (Hycl : ((φ y) mod D = p mod D)%Z) by (rewrite Hy; apply class').
      assert (HyE : W As (φ y) = W E0 (φ y)) by (apply HAsE; assumption).
      pose proof (form_bound _ _ _ Hcf) as Hcb.
      assert (Hjb : (((φ j) + 1) * Aa <= M * Aa)%Z) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (Hab : (Aa <= M * Aa)%Z)
        by (rewrite <- (Z.mul_1_l Aa) at 1; apply Z.mul_le_mono_nonneg_r; lia).
      assert (Hcb' : ((φ cur) + Aa < 4611686018427387904)%Z) by lia.
      assert (Hc : (φ (cur + a)) = ((φ cur) + Aa)%Z).
      { rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded cur).
        rewrite wB_val. unfold Aa in *. lia. }
      assert (Hxy : (φ x) <> (φ y)).
      { rewrite Hx, Hy. intro E. apply inj' in E; lia. }
      assert (HyA : ((φ y) < (φ (PArray.length A)))%Z) by (rewrite HA; exact (proj2 Hyb)).
      destruct (cur + a <? A.[y]) eqn:Ec.
      + rewrite ltb_spec, Hc, W_get in Ec.
        assert (Hcf' : form E0 M Aa (φ (cur + a)) (φ y) ((φ j) + 1)).
        { destruct Hcf as (s & t & H1 & H2 & H3 & H4 & H5).
          exists s, (t + 1)%Z.
          refine (conj H1 (conj _ (conj H3 (conj _ _)))).
          - lia.
          - rewrite Hc, H4. ring.
          - rewrite Hy', <- H5, Zplus_mod_idemp_l. f_equal. ring. }
        eapply IH; [rewrite <- Hz; apply dec_step; exact Hj1 | reflexivity | | | | | | | | | | ].
        * rewrite alength_set. exact HA.
        * lia.
        * rewrite HJ. exact Hy.
        * rewrite W_set_same by exact HyA. reflexivity.
        * intros z Hz'. destruct (Z.eq_dec z (φ y)) as [E|E].
          -- subst z. rewrite W_set_same by exact HyA. lia.
          -- rewrite W_set_other by (first [exact E | apply inM; exact Hz']). apply HAle. exact Hz'.
        * intros z Hz' Hn. rewrite W_set_other.
          -- apply HAun; [exact Hz'|]. intros j' Hj'. apply Hn. lia.
          -- apply inM; exact Hz'.
          -- rewrite Hy. apply Hn. lia.
        * rewrite HJ. exact Hcf'.
        * intros z Hz' Hinf. destruct (Z.eq_dec z (φ y)) as [E|E].
          -- subst z. rewrite W_set_same by exact HyA. eapply form_mono; [exact Hcf'|lia].
          -- rewrite W_set_other in * by (first [exact E | apply inM; exact Hz']). apply HAf; assumption.
        * intros j' Hj'. rewrite HJ in Hj'.
          destruct (Z.eq_dec j' (φ j)) as [E|E].
          -- subst j'. rewrite <- Hy, <- Hx. rewrite W_set_same by exact HyA.
             rewrite W_set_other by (first [exact Hxy | apply inM; exact Hxb]).
             rewrite <- Hcur. lia.
          -- assert (Hj'' : (0 <= j' < (φ j))%Z) by lia. clear E Hxy.
             assert (N1 : ((p + (j' + 1) * Aa) mod M)%Z <> (φ y)).
             { rewrite Hy. intro F. apply inj' in F; lia. }
             assert (N2 : ((p + j' * Aa) mod M)%Z <> (φ y)).
             { rewrite Hy. intro F. apply inj' in F; lia. }
             assert (B1 := Z.mod_pos_bound (p + (j' + 1) * Aa) M HM0).
             assert (B2 := Z.mod_pos_bound (p + j' * Aa) M HM0).
             rewrite !W_set_other by (first [assumption | apply inM; assumption]).
             apply Hcl. lia.
        * lia.
      + rewrite <- Bool.not_true_iff_false, ltb_spec, Hc, W_get in Ec.
        eapply IH; [rewrite <- Hz; apply dec_step; exact Hj1 | reflexivity | | | | | | | | | | ].
        * exact HA.
        * lia.
        * rewrite HJ. exact Hy.
        * apply W_get.
        * exact HAle.
        * intros z Hz' Hn. apply HAun; [exact Hz'|]. intros j' Hj'. apply Hn. lia.
        * rewrite HJ, W_get. exists (φ y), 0%Z.
          pose proof (W_bound A (φ y)).
          refine (conj Hyb (conj _ (conj _ (conj _ _)))).
          -- lia.
          -- rewrite <- HyE, <- Hyun. unfold INF in *. lia.
          -- rewrite <- HyE, <- Hyun. ring.
          -- rewrite Z.mul_0_l, Z.add_0_r. apply Z.mod_small. exact Hyb.
        * exact HAf.
        * intros j' Hj'. rewrite HJ in Hj'.
          destruct (Z.eq_dec j' (φ j)) as [E|E].
          -- subst j'. rewrite <- Hy, <- Hx. rewrite <- Hcur. lia.
          -- apply Hcl. lia.
        * rewrite W_get, Hyun. apply Hmin; assumption.
    - rewrite <- Bool.not_true_iff_false, ltb_spec, HL1 in Hj1.
      assert (Hjl : (φ j) = (Lz - 1)%Z) by lia.
      split; [exact HA|]. split; [exact HAle|]. split.
      { intros z Hz' Hn. apply HAun; [exact Hz'|]. intros j' Hj' E.
        apply Hn. rewrite E. apply class'. }
      split; [exact HAf|].
      intros z Hz' Hzc.
      destruct (cover' p z Hz' Hzc) as (j0 & Hj0 & Ej0).
      rewrite <- Ej0, pos_succ by lia.
      destruct (Z.eq_dec j0 (Lz - 1)) as [E|E].
      + subst j0. replace (Lz - 1 + 1)%Z with Lz by lia.
        rewrite wrap', (Z.mod_small p) by lia.
        assert (HAp : W A p = W As p).
        { apply HAun; [lia|]. intros j' Hj' F.
          assert (F' : ((p + 0 * Aa) mod M = (p + j' * Aa) mod M)%Z)
            by (rewrite Z.mul_0_l, Z.add_0_r, Z.mod_small by lia; exact F).
          apply inj' in F'; lia. }
        rewrite HAp, <- Hjl, <- Hx, <- Hcur. lia.
      + apply Hcl. lia.
  Qed.

  Lemma scan_spec : forall (A : array int) (a' L : int) (c : Z),
    PArray.length A = m -> (φ a') = (Aa mod M)%Z -> (φ L) = Lz -> (0 <= c < M)%Z ->
    forall (zm : Z) (j x p : int) (H : Acc (Zwf 0) (gap L j)),
    gap L j = zm ->
    (0 <= (φ j) <= Lz)%Z ->
    (φ x) = ((c + (φ j) * Aa) mod M)%Z ->
    (0 <= (φ p) < M)%Z -> ((φ p) mod D = c mod D)%Z ->
    (forall j', (0 <= j' < (φ j))%Z -> W A (φ p) <= W A ((c + j' * Aa) mod M))%Z ->
    let r := scan A m a' L j x p H in
    (0 <= (φ r) < M)%Z /\ ((φ r) mod D = c mod D)%Z /\
    (forall z, (0 <= z < M)%Z -> (z mod D = c mod D)%Z -> W A (φ r) <= W A z)%Z.
  Proof.
    intros A a' L c HA Ha' HL Hc zm.
    clearbody Lz D.
    pose proof HM0 as HM0. pose proof Ha0 as Ha0.
    induction zm as [zm IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros j x p H Hz Hj Hx Hp Hpc Hmin.
    rewrite scan_eq.
    destruct (bdec (j <? L)) as [Hj1 | Hj1].
    - pose proof Hj1 as Hj1'. rewrite ltb_spec, HL in Hj1'.
      assert (HJ : (φ (j + 1)) = ((φ j) + 1)%Z) by (rewrite add_spec; apply Z.mod_small;
        change (φ 1) with 1%Z; rewrite wB_val; lia).
      assert (Hxb : (0 <= (φ x) < M)%Z) by (rewrite Hx; apply Z.mod_pos_bound; lia).
      assert (Hxc : ((φ x) mod D = c mod D)%Z) by (rewrite Hx; apply class').
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hj1 | reflexivity | | | | | ].
      + lia.
      + rewrite HJ, (nxt_spec m a a' x) by (unfold M, Aa in *; lia). rewrite Hx. apply pos_succ. lia.
      + destruct (A.[x] <? A.[p]); assumption.
      + destruct (A.[x] <? A.[p]); assumption.
      + intros j' Hj'. rewrite HJ in Hj'.
        destruct (A.[x] <? A.[p]) eqn:E.
        * rewrite ltb_spec, !W_get in E.
          destruct (Z.eq_dec j' (φ j)) as [F|F].
          -- subst j'. rewrite <- Hx. lia.
          -- pose proof (Hmin j' ltac:(lia)). lia.
        * rewrite <- Bool.not_true_iff_false, ltb_spec, !W_get in E.
          destruct (Z.eq_dec j' (φ j)) as [F|F].
          -- subst j'. rewrite <- Hx. lia.
          -- apply Hmin. lia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec, HL in Hj1.
      split; [exact Hp|]. split; [exact Hpc|].
      intros z Hz' Hzc.
      destruct (cover' c z Hz' Hzc) as (j0 & Hj0 & Ej0).
      rewrite <- Ej0. apply Hmin. lia.
  Qed.

  Lemma classes_spec : forall (a' d L : int),
    (φ a') = (Aa mod M)%Z -> (φ d) = D -> (φ L) = Lz ->
    forall (zm : Z) (c : int) (A : array int) (H : Acc (Zwf 0) (gap d c)),
    gap d c = zm ->
    (0 <= (φ c) <= D)%Z ->
    PArray.length A = m ->
    (forall z, (0 <= z < M)%Z -> W A z <= W E0 z)%Z ->
    (forall z, (0 <= z < M)%Z -> (W A z < INF)%Z -> form E0 M Aa (W A z) z (Lz - 1)) ->
    (forall z, (0 <= z < M)%Z -> ((φ c) <= z mod D)%Z -> W A z = W E0 z) ->
    (forall z, (0 <= z < M)%Z -> (z mod D < (φ c))%Z ->
       W A ((z + Aa) mod M) <= W A z + Aa)%Z ->
    let R := classes m a a' d L c A H in
    PArray.length R = m /\
    (forall z, (0 <= z < M)%Z -> W R z <= W E0 z)%Z /\
    (forall z, (0 <= z < M)%Z -> (W R z < INF)%Z -> form E0 M Aa (W R z) z (Lz - 1)) /\
    (forall z, (0 <= z < M)%Z -> W R ((z + Aa) mod M) <= W R z + Aa)%Z.
  Proof.
    intros a' d L Ha' Hd HL zm.
    pose proof D_le' as HDle. pose proof D_pos' as HDp. pose proof L_pos' as HLp.
    clearbody Lz D.
    pose proof HM0 as HM0. pose proof Ha0 as Ha0.
    induction zm as [zm IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros c A H Hz Hc HA HAle HAf HAu HAcl.
    rewrite classes_eq.
    destruct (bdec (c <? d)) as [Hc1 | Hc1].
    - cbv zeta.
      pose proof Hc1 as Hc1'. rewrite ltb_spec, Hd in Hc1'.
      assert (HC : (φ (c + 1)) = ((φ c) + 1)%Z) by (rewrite add_spec; apply Z.mod_small;
        change (φ 1) with 1%Z; rewrite wB_val; lia).
      assert (Hcm : ((φ c) mod D = (φ c))%Z) by (apply Z.mod_small; lia).
      destruct (scan_spec A a' L (φ c) HA Ha' HL ltac:(lia) _ 0 c c
                  (Zwf_well_founded 0 (gap L 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; lia)
                  ltac:(change (φ 0) with 0%Z; rewrite Z.mul_0_l, Z.add_0_r, Z.mod_small; lia)
                  ltac:(lia) eq_refl
                  ltac:(intros j' Hj'; change (φ 0) with 0%Z in Hj'; lia))
        as (Hpb & Hpc & Hpmin).
      set (p := scan A m a' L 0 c c (Zwf_well_founded 0 (gap L 0))) in *.
      rewrite Hcm in Hpc.
      assert (HpE : W A (φ p) = W E0 (φ p)) by (apply HAu; lia).
      destruct (A.[p] =? inf) eqn:Ev.
      + rewrite eqb_spec in Ev.
        assert (HpI : W A (φ p) = INF) by (rewrite <- W_get, Ev; reflexivity).
        eapply IH; [rewrite <- Hz; apply dec_step; exact Hc1 | reflexivity | | | | | | ].
        * lia.
        * exact HA.
        * exact HAle.
        * exact HAf.
        * intros z Hz' Hzc. apply HAu; lia.
        * intros z Hz' Hzc. destruct (Z.eq_dec (z mod D) (φ c)) as [E|E].
          -- pose proof (Hpmin z Hz' ltac:(lia)). pose proof (W_bound A z).
             pose proof (W_bound A ((z + Aa) mod M)). lia.
          -- apply HAcl; lia.
      + rewrite eqb_false_spec in Ev.
        assert (HpI : (W A (φ p) < INF)%Z).
        { pose proof (W_bound A (φ p)). rewrite <- W_get in *.
          assert ((φ (A.[p])) <> INF); [|lia].
          intro F. apply Ev. apply to_Z_inj. rewrite F. reflexivity. }
        assert (HL1 : (φ (L - 1)) = (Lz - 1)%Z).
        { pose proof (to_Z_bounded L). rewrite sub_spec, HL. change (φ 1) with 1%Z.
          apply Z.mod_small. rewrite wB_val. rewrite HL in *. lia. }
        destruct (relax_spec A (φ p) (L - 1) a' HA Ha' HL1 Hpb
                    ltac:(intros z Hz' Hzc; apply HAu; lia)
                    ltac:(intros z Hz' Hzc; apply Hpmin; lia)
                    HAf _ 0 p A.[p] A (Zwf_well_founded 0 (gap (L - 1) 0)) eq_refl HA
                    ltac:(change (φ 0) with 0%Z; lia)
                    ltac:(change (φ 0) with 0%Z; rewrite Z.mul_0_l, Z.add_0_r, Z.mod_small; lia)
                    (W_get A p)
                    ltac:(intros; lia)
                    ltac:(intros; reflexivity))
          as (R1 & R2 & R3 & R4 & R5).
        { change (φ 0) with 0%Z. exists (φ p), 0%Z.
          refine (conj Hpb (conj _ (conj _ (conj _ _)))).
          - lia.
          - rewrite <- HpE. exact HpI.
          - rewrite W_get, HpE. ring.
          - rewrite Z.mul_0_l, Z.add_0_r. apply Z.mod_small. exact Hpb. }
        { exact HAf. }
        { intros j' Hj'. change (φ 0) with 0%Z in Hj'. lia. }
        { rewrite W_get. lia. }
        eapply IH; [rewrite <- Hz; apply dec_step; exact Hc1 | reflexivity | | | | | | ].
        * lia.
        * exact R1.
        * intros z Hz'. pose proof (R2 z Hz'). pose proof (HAle z Hz'). lia.
        * exact R4.
        * intros z Hz' Hzc. rewrite R3 by (try exact Hz'; lia). apply HAu; lia.
        * intros z Hz' Hzc. destruct (Z.eq_dec (z mod D) (φ c)) as [E|E].
          -- apply R5; lia.
          -- assert (Ht := Z.mod_pos_bound (z + Aa) M HM0).
             assert (Htc : (((z + Aa) mod M) mod D = z mod D)%Z).
             { rewrite <- (class' z 1). f_equal. f_equal. ring. }
             rewrite !R3 by (try lia). apply HAcl; lia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec, Hd in Hc1.
      split; [exact HA|]. split; [exact HAle|]. split; [exact HAf|].
      intros z Hz'. apply HAcl; [exact Hz'|].
      pose proof (Z.mod_pos_bound z D HDp). lia.
  Qed.

  Lemma item_spec :
    let R := item m a E0 in
    PArray.length R = m /\
    (forall z, (0 <= z < M)%Z -> W R z <= W E0 z)%Z /\
    (forall z, (0 <= z < M)%Z -> (W R z < INF)%Z -> form E0 M Aa (W R z) z (M - 1)) /\
    (forall z, (0 <= z < M)%Z -> W R ((z + Aa) mod M) <= W R z + Aa)%Z.
  Proof.
    pose proof HM0 as HM0. pose proof Ha0 as Ha0. pose proof L_le' as HLle.
    pose proof D_pos' as HDp. pose proof L_pos' as HLp.
    unfold item.
    assert (Ha' : (φ (a mod m)) = (Aa mod M)%Z) by (rewrite mod_spec; reflexivity).
    assert (Hd : (φ (gcd_loop m (a mod m) (Zwf_well_founded 0 (φ (a mod m))))) = D).
    { rewrite (gcd_spec _ m (a mod m) _ eq_refl), Ha'. unfold D. rewrite Z.gcd_comm, Z.gcd_mod by lia.
      reflexivity. }
    set (d := gcd_loop m (a mod m) (Zwf_well_founded 0 (φ (a mod m)))) in *.
    assert (HL : (φ (m / d)) = Lz) by (rewrite div_spec, Hd; reflexivity).
    clearbody Lz D.
    assert (C1 : (0 <= (φ 0) <= D)%Z) by (change (φ 0) with 0%Z; lia).
    assert (C2 : forall z, (0 <= z < M)%Z -> (W E0 z <= W E0 z)%Z) by (intros; lia).
    assert (C3 : forall z, (0 <= z < M)%Z -> (W E0 z < INF)%Z ->
                 form E0 M Aa (W E0 z) z (Lz - 1)).
    { intros z Hz Hinf. exists z, 0%Z.
      refine (conj Hz (conj _ (conj Hinf (conj _ _)))).
      - lia.
      - ring.
      - rewrite Z.mul_0_l, Z.add_0_r. apply Z.mod_small. exact Hz. }
    assert (C4 : forall z, (0 <= z < M)%Z -> ((φ 0) <= z mod D)%Z -> W E0 z = W E0 z)
      by reflexivity.
    assert (C5 : forall z, (0 <= z < M)%Z -> (z mod D < (φ 0))%Z ->
                 (W E0 ((z + Aa) mod M) <= W E0 z + Aa)%Z).
    { intros z Hz Hzc. change (φ 0) with 0%Z in Hzc.
      pose proof (Z.mod_pos_bound z D HDp). lia. }
    destruct (classes_spec (a mod m) d (m / d) Ha' Hd HL _ 0 E0
                (Zwf_well_founded 0 (gap d 0)) eq_refl C1 Hlen C2 C3 C4 C5)
      as (R1 & R2 & R3 & R4).
    split; [exact R1|]. split; [exact R2|]. split; [|exact R4].
    intros z Hz Hinf. eapply form_mono; [apply R3; assumption | lia].
  Qed.

End Item.

(* ------------------------------------------------------------------ *)
(* Closure under one item survives closing under another              *)
(* ------------------------------------------------------------------ *)

Lemma closed_iter : forall (R : array int) (M Aa : Z), (0 < M)%Z -> (0 <= Aa)%Z ->
  (forall z, (0 <= z < M)%Z -> W R ((z + Aa) mod M) <= W R z + Aa)%Z ->
  forall t, (0 <= t)%Z -> forall z, (0 <= z < M)%Z ->
  (W R ((z + t * Aa) mod M) <= W R z + t * Aa)%Z.
Proof.
  intros R M Aa HM Ha Hcl t Ht.
  pattern t. apply natlike_ind; [| | exact Ht].
  - intros z Hz. rewrite Z.mul_0_l, Z.add_0_r, Z.mod_small by exact Hz. lia.
  - intros t' Ht' IH z Hz.
    replace (z + Z.succ t' * Aa)%Z with ((z + t' * Aa) + Aa)%Z by ring.
    rewrite <- Zplus_mod_idemp_l.
    assert (Hb := Z.mod_pos_bound (z + t' * Aa) M HM).
    pose proof (Hcl _ Hb). pose proof (IH z Hz). lia.
Qed.

Lemma closed_preserve : forall (E R : array int) (M Aa b tb : Z),
  (0 < M)%Z -> (0 <= Aa)%Z -> (0 <= b)%Z ->
  (forall z, (0 <= z < M)%Z -> W R z <= W E z)%Z ->
  (forall z, (0 <= z < M)%Z -> (W R z < INF)%Z -> form E M Aa (W R z) z tb) ->
  (forall z, (0 <= z < M)%Z -> W R ((z + Aa) mod M) <= W R z + Aa)%Z ->
  (forall z, (0 <= z < M)%Z -> W E ((z + b) mod M) <= W E z + b)%Z ->
  forall z, (0 <= z < M)%Z -> (W R ((z + b) mod M) <= W R z + b)%Z.
Proof.
  intros E R M Aa b tb HM Ha Hb Hle Hf Hcl HEb z Hz.
  destruct (Z_lt_le_dec (W R z) INF) as [Hi|Hi].
  - destruct (Hf z Hz Hi) as (s & t & H1 & H2 & H3 & H4 & H5).
    set (s' := ((s + b) mod M)%Z).
    assert (Hs' : (0 <= s' < M)%Z) by (apply Z.mod_pos_bound; exact HM).
    assert (Eq : ((s' + t * Aa) mod M = (z + b) mod M)%Z).
    { unfold s'. rewrite <- H5. rewrite !Zplus_mod_idemp_l. f_equal. ring. }
    pose proof (closed_iter R M Aa HM Ha Hcl t ltac:(lia) s' Hs') as C.
    rewrite Eq in C.
    pose proof (Hle s' Hs'). pose proof (HEb s H1). unfold s' in *. lia.
  - pose proof (W_bound R z). pose proof (W_bound R ((z + b) mod M)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Fillings                                                            *)
(* ------------------------------------------------------------------ *)

Lemma ef_zero : forall gl, exact_filling gl 0.
Proof. intros gl. exists []. split; [constructor | reflexivity]. Qed.

Lemma ef_add : forall gl s i, exact_filling gl s -> (i < len gl)%N ->
  exact_filling gl (get_list_N gl i + s).
Proof.
  intros gl s i (l & Hb & Ht) Hi. exists (i :: l). split.
  - constructor; assumption.
  - simpl. rewrite Ht. reflexivity.
Qed.

Lemma ef_addt : forall gl s i (t : nat), exact_filling gl s -> (i < len gl)%N ->
  exact_filling gl (N.of_nat t * get_list_N gl i + s).
Proof.
  intros gl s i t Hs Hi. induction t as [|t IH].
  - exact Hs.
  - replace (N.of_nat (S t) * get_list_N gl i + s)%N
      with (get_list_N gl i + (N.of_nat t * get_list_N gl i + s))%N by lia.
    apply ef_add; assumption.
Qed.

Lemma arith1 : forall i M Aa : Z, (0 <= i <= 20)%Z -> (1 <= M <= 1000)%Z ->
  (0 <= Aa <= 1000)%Z ->
  (0 <= i * M * 1000 /\ i * M * 1000 + M * Aa < 4611686018427387904)%Z.
Proof. intros. nia. Qed.

Lemma arith2 : forall i M Aa w t : Z, (0 <= i)%Z -> (1 <= M)%Z ->
  (0 <= Aa <= 1000)%Z -> (w <= i * M * 1000)%Z -> (0 <= t <= M - 1)%Z ->
  (w + t * Aa <= (i + 1) * M * 1000)%Z.
Proof. intros. nia. Qed.

(* ------------------------------------------------------------------ *)
(* The item loop and the answer                                        *)
(* ------------------------------------------------------------------ *)

Section Global.
  Variables (gl : list N) (g : array int).
  Hypothesis Hg : repr (g : array uint) gl.
  Hypothesis Hn : (1 <= len gl <= 20)%N.
  Hypothesis Hgs : Forall (fun s => (1 <= s <= 1000)%N) gl.

  Lemma g_length : (φ (PArray.length g)) = Z.of_nat (List.length gl).
  Proof. destruct Hg as [Hl _]. symmetry. exact Hl. Qed.

  Lemma g_cell : forall i : int, ((φ i) < (φ (PArray.length g)))%Z ->
    (1 <= (φ (g.[i])) <= 1000)%Z /\
    Z.of_N (get_list_N gl (Z.to_N (φ i))) = (φ (g.[i])).
  Proof.
    intros i Hi. rewrite g_length in Hi.
    destruct Hg as [_ Hc].
    destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (v & Hv & Hr).
    unfold repr, repr_uint in Hr.
    rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
    rewrite of_to_Z in Hr.
    change (Z.to_N (φ (@PArray.get@{Set} int g i)) = v) in Hr.
    assert (Hin : In v gl) by (eapply nth_error_In; exact Hv).
    rewrite Forall_forall in Hgs. pose proof (Hgs v Hin) as Hb.
    assert (Hget : get_list_N gl (Z.to_N (φ i)) = v).
    { unfold get_list_N. rewrite Z_N_nat. apply nth_error_nth. exact Hv. }
    pose proof (to_Z_bounded (@PArray.get@{Set} int g i)).
    assert (Hgi : (φ (@PArray.get@{Set} int g i)) = Z.of_N v).
    { rewrite <- Hr. rewrite Z2N.id; [reflexivity|]. lia. }
    rewrite Hget. split; lia.
  Qed.

  Variable m : int.
  Let M := (φ m).
  Hypothesis Hm : (1 <= M <= 1000)%Z.

  Lemma items_spec : forall (zm : Z) (i : int) (E : array int)
      (H : Acc (Zwf 0) (gap (PArray.length g) i)),
    gap (PArray.length g) i = zm ->
    ((φ i) <= (φ (PArray.length g)))%Z ->
    PArray.length E = m ->
    W E 0 = 0%Z ->
    (forall z, (0 <= z < M)%Z -> (W E z < INF)%Z ->
       exact_filling gl (Z.to_N (W E z)) /\ (W E z mod M = z)%Z) ->
    (forall z, (0 <= z < M)%Z -> (W E z < INF)%Z -> (W E z <= (φ i) * M * 1000)%Z) ->
    (forall i' : int, ((φ i') < (φ i))%Z -> forall z, (0 <= z < M)%Z ->
       (W E ((z + (φ (g.[i']))) mod M) <= W E z + (φ (g.[i'])))%Z) ->
    let R := items g (PArray.length g) m i E H in
    PArray.length R = m /\ W R 0 = 0%Z /\
    (forall z, (0 <= z < M)%Z -> (W R z < INF)%Z ->
       exact_filling gl (Z.to_N (W R z)) /\ (W R z mod M = z)%Z) /\
    (forall i' : int, ((φ i') < (φ (PArray.length g)))%Z -> forall z, (0 <= z < M)%Z ->
       (W R ((z + (φ (g.[i']))) mod M) <= W R z + (φ (g.[i'])))%Z).
  Proof.
    intros zm. unfold M in *.
    induction zm as [zm IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i E H Hz Hi HE HE0 HEs HEb HEc.
    rewrite items_eq.
    destruct (bdec (i <? PArray.length g)) as [Hi1 | Hi1].
    - pose proof Hi1 as Hi1'. rewrite ltb_spec in Hi1'.
      pose proof g_length as Hgl. unfold len in Hn.
      assert (HI : (φ (i + 1)) = ((φ i) + 1)%Z) by (rewrite add_spec; apply Z.mod_small;
        change (φ 1) with 1%Z; rewrite wB_val; lia).
      destruct (g_cell i Hi1') as [Hgb Hgv].
      pose proof (to_Z_bounded i) as Bi.
      destruct (arith1 (φ i) (φ m) (φ (g.[i])) ltac:(lia) Hm ltac:(lia)) as [HB1 HB2].
      destruct (item_spec m (g.[i]) E ((φ i) * (φ m) * 1000) ltac:(lia) HE
                  (conj HB1 HB2) HEb)
        as (R1 & R2 & R3 & R4).
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hi1 | reflexivity | | | | | | ].
      + lia.
      + exact R1.
      + pose proof (R2 0%Z ltac:(lia)). pose proof (W_bound (item m g.[i] E) 0). lia.
      + intros z Hz' Hinf.
        destruct (R3 z Hz' Hinf) as (s & t & H1 & H2 & H3 & H4 & H5).
        destruct (HEs s H1 H3) as [Hf Hmod].
        rewrite H4. split.
        * set (gi := get_list_N gl (Z.to_N (φ i))) in *.
          replace (Z.to_N (W E s + t * (φ (g.[i]))))
            with (N.of_nat (Z.to_nat t) * gi + Z.to_N (W E s))%N.
          -- apply ef_addt; [exact Hf|]. unfold len. lia.
          -- apply N2Z.inj. rewrite N2Z.inj_add, N2Z.inj_mul, Hgv, nat_N_Z, Z2Nat.id by lia.
             assert (P1 : (0 <= W E s)%Z) by (pose proof (W_bound E s); lia).
             assert (P2 : (0 <= W E s + t * (φ (g.[i])))%Z)
               by (apply Z.add_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; lia]).
             rewrite !Z2N.id by assumption. ring.
        * rewrite <- Zplus_mod_idemp_l, Hmod. exact H5.
      + intros z Hz' Hinf. rewrite HI.
        destruct (R3 z Hz' Hinf) as (s & t & H1 & H2 & H3 & H4 & H5).
        rewrite H4. apply arith2; try lia. apply HEb; assumption.
      + intros i' Hi' z Hz'. rewrite HI in Hi'.
        destruct (Z.eq_dec (φ i') (φ i)) as [E1|E1].
        * apply to_Z_inj in E1. subst i'. apply R4. exact Hz'.
        * destruct (g_cell i' ltac:(lia)) as [Hgb' _].
          apply (closed_preserve E (item m g.[i] E) (φ m) (φ (g.[i])) (φ (g.[i'])) ((φ m) - 1));
            [lia | lia | lia | exact R2 | exact R3 | exact R4 | | exact Hz'].
          intros z0 Hz0. apply HEc; [lia | exact Hz0].
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi1.
      split; [exact HE|]. split; [exact HE0|]. split; [exact HEs|].
      intros i' Hi' z Hz'. apply HEc; [lia | exact Hz'].
  Qed.

End Global.

Lemma min_loop_spec : forall (P : int -> Prop) (g : array int) (n : int),
  (forall i, ((φ i) < (φ n))%Z -> P (g.[i])) ->
  forall zm i best H, gap n i = zm -> P best -> P (min_loop g n i best H).
Proof.
  intros P g n HP zm.
  induction zm as [zm IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i best H Hz Hb. rewrite min_loop_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - eapply IH; [rewrite <- Hz; apply dec_step; exact Hi | reflexivity |].
    destruct (g.[i] <? best); [apply HP; rewrite ltb_spec in Hi; exact Hi | exact Hb].
  - exact Hb.
Qed.

Lemma arith3 : forall K w M : Z, (0 < M)%Z -> (w <= K)%Z -> (w mod M = K mod M)%Z ->
  exists q, (0 <= q /\ K = w + q * M)%Z.
Proof.
  intros K w M HM Hle Hmod.
  assert (Hd : (M | K - w)%Z).
  { apply Z.mod_divide; [lia|]. rewrite Zminus_mod, Hmod, Z.sub_diag. reflexivity. }
  destruct Hd as [q Hq]. exists q. split; [|lia].
  destruct (Z_lt_le_dec q 0); [nia | lia].
Qed.

Lemma complete : forall gl (g E : array int) (m : int),
  repr (g : array uint) gl -> (1 <= len gl <= 20)%N -> Forall (fun s => (1 <= s <= 1000)%N) gl -> (1 <= (φ m))%Z ->
  W E 0 = 0%Z ->
  (forall i' : int, ((φ i') < (φ (PArray.length g)))%Z -> forall z, (0 <= z < (φ m))%Z ->
       (W E ((z + (φ (g.[i']))) mod (φ m)) <= W E z + (φ (g.[i'])))%Z) ->
  forall l, bag gl l ->
  (W E ((Z.of_N (total_size gl l)) mod (φ m)) <= Z.of_N (total_size gl l))%Z.
Proof.
  intros gl g E m Hg Hn Hgs Hm HE0 Hcl l. induction l as [|i l IH]; intros Hb.
  - simpl. rewrite Zmod_0_l, HE0. lia.
  - inversion Hb as [|? ? Hi Hb']; subst.
    specialize (IH Hb').
    pose proof (g_length gl g Hg) as Hgl.
    pose proof (to_Z_bounded (PArray.length g)) as Bl.
    unfold len in Hi.
    assert (Hi' : (φ (of_Z (Z.of_N i))) = Z.of_N i) by (apply phi_of_Z; lia).
    destruct (g_cell gl g Hg Hn Hgs (of_Z (Z.of_N i)) ltac:(lia)) as [Hgb Hgv].
    rewrite Hi', N2Z.id in Hgv.
    simpl total_size. rewrite N2Z.inj_add, Hgv.
    set (T := Z.of_N (total_size gl l)) in *.
    assert (HT := Z.mod_pos_bound T (φ m) ltac:(lia)).
    pose proof (Hcl (of_Z (Z.of_N i)) ltac:(lia) (T mod (φ m))%Z HT) as C.
    rewrite Zplus_mod_idemp_l in C. rewrite Z.add_comm. lia.
Qed.

(* Bridge from the iff form to the spec's match on the bool. *)
Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P H; [exact (proj1 H eq_refl)|].
  intro p. discriminate (proj2 H p).
Qed.

Lemma fillable_impl_correct : forall (k : N) (gl : list N) (xk : uint) (xg : array uint),
  valid_input k gl -> repr xk k -> repr xg gl ->
  exists b : bool, repr (fillable_impl xk xg) b /\ fillable_spec k gl b.
Proof.
  intros k gl xk xg Hv Hk Hg.
  destruct Hv as [Hn Hks Hgs].
  exists (fillable_impl xk xg). split; [reflexivity|].
  unfold fillable_spec, fillable_impl, fillable_core.
  apply bool_match_of_iff.
  pose proof (g_length gl xg Hg) as Hgl.
  assert (Hl1 : (1 <= (φ (@PArray.length int xg)) <= 20)%Z) by (unfold len in Hn; lia).
  set (m := min_loop xg (@PArray.length int xg) 1 (@PArray.get int xg 0)
              (Zwf_well_founded 0 (gap (@PArray.length int xg) 1))).
  assert (Hmin : exists j, ((φ j) < (φ (@PArray.length int xg)))%Z /\ @PArray.get int xg j = m).
  { unfold m. apply (min_loop_spec (fun x => exists j, ((φ j) < (φ (@PArray.length int xg)))%Z /\ @PArray.get int xg j = x)) with (zm := gap (@PArray.length int xg) 1).
    - intros i Hi. exists i. split; [exact Hi | reflexivity].
    - reflexivity.
    - exists 0. split; [change (φ 0) with 0%Z; lia | reflexivity]. }
  destruct Hmin as (j0 & Hj0 & Ej0).
  destruct (g_cell gl xg Hg Hn Hgs j0 Hj0) as [Hgb Hgv].
  rewrite Ej0 in Hgb, Hgv.
  assert (HM : (1 <= (φ m) <= 1000)%Z) by exact Hgb.
  set (A0 := (PArray.make m inf).[0 <- 0]).
  assert (HA0len : PArray.length A0 = m).
  { unfold A0. rewrite alength_set, alength_make.
    replace (m <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (HA00 : W A0 0 = 0%Z).
  { unfold A0. change 0%Z with (φ 0) at 1. rewrite W_set_same; [reflexivity|].
    rewrite alength_make.
    replace (m <=? PArray.max_length) with true; [change (φ 0) with 0%Z; lia|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (HA0 : forall z, z <> 0%Z -> (0 <= z < (φ m))%Z -> W A0 z = INF).
  { intros z Hz0 Hz. unfold A0. rewrite W_set_other.
    - unfold W. rewrite aget_make. reflexivity.
    - rewrite wB_val. lia.
    - exact Hz0. }
  destruct (items_spec gl xg Hg Hn Hgs m HM _ 0 A0
              (Zwf_well_founded 0 (gap (@PArray.length int xg) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) HA0len HA00)
    as (E1 & E2 & E3 & E4).
  { intros z Hz Hinf. destruct (Z.eq_dec z 0) as [Ez|Ez].
    - subst z. rewrite HA00. split; [apply ef_zero | apply Zmod_0_l].
    - rewrite (HA0 z Ez Hz) in Hinf. lia. }
  { intros z Hz Hinf. destruct (Z.eq_dec z 0) as [Ez|Ez].
    - subst z. rewrite HA00. change (φ 0) with 0%Z. lia.
    - rewrite (HA0 z Ez Hz) in Hinf. lia. }
  { intros i' Hi'. change (φ 0) with 0%Z in Hi'. pose proof (to_Z_bounded i'). lia. }
  set (E := items xg (@PArray.length int xg) m 0 A0
              (Zwf_well_founded 0 (gap (@PArray.length int xg) 0))) in *.
  set (K := (φ xk)).
  assert (HkK : k = Z.to_N K) by (symmetry; exact Hk).
  assert (HK : (1 <= K <= 10 ^ 18)%Z) by (subst k; lia).
  assert (Hidx : (φ (xk mod m)) = (K mod (φ m))%Z) by (rewrite mod_spec; reflexivity).
  rewrite leb_spec, W_get, Hidx. fold K.
  assert (HKb := Z.mod_pos_bound K (φ m) ltac:(lia)).
  split.
  - intro Hle.
    assert (Hinf : (W E (K mod (φ m)) < INF)%Z) by (unfold INF; lia).
    destruct (E3 _ HKb Hinf) as [Hf Hmod].
    destruct (arith3 K (W E (K mod (φ m))) (φ m) ltac:(lia) Hle Hmod) as (q & Hq & HKq).
    pose proof (W_bound E (K mod (φ m))) as Bw.
    assert (Hj0' : (Z.to_N (φ j0) < len gl)%N) by (unfold len; lia).
    pose proof (ef_addt gl _ _ (Z.to_nat q) Hf Hj0') as Hfill.
    replace (N.of_nat (Z.to_nat q) * get_list_N gl (Z.to_N (φ j0))
             + Z.to_N (W E (K mod (φ m))))%N with k in Hfill; [exact Hfill|].
    apply N2Z.inj. rewrite N2Z.inj_add, N2Z.inj_mul, Hgv, nat_N_Z, Z2Nat.id by lia.
    rewrite Z2N.id by lia. rewrite HkK, Z2N.id by lia. lia.
  - intros (l & Hb & Ht).
    pose proof (complete gl xg E m Hg Hn Hgs ltac:(lia) E2 E4 l Hb) as C.
    rewrite Ht, HkK, Z2N.id in C by lia. exact C.
Qed.

Definition fillable_correct : forall (k : N) (g : list N) (xk : uint) (xg : array uint),
  valid_input k g -> repr xk k -> repr xg g ->
  exists b : bool, repr (fillable xk xg) b /\ fillable_spec k g b
  := fillable_impl_correct.
