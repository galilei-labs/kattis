(* Correctness proofs for loopycabdrivers_implem.v. *)
(* Implementation of loopycabdrivers (loopycabdrivers.spec). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Relations Sorting Permutation.
From Stdlib Require String Ascii PrimString PString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export loopycabdrivers_implem.
Open Scope uint63_scope.
Open Scope array_scope.


Notation pstring := PrimString.string.

(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma neq_phi : forall a b : int, (φ a) <> (φ b) -> a <> b.
Proof. intros a b H E. subst. apply H. reflexivity. Qed.

Lemma phi_eq : forall a b : int, (φ a) = (φ b) -> a = b.
Proof. intros a b H. apply to_Z_inj. exact H. Qed.

Section AL.
Context {A : Set}.

Lemma len_set : forall (t : array A) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set A t i v). Qed.

Lemma get_same : forall (t : array A) i v,
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. rewrite <- ltb_spec in H. exact (get_set_same A t i v H). Qed.

Lemma get_other : forall (t : array A) i j v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros. exact (get_set_other A t i j v H). Qed.

Lemma get_other_phi : forall (t : array A) i j v, (φ i) <> (φ j) -> t.[i <- v].[j] = t.[j].
Proof. intros. exact (get_set_other A t i j v (neq_phi _ _ H)). Qed.

Lemma len_make : forall n (v : A), ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H. pose proof (length_make A n v) as E. change (PArray.length (PArray.make n v) = (if n ≤? PArray.max_length then n else PArray.max_length)) in E. refine (eq_trans E _).
  replace (n ≤? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma get_mk : forall n (v : A) i, (PArray.make n v).[i] = v.
Proof. intros. exact (get_make A v n i). Qed.

Lemma len_copy : forall (t : array A), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros. exact (length_copy A t). Qed.

Lemma get_cp : forall (t : array A) i, (PArray.copy t).[i] = t.[i].
Proof. intros. exact (get_copy A t i). Qed.

Lemma len_bound : forall (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

End AL.


Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma phi_add : forall a b : int, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof. intros a b H. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia. Qed.

Lemma phi_sub : forall a b : int, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof. intros a b H. rewrite sub_spec. apply Z.mod_small. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia. Qed.

Lemma phi_add1 : forall a : int, ((φ a) < 4611686018427387904)%Z -> (φ (a + 1)) = ((φ a) + 1)%Z.
Proof. intros a H. rewrite phi_add; [reflexivity|]. change (φ 1) with 1%Z. rewrite wB_val. lia. Qed.

Lemma phi_add1_lt : forall a b : int, ((φ a) < (φ b))%Z -> (φ (a + 1)) = ((φ a) + 1)%Z.
Proof. intros a b H. rewrite phi_add; [reflexivity|]. change (φ 1) with 1%Z. pose proof (to_Z_bounded b). lia. Qed.

Lemma phi_sub1 : forall a : int, (1 <= (φ a))%Z -> (φ (a - 1)) = ((φ a) - 1)%Z.
Proof. intros a H. rewrite phi_sub; [reflexivity|]. change (φ 1) with 1%Z. lia. Qed.

Lemma ltb_true : forall a b : int, (a <? b) = true <-> ((φ a) < (φ b))%Z.
Proof. intros. apply ltb_spec. Qed.

Lemma ltb_false : forall a b : int, (a <? b) = false <-> ((φ b) <= (φ a))%Z.
Proof. intros. rewrite <- Bool.not_true_iff_false, ltb_spec. lia. Qed.

Lemma eqb_true : forall a b : int, (a =? b) = true <-> a = b.
Proof. intros. apply eqb_spec. Qed.

Lemma eqb_false : forall a b : int, (a =? b) = false <-> a <> b.
Proof. intros. apply eqb_false_spec. Qed.

(* ------------------------------------------------------------------ *)
(* Pigeonhole                                                          *)
(* ------------------------------------------------------------------ *)

Lemma NoDup_map_on : forall {A B} (g : A -> B) (l : list A),
  NoDup l -> (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup (map g l).
Proof.
  intros A B g l. induction l as [|a l IH]; intros Hn Hi; simpl; [constructor|].
  inversion Hn; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Hy & Hyl).
    assert (y = a) by (apply Hi; simpl; auto). subst. contradiction.
  - apply IH; [assumption|]. intros x y Hx Hy. apply Hi; simpl; auto.
Qed.

Lemma pigeon : forall (f : Z -> Z) (a n c : Z), (0 <= n)%Z -> (0 <= c)%Z ->
  (forall q, (a <= q < a + n)%Z -> (1 <= f q <= c)%Z) ->
  (forall q1 q2, (a <= q1 < a + n)%Z -> (a <= q2 < a + n)%Z -> f q1 = f q2 -> q1 = q2) ->
  (n <= c)%Z.
Proof.
  intros f a n c Hn Hc Hr Hi.
  set (l := map (fun k => Z.to_nat (f (a + Z.of_nat k)%Z)) (seq 0 (Z.to_nat n))).
  assert (Hnd : NoDup l).
  { apply NoDup_map_on; [apply seq_NoDup|].
    intros x y Hx Hy E. apply in_seq in Hx, Hy.
    pose proof (Hr (a + Z.of_nat x)%Z ltac:(lia)).
    pose proof (Hr (a + Z.of_nat y)%Z ltac:(lia)).
    assert (E' : f (a + Z.of_nat x)%Z = f (a + Z.of_nat y)%Z) by lia.
    apply Hi in E'; lia. }
  assert (Hinc : incl l (seq 1 (Z.to_nat c))).
  { intros z Hz. apply in_map_iff in Hz as (k & <- & Hk). apply in_seq in Hk.
    pose proof (Hr (a + Z.of_nat k)%Z ltac:(lia)). apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hinc) as HL.
  unfold l in HL. rewrite length_map, !length_seq in HL.
  lia.
Qed.


Lemma step_le : forall m i : int, (i <? m) = true -> (φ (i + 1)) = ((φ i) + 1)%Z /\ ((φ i) + 1 <= (φ m))%Z.
Proof. intros m i H. rewrite ltb_spec in H. split; [|lia]. pose proof (to_Z_bounded m). sia. Qed.

(* ------------------------------------------------------------------ *)
(* Phase 1 proofs: the hash table                                      *)
(* ------------------------------------------------------------------ *)

Lemma hash_bound : forall s, ((φ (hash s)) <= 65535)%Z.
Proof.
  intros s. unfold hash. rewrite land_spec'.
  change (φ hmask) with (Z.ones 16). rewrite Z.land_ones by lia.
  match goal with |- context [(?a mod ?b)%Z] =>
    pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) end.
  change (2 ^ 16)%Z with 65536%Z in *. lia.
Qed.

Ltac gen_acc := match goal with |- context [Acc_inv ?a ?b] =>
  generalize (Acc_inv a b); intros ?Hn end.

Lemma probe_spec : forall tbl names s T z p (H : Acc (Zwf 0) (gap T p)),
  gap T p = z -> ((φ p) <= (φ T))%Z ->
  ((φ p) <= (φ (fst (probe tbl names s T p H))) <= (φ T))%Z /\
  (forall q, ((φ p) <= (φ q) < (φ (fst (probe tbl names s T p H))))%Z ->
     tbl.[q] <> 0 /\ names.[tbl.[q] - 1] <> s) /\
  (snd (probe tbl names s T p H) = true ->
     ((φ (fst (probe tbl names s T p H))) < (φ T))%Z /\
     tbl.[fst (probe tbl names s T p H)] <> 0 /\
     names.[tbl.[fst (probe tbl names s T p H)] - 1] = s) /\
  (snd (probe tbl names s T p H) = false ->
     (φ (fst (probe tbl names s T p H))) = (φ T) \/
     (((φ (fst (probe tbl names s T p H))) < (φ T))%Z /\
      tbl.[fst (probe tbl names s T p H)] = 0)).
Proof.
  intros tbl names s T z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p H Hz HpT. destruct H as [Hacc]. cbn [probe].
  destruct (bdec (p <? T)) as [Hp | Hp].
  - pose proof Hp as Hp'. rewrite ltb_spec in Hp'.
    destruct (tbl.[p] =? 0) eqn:E0.
    + apply eqb_true in E0. cbn [fst snd].
      repeat split; first [lia | intros q Hq; lia | intros F; discriminate F
                          | intros _; right; split; assumption].
    + apply eqb_false in E0.
      destruct (PrimString.compare names.[tbl.[p] - 1] s) eqn:Ec.
      * apply PString.compare_eq in Ec. cbn [fst snd].
        repeat split; first [lia | intros q Hq; lia | intros F; discriminate F | assumption
                            | intros _; repeat split; first [lia | assumption]].
      * destruct (step_le T p Hp) as [E1 E2].
        gen_acc.
        destruct (IH (gap T (p + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hp)
                    (p + 1) Hn eq_refl ltac:(lia)) as (A1 & A2 & A3 & A4).
        split; [lia|]. split; [|exact (conj A3 A4)].
        intros q Hq. destruct (Z.eq_dec (φ q) (φ p)) as [Eq | Eq].
        -- apply phi_eq in Eq. subst q. split; [exact E0|].
           intro F. apply PString.compare_eq in F. congruence.
        -- apply A2. lia.
      * destruct (step_le T p Hp) as [E1 E2].
        gen_acc.
        destruct (IH (gap T (p + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hp)
                    (p + 1) Hn eq_refl ltac:(lia)) as (A1 & A2 & A3 & A4).
        split; [lia|]. split; [|exact (conj A3 A4)].
        intros q Hq. destruct (Z.eq_dec (φ q) (φ p)) as [Eq | Eq].
        -- apply phi_eq in Eq. subst q. split; [exact E0|].
           intro F. apply PString.compare_eq in F. congruence.
        -- apply A2. lia.
  - rewrite ltb_false in Hp. cbn [fst snd].
    repeat split; first [lia | intros q Hq; lia | intros F; discriminate F | intros _; left; lia].
Qed.

Definition HInv (Mx : Z) (st : hstate) : Prop :=
  (φ (PArray.length (ht st))) = (65536 + Mx + 1)%Z /\
  (φ (PArray.length (hn st))) = (Mx + 1)%Z /\
  (0 <= (φ (hc st)) <= Mx)%Z /\
  (forall k1 k2 : int, ((φ k1) < (φ (hc st)))%Z -> ((φ k2) < (φ (hc st)))%Z ->
     (hn st).[k1] = (hn st).[k2] -> k1 = k2) /\
  (forall p : int, ((φ p) < 65536 + Mx + 1)%Z ->
     (ht st).[p] = 0 \/
     ((0 < (φ ((ht st).[p])) <= (φ (hc st)))%Z /\
      ((φ (hash ((hn st).[(ht st).[p] - 1]))) <= (φ p))%Z /\
      forall q : int, ((φ (hash ((hn st).[(ht st).[p] - 1]))) <= (φ q) < (φ p))%Z ->
        (ht st).[q] <> 0)) /\
  (forall k : int, ((φ k) < (φ (hc st)))%Z ->
     exists p, ((φ p) < 65536 + Mx + 1)%Z /\ (ht st).[p] = k + 1) /\
  (forall p q : int, ((φ p) < 65536 + Mx + 1)%Z -> ((φ q) < 65536 + Mx + 1)%Z ->
     (ht st).[p] = (ht st).[q] -> (ht st).[p] <> 0 -> p = q).

Lemma lookup_spec : forall Mx st s, (Mx <= 4000000)%Z -> HInv Mx st -> ((φ (hc st)) < Mx)%Z ->
  HInv Mx (fst (lookup st s)) /\
  ((φ (snd (lookup st s))) < (φ (hc (fst (lookup st s)))))%Z /\
  (hn (fst (lookup st s))).[snd (lookup st s)] = s /\
  ((φ (hc (fst (lookup st s)))) = (φ (hc st)) \/
   (φ (hc (fst (lookup st s)))) = ((φ (hc st)) + 1)%Z)%Z /\
  (forall k, ((φ k) < (φ (hc st)))%Z -> (hn (fst (lookup st s))).[k] = (hn st).[k]) /\
  ((φ (hc (fst (lookup st s)))) = ((φ (hc st)) + 1)%Z -> snd (lookup st s) = hc st).
Proof.
  intros Mx [tbl names cnt] s HMx Hinv Hroom.
  destruct Hinv as (Lt & Ln & Hc & Hinj & Hslot & Hall & Huniq).
  cbn [ht hn hc] in *.
  unfold lookup. cbn [ht hn hc].
  set (T := PArray.length tbl) in *.
  pose proof (hash_bound s) as Hh.
  destruct (probe_spec tbl names s T _ (hash s) (Zwf_well_founded 0 (gap T (hash s)))
              eq_refl ltac:(lia)) as (P1 & P2 & P3 & P4).
  set (pr := probe tbl names s T (hash s) (Zwf_well_founded 0 (gap T (hash s)))) in *.
  destruct pr as [p f]. cbn [fst snd] in *.
  destruct f.
  - destruct (P3 eq_refl) as (Q1 & Q2 & Q3). cbn [fst snd ht hn hc].
    destruct (Hslot p ltac:(lia)) as [Z0 | (S1 & S2 & S3)]; [contradiction|].
    unfold HInv; cbn [fst snd ht hn hc].
    repeat split; try assumption; try lia; try (intros; reflexivity);
      try (rewrite phi_sub1 by lia; lia); intros; lia.
  - assert (Hp : ((φ p) < (φ T))%Z /\ tbl.[p] = 0).
    { destruct (P4 eq_refl) as [Ep | Ep]; [|exact Ep]. exfalso.
      assert (HH : ((φ T) - (φ (hash s)) <= (φ cnt))%Z).
      { apply (pigeon (fun q => (φ (tbl.[of_Z q]))) (φ (hash s)) ((φ T) - (φ (hash s))) (φ cnt)); [lia | lia | |].
        - intros q Hq. pose proof (to_Z_bounded (hash s)).
          assert (Eq : (φ (of_Z q)) = q) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
          destruct (P2 (of_Z q) ltac:(lia)) as [N0 _].
          destruct (Hslot (of_Z q) ltac:(lia)) as [Z0 | (S1 & _)]; [contradiction|]. lia.
        - intros q1 q2 Hq1 Hq2 E. pose proof (to_Z_bounded (hash s)).
          assert (Eq1 : (φ (of_Z q1)) = q1) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
          assert (Eq2 : (φ (of_Z q2)) = q2) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
          apply phi_eq in E.
          destruct (P2 (of_Z q1) ltac:(lia)) as [N0 _].
          pose proof (Huniq (of_Z q1) (of_Z q2) ltac:(lia) ltac:(lia) E N0) as U.
          rewrite <- Eq1, <- Eq2, U. reflexivity. }
      lia. }
    destruct Hp as [HpT Hp0].
    (* s is not yet named *)
    assert (Hnew : forall k, ((φ k) < (φ cnt))%Z -> names.[k] <> s).
    { intros k Hk Ek.
      destruct (Hall k Hk) as (pk & Hpk & Tk).
      assert (Ek1 : tbl.[pk] - 1 = k).
      { rewrite Tk. apply phi_eq. rewrite phi_sub1; rewrite phi_add1; try lia. }
      destruct (Hslot pk Hpk) as [Z0 | (S1 & S2 & S3)].
      { rewrite Tk in Z0. apply (f_equal to_Z) in Z0. rewrite phi_add1 in Z0 by lia.
        change (φ 0) with 0%Z in Z0. pose proof (to_Z_bounded k). lia. }
      rewrite Ek1, Ek in S2, S3.
      destruct (Z.lt_trichotomy (φ pk) (φ p)) as [Lp | [Ep | Gp]].
      - destruct (P2 pk ltac:(lia)) as [_ Ne]. apply Ne. rewrite Ek1. exact Ek.
      - apply phi_eq in Ep. subst pk. rewrite Hp0 in Tk.
        apply (f_equal to_Z) in Tk. rewrite phi_add1 in Tk by lia.
        change (φ 0) with 0%Z in Tk. pose proof (to_Z_bounded k). lia.
      - apply (S3 p ltac:(lia)). exact Hp0. }
    unfold HInv; cbn [fst snd ht hn hc].
    assert (Ec1 : (φ (cnt + 1)) = ((φ cnt) + 1)%Z) by (apply phi_add1; lia).
    assert (Lp' : ((φ p) < (φ (PArray.length tbl)))%Z) by exact HpT.
    assert (Lc' : ((φ cnt) < (φ (PArray.length names)))%Z) by lia.
    assert (Ntbl : forall q, tbl.[p <- cnt + 1].[q] = if (p =? q) then cnt + 1 else tbl.[q]).
    { intros q. destruct (p =? q) eqn:E.
      - apply eqb_true in E. subst q. apply get_same. exact Lp'.
      - apply eqb_false in E. apply get_other. exact E. }
    assert (Nnm : forall k, names.[cnt <- s].[k] = if (cnt =? k) then s else names.[k]).
    { intros k. destruct (cnt =? k) eqn:E.
      - apply eqb_true in E. subst k. apply get_same. exact Lc'.
      - apply eqb_false in E. apply get_other. exact E. }
    assert (Hpq : forall q, (p =? q) = true <-> (φ p) = (φ q)).
    { intros q. rewrite eqb_true. split; [intros ->; reflexivity | apply phi_eq]. }
    assert (Hck : forall k, (cnt =? k) = true <-> (φ cnt) = (φ k)).
    { intros k. rewrite eqb_true. split; [intros ->; reflexivity | apply phi_eq]. }
    assert (Cm1 : cnt + 1 - 1 = cnt).
    { apply phi_eq. rewrite phi_sub1; [|lia]. change (φ 1) with 1%Z. lia. }
    repeat split.
    + rewrite len_set. exact Lt.
    + rewrite len_set. exact Ln.
    + lia.
    + lia.
    + intros k1 k2 H1 H2 E. rewrite !Nnm in E.
      destruct (cnt =? k1) eqn:E1, (cnt =? k2) eqn:E2.
      * apply Hck in E1, E2. apply phi_eq. lia.
      * apply Hck in E1. exfalso. apply (Hnew k2); [rewrite <- Bool.not_true_iff_false, Hck in E2; rewrite Ec1 in H2; lia| congruence].
      * apply Hck in E2. exfalso. apply (Hnew k1); [rewrite <- Bool.not_true_iff_false, Hck in E1; rewrite Ec1 in H1; lia| congruence].
      * rewrite <- Bool.not_true_iff_false, Hck in E1, E2.
        apply Hinj; [lia | lia | exact E].
    + intros p' Hp'. rewrite !Ntbl.
      destruct (p =? p') eqn:Ep.
      * right. apply Hpq in Ep. rewrite Cm1, Nnm.
        replace (cnt =? cnt) with true by (symmetry; apply eqb_true; reflexivity).
        repeat split; [lia | lia | lia |].
        intros q Hq. rewrite Ntbl. destruct (p =? q) eqn:Eq.
        -- intro F. apply (f_equal to_Z) in F. rewrite Ec1 in F. change (φ 0) with 0%Z in F. lia.
        -- apply (P2 q). lia.
      * destruct (Hslot p' Hp') as [Z0 | (S1 & S2 & S3)]; [left; exact Z0|].
        right.
        assert (Ne : cnt <> tbl.[p'] - 1) by (apply neq_phi; rewrite phi_sub1 by lia; change (φ 1) with 1%Z; lia).
        rewrite Nnm. replace (cnt =? tbl.[p'] - 1) with false by (symmetry; apply eqb_false; exact Ne).
        repeat split; [lia | lia | lia |].
        intros q Hq. rewrite Ntbl. destruct (p =? q) eqn:Eq.
        -- intro F. apply (f_equal to_Z) in F. rewrite Ec1 in F. change (φ 0) with 0%Z in F. lia.
        -- apply S3. exact Hq.
    + intros k Hk. destruct (Z.eq_dec (φ k) (φ cnt)) as [Ek | Ek].
      * apply phi_eq in Ek. subst k. exists p. split; [lia|].
        rewrite Ntbl. replace (p =? p) with true by (symmetry; apply eqb_true; reflexivity). reflexivity.
      * destruct (Hall k ltac:(lia)) as (pk & Hpk & Tk). exists pk. split; [exact Hpk|].
        rewrite Ntbl. destruct (p =? pk) eqn:E.
        -- apply eqb_true in E. subst pk. rewrite Hp0 in Tk.
           apply (f_equal to_Z) in Tk. rewrite phi_add1 in Tk by lia.
           change (φ 0) with 0%Z in Tk. pose proof (to_Z_bounded k). lia.
        -- exact Tk.
    + intros p1 p2 H1 H2. rewrite !Ntbl.
      destruct (p =? p1) eqn:E1, (p =? p2) eqn:E2; intros E N.
      * apply Hpq in E1, E2. apply phi_eq. lia.
      * exfalso. destruct (Hslot p2 H2) as [Z0 | (S1 & _)]; [congruence|].
        rewrite <- E in S1. lia.
      * exfalso. destruct (Hslot p1 H1) as [Z0 | (S1 & _)]; [congruence|].
        rewrite E in S1. lia.
      * apply Huniq; assumption.
    + rewrite Ec1. lia.
    + rewrite Nnm. replace (cnt =? cnt) with true by (symmetry; apply eqb_true; reflexivity). reflexivity.
    + right. exact Ec1.
    + intros k Hk. rewrite Nnm. replace (cnt =? k) with false; [reflexivity|].
      symmetry. apply eqb_false. apply neq_phi. lia.
Qed.

Definition IdOK (x y : array pstring) (m k : int) (st : hstate) (is id : array int) : Prop :=
  HInv (2 * (φ m)) st /\ ((φ (hc st)) <= 2 * (φ k))%Z /\
  PArray.length is = m /\ PArray.length id = m /\
  (forall k', ((φ k') < (φ k))%Z ->
     ((φ (is.[k'])) < (φ (hc st)))%Z /\ (hn st).[is.[k']] = x.[k'] /\
     ((φ (id.[k'])) < (φ (hc st)))%Z /\ (hn st).[id.[k']] = y.[k']) /\
  (forall v, ((φ v) < (φ (hc st)))%Z ->
     exists k', ((φ k') < (φ k))%Z /\ ((hn st).[v] = x.[k'] \/ (hn st).[v] = y.[k'])).

Lemma idloop_spec : forall (x y : array pstring) (m : int), ((φ m) <= 10000)%Z ->
  forall z k st is id (H : Acc (Zwf 0) (gap m k)), gap m k = z ->
  ((φ k) <= (φ m))%Z -> IdOK x y m k st is id ->
  IdOK x y m m (fst (fst (idloop x y m k st is id H)))
       (snd (fst (idloop x y m k st is id H))) (snd (idloop x y m k st is id H)).
Proof.
  intros x y m Hm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k st is id H Hz Hk Hok. destruct H as [Hacc]. cbn [idloop].
  destruct (bdec (k <? m)) as [Hlt | Hge].
  - destruct (step_le m k Hlt) as [E1 E2].
    gen_acc.
    apply (IH (gap m (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hlt) (k + 1) _ _ _ Hn
             eq_refl ltac:(lia)).
    destruct Hok as (Hinv & Hc & Li & Ld & Hids & Hnm).
    pose proof (lookup_spec (2 * (φ m)) st x.[k] ltac:(lia) Hinv ltac:(rewrite ltb_spec in Hlt; lia))
      as (I1 & A1 & N1 & C1 & P1 & F1).
    set (r1 := lookup st x.[k]) in *.
    pose proof (lookup_spec (2 * (φ m)) (fst r1) y.[k] ltac:(lia) I1
                  ltac:(rewrite ltb_spec in Hlt; lia))
      as (I2 & A2 & N2 & C2 & P2 & F2).
    set (r2 := lookup (fst r1) y.[k]) in *.
    assert (Lk : ((φ k) < (φ (PArray.length is)))%Z) by (rewrite Li; lia).
    assert (Lk' : ((φ k) < (φ (PArray.length id)))%Z) by (rewrite Ld; lia).
    unfold IdOK. refine (conj I2 (conj _ (conj _ (conj _ (conj _ _))))).
    + lia.
    + rewrite len_set. exact Li.
    + rewrite len_set. exact Ld.
    + intros k' Hk'. destruct (Z.eq_dec (φ k') (φ k)) as [Eq | Ne].
      * apply phi_eq in Eq. subst k'. rewrite (get_same is) by exact Lk.
        rewrite (get_same id) by exact Lk'.
        rewrite (P2 (snd r1)) by lia. repeat split; first [lia | exact N1 | exact N2].
      * rewrite (get_other_phi is), (get_other_phi id) by lia.
        destruct (Hids k' ltac:(lia)) as (B1 & B2 & B3 & B4).
        rewrite (P2 is.[k']), (P1 is.[k']), (P2 id.[k']), (P1 id.[k']) by lia.
        repeat split; first [lia | assumption].
    + intros v Hv.
      destruct (Z.lt_ge_cases (φ v) (φ (hc st))) as [Lv | Gv].
      * destruct (Hnm v Lv) as (k' & Hk' & Hw). exists k'. split; [lia|].
        rewrite P2 by lia. rewrite P1 by lia. exact Hw.
      * exists k. split; [lia|].
        destruct (Z.lt_ge_cases (φ v) (φ (hc (fst r1)))) as [Lv1 | Gv1].
        -- left. rewrite P2 by lia.
           assert (Ec : (φ (hc (fst r1))) = ((φ (hc st)) + 1)%Z) by lia.
           specialize (F1 Ec). assert (v = snd r1) by (apply phi_eq; rewrite F1; lia).
           subst v. exact N1.
        -- right.
           assert (Ec : (φ (hc (fst r2))) = ((φ (hc (fst r1))) + 1)%Z) by lia.
           specialize (F2 Ec). assert (v = snd r2) by (apply phi_eq; rewrite F2; lia).
           subst v. exact N2.
  - rewrite ltb_false in Hge. cbn [fst snd].
    assert (k = m) by (apply phi_eq; lia). subst k. exact Hok.
Qed.

Lemma hash_phase : forall (x y : array pstring), ((φ (PArray.length x)) <= 10000)%Z ->
  IdOK x y (PArray.length x) (PArray.length x)
    (fst (fst (idloop x y (PArray.length x) 0
       (HS (PArray.make (hsize + 2 * PArray.length x + 1) 0)
           (PArray.make (2 * PArray.length x + 1) empty_str) 0)
       (PArray.make (PArray.length x) 0) (PArray.make (PArray.length x) 0)
       (Zwf_well_founded 0 (gap (PArray.length x) 0)))))
    (snd (fst (idloop x y (PArray.length x) 0
       (HS (PArray.make (hsize + 2 * PArray.length x + 1) 0)
           (PArray.make (2 * PArray.length x + 1) empty_str) 0)
       (PArray.make (PArray.length x) 0) (PArray.make (PArray.length x) 0)
       (Zwf_well_founded 0 (gap (PArray.length x) 0)))))
    (snd (idloop x y (PArray.length x) 0
       (HS (PArray.make (hsize + 2 * PArray.length x + 1) 0)
           (PArray.make (2 * PArray.length x + 1) empty_str) 0)
       (PArray.make (PArray.length x) 0) (PArray.make (PArray.length x) 0)
       (Zwf_well_founded 0 (gap (PArray.length x) 0)))).
Proof.
  intros x y Hm.
  set (m := PArray.length x) in *.
  pose proof (to_Z_bounded m) as Bm.
  apply (idloop_spec x y m Hm _ 0 _ _ _ _ eq_refl ltac:(change (φ 0) with 0%Z; lia)).
  assert (E1 : (φ (hsize + 2 * m + 1)) = (65536 + 2 * (φ m) + 1)%Z)
    by (unfold hsize; sia).
  assert (E2 : (φ (2 * m + 1)) = (2 * (φ m) + 1)%Z) by sia.
  unfold IdOK, HInv; cbn [ht hn hc]. change (φ 0) with 0%Z.
  repeat split.
  all: first [ rewrite len_make by lia; first [exact E1 | lia]
             | apply len_make; lia
             | intros; left; apply get_mk
             | intros p q _ _ _ N; exfalso; apply N; apply get_mk
             | intros; lia ].
Qed.

(* ------------------------------------------------------------------ *)
(* nat views                                                           *)
(* ------------------------------------------------------------------ *)

Definition ofn (k : nat) : int := of_Z (Z.of_nat k).
Definition nz (i : int) : nat := Z.to_nat (φ i).

Lemma phi_ofn : forall k, (Z.of_nat k < wB)%Z -> (φ (ofn k)) = Z.of_nat k.
Proof. intros k H. unfold ofn. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma ofn_nz : forall i, ofn (nz i) = i.
Proof.
  intros i. unfold ofn, nz. pose proof (to_Z_bounded i).
  rewrite Z2Nat.id by lia. apply of_to_Z.
Qed.

Lemma nz_phi : forall i, Z.of_nat (nz i) = (φ i).
Proof. intros i. unfold nz. pose proof (to_Z_bounded i). lia. Qed.

Lemma nz_add1 : forall i, ((φ i) < 4611686018427387904)%Z -> nz (i + 1) = S (nz i).
Proof. intros i H. unfold nz. rewrite phi_add1 by exact H. pose proof (to_Z_bounded i). lia. Qed.

Lemma list_sum_map_add : forall {A} (f g : A -> nat) l,
  list_sum (map (fun x => (f x + g x)%nat) l) = (list_sum (map f l) + list_sum (map g l))%nat.
Proof.
  intros A f g l. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia.
Qed.

Definition slice (a : array int) (lo : Z) (n : nat) : list int :=
  map (fun k => a.[of_Z (lo + Z.of_nat k)]) (seq 0 n).

Lemma slice_S : forall a lo n,
  slice a lo (S n) = slice a lo n ++ [a.[of_Z (lo + Z.of_nat n)]].
Proof. intros. unfold slice. rewrite seq_S, map_app. reflexivity. Qed.

Lemma slice_set_out : forall a lo n p v, (0 <= lo)%Z -> (lo + Z.of_nat n <= 4194303)%Z ->
  ((φ p) < lo \/ lo + Z.of_nat n <= (φ p))%Z ->
  slice a.[p <- v] lo n = slice a lo n.
Proof.
  intros a lo n p v H1 H2 H3. unfold slice. apply map_ext_in. intros k Hk.
  apply in_seq in Hk. apply get_other_phi. rewrite of_Z_spec, Z.mod_small; rewrite ?wB_val; lia.
Qed.

Lemma slice_ext : forall a b lo n, (forall k, (k < n)%nat -> a.[of_Z (lo + Z.of_nat k)] = b.[of_Z (lo + Z.of_nat k)]) ->
  slice a lo n = slice b lo n.
Proof.
  intros a b lo n H. unfold slice. apply map_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Phase 2 proofs: CSR                                                 *)
(* ------------------------------------------------------------------ *)

Section CSR.
Variables es ed : int -> int.

Definition sel (u : int) (k : nat) : bool := es (ofn k) =? u.
Definition cntl (u : int) (n : nat) : nat := List.length (filter (sel u) (seq 0 n)).
Definition outl (u : int) (n : nat) : list int :=
  map (fun k => ed (ofn k)) (filter (sel u) (seq 0 n)).
Definition psum (n w : nat) : nat :=
  list_sum (map (fun w' => cntl (ofn w') n) (seq 0 w)).

Lemma cntl_S : forall u n, cntl u (S n) = (cntl u n + (if sel u n then 1 else 0))%nat.
Proof.
  intros u n. unfold cntl. rewrite seq_S, filter_app, length_app. simpl.
  destruct (sel u n); simpl; lia.
Qed.

Lemma outl_S : forall u n,
  outl u (S n) = outl u n ++ (if sel u n then [ed (ofn n)] else []).
Proof.
  intros u n. unfold outl. rewrite seq_S, filter_app, map_app. simpl.
  destruct (sel u n); reflexivity.
Qed.

Lemma cntl_le : forall u n, (cntl u n <= n)%nat.
Proof.
  intros u n. induction n as [|n IH]; [unfold cntl; simpl; lia|]. rewrite cntl_S.
  destruct (sel u n); lia.
Qed.

Lemma cntl_mono : forall u n n', (n <= n')%nat -> (cntl u n <= cntl u n')%nat.
Proof.
  intros u n n' H. induction H as [|n' H IH]; [lia|]. rewrite cntl_S. lia.
Qed.

Lemma outl_length : forall u n, List.length (outl u n) = cntl u n.
Proof. intros. unfold outl, cntl. rewrite length_map. reflexivity. Qed.

Lemma psum_S : forall n w, psum n (S w) = (psum n w + cntl (ofn w) n)%nat.
Proof.
  intros n w. unfold psum. rewrite seq_S, map_app, list_sum_app. simpl. lia.
Qed.

Lemma psum_mono : forall n w w', (w <= w')%nat -> (psum n w <= psum n w')%nat.
Proof.
  intros n w w' H. induction H as [|w' H IH]; [lia|]. rewrite psum_S. lia.
Qed.

Lemma sum_ind : forall (x : int) w, (Z.of_nat w <= 4194303)%Z ->
  list_sum (map (fun w' => if es x =? ofn w' then 1%nat else 0%nat) (seq 0 w))
  = (if ((φ (es x)) <? Z.of_nat w)%Z then 1 else 0)%nat.
Proof.
  intros x w. induction w as [|w IH]; intros Hw.
  - simpl. pose proof (to_Z_bounded (es x)).
    destruct ((φ (es x)) <? 0)%Z eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
  - rewrite seq_S, map_app, list_sum_app, IH by lia. cbn [map list_sum].
    replace (0 + w)%nat with w by lia.
    pose proof (phi_ofn w ltac:(rewrite wB_val; lia)) as Ew.
    destruct (es x =? ofn w) eqn:E.
    + apply eqb_true in E. rewrite E, Ew.
      rewrite (proj2 (Z.ltb_ge (Z.of_nat w) (Z.of_nat w)) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt (Z.of_nat w) (Z.of_nat (S w))) ltac:(lia)). reflexivity.
    + apply eqb_false in E. assert ((φ (es x)) <> Z.of_nat w) by (intro F; apply E; apply phi_eq; lia).
      destruct ((φ (es x)) <? Z.of_nat w)%Z eqn:E1; destruct ((φ (es x)) <? Z.of_nat (S w))%Z eqn:E2;
      rewrite ?Z.ltb_lt, ?Z.ltb_ge in E1, E2; try lia; reflexivity.
Qed.

Lemma psum_le : forall n w, (Z.of_nat w <= 4194303)%Z -> (psum n w <= n)%nat.
Proof.
  intros n w Hw. induction n as [|n IH].
  - unfold psum. replace (map (fun w' => cntl (ofn w') 0) (seq 0 w)) with (map (fun _ => 0%nat) (seq 0 w)).
    + clear. induction (seq 0 w); simpl; lia.
    + apply map_ext. intros a. reflexivity.
  - unfold psum.
    replace (map (fun w' => cntl (ofn w') (S n)) (seq 0 w))
      with (map (fun w' => (cntl (ofn w') n + (if (es (ofn n) =? ofn w')%uint63 then 1 else 0))%nat) (seq 0 w))
      by (apply map_ext; intros a; rewrite cntl_S; reflexivity).
    rewrite list_sum_map_add, sum_ind by exact Hw. fold (psum n w).
    destruct ((φ (es (ofn n))) <? Z.of_nat w)%Z; lia.
Qed.

Variables (V m : int).
Hypothesis HV : ((φ V) <= 4194302)%Z.
Hypothesis Hm : ((φ m) <= 4194303)%Z.
Hypothesis Hes : forall k, ((φ k) < (φ m))%Z -> ((φ (es k)) < (φ V))%Z.

Lemma cnt_loop_spec : forall z k cnt (H : Acc (Zwf 0) (gap m k)), gap m k = z ->
  ((φ k) <= (φ m))%Z -> PArray.length cnt = V ->
  (forall u, ((φ u) < (φ V))%Z -> (φ (cnt.[u])) = Z.of_nat (cntl u (nz k))) ->
  PArray.length (cnt_loop es m k cnt H) = V /\
  (forall u, ((φ u) < (φ V))%Z -> (φ ((cnt_loop es m k cnt H).[u])) = Z.of_nat (cntl u (nz m))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k cnt H Hz Hk Hl Hc. destruct H as [Hacc]. cbn [cnt_loop].
  destruct (bdec (k <? m)) as [Hlt | Hge].
  - destruct (step_le m k Hlt) as [E1 E2]. gen_acc.
    rewrite ltb_spec in Hlt.
    apply (IH (gap m (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ Hn eq_refl ltac:(lia)).
    + rewrite len_set. exact Hl.
    + intros u Hu. rewrite nz_add1 by lia. rewrite cntl_S.
      unfold sel. rewrite ofn_nz.
      pose proof (Hes k Hlt) as Hek.
      destruct (es k =? u) eqn:E.
      * apply eqb_true in E. subst u. rewrite get_same by (rewrite Hl; lia).
        rewrite phi_add1, Hc by (try rewrite Hc; pose proof (cntl_le (es k) (nz k)); pose proof (nz_phi k); lia).
        lia.
      * apply eqb_false in E. rewrite get_other by exact E. rewrite Hc by exact Hu. lia.
  - rewrite ltb_false in Hge. assert (k = m) by (apply phi_eq; lia). subst k.
    split; assumption.
Qed.

Lemma pre_loop_spec : forall cnt, PArray.length cnt = V ->
  (forall u, ((φ u) < (φ V))%Z -> (φ (cnt.[u])) = Z.of_nat (cntl u (nz m))) ->
  forall z u off (H : Acc (Zwf 0) (gap V u)), gap V u = z ->
  ((φ u) <= (φ V))%Z -> PArray.length off = V + 1 ->
  (forall w, ((φ w) <= (φ u))%Z -> (φ (off.[w])) = Z.of_nat (psum (nz m) (nz w))) ->
  PArray.length (pre_loop cnt V u off H) = V + 1 /\
  (forall w, ((φ w) <= (φ V))%Z -> (φ ((pre_loop cnt V u off H).[w])) = Z.of_nat (psum (nz m) (nz w))).
Proof.
  intros cnt Hl Hc z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u off H Hz Hu Ho Hinv. destruct H as [Hacc]. cbn [pre_loop].
  destruct (bdec (u <? V)) as [Hlt | Hge].
  - destruct (step_le V u Hlt) as [E1 E2]. gen_acc.
    rewrite ltb_spec in Hlt.
    apply (IH (gap V (u + 1)) ltac:(unfold Zwf, gap in *; lia) (u + 1) _ Hn eq_refl ltac:(lia)).
    + rewrite len_set. exact Ho.
    + intros w Hw.
      assert (EV : (φ (V + 1)) = ((φ V) + 1)%Z) by (apply phi_add1; lia).
      destruct (Z.eq_dec (φ w) (φ (u + 1))) as [Ew | Ew].
      * apply phi_eq in Ew. subst w. rewrite get_same by (rewrite Ho, EV; lia).
        pose proof (psum_le (nz m) (nz u) ltac:(rewrite nz_phi; lia)).
        pose proof (psum_le (nz m) (S (nz u)) ltac:(rewrite Nat2Z.inj_succ, nz_phi; lia)).
        rewrite psum_S, ofn_nz in H0.
        pose proof (nz_phi m).
        assert (Hcu := Hc u Hlt). assert (Hou := Hinv u ltac:(lia)).
        rewrite phi_add by (rewrite Hcu, Hou, wB_val; lia).
        rewrite Hcu, Hou. rewrite nz_add1 by lia. rewrite psum_S, ofn_nz. lia.
      * rewrite get_other_phi by lia. apply Hinv. lia.
  - rewrite ltb_false in Hge. assert (u = V) by (apply phi_eq; lia). subst u.
    split; assumption.
Qed.

Lemma fill_loop_spec : forall off, PArray.length off = V + 1 ->
  (forall w, ((φ w) <= (φ V))%Z -> (φ (off.[w])) = Z.of_nat (psum (nz m) (nz w))) ->
  forall z k pos adj (H : Acc (Zwf 0) (gap m k)), gap m k = z ->
  ((φ k) <= (φ m))%Z -> PArray.length adj = m -> PArray.length pos = V + 1 ->
  (forall u, ((φ u) < (φ V))%Z -> (φ (pos.[u])) = ((φ (off.[u])) + Z.of_nat (cntl u (nz k)))%Z) ->
  (forall u, ((φ u) < (φ V))%Z -> slice adj (φ (off.[u])) (cntl u (nz k)) = outl u (nz k)) ->
  PArray.length (fill_loop es ed m k pos adj H) = m /\
  (forall u, ((φ u) < (φ V))%Z ->
     slice (fill_loop es ed m k pos adj H) (φ (off.[u])) (cntl u (nz m)) = outl u (nz m)).
Proof.
  intros off Ho Hoff z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k pos adj H Hz Hk Ha Hpl Hpos Hsl. destruct H as [Hacc]. cbn [fill_loop].
  assert (Hmono : forall a b, ((φ a) <= (φ b) <= (φ V))%Z -> ((φ (off.[a])) <= (φ (off.[b])))%Z).
  { intros a b Hab. rewrite !Hoff by lia. apply inj_le. apply psum_mono.
    unfold nz. lia. }
  assert (Hnext : forall u, ((φ u) < (φ V))%Z ->
            ((φ (off.[u + 1])) = (φ (off.[u])) + Z.of_nat (cntl u (nz m)))%Z).
  { intros u Hu. rewrite !Hoff by (rewrite ?phi_add1; lia).
    rewrite nz_add1 by lia. rewrite psum_S, ofn_nz. lia. }
  assert (Htop : forall u, ((φ u) <= (φ V))%Z -> ((φ (off.[u])) <= (φ m))%Z).
  { intros u Hu. rewrite Hoff by lia. pose proof (psum_le (nz m) (nz u) ltac:(rewrite nz_phi; lia)).
    pose proof (nz_phi m). lia. }
  destruct (bdec (k <? m)) as [Hlt | Hge].
  - destruct (step_le m k Hlt) as [E1 E2]. gen_acc.
    rewrite ltb_spec in Hlt.
    pose proof (Hes k Hlt) as Hek.
    set (e := es k) in *.
    assert (Hsel : forall u, sel u (nz k) = (e =? u)) by (intros u; unfold sel; rewrite ofn_nz; reflexivity).
    (* the write position lies inside e's block *)
    assert (Hce : (cntl e (S (nz k)) <= cntl e (nz m))%nat)
      by (apply cntl_mono; pose proof (nz_phi k); pose proof (nz_phi m); lia).
    rewrite cntl_S, Hsel in Hce.
    replace (e =? e) with true in Hce by (symmetry; apply eqb_true; reflexivity).
    pose proof (Hnext e Hek) as Hne.
    pose proof (Htop (e + 1) ltac:(rewrite phi_add1; lia)) as Hte.
    pose proof (Hpos e Hek) as Hpe.
    apply (IH (gap m (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ _ Hn eq_refl ltac:(lia)).
    + rewrite len_set. exact Ha.
    + rewrite len_set. exact Hpl.
    + intros u Hu. rewrite nz_add1 by lia. rewrite cntl_S, Hsel.
      destruct (e =? u) eqn:E.
      * apply eqb_true in E. rewrite <- E. rewrite get_same by (rewrite Hpl, phi_add1; lia).
        rewrite phi_add1 by lia. rewrite Hpe. lia.
      * apply eqb_false in E. rewrite get_other by exact E. rewrite Hpos by exact Hu. lia.
    + intros u Hu. rewrite nz_add1 by lia. rewrite cntl_S, outl_S, Hsel.
      destruct (e =? u) eqn:E.
      * apply eqb_true in E. subst u.
        replace (cntl e (nz k) + 1)%nat with (S (cntl e (nz k))) by lia.
        rewrite slice_S, <- Hsl by exact Hek.
        assert (Ep : of_Z ((φ (off.[e])) + Z.of_nat (cntl e (nz k))) = pos.[e]).
        { apply phi_eq. rewrite of_Z_spec, Z.mod_small; [lia|].
          pose proof (to_Z_bounded (off.[e])). rewrite wB_val. lia. }
        rewrite Ep. rewrite get_same by (rewrite Ha; lia).
        rewrite ofn_nz. f_equal.
        apply slice_set_out; [apply to_Z_bounded | lia | lia].
      * apply eqb_false in E. rewrite app_nil_r, Nat.add_0_r.
        rewrite <- (Hsl u Hu).
        pose proof (cntl_mono u (nz k) (nz m) ltac:(pose proof (nz_phi k); pose proof (nz_phi m); lia)).
        pose proof (Hnext u Hu).
        apply slice_set_out; [apply to_Z_bounded | pose proof (Htop (u + 1) ltac:(rewrite phi_add1; lia)); lia |].
        destruct (Z.lt_ge_cases (φ u) (φ e)) as [Lu | Gu].
        -- right. pose proof (Hmono (u + 1) e ltac:(rewrite phi_add1; lia)).
           rewrite phi_add1 in * by lia. lia.
        -- left. assert ((φ u) <> (φ e)) by (intro F; apply E; apply phi_eq; lia).
           pose proof (Hmono (e + 1) u ltac:(rewrite phi_add1; lia)). lia.
  - rewrite ltb_false in Hge. assert (k = m) by (apply phi_eq; lia). subst k.
    split; assumption.
Qed.

End CSR.

Definition CSROK (es ed : int -> int) (V m : int) (off adj : array int) : Prop :=
  PArray.length off = V + 1 /\ PArray.length adj = m /\
  (forall u, ((φ u) < (φ V))%Z ->
     ((φ (off.[u + 1])) = (φ (off.[u])) + Z.of_nat (cntl es u (nz m)))%Z /\
     ((φ (off.[u + 1])) <= (φ m))%Z) /\
  (forall u, ((φ u) < (φ V))%Z -> slice adj (φ (off.[u])) (cntl es u (nz m)) = outl es ed u (nz m)).

Lemma csr_ok : forall es ed V m, ((φ V) <= 4194302)%Z -> ((φ m) <= 4194303)%Z ->
  (forall k, ((φ k) < (φ m))%Z -> ((φ (es k)) < (φ V))%Z) ->
  CSROK es ed V m (fst (csr V m es ed)) (snd (csr V m es ed)).
Proof.
  intros es ed V m HV Hm Hes. unfold csr. cbn [fst snd].
  assert (EV : (φ (V + 1)) = ((φ V) + 1)%Z) by (apply phi_add1; lia).
  destruct (cnt_loop_spec es ed V m Hm Hes _ 0 (PArray.make V 0) (Zwf_well_founded 0 (gap m 0))
              eq_refl ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded m); lia)
              ltac:(apply len_make; lia)
              ltac:(intros u Hu; rewrite get_mk; reflexivity)) as [C1 C2].
  set (cnt := cnt_loop es m 0 (PArray.make V 0) (Zwf_well_founded 0 (gap m 0))) in *.
  destruct (pre_loop_spec es ed V m HV Hm cnt C1 C2 _ 0 (PArray.make (V + 1) 0)
              (Zwf_well_founded 0 (gap V 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded V); lia)
              ltac:(apply len_make; lia)
              ltac:(intros w Hw; rewrite get_mk; change (φ 0) with 0%Z in *;
                    pose proof (to_Z_bounded w); assert (Hw0 : nz w = 0%nat) by (unfold nz; lia);
                    rewrite Hw0; reflexivity)) as [O1 O2].
  set (off := pre_loop cnt V 0 (PArray.make (V + 1) 0) (Zwf_well_founded 0 (gap V 0))) in *.
  destruct (fill_loop_spec es ed V m HV Hm Hes off O1 O2 _ 0 (PArray.copy off) (PArray.make m 0)
              (Zwf_well_founded 0 (gap m 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded m); lia)
              ltac:(apply len_make; lia)
              ltac:(rewrite len_copy; exact O1)
              ltac:(intros u Hu; rewrite get_cp; change (nz 0) with 0%nat; unfold cntl; simpl; lia)
              ltac:(intros u Hu; change (nz 0) with 0%nat; reflexivity)) as [F1 F2].
  unfold CSROK. split; [exact O1|]. split; [exact F1|]. split; [|exact F2].
  intros u Hu. rewrite !O2 by (rewrite ?phi_add1; lia).
  pose proof (psum_le es ed (nz m) (nz (u + 1)) ltac:(rewrite nz_phi, phi_add1; lia)).
  pose proof (nz_phi m).
  rewrite nz_add1 by lia. rewrite psum_S, ofn_nz. rewrite nz_add1, psum_S, ofn_nz in H by lia.
  lia.
Qed.

Lemma in_slice : forall a lo n v, In v (slice a lo n) <->
  exists t, (t < n)%nat /\ a.[of_Z (lo + Z.of_nat t)] = v.
Proof.
  intros a lo n v. unfold slice. rewrite in_map_iff. split.
  - intros (t & <- & Ht). apply in_seq in Ht. exists t. split; [lia|reflexivity].
  - intros (t & Ht & <-). exists t. split; [reflexivity|]. apply in_seq. lia.
Qed.

Lemma in_outl : forall es ed u n v, In v (outl es ed u n) <->
  exists k, (k < n)%nat /\ es (ofn k) = u /\ ed (ofn k) = v.
Proof.
  intros es ed u n v. unfold outl. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply filter_In in Hk as [Hk Hs]. apply in_seq in Hk.
    unfold sel in Hs. apply eqb_true in Hs. exists k. repeat split; [lia | exact Hs].
  - intros (k & Hk & Hs & <-). exists k. split; [reflexivity|].
    apply filter_In. split; [apply in_seq; lia|]. unfold sel. apply eqb_true. exact Hs.
Qed.

Lemma csr_sound : forall es ed V m off adj, CSROK es ed V m off adj ->
  ((φ m) <= 4194303)%Z ->
  forall u j, ((φ u) < (φ V))%Z -> ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
  exists k, ((φ k) < (φ m))%Z /\ es k = u /\ ed k = adj.[j].
Proof.
  intros es ed V m off adj (L1 & L2 & H3 & H4) Hm u j Hu Hj.
  destruct (H3 u Hu) as [N1 N2].
  assert (Hin : In adj.[j] (slice adj (φ (off.[u])) (cntl es u (nz m)))).
  { apply in_slice. exists (Z.to_nat ((φ j) - (φ (off.[u])))). split; [lia|].
    f_equal. apply phi_eq. rewrite of_Z_spec, Z.mod_small; [lia|].
    pose proof (to_Z_bounded j). lia. }
  rewrite H4 in Hin by exact Hu. apply in_outl in Hin as (k & Hk & Hs & Hd).
  exists (ofn k). split; [|split; [exact Hs | exact Hd]].
  rewrite phi_ofn; [|rewrite wB_val; pose proof (nz_phi m); lia].
  pose proof (nz_phi m). lia.
Qed.

Lemma csr_complete : forall es ed V m off adj, CSROK es ed V m off adj ->
  (forall k, ((φ k) < (φ m))%Z -> ((φ (es k)) < (φ V))%Z) ->
  forall k, ((φ k) < (φ m))%Z ->
  exists j, ((φ (off.[es k])) <= (φ j) < (φ (off.[es k + 1])))%Z /\ adj.[j] = ed k.
Proof.
  intros es ed V m off adj (L1 & L2 & H3 & H4) Hes k Hk.
  pose proof (Hes k Hk) as Hek.
  assert (Hin : In (ed k) (outl es ed (es k) (nz m))).
  { apply in_outl. exists (nz k). rewrite ofn_nz. split; [|split; reflexivity].
    unfold nz. pose proof (to_Z_bounded k). lia. }
  rewrite <- H4 in Hin by exact Hek. apply in_slice in Hin as (t & Ht & Ha).
  destruct (H3 (es k) Hek) as [N1 N2].
  exists (of_Z ((φ (off.[es k])) + Z.of_nat t)). split; [|exact Ha].
  pose proof (to_Z_bounded (off.[es k])).
  rewrite of_Z_spec, Z.mod_small; [lia|]. rewrite wB_val. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Lists                                                               *)
(* ------------------------------------------------------------------ *)

Definition idec (a b : int) : {a = b} + {a <> b}.
Proof.
  destruct (a =? b) eqn:E; [left; apply eqb_true; exact E | right; apply eqb_false; exact E].
Defined.

Lemma nodup_bound : forall (V : int) (l : list int), NoDup l ->
  (forall v, In v l -> ((φ v) < (φ V))%Z) -> (Z.of_nat (List.length l) <= (φ V))%Z.
Proof.
  intros V l Hn Hl.
  assert (Hinc : incl l (map ofn (seq 0 (nz V)))).
  { intros v Hv. apply in_map_iff. exists (nz v). split; [apply ofn_nz|].
    apply in_seq. pose proof (Hl v Hv). unfold nz. pose proof (to_Z_bounded v). lia. }
  pose proof (NoDup_incl_length Hn Hinc) as H.
  rewrite length_map, length_seq in H. pose proof (nz_phi V). lia.
Qed.

Definition before (P : list int) (a b : int) : Prop :=
  exists i j, (i <= j)%nat /\ nth_error P i = Some a /\ nth_error P j = Some b.

Lemma before_app : forall P Q a b, before P a b -> before (P ++ Q) a b.
Proof.
  intros P Q a b (i & j & Hij & Hi & Hj). exists i, j. split; [exact Hij|].
  split; rewrite nth_error_app1; try assumption;
    apply nth_error_Some; congruence.
Qed.

Lemma before_last : forall P a b, In a (P ++ [b]) -> before (P ++ [b]) a b.
Proof.
  intros P a b Ha. apply In_nth_error in Ha as (i & Hi).
  exists i, (List.length P). split.
  - assert (i < List.length (P ++ [b]))%nat by (apply nth_error_Some; congruence).
    rewrite length_app in H. simpl in H. lia.
  - split; [exact Hi|]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma slice0_nth : forall a n L, slice a 0 n = L -> forall k, (k < n)%nat -> a.[ofn k] = nth k L 0.
Proof.
  intros a n L H k Hk. subst L. unfold slice.
  assert (E := map_nth (fun k0 => a.[of_Z (0 + Z.of_nat k0)]) (seq 0 n) 0%nat k). cbn beta in E.
  rewrite (nth_indep _ _ (a.[of_Z (0 + Z.of_nat 0)])) by (rewrite length_map, length_seq; lia).
  rewrite E, seq_nth by lia. unfold ofn. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma slice0_length : forall a n, List.length (slice a 0 n) = n.
Proof. intros. unfold slice. rewrite length_map, length_seq. reflexivity. Qed.

Lemma slice0_extend : forall a n L v, slice a 0 n = L -> (Z.of_nat n < (φ (PArray.length a)))%Z ->
  slice a.[ofn n <- v] 0 (S n) = L ++ [v].
Proof.
  intros a n L v H Hn. rewrite slice_S. rewrite slice_set_out.
  - rewrite H. f_equal. f_equal. rewrite Z.add_0_l. change (of_Z (Z.of_nat n)) with (ofn n).
    apply get_same. rewrite phi_ofn; [lia|].
    pose proof (to_Z_bounded (PArray.length a)). lia.
  - lia.
  - pose proof (len_bound a). lia.
  - right. rewrite phi_ofn; [lia|]. pose proof (to_Z_bounded (PArray.length a)). lia.
Qed.

Lemma slice0_set_out : forall a n L p v, slice a 0 n = L -> (Z.of_nat n <= (φ p))%Z ->
  (Z.of_nat n <= 4194303)%Z -> slice a.[p <- v] 0 n = L.
Proof. intros a n L p v H Hp Hn. rewrite slice_set_out; [exact H | lia | lia | right; lia]. Qed.

Lemma slice0_prefix : forall a n L v, slice a 0 (S n) = L ++ [v] -> slice a 0 n = L /\ a.[ofn n] = v.
Proof.
  intros a n L v H. rewrite slice_S in H. apply app_inj_tail in H as [H1 H2].
  split; [exact H1|]. rewrite <- H2. rewrite Z.add_0_l. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Phase 3 proofs: the first pass of Kosaraju                          *)
(* ------------------------------------------------------------------ *)

Lemma scan_spec : forall mark adj e z j (H : Acc (Zwf 0) (gap e j)), gap e j = z ->
  ((φ j) <= (φ e))%Z ->
  ((φ j) <= (φ (scan mark adj e j H)) <= (φ e))%Z /\
  (forall q, ((φ j) <= (φ q) < (φ (scan mark adj e j H)))%Z -> mark.[adj.[q]] <> 0) /\
  (((φ (scan mark adj e j H)) < (φ e))%Z -> mark.[adj.[scan mark adj e j H]] = 0).
Proof.
  intros mark adj e z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j H Hz Hj. destruct H as [Hacc]. cbn [scan].
  destruct (bdec (j <? e)) as [Hlt | Hge].
  - destruct (mark.[adj.[j]] =? 0) eqn:E0.
    + apply eqb_true in E0. split; [lia|]. split; [intros q Hq; lia|]. intros _. exact E0.
    + apply eqb_false in E0. destruct (step_le e j Hlt) as [E1 E2]. gen_acc.
      destruct (IH (gap e (j + 1)) ltac:(unfold Zwf, gap in *; lia) (j + 1) Hn eq_refl ltac:(lia))
        as (A1 & A2 & A3).
      split; [lia|]. split; [|exact A3].
      intros q Hq. destruct (Z.eq_dec (φ q) (φ j)) as [Eq | Ne].
      * apply phi_eq in Eq. subst. exact E0.
      * apply A2. lia.
  - rewrite ltb_false in Hge. split; [lia|]. split; [intros q Hq; lia|]. intros F. lia.
Qed.

Lemma first_exit : forall (E : int -> int -> Prop) (L : list int) y x,
  clos_refl_trans int E y x -> In y L -> ~ In x L ->
  exists z1 z2, In z1 L /\ clos_refl_trans int E y z1 /\ E z1 z2 /\ ~ In z2 L.
Proof.
  intros E L y x H. apply clos_rt_rt1n in H. induction H as [y | y y1 x Hy Hr IH]; intros Hin Hout.
  - contradiction.
  - destruct (in_dec idec y1 L) as [Hy1 | Hy1].
    + destruct (IH Hy1 Hout) as (z1 & z2 & A & B & C & D).
      exists z1, z2. repeat split; try assumption.
      eapply rt_trans; [apply rt_step; exact Hy | exact B].
    + exists y, y1. repeat split; try assumption. apply rt_refl.
Qed.

Lemma nth_in_app1 : forall (l1 l2 : list int) i, (i < List.length l1)%nat ->
  nth i (l1 ++ l2) 0 = nth i l1 0.
Proof. intros. apply app_nth1. exact H. Qed.

Lemma nth_last : forall (l : list int) a, nth (List.length l) (l ++ [a]) 0 = a.
Proof. intros. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma one_nz : (1 : int) <> 0.
Proof. intro H. apply (f_equal to_Z) in H. change (φ 1) with 1%Z in H. change (φ 0) with 0%Z in H. discriminate. Qed.

Ltac one0 := match goal with
  | F : (1 : int) = 0 |- _ => exfalso; exact (one_nz F)
  | |- (1 : int) <> 0 => exact one_nz
  | |- (1 : int) = 0 -> _ => let F := fresh in intro F; exfalso; exact (one_nz F)
  end.

Lemma ofn_0 : ofn 0 = 0.
Proof. reflexivity. Qed.

Lemma nodup_perm_mid : forall (S P : list int) w,
  NoDup (S ++ P) -> ~ In w (S ++ P) -> NoDup ((S ++ [w]) ++ P).
Proof.
  intros S P w H1 H2. rewrite <- app_assoc. simpl.
  apply (Permutation_NoDup (Permutation_middle S P w)). constructor; assumption.
Qed.

Lemma nodup_pop : forall (S0 P : list int) u,
  NoDup ((S0 ++ [u]) ++ P) -> NoDup (S0 ++ P ++ [u]).
Proof.
  intros S0 P u H. rewrite <- app_assoc in H. simpl in H.
  apply (Permutation_NoDup (Permutation_sym (Permutation_middle S0 P u))) in H.
  apply (Permutation_NoDup (l := u :: S0 ++ P)); [|exact H].
  rewrite app_assoc. apply Permutation_cons_append.
Qed.

Section Pass1.
Variables (V : int) (off adj : array int) (E : int -> int -> Prop).
Hypothesis HV : ((φ V) <= 4194302)%Z.
Hypothesis Hoff : forall u, ((φ u) < (φ V))%Z -> ((φ (off.[u])) <= (φ (off.[u + 1])))%Z.
Hypothesis Hsound : forall u j, ((φ u) < (φ V))%Z -> ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
  E u (adj.[j]).
Hypothesis Hcomp : forall u v, E u v ->
  exists j, ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z /\ adj.[j] = v.
Hypothesis HEV : forall u v, E u v -> ((φ u) < (φ V))%Z /\ ((φ v) < (φ V))%Z.

Notation R := (clos_refl_trans int E).

Record D1inv (s : d1) (S P : list int) : Prop := {
  d_lmk : PArray.length (mk s) = V;
  d_lsv : PArray.length (sv s) = V;
  d_lsc : PArray.length (sc s) = V;
  d_lpo : PArray.length (po s) = V;
  d_sp : (φ (sp s)) = Z.of_nat (List.length S);
  d_np : (φ (np s)) = Z.of_nat (List.length P);
  d_ssv : slice (sv s) 0 (List.length S) = S;
  d_spo : slice (po s) 0 (List.length P) = P;
  d_nd : NoDup (S ++ P);
  d_bnd : forall v, In v (S ++ P) -> ((φ v) < (φ V))%Z;
  d_mk : forall v, ((φ v) < (φ V))%Z -> ((mk s).[v] = 0 <-> ~ In v (S ++ P));
  d_path : forall i j, (i <= j < List.length S)%nat -> R (nth i S 0) (nth j S 0);
  d_cur : forall t, (t < List.length S)%nat ->
    ((φ (off.[nth t S 0%uint63])) <= (φ ((sc s).[ofn t])) <= (φ (off.[(nth t S 0%uint63 + 1)%uint63])))%Z /\
    forall j, ((φ (off.[nth t S 0%uint63])) <= (φ j) < (φ ((sc s).[ofn t])))%Z -> (mk s).[adj.[j]] <> 0;
  d_cl : forall b w, In b P -> E b w -> In w (S ++ P);
  d_f : forall b w, In b P -> In w P -> R b w ->
    exists b', R b b' /\ R b' b /\ (In b' S \/ before P w b');
  d_d : forall b w, In b P -> R b w -> ~ In w P -> exists g, In g S /\ R b g /\ R g b;
  d_rt : ((φ (rt s)) <= (φ V))%Z;
  d_rtin : forall v, ((φ v) < (φ (rt s)))%Z -> In v (S ++ P)
}.

Definition Phi (s : d1) (S P : list int) : Z :=
  (3 * (φ V) - (φ (rt s)) - Z.of_nat (List.length S) - 2 * Z.of_nat (List.length P))%Z.

Lemma d1_size : forall s S P, D1inv s S P ->
  (Z.of_nat (List.length S) + Z.of_nat (List.length P) <= (φ V))%Z.
Proof.
  intros s S P D. pose proof (nodup_bound V (S ++ P) (d_nd _ _ _ D) (d_bnd _ _ _ D)).
  rewrite length_app in H. lia.
Qed.

Lemma phi_pos : forall s S P, D1inv s S P -> (S <> [] \/ ((φ (rt s)) < (φ V))%Z) -> (1 <= Phi s S P)%Z.
Proof.
  intros s S P D H. pose proof (d1_size s S P D). pose proof (d_rt _ _ _ D). unfold Phi.
  destruct H as [H | H]; [|lia].
  destruct S; [congruence|]. simpl List.length in *. lia.
Qed.

Lemma sp_ofn : forall (x : int) n, (φ x) = Z.of_nat n -> x = ofn n.
Proof.
  intros x n H. apply phi_eq. rewrite phi_ofn; [lia|]. rewrite <- H. apply to_Z_bounded.
Qed.

Lemma in_S_reach_top : forall s S0 u P, D1inv s (S0 ++ [u]) P ->
  forall g, In g (S0 ++ [u]) -> R g u.
Proof.
  intros s S0 u P D g Hg. apply In_nth with (d := 0) in Hg as (i & Hi & Hgi).
  rewrite <- Hgi. rewrite <- (nth_last S0 u) at 2.
  apply (d_path _ _ _ D). rewrite length_app in *. simpl in *. lia.
Qed.

(* Case 1: a white successor of the top is pushed. *)
Lemma step_push : forall s S0 u P j,
  D1inv s (S0 ++ [u]) P ->
  ((φ ((sc s).[ofn (List.length S0)])) <= (φ j) < (φ (off.[u + 1])))%Z ->
  (forall q, ((φ ((sc s).[ofn (List.length S0)])) <= (φ q) < (φ j))%Z -> (mk s).[adj.[q]] <> 0) ->
  (mk s).[adj.[j]] = 0 ->
  D1inv (D1 (mk s).[adj.[j] <- 1] (sv s).[sp s <- adj.[j]]
            (sc s).[ofn (List.length S0) <- j + 1].[sp s <- off.[adj.[j]]]
            (po s) (sp s + 1) (np s) (rt s))
        ((S0 ++ [u]) ++ [adj.[j]]) P.
Proof.
  intros s S0 u P j D Hj Hpre Hw.
  set (St := S0 ++ [u]) in *.
  set (w := adj.[j]) in *.
  assert (LS : List.length St = S (List.length S0)) by (unfold St; rewrite length_app; simpl; lia).
  assert (Hu : In u St) by (unfold St; apply in_or_app; right; left; reflexivity).
  assert (HuV : ((φ u) < (φ V))%Z) by (apply (d_bnd _ _ _ D); apply in_or_app; left; exact Hu).
  assert (Hnu : nth (List.length S0) St 0 = u) by apply nth_last.
  destruct (d_cur _ _ _ D (List.length S0) ltac:(lia)) as [[C1 C2] C3].
  rewrite Hnu in C1, C2, C3.
  assert (Euw : E u w) by (apply Hsound; [exact HuV | lia]).
  destruct (HEV u w Euw) as [_ HwV].
  assert (Hnw : ~ In w (St ++ P)) by (apply (d_mk _ _ _ D w HwV); exact Hw).
  pose proof (d1_size s St P D) as Hsz.
  assert (Hsz' : (Z.of_nat (List.length St) + 1 + Z.of_nat (List.length P) <= (φ V))%Z).
  { pose proof (nodup_bound V ((St ++ [w]) ++ P) (nodup_perm_mid St P w (d_nd _ _ _ D) Hnw)) as B.
    rewrite !length_app in B. simpl in B.
    assert (Z.of_nat (List.length St + 1 + List.length P) <= (φ V))%Z.
    { apply B. intros v Hv. rewrite !in_app_iff in Hv. destruct Hv as [[Hv | [Hv | []]] | Hv].
      - apply (d_bnd _ _ _ D). apply in_or_app. left. exact Hv.
      - rewrite <- Hv. exact HwV.
      - apply (d_bnd _ _ _ D). apply in_or_app. right. exact Hv. }
    lia. }
  assert (Hsp : sp s = ofn (List.length St)) by (apply sp_ofn; exact (d_sp _ _ _ D)).
  assert (HspZ : (φ (sp s)) = Z.of_nat (List.length St)) by exact (d_sp _ _ _ D).
  assert (Hlt : (Z.of_nat (List.length St) < (φ V))%Z) by lia.
  assert (Ht : (φ (ofn (List.length S0))) = Z.of_nat (List.length S0))
    by (apply phi_ofn; rewrite wB_val; lia).
  assert (Hts : (φ (ofn (List.length St))) = Z.of_nat (List.length St))
    by (apply phi_ofn; rewrite wB_val; lia).
  assert (Hmk : forall v, (mk s).[w <- 1].[v] = if (w =? v) then 1 else (mk s).[v]).
  { intros v. destruct (w =? v) eqn:Ev.
    - apply eqb_true in Ev. subst v. apply get_same. rewrite (d_lmk _ _ _ D). exact HwV.
    - apply eqb_false in Ev. apply get_other. exact Ev. }
  assert (Hmk_nz : forall v, (mk s).[v] <> 0 -> (mk s).[w <- 1].[v] <> 0).
  { intros v Hv. rewrite Hmk. destruct (w =? v); [one0 | exact Hv]. }
  assert (Hinw : forall v, In v (St ++ P) -> In v ((St ++ [w]) ++ P)).
  { intros v. rewrite !in_app_iff. tauto. }
  constructor; cbn [mk sv sc po sp np rt].
  - rewrite len_set. exact (d_lmk _ _ _ D).
  - rewrite len_set. exact (d_lsv _ _ _ D).
  - rewrite !len_set. exact (d_lsc _ _ _ D).
  - exact (d_lpo _ _ _ D).
  - rewrite length_app. simpl. rewrite phi_add1 by lia. lia.
  - exact (d_np _ _ _ D).
  - rewrite length_app. simpl. rewrite Nat.add_1_r. rewrite Hsp.
    apply slice0_extend; [exact (d_ssv _ _ _ D) | rewrite (d_lsv _ _ _ D); lia].
  - exact (d_spo _ _ _ D).
  - apply nodup_perm_mid; [exact (d_nd _ _ _ D) | exact Hnw].
  - intros v Hv. rewrite !in_app_iff in Hv. destruct Hv as [[Hv | [Hv | []]] | Hv].
    + apply (d_bnd _ _ _ D). apply in_or_app. left. exact Hv.
    + rewrite <- Hv. exact HwV.
    + apply (d_bnd _ _ _ D). apply in_or_app. right. exact Hv.
  - intros v Hv. rewrite Hmk. destruct (w =? v) eqn:Ev.
    + apply eqb_true in Ev. rewrite <- Ev. split; [one0|].
      intros F. exfalso. apply F. rewrite !in_app_iff. simpl. tauto.
    + apply eqb_false in Ev. rewrite (d_mk _ _ _ D v Hv). rewrite !in_app_iff. simpl.
      split; intros F G; apply F; [|tauto].
      destruct G as [[G | [G | []]] | G]; [tauto | congruence | tauto].
  - intros i k Hik. rewrite length_app in Hik. simpl in Hik.
    destruct (Nat.eq_dec k (List.length St)) as [Ek | Ek].
    + subst k. rewrite nth_last.
      destruct (Nat.eq_dec i (List.length St)) as [Ei | Ei].
      * subst i. rewrite nth_last. apply rt_refl.
      * rewrite nth_in_app1 by lia.
        eapply rt_trans; [|apply rt_step; exact Euw].
        rewrite <- Hnu. apply (d_path _ _ _ D). lia.
    + rewrite !nth_in_app1 by lia. apply (d_path _ _ _ D). lia.
  - intros t Ht'. rewrite length_app in Ht'. simpl in Ht'.
    destruct (Nat.eq_dec t (List.length St)) as [Et | Et].
    + subst t. rewrite nth_last. rewrite Hsp. rewrite get_same
        by (rewrite !len_set, (d_lsc _ _ _ D), Hts; lia).
      split; [pose proof (Hoff w HwV); lia|]. intros q Hq. lia.
    + rewrite nth_in_app1 by lia.
      rewrite get_other_phi by (rewrite Hsp, Hts, phi_ofn; [lia | rewrite wB_val; lia]).
      destruct (Nat.eq_dec t (List.length S0)) as [Et0 | Et0].
      * subst t. rewrite Hnu. rewrite get_same by (rewrite (d_lsc _ _ _ D), Ht; lia).
        rewrite (phi_add1_lt j (off.[u + 1])) by lia. split; [lia|].
        intros q Hq.
        destruct (Z.lt_ge_cases (φ q) (φ ((sc s).[ofn (List.length S0)]))) as [Lq | Gq].
        -- apply Hmk_nz. apply C3. lia.
        -- destruct (Z.eq_dec (φ q) (φ j)) as [Eq | Nq].
           ++ apply phi_eq in Eq. subst q. rewrite Hmk.
              rewrite (proj2 (eqb_true w adj.[j]) eq_refl). one0.
           ++ apply Hmk_nz. apply (Hpre q). lia.
      * rewrite get_other_phi by (rewrite Ht, phi_ofn; [lia | rewrite wB_val; lia]).
        destruct (d_cur _ _ _ D t ltac:(lia)) as [B1 B2]. split; [exact B1|].
        intros q Hq. apply Hmk_nz. apply B2. exact Hq.
  - intros b x Hb Hbx. apply Hinw. exact (d_cl _ _ _ D b x Hb Hbx).
  - intros b x Hb Hx Hbx. destruct (d_f _ _ _ D b x Hb Hx Hbx) as (b' & B1 & B2 & B3).
    exists b'. split; [exact B1|]. split; [exact B2|].
    destruct B3 as [B3 | B3]; [left; apply in_or_app; left; exact B3 | right; exact B3].
  - intros b x Hb Hbx Hx. destruct (d_d _ _ _ D b x Hb Hbx Hx) as (g & G1 & G2 & G3).
    exists g. split; [apply in_or_app; left; exact G1|]. split; assumption.
  - exact (d_rt _ _ _ D).
  - intros v Hv. apply Hinw. exact (d_rtin _ _ _ D v Hv).
Qed.


Lemma in_dec_nn : forall v (L : list int), ~ ~ In v L -> In v L.
Proof. intros v L H. destruct (in_dec idec v L); [assumption | contradiction]. Qed.

(* Case 2: the top has no white successor left; it is finished. *)
Lemma step_pop : forall s S0 u P,
  D1inv s (S0 ++ [u]) P ->
  (forall q, ((φ ((sc s).[ofn (List.length S0)])) <= (φ q) < (φ (off.[u + 1])))%Z -> (mk s).[adj.[q]] <> 0) ->
  D1inv (D1 (mk s) (sv s) (sc s) (po s).[np s <- u] (sp s - 1) (np s + 1) (rt s))
        S0 (P ++ [u]).
Proof.
  intros s S0 u P D Hrest.
  set (St := S0 ++ [u]) in *.
  assert (LS : List.length St = S (List.length S0)) by (unfold St; rewrite length_app; simpl; lia).
  assert (Hu : In u St) by (unfold St; apply in_or_app; right; left; reflexivity).
  assert (HuV : ((φ u) < (φ V))%Z) by (apply (d_bnd _ _ _ D); apply in_or_app; left; exact Hu).
  assert (Hnu : nth (List.length S0) St 0 = u) by apply nth_last.
  destruct (d_cur _ _ _ D (List.length S0) ltac:(lia)) as [[C1 C2] C3].
  rewrite Hnu in C1, C2, C3.
  assert (Hall : forall q, ((φ (off.[u])) <= (φ q) < (φ (off.[u + 1])))%Z -> (mk s).[adj.[q]] <> 0).
  { intros q Hq. destruct (Z.lt_ge_cases (φ q) (φ ((sc s).[ofn (List.length S0)]))).
    - apply C3. lia.
    - apply Hrest. lia. }
  assert (Hsucc : forall w, E u w -> In w (St ++ P)).
  { intros w Hw. destruct (Hcomp u w Hw) as (q & Hq & Hqw).
    destruct (HEV u w Hw) as [_ HwV]. apply in_dec_nn. intros F.
    apply (Hall q Hq). rewrite Hqw. apply (d_mk _ _ _ D w HwV). exact F. }
  assert (HuP : ~ In u P).
  { intros F. pose proof (d_nd _ _ _ D) as N. unfold St in N. rewrite <- app_assoc in N.
    apply NoDup_remove_2 in N. apply N. apply in_or_app. right. exact F. }
  assert (Hset : forall v, In v (S0 ++ P ++ [u]) <-> In v (St ++ P)).
  { intros v. unfold St. rewrite !in_app_iff. simpl. tauto. }
  pose proof (d1_size s St P D) as Hsz.
  assert (Hnp : np s = ofn (List.length P)) by (apply sp_ofn; exact (d_np _ _ _ D)).
  assert (HS0reach : forall g, In g S0 -> R g u).
  { intros g Hg. apply (in_S_reach_top s S0 u P D). apply in_or_app. left. exact Hg. }
  (* the new closure *)
  assert (Hcl' : forall b w, In b (P ++ [u]) -> E b w -> In w (S0 ++ P ++ [u])).
  { intros b w Hb Hbw. apply Hset. apply in_app_iff in Hb as [Hb | [Hb | []]].
    - exact (d_cl _ _ _ D b w Hb Hbw).
    - subst b. apply Hsucc. exact Hbw. }
  assert (Hexit : forall x, R u x -> ~ In x (P ++ [u]) -> exists g, In g S0 /\ R u g /\ R g u).
  { intros x Hux Hx.
    destruct (first_exit E (P ++ [u]) u x Hux ltac:(apply in_or_app; right; left; reflexivity) Hx)
      as (z1 & z2 & Z1 & Z2 & Z3 & Z4).
    pose proof (Hcl' z1 z2 Z1 Z3) as Hz2. rewrite !in_app_iff in Hz2.
    assert (Hz2S : In z2 S0).
    { destruct Hz2 as [H | [H | H]]; [exact H | | ]; exfalso; apply Z4; apply in_app_iff; tauto. }
    exists z2. split; [exact Hz2S|]. split; [|exact (HS0reach z2 Hz2S)].
    eapply rt_trans; [exact Z2 | apply rt_step; exact Z3]. }
  constructor; cbn [mk sv sc po sp np rt].
  - exact (d_lmk _ _ _ D).
  - exact (d_lsv _ _ _ D).
  - exact (d_lsc _ _ _ D).
  - rewrite len_set. exact (d_lpo _ _ _ D).
  - rewrite phi_sub1 by (rewrite (d_sp _ _ _ D); lia). rewrite (d_sp _ _ _ D). change (φ 1) with 1%Z. lia.
  - rewrite length_app. simpl. rewrite phi_add1 by (rewrite (d_np _ _ _ D); lia).
    rewrite (d_np _ _ _ D). lia.
  - pose proof (d_ssv _ _ _ D) as H. rewrite LS in H. unfold St in H.
    exact (proj1 (slice0_prefix _ _ _ _ H)).
  - rewrite length_app. simpl. rewrite Nat.add_1_r. rewrite Hnp.
    apply slice0_extend; [exact (d_spo _ _ _ D) | rewrite (d_lpo _ _ _ D); lia].
  - apply nodup_pop. exact (d_nd _ _ _ D).
  - intros v Hv. apply (d_bnd _ _ _ D). apply Hset. exact Hv.
  - intros v Hv. rewrite (d_mk _ _ _ D v Hv). rewrite Hset. tauto.
  - intros i j Hij.
    replace (nth i S0 0) with (nth i St 0) by (unfold St; apply nth_in_app1; lia).
    replace (nth j S0 0) with (nth j St 0) by (unfold St; apply nth_in_app1; lia).
    apply (d_path _ _ _ D). lia.
  - intros t Ht. replace (nth t S0 0) with (nth t St 0) by (unfold St; apply nth_in_app1; lia).
    apply (d_cur _ _ _ D t). lia.
  - exact Hcl'.
  - intros b w Hb Hw Hbw. apply in_app_iff in Hb as [Hb | [Hb | []]].
    + apply in_app_iff in Hw as [Hw | [Hw | []]].
      * destruct (d_f _ _ _ D b w Hb Hw Hbw) as (b' & B1 & B2 & B3).
        exists b'. split; [exact B1|]. split; [exact B2|].
        destruct B3 as [B3 | B3].
        -- unfold St in B3. apply in_app_iff in B3 as [B3 | [B3 | []]].
           ++ left. exact B3.
           ++ subst b'. right. apply before_last. apply in_or_app. left. exact Hw.
        -- right. apply before_app. exact B3.
      * subst w. destruct (d_d _ _ _ D b u Hb Hbw HuP) as (g & G1 & G2 & G3).
        unfold St in G1. apply in_app_iff in G1 as [G1 | [G1 | []]].
        -- exists g. split; [exact G2|]. split; [exact G3|]. left. exact G1.
        -- subst g. exists u. split; [exact G2|]. split; [exact G3|]. right.
           apply before_last. apply in_or_app. right. left. reflexivity.
    + subst b. exists u. split; [apply rt_refl|]. split; [apply rt_refl|].
      right. apply before_last. exact Hw.
  - intros b w Hb Hbw Hw. apply in_app_iff in Hb as [Hb | [Hb | []]].
    + assert (HwP : ~ In w P) by (intros F; apply Hw; apply in_or_app; left; exact F).
      destruct (d_d _ _ _ D b w Hb Hbw HwP) as (g & G1 & G2 & G3).
      unfold St in G1. apply in_app_iff in G1 as [G1 | [G1 | []]].
      * exists g. split; [exact G1|]. split; assumption.
      * subst g. destruct (Hexit w (rt_trans _ _ _ _ _ G3 Hbw) Hw) as (g' & H1 & H2 & H3).
        exists g'. split; [exact H1|]. split.
        -- eapply rt_trans; [exact G2 | exact H2].
        -- eapply rt_trans; [exact H3 | exact G3].
    + subst b. exact (Hexit w Hbw Hw).
  - exact (d_rt _ _ _ D).
  - intros v Hv. apply Hset. exact (d_rtin _ _ _ D v Hv).
Qed.

(* Case 3: a new root. *)
Lemma step_root : forall s P,
  D1inv s [] P -> ((φ (rt s)) < (φ V))%Z -> (mk s).[rt s] = 0 ->
  D1inv (D1 (mk s).[rt s <- 1] (sv s).[0 <- rt s] (sc s).[0 <- off.[rt s]]
            (po s) 1 (np s) (rt s + 1)) [rt s] P.
Proof.
  intros s P D Hr Hm.
  set (r := rt s) in *.
  assert (HrP : ~ In r P) by (apply (d_mk _ _ _ D r Hr); exact Hm).
  assert (Hmk : forall v, (mk s).[r <- 1].[v] = if (r =? v) then 1 else (mk s).[v]).
  { intros v. destruct (r =? v) eqn:Ev.
    - apply eqb_true in Ev. subst v. apply get_same. rewrite (d_lmk _ _ _ D). exact Hr.
    - apply eqb_false in Ev. apply get_other. exact Ev. }
  assert (HV0 : (0 < (φ V))%Z) by (pose proof (to_Z_bounded r); lia).
  constructor; cbn [mk sv sc po sp np rt].
  - rewrite len_set. exact (d_lmk _ _ _ D).
  - rewrite len_set. exact (d_lsv _ _ _ D).
  - rewrite len_set. exact (d_lsc _ _ _ D).
  - exact (d_lpo _ _ _ D).
  - reflexivity.
  - exact (d_np _ _ _ D).
  - change [r] with ([] ++ [r]). rewrite <- ofn_0.
    apply slice0_extend; [reflexivity | rewrite (d_lsv _ _ _ D); simpl; lia].
  - exact (d_spo _ _ _ D).
  - simpl. constructor; [exact HrP | exact (d_nd _ _ _ D)].
  - intros v Hv. simpl in Hv. destruct Hv as [Hv | Hv]; [subst v; exact Hr|].
    apply (d_bnd _ _ _ D). exact Hv.
  - intros v Hv. rewrite Hmk. destruct (r =? v) eqn:Ev.
    + apply eqb_true in Ev. subst v. split; [one0|]. intros F. exfalso. apply F. left. reflexivity.
    + apply eqb_false in Ev. rewrite (d_mk _ _ _ D v Hv). simpl. split; intros F G; apply F.
      * destruct G as [G | G]; [congruence | exact G].
      * right. exact G.
  - intros i j Hij. simpl in Hij. replace i with 0%nat by lia. replace j with 0%nat by lia.
    apply rt_refl.
  - intros t Ht. simpl in Ht. replace t with 0%nat by lia. simpl nth. rewrite ofn_0.
    rewrite get_same by (rewrite (d_lsc _ _ _ D); lia).
    split; [pose proof (Hoff r Hr); lia|]. intros q Hq. lia.
  - intros b w Hb Hbw. right. exact (d_cl _ _ _ D b w Hb Hbw).
  - intros b w Hb Hw Hbw. destruct (d_f _ _ _ D b w Hb Hw Hbw) as (b' & B1 & B2 & [[] | B3]).
    exists b'. split; [exact B1|]. split; [exact B2|]. right. exact B3.
  - intros b w Hb Hbw Hw. destruct (d_d _ _ _ D b w Hb Hbw Hw) as (g & [] & _).
  - rewrite phi_add1 by lia. lia.
  - intros v Hv. rewrite phi_add1 in Hv by lia.
    destruct (Z.eq_dec (φ v) (φ r)) as [Ev | Ev].
    + apply phi_eq in Ev. subst v. left. reflexivity.
    + right. exact (d_rtin _ _ _ D v ltac:(lia)).
Qed.

(* Case 4: the next root is already visited. *)
Lemma step_skip : forall s P,
  D1inv s [] P -> ((φ (rt s)) < (φ V))%Z -> (mk s).[rt s] <> 0 ->
  D1inv (D1 (mk s) (sv s) (sc s) (po s) (sp s) (np s) (rt s + 1)) [] P.
Proof.
  intros s P D Hr Hm.
  destruct D as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18].
  constructor; cbn [mk sv sc po sp np rt]; try assumption.
  - rewrite phi_add1 by lia. lia.
  - intros v Hv. rewrite phi_add1 in Hv by lia.
    destruct (Z.eq_dec (φ v) (φ (rt s))) as [Ev | Ev].
    + apply phi_eq in Ev. subst v. apply in_dec_nn. intros F. apply Hm. apply A11; assumption.
    + apply A18. lia.
Qed.


Lemma dfs_step_spec : forall s S P, D1inv s S P ->
  match dfs_step V off adj s with
  | Some s' => exists S' P', D1inv s' S' P' /\ (Phi s' S' P' < Phi s S P)%Z
  | None => S = [] /\ (φ (rt s)) = (φ V)
  end.
Proof.
  intros s S P D. unfold dfs_step. cbv zeta.
  destruct (0 <? sp s) eqn:Hsp.
  - rewrite ltb_true in Hsp. change (φ 0) with 0%Z in Hsp.
    assert (HS : S <> []) by (intros ->; rewrite (d_sp _ _ _ D) in Hsp; simpl in Hsp; lia).
    destruct (exists_last HS) as (S0 & u & ->).
    assert (LS : List.length (S0 ++ [u]) = S (List.length S0)) by (rewrite length_app; simpl; lia).
    assert (Ht : sp s - 1 = ofn (List.length S0)).
    { apply phi_eq. rewrite phi_sub1 by lia. rewrite (d_sp _ _ _ D), LS.
      rewrite phi_ofn; [lia|]. pose proof (d1_size s _ _ D). rewrite wB_val. lia. }
    assert (Hu : (sv s).[ofn (List.length S0)] = u).
    { pose proof (d_ssv _ _ _ D) as H. rewrite LS in H.
      exact (proj2 (slice0_prefix _ _ _ _ H)). }
    rewrite Ht, Hu.
    destruct (d_cur _ _ _ D (List.length S0) ltac:(lia)) as [[C1 C2] C3].
    rewrite nth_last in C1, C2, C3.
    destruct (scan_spec (mk s) adj (off.[u + 1]) _ ((sc s).[ofn (List.length S0)])
                (Zwf_well_founded 0 (gap (off.[u + 1]) (sc s).[ofn (List.length S0)])) eq_refl C2)
      as (A1 & A2 & A3).
    set (j := scan (mk s) adj (off.[u + 1]) (sc s).[ofn (List.length S0)]
                (Zwf_well_founded 0 (gap (off.[u + 1]) (sc s).[ofn (List.length S0)]))) in *.
    destruct (j <? off.[u + 1]) eqn:Hj.
    + rewrite ltb_true in Hj.
      exists ((S0 ++ [u]) ++ [adj.[j]]), P. split.
      * apply step_push; [exact D | lia | exact A2 | exact (A3 Hj)].
      * unfold Phi. cbn [rt]. rewrite !length_app. cbn [List.length]. lia.
    + rewrite ltb_false in Hj.
      exists S0, (P ++ [u]). split.
      * rewrite <- Ht. apply step_pop; [exact D|]. intros q Hq. apply A2. lia.
      * unfold Phi. cbn [rt]. rewrite !length_app. cbn [List.length]. lia.
  - rewrite ltb_false in Hsp. change (φ 0) with 0%Z in Hsp.
    assert (HS : S = []).
    { destruct S; [reflexivity|]. pose proof (d_sp _ _ _ D). simpl in H. lia. }
    subst S.
    destruct (rt s <? V) eqn:Hr.
    + rewrite ltb_true in Hr. destruct ((mk s).[rt s] =? 0) eqn:Hm.
      * apply eqb_true in Hm. exists [rt s], P. split.
        -- apply step_root; assumption.
        -- unfold Phi. cbn [rt]. rewrite phi_add1 by lia. cbn [List.length]. lia.
      * apply eqb_false in Hm. exists [], P. split.
        -- apply step_skip; assumption.
        -- unfold Phi. cbn [rt]. rewrite phi_add1 by lia. cbn [List.length]. lia.
    + rewrite ltb_false in Hr. split; [reflexivity|]. pose proof (d_rt _ _ _ D). lia.
Qed.

Lemma dfs_spec : forall bound z steps s S P (H : Acc (Zwf 0) (gap bound steps)),
  gap bound steps = z -> D1inv s S P -> ((φ steps) + Phi s S P <= (φ bound))%Z ->
  exists sf Pf, D1inv sf [] Pf /\ (φ (rt sf)) = (φ V) /\ dfs V off adj s bound steps H = po sf.
Proof.
  intros bound z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros steps s S P H Hz D Hb. destruct H as [Hacc]. cbn [dfs].
  destruct (bdec (steps <? bound)) as [Hlt | Hge].
  - pose proof (dfs_step_spec s S P D) as Hs.
    destruct (dfs_step V off adj s) as [s' |] eqn:Es.
    + destruct Hs as (S' & P' & D' & Hph).
      destruct (step_le bound steps Hlt) as [E1 E2]. gen_acc.
      apply (IH (gap bound (steps + 1)) ltac:(unfold Zwf, gap in *; lia) (steps + 1) s' S' P' Hn eq_refl D').
      lia.
    + destruct Hs as [-> Hr]. exists s, P. split; [exact D|]. split; [exact Hr | reflexivity].
  - rewrite ltb_false in Hge.
    assert (Hd : S <> [] \/ ((φ (rt s)) < (φ V))%Z \/ (S = [] /\ (φ (rt s)) = (φ V))).
    { destruct S; [|left; congruence]. pose proof (d_rt _ _ _ D).
      destruct (Z.lt_ge_cases (φ (rt s)) (φ V)); [right; left; lia | right; right; split; [reflexivity | lia]]. }
    destruct Hd as [Hd | [Hd | [-> Hd]]].
    + exfalso. pose proof (phi_pos s S P D (or_introl Hd)). lia.
    + exfalso. pose proof (phi_pos s S P D (or_intror Hd)). lia.
    + exists s, P. split; [exact D|]. split; [exact Hd | reflexivity].
Qed.


Lemma pass1_final : forall s P, D1inv s [] P -> (φ (rt s)) = (φ V) ->
  List.length P = nz V /\ slice (po s) 0 (nz V) = P /\ NoDup P /\
  (forall v, In v P <-> ((φ v) < (φ V))%Z) /\
  (forall b w, In b P -> R b w -> exists b', R b b' /\ R b' b /\ before P w b').
Proof.
  intros s P D Hr.
  assert (Hin : forall v, In v P <-> ((φ v) < (φ V))%Z).
  { intros v. split.
    - intros Hv. apply (d_bnd _ _ _ D). exact Hv.
    - intros Hv. exact (d_rtin _ _ _ D v ltac:(lia)). }
  assert (Hlen : List.length P = nz V).
  { pose proof (nodup_bound V P (d_nd _ _ _ D) (fun v H => proj1 (Hin v) H)) as B1.
    assert (B2 : (nz V <= List.length P)%nat).
    { replace (nz V) with (List.length (map ofn (seq 0 (nz V)))) by (rewrite length_map, length_seq; reflexivity).
      apply NoDup_incl_length.
      - apply NoDup_map_on; [apply seq_NoDup|]. intros a b Ha Hb E'.
        apply in_seq in Ha, Hb. pose proof (nz_phi V).
        apply (f_equal to_Z) in E'. rewrite !phi_ofn in E' by (rewrite wB_val; lia). lia.
      - intros v Hv. apply in_map_iff in Hv as (k & <- & Hk). apply in_seq in Hk.
        pose proof (nz_phi V). apply Hin. rewrite phi_ofn; [|rewrite wB_val; lia]. lia. }
    pose proof (nz_phi V). lia. }
  split; [exact Hlen|]. split; [rewrite <- Hlen; exact (d_spo _ _ _ D)|].
  split; [exact (d_nd _ _ _ D)|]. split; [exact Hin|].
  intros b w Hb Hbw.
  assert (Hw : In w P).
  { apply in_dec_nn. intros F. destruct (d_d _ _ _ D b w Hb Hbw F) as (g & [] & _). }
  destruct (d_f _ _ _ D b w Hb Hw Hbw) as (b' & B1 & B2 & [[] | B3]).
  exists b'. auto.
Qed.

Lemma pass1_init :
  D1inv (D1 (PArray.make V 0) (PArray.make V 0) (PArray.make V 0) (PArray.make V 0) 0 0 0) [] [].
Proof.
  constructor; cbn [mk sv sc po sp np rt]; try (apply len_make; lia); try reflexivity.
  - constructor.
  - intros v [].
  - intros v Hv. rewrite get_mk. split; [intros _ []|reflexivity].
  - intros i j H. simpl in H. lia.
  - intros t H. simpl in H. lia.
  - intros b w [].
  - intros b w [].
  - intros b w [].
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded V). lia.
  - intros v Hv. change (φ 0) with 0%Z in Hv. pose proof (to_Z_bounded v). lia.
Qed.

Lemma pass1 : exists P,
  List.length P = nz V /\
  slice (dfs V off adj
           (D1 (PArray.make V 0) (PArray.make V 0) (PArray.make V 0) (PArray.make V 0) 0 0 0)
           (3 * V + 1) 0 (Zwf_well_founded 0 (gap (3 * V + 1) 0))) 0 (nz V) = P /\
  NoDup P /\ (forall v, In v P <-> ((φ v) < (φ V))%Z) /\
  (forall b w, In b P -> R b w -> exists b', R b b' /\ R b' b /\ before P w b').
Proof.
  destruct (dfs_spec (3 * V + 1) _ 0 _ [] [] (Zwf_well_founded 0 (gap (3 * V + 1) 0)) eq_refl pass1_init)
    as (sf & Pf & Df & Hr & Eq).
  - unfold Phi. cbn [rt List.length]. change (φ 0) with 0%Z.
    assert ((φ (3 * V + 1)) = 3 * (φ V) + 1)%Z by sia. lia.
  - rewrite Eq. exists Pf. exact (pass1_final sf Pf Df Hr).
Qed.

End Pass1.

(* ------------------------------------------------------------------ *)
(* Phase 4 proofs: the second pass of Kosaraju                         *)
(* ------------------------------------------------------------------ *)

Section Pass2.
Variables (V : int) (roff radj : array int) (E : int -> int -> Prop) (P : list int).
Hypothesis HV : ((φ V) <= 4194302)%Z.
Hypothesis Hroff : forall u, ((φ u) < (φ V))%Z -> ((φ (roff.[u])) <= (φ (roff.[u + 1])))%Z.
Hypothesis Hrsound : forall u j, ((φ u) < (φ V))%Z -> ((φ (roff.[u])) <= (φ j) < (φ (roff.[u + 1])))%Z ->
  E (radj.[j]) u.
Hypothesis Hrcomp : forall u v, E v u ->
  exists j, ((φ (roff.[u])) <= (φ j) < (φ (roff.[u + 1])))%Z /\ radj.[j] = v.
Hypothesis HEV : forall u v, E u v -> ((φ u) < (φ V))%Z /\ ((φ v) < (φ V))%Z.
Hypothesis HPl : List.length P = nz V.
Hypothesis HPnd : NoDup P.
Hypothesis HPin : forall v, In v P <-> ((φ v) < (φ V))%Z.
Hypothesis HPf : forall b w, In b P -> clos_refl_trans int E b w ->
  exists b', clos_refl_trans int E b b' /\ clos_refl_trans int E b' b /\ before P w b'.

Notation R := (clos_refl_trans int E).

Record D2core (s : d2) (Sk Lb : list int) (rC : int) (pr : nat) (pend : list int) : Prop := {
  e_llb : PArray.length (lb s) = V;
  e_lsk : PArray.length (sk s) = V;
  e_sq : (φ (sq s)) = Z.of_nat (List.length Sk);
  e_ssk : slice (sk s) 0 (List.length Sk) = Sk;
  e_ii : ((φ (ii s)) <= (φ V))%Z;
  e_cc : ((φ (cc s)) + (φ (ii s)) <= (φ V))%Z;
  e_lab : forall v, ((φ v) < (φ V))%Z -> ((φ ((lb s).[v])) <= (φ (cc s)))%Z;
  e_Lbnd : NoDup Lb;
  e_Lbin : forall v, In v Lb -> ((φ v) < (φ V))%Z;
  e_Lb : forall v, ((φ v) < (φ V))%Z -> ((lb s).[v] <> 0 <-> In v Lb);
  e_P1 : forall k, (nz (ii s) <= k < nz V)%nat -> (lb s).[nth k P 0] <> 0;
  e_cur0 : (φ (cc s)) = 0%Z -> Sk = [] /\ (forall v, ((φ v) < (φ V))%Z -> (lb s).[v] = 0);
  e_cur : (φ (cc s)) <> 0%Z -> rC = nth pr P 0 /\ (nz (ii s) <= pr < nz V)%nat /\ (lb s).[rC] = cc s;
  e_S1 : forall v, ((φ v) < (φ V))%Z -> (lb s).[v] = cc s -> (φ (cc s)) <> 0%Z -> R v rC /\ R rC v;
  e_S2 : forall v, ((φ v) < (φ V))%Z -> (lb s).[v] = cc s -> (φ (cc s)) <> 0%Z -> ~ In v pend ->
           forall w, E w v -> (lb s).[w] <> 0;
  e_S3nd : NoDup Sk;
  e_S3 : forall v, In v Sk -> ((φ v) < (φ V))%Z /\ (lb s).[v] = cc s;
  e_S4 : forall v w, ((φ v) < (φ V))%Z -> ((φ w) < (φ V))%Z -> (lb s).[v] <> 0 ->
           ((φ ((lb s).[v])) < (φ (cc s)))%Z -> ((lb s).[w] = (lb s).[v] <-> (R v w /\ R w v))
}.

Lemma nth_P_in : forall k, (k < nz V)%nat -> ((φ (nth k P 0%uint63)) < (φ V))%Z.
Proof. intros k Hk. apply HPin. apply nth_In. lia. Qed.

(* a vertex reaching the current root, if unlabeled, belongs to its component *)
Lemma reach_root_mutual : forall s Sk Lb rC pr pend w,
  D2core s Sk Lb rC pr pend -> (φ (cc s)) <> 0%Z -> ((φ w) < (φ V))%Z ->
  (lb s).[w] = 0 -> R w rC -> R rC w.
Proof.
  intros s Sk Lb rC pr pend w D Hc Hw H0 Hwr.
  destruct (e_cur _ _ _ _ _ _ D Hc) as (Er & Hpr & Lr).
  destruct (HPf w rC (proj2 (HPin w) Hw) Hwr) as (w' & W1 & W2 & (i & j & Hij & Hi & Hj)).
  assert (Hi' : i = pr).
  { assert (Hpr' : nth_error P pr = Some rC).
    { rewrite Er. apply nth_error_nth'. lia. }
    eapply NoDup_nth_error; [exact HPnd | apply nth_error_Some; congruence | congruence]. }
  subst i.
  destruct (Nat.eq_dec j pr) as [Ej | Ej].
  - subst j. rewrite Hj in Hi. injection Hi as ->. exact W2.
  - assert (Hjl : (j < nz V)%nat) by (rewrite <- HPl; apply nth_error_Some; congruence).
    assert (Ew' : nth j P 0 = w') by (apply nth_error_nth; exact Hj).
    pose proof (e_P1 _ _ _ _ _ _ D j ltac:(lia)) as Hl. rewrite Ew' in Hl.
    assert (Hw'V : ((φ w') < (φ V))%Z) by (rewrite <- Ew'; apply nth_P_in; exact Hjl).
    pose proof (e_lab _ _ _ _ _ _ D w' Hw'V) as Hle.
    destruct (idec ((lb s).[w']) (cc s)) as [Ec | Ec].
    + destruct (e_S1 _ _ _ _ _ _ D w' Hw'V Ec Hc) as [_ H2]. eapply rt_trans; [exact H2 | exact W2].
    + exfalso. assert (Hlt : ((φ ((lb s).[w'])) < (φ (cc s)))%Z).
      { assert ((φ ((lb s).[w'])) <> (φ (cc s))) by (intro F; apply Ec; apply phi_eq; exact F). lia. }
      pose proof (proj2 (e_S4 _ _ _ _ _ _ D w' w Hw'V Hw Hl Hlt) (conj W2 W1)) as Hww.
      rewrite H0 in Hww. apply Hl. symmetry. exact Hww.
Qed.


Lemma d2_size : forall s Sk Lb rC pr pend, D2core s Sk Lb rC pr pend ->
  (Z.of_nat (List.length Lb) <= (φ V))%Z.
Proof.
  intros s Sk Lb rC pr pend D. apply (nodup_bound V Lb (e_Lbnd _ _ _ _ _ _ D) (e_Lbin _ _ _ _ _ _ D)).
Qed.

Lemma pp_push : forall lab stk sp i c Sk Lb rC pr u w,
  D2core (D2 lab stk sp i c) Sk Lb rC pr (u :: Sk) ->
  (φ c) <> 0%Z -> ((φ u) < (φ V))%Z -> lab.[u] = c -> E w u -> lab.[w] = 0 ->
  D2core (D2 lab.[w <- c] stk.[sp <- w] (sp + 1) i c) (Sk ++ [w]) (w :: Lb) rC pr (u :: Sk ++ [w]).
Proof.
  intros lab stk sp i c Sk Lb rC pr u w D Hc Hu Hlu Ewu Hw0.
  destruct (HEV w u Ewu) as [HwV _].
  pose proof (e_llb _ _ _ _ _ _ D) as Lll. pose proof (e_lsk _ _ _ _ _ _ D) as Lsk.
  pose proof (e_sq _ _ _ _ _ _ D) as Lsq. cbn [lb sk sq] in Lll, Lsk, Lsq.
  assert (Hmut : R w rC /\ R rC w).
  { destruct (e_S1 _ _ _ _ _ _ D u Hu Hlu Hc) as [U1 U2].
    assert (R w rC) by (eapply rt_trans; [apply rt_step; exact Ewu | exact U1]).
    split; [assumption|]. eapply reach_root_mutual; eassumption. }
  assert (HwSk : ~ In w Sk).
  { intros F. destruct (e_S3 _ _ _ _ _ _ D w F) as [_ F2]. cbn [lb cc] in F2.
    rewrite Hw0 in F2. apply Hc. rewrite <- F2. reflexivity. }
  assert (HwLb : ~ In w Lb).
  { intros F. apply (e_Lb _ _ _ _ _ _ D w HwV) in F. cbn [lb] in F. contradiction. }
  assert (Hsz : (Z.of_nat (List.length Sk) + 1 <= (φ V))%Z).
  { pose proof (nodup_bound V (Sk ++ [w])) as B. rewrite length_app in B. simpl in B.
    assert (Z.of_nat (List.length Sk + 1) <= (φ V))%Z; [|lia]. apply B.
    - apply (Permutation_NoDup (Permutation_cons_append Sk w)). constructor; [exact HwSk | exact (e_S3nd _ _ _ _ _ _ D)].
    - intros v Hv. apply in_app_iff in Hv as [Hv | [Hv | []]].
      + exact (proj1 (e_S3 _ _ _ _ _ _ D v Hv)).
      + subst. exact HwV. }
  assert (Hsp : sp = ofn (List.length Sk)).
  { apply phi_eq. rewrite phi_ofn by (rewrite wB_val; lia). exact Lsq. }
  assert (Hlab : forall v, lab.[w <- c].[v] = if w =? v then c else lab.[v]).
  { intros v. destruct (w =? v) eqn:Ev.
    - apply eqb_true in Ev. subst v. apply get_same. rewrite Lll. exact HwV.
    - apply eqb_false in Ev. apply get_other. exact Ev. }
  assert (Hcnz : c <> 0) by (intros F; apply Hc; rewrite F; reflexivity).
  assert (Hkeep : forall v, lab.[v] <> 0 -> lab.[w <- c].[v] <> 0).
  { intros v Hv. rewrite Hlab. destruct (w =? v); assumption. }
  constructor; cbn [lb sk sq ii cc].
  - rewrite len_set. exact (e_llb _ _ _ _ _ _ D).
  - rewrite len_set. exact (e_lsk _ _ _ _ _ _ D).
  - rewrite length_app. simpl. rewrite phi_add1 by (rewrite Lsq; lia).
    rewrite Lsq. lia.
  - rewrite length_app. simpl. rewrite Nat.add_1_r. rewrite Hsp.
    apply slice0_extend; [exact (e_ssk _ _ _ _ _ _ D) | rewrite Lsk; lia].
  - exact (e_ii _ _ _ _ _ _ D).
  - exact (e_cc _ _ _ _ _ _ D).
  - intros v Hv. rewrite Hlab. destruct (w =? v); [lia | exact (e_lab _ _ _ _ _ _ D v Hv)].
  - constructor; [exact HwLb | exact (e_Lbnd _ _ _ _ _ _ D)].
  - intros v [Hv | Hv]; [subst; exact HwV | exact (e_Lbin _ _ _ _ _ _ D v Hv)].
  - intros v Hv. rewrite Hlab. destruct (w =? v) eqn:Ev.
    + apply eqb_true in Ev. subst v. split; [intros _; left; reflexivity | intros _; exact Hcnz].
    + apply eqb_false in Ev. pose proof (e_Lb _ _ _ _ _ _ D v Hv) as LbI. cbn [lb] in LbI.
      rewrite LbI. simpl. split; [tauto|].
      intros [F | F]; [congruence | exact F].
  - intros k Hk. apply Hkeep. exact (e_P1 _ _ _ _ _ _ D k Hk).
  - intros F. contradiction.
  - intros F. destruct (e_cur _ _ _ _ _ _ D F) as (C1 & C2 & C3). cbn [lb cc] in C3.
    split; [exact C1|]. split; [exact C2|]. rewrite Hlab.
    destruct (w =? rC) eqn:Ew; [reflexivity | exact C3].
  - intros v Hv Hl _. rewrite Hlab in Hl. destruct (w =? v) eqn:Ev.
    + apply eqb_true in Ev. subst v. exact Hmut.
    + exact (e_S1 _ _ _ _ _ _ D v Hv Hl Hc).
  - intros v Hv Hl _ Hp x Exv. apply Hkeep. rewrite Hlab in Hl. destruct (w =? v) eqn:Ev.
    + apply eqb_true in Ev. subst v. exfalso. apply Hp. right. apply in_or_app. right. left. reflexivity.
    + refine (e_S2 _ _ _ _ _ _ D v Hv Hl Hc _ x Exv).
      intros [F | F]; apply Hp; [left; exact F | right; apply in_or_app; left; exact F].
  - apply (Permutation_NoDup (Permutation_cons_append Sk w)). constructor; [exact HwSk | exact (e_S3nd _ _ _ _ _ _ D)].
  - intros v Hv. rewrite Hlab. apply in_app_iff in Hv as [Hv | [Hv | []]].
    + destruct (e_S3 _ _ _ _ _ _ D v Hv) as [A B]. split; [exact A|].
      destruct (w =? v); [reflexivity | exact B].
    + subst v. split; [exact HwV|]. rewrite (proj2 (eqb_true w w) eq_refl). reflexivity.
  - intros v x Hv Hx Hlv Hlt. rewrite !Hlab in *. destruct (w =? v) eqn:Ev.
    + lia.
    + destruct (w =? x) eqn:Ex.
      * apply eqb_true in Ex. subst x. split.
        -- intros F. rewrite <- F in Hlt. lia.
        -- intros Hm. exfalso. pose proof (proj2 (e_S4 _ _ _ _ _ _ D v w Hv HwV Hlv Hlt) Hm) as F.
           cbn [lb] in F. rewrite Hw0 in F. apply Hlv. symmetry. exact F.
      * exact (e_S4 _ _ _ _ _ _ D v x Hv Hx Hlv Hlt).
Qed.

Lemma push_spec : forall u i c rC pr, (φ c) <> 0%Z -> ((φ u) < (φ V))%Z ->
  forall z j lab stk sp Sk Lb (H : Acc (Zwf 0) (gap (roff.[u + 1]) j)),
  gap (roff.[u + 1]) j = z ->
  ((φ (roff.[u])) <= (φ j) <= (φ (roff.[u + 1])))%Z ->
  D2core (D2 lab stk sp i c) Sk Lb rC pr (u :: Sk) -> lab.[u] = c ->
  (forall j', ((φ (roff.[u])) <= (φ j') < (φ j))%Z -> lab.[radj.[j']] <> 0) ->
  exists Sk' Lb',
    D2core (D2 (fst (fst (push_preds radj c (roff.[u + 1]) j lab stk sp H)))
               (snd (fst (push_preds radj c (roff.[u + 1]) j lab stk sp H)))
               (snd (push_preds radj c (roff.[u + 1]) j lab stk sp H)) i c) Sk' Lb' rC pr Sk' /\
    (Z.of_nat (List.length Sk') - 2 * Z.of_nat (List.length Lb') <=
     Z.of_nat (List.length Sk) - 2 * Z.of_nat (List.length Lb))%Z.
Proof.
  intros u i c rC pr Hc Hu z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j lab stk sp Sk Lb H Hz Hj D Hlu Hdone. destruct H as [Hacc]. cbn [push_preds].
  destruct (bdec (j <? roff.[u + 1])) as [Hlt | Hge].
  - destruct (step_le _ j Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    pose proof (Hrsound u j Hu ltac:(lia)) as Ewu.
    destruct (HEV _ _ Ewu) as [HwV _].
    destruct (lab.[radj.[j]] =? 0) eqn:Hw0.
    + apply eqb_true in Hw0.
      pose proof (pp_push lab stk sp i c Sk Lb rC pr u (radj.[j]) D Hc Hu Hlu Ewu Hw0) as D'.
      assert (Hneq : radj.[j] <> u) by (intro F; rewrite F in Hw0; rewrite Hw0 in Hlu; apply Hc; rewrite <- Hlu; reflexivity).
      destruct (IH (gap (roff.[u + 1]) (j + 1)) ltac:(unfold Zwf, gap in *; lia) (j + 1)
                  lab.[radj.[j] <- c] stk.[sp <- radj.[j]] (sp + 1) (Sk ++ [radj.[j]]) (radj.[j] :: Lb)
                  Hn eq_refl ltac:(lia) D')
        as (Sk' & Lb' & D'' & Hp).
      * rewrite get_other by exact Hneq. exact Hlu.
      * intros j' Hj'. destruct (Z.eq_dec (φ j') (φ j)) as [Ej | Ej].
        -- apply phi_eq in Ej. subst j'. rewrite get_same by (pose proof (e_llb _ _ _ _ _ _ D) as L; cbn [lb] in L; rewrite L; exact HwV).
           intros F. apply Hc. rewrite F. reflexivity.
        -- assert (Hl := Hdone j' ltac:(lia)). intros F. apply Hl.
           destruct (idec (radj.[j]) (radj.[j'])) as [Ee | Ee].
           ++ rewrite <- Ee. exact Hw0.
           ++ rewrite get_other in F by exact Ee. exact F.
      * exists Sk', Lb'. split; [exact D''|]. rewrite length_app in Hp. cbn [List.length] in Hp. lia.
    + apply eqb_false in Hw0.
      destruct (IH (gap (roff.[u + 1]) (j + 1)) ltac:(unfold Zwf, gap in *; lia) (j + 1)
                  lab stk sp Sk Lb Hn eq_refl ltac:(lia) D Hlu)
        as (Sk' & Lb' & D'' & Hp).
      * intros j' Hj'. destruct (Z.eq_dec (φ j') (φ j)) as [Ej | Ej].
        -- apply phi_eq in Ej. subst j'. exact Hw0.
        -- apply Hdone. lia.
      * exists Sk', Lb'. split; [exact D''|exact Hp].
  - rewrite ltb_false in Hge. cbn [fst snd]. exists Sk, Lb. split; [|lia].
    destruct D as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18].
    constructor; try assumption.
    intros v Hv Hl Hcc Hp w Ewv. cbn [lb cc] in *.
    destruct (idec v u) as [Evu | Evu].
    + subst v. destruct (Hrcomp u w Ewv) as (j' & Hj' & Ej'). rewrite <- Ej'. apply Hdone. lia.
    + apply (A15 v Hv Hl Hcc); [|exact Ewv]. intros [F | F]; [congruence | contradiction].
Qed.


Lemma complete_cc : forall s Lb rC pr, D2core s [] Lb rC pr [] -> (φ (cc s)) <> 0%Z ->
  forall x, R x rC -> R rC x -> ((φ x) < (φ V))%Z -> (lb s).[x] = cc s.
Proof.
  intros s Lb rC pr D Hc x Hx. apply clos_rt_rt1n in Hx.
  induction Hx as [x | x y z Exy Hyz IH]; intros Hzx HxV.
  - exact (proj2 (proj2 (e_cur _ _ _ _ _ _ D Hc))).
  - destruct (HEV x y Exy) as [_ HyV].
    assert (Hy : (lb s).[y] = cc s).
    { apply IH; [exact D | eapply rt_trans; [exact Hzx | apply rt_step; exact Exy] | exact HyV]. }
    assert (Hx0 : (lb s).[x] <> 0)
      by exact (e_S2 _ _ _ _ _ _ D y HyV Hy Hc (fun F => F) x Exy).
    destruct (idec ((lb s).[x]) (cc s)) as [Ec | Ec]; [exact Ec|].
    exfalso. pose proof (e_lab _ _ _ _ _ _ D x HxV).
    assert (Hlt : ((φ ((lb s).[x])) < (φ (cc s)))%Z).
    { assert ((φ ((lb s).[x])) <> (φ (cc s))) by (intro F; apply Ec; apply phi_eq; exact F). lia. }
    assert (Hm : R x y /\ R y x).
    { split; [apply rt_step; exact Exy|]. eapply rt_trans; [apply clos_rt1n_rt; exact Hyz | exact Hzx]. }
    pose proof (proj2 (e_S4 _ _ _ _ _ _ D x y HxV HyV Hx0 Hlt) Hm) as F.
    rewrite Hy in F. apply Ec. symmetry. exact F.
Qed.

Definition Phi2 (s : d2) (Sk Lb : list int) : Z :=
  ((φ (ii s)) + 2 * ((φ V) - Z.of_nat (List.length Lb)) + Z.of_nat (List.length Sk))%Z.

Variable post : array int.
Hypothesis HPs : slice post 0 (nz V) = P.

Lemma asg_step_spec : forall s Sk Lb rC pr, D2core s Sk Lb rC pr Sk ->
  match asg_step roff radj post s with
  | Some s' => exists Sk' Lb' rC' pr', D2core s' Sk' Lb' rC' pr' Sk' /\ (Phi2 s' Sk' Lb' < Phi2 s Sk Lb)%Z
  | None => Sk = [] /\ (φ (ii s)) = 0%Z
  end.
Proof.
  intros [lab stk sp i c] Sk Lb rC pr D. unfold asg_step. cbn [lb sk sq ii cc] in *. cbv zeta.
  pose proof (e_llb _ _ _ _ _ _ D) as Lll. pose proof (e_lsk _ _ _ _ _ _ D) as Lsk.
  pose proof (e_sq _ _ _ _ _ _ D) as Lsq. pose proof (e_ssk _ _ _ _ _ _ D) as Lssk.
  pose proof (e_ii _ _ _ _ _ _ D) as Lii. pose proof (e_cc _ _ _ _ _ _ D) as Lcc.
  cbn [lb sk sq ii cc] in Lll, Lsk, Lsq, Lssk, Lii, Lcc.
  pose proof (d2_size _ _ _ _ _ _ D) as HLb.
  destruct (0 <? sp) eqn:Hsp.
  - rewrite ltb_true in Hsp. change (φ 0) with 0%Z in Hsp.
    assert (HS : Sk <> []) by (intros ->; simpl in Lsq; lia).
    destruct (exists_last HS) as (Sk0 & u & ->).
    assert (LS : List.length (Sk0 ++ [u]) = S (List.length Sk0)) by (rewrite length_app; simpl; lia).
    assert (Hszk : (Z.of_nat (List.length (Sk0 ++ [u])) <= (φ V))%Z).
    { apply (nodup_bound V _ (e_S3nd _ _ _ _ _ _ D)). intros v Hv. exact (proj1 (e_S3 _ _ _ _ _ _ D v Hv)). }
    assert (Ht : sp - 1 = ofn (List.length Sk0)).
    { apply phi_eq. rewrite phi_sub1 by lia. rewrite Lsq, LS.
      rewrite phi_ofn; [lia|]. rewrite wB_val. lia. }
    rewrite LS in Lssk. destruct (slice0_prefix _ _ _ _ Lssk) as [Lssk0 Hu].
    rewrite Ht, Hu.
    destruct (e_S3 _ _ _ _ _ _ D u ltac:(apply in_or_app; right; left; reflexivity)) as [HuV Hlu].
    cbn [lb cc] in Hlu.
    assert (Hc : (φ c) <> 0%Z).
    { intros F. destruct (e_cur0 _ _ _ _ _ _ D F) as [F' _]. destruct Sk0; discriminate. }
    assert (D0 : D2core (D2 lab stk (ofn (List.length Sk0)) i c) Sk0 Lb rC pr (u :: Sk0)).
    { destruct D as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18].
      constructor; cbn [lb sk sq ii cc] in *; try assumption.
      - rewrite phi_ofn; [reflexivity|]. rewrite wB_val. lia.
      - intros F. exfalso. exact (Hc F).
      - intros v Hv Hl Hcc Hp. apply (A15 v Hv Hl Hcc). intros F. apply Hp.
        apply in_app_iff in F as [F | [F | []]]; [right; exact F | left; exact F].
      - apply NoDup_app_remove_r in A16. exact A16.
      - intros v Hv. apply A17. apply in_or_app. left. exact Hv. }
    destruct (push_spec u i c rC pr Hc HuV _ (roff.[u]) lab stk (ofn (List.length Sk0)) Sk0 Lb
                (Zwf_well_founded 0 (gap (roff.[u + 1]) (roff.[u]))) eq_refl
                ltac:(pose proof (Hroff u HuV); lia) D0 Hlu ltac:(intros j' Hj'; lia))
      as (Sk' & Lb' & D' & Hp).
    exists Sk', Lb', rC, pr. split; [exact D'|].
    unfold Phi2. cbn [ii]. rewrite length_app in *. cbn [List.length] in *. lia.
  - rewrite ltb_false in Hsp. change (φ 0) with 0%Z in Hsp.
    assert (HS : Sk = []) by (destruct Sk; [reflexivity|]; simpl in Lsq; lia).
    subst Sk.
    destruct (0 <? i) eqn:Hi.
    + rewrite ltb_true in Hi. change (φ 0) with 0%Z in Hi.
      assert (Hi1 : (φ (i - 1)) = ((φ i) - 1)%Z) by (apply phi_sub1; lia).
      assert (Hni : nz (i - 1) = (nz i - 1)%nat) by (unfold nz; rewrite Hi1; lia).
      assert (Hk : (nz (i - 1) < nz V)%nat) by (unfold nz; rewrite Hi1; lia).
      assert (Hr : post.[i - 1] = nth (nz (i - 1)) P 0).
      { rewrite <- (ofn_nz (i - 1)) at 1. apply (slice0_nth post (nz V) P HPs). exact Hk. }
      assert (HrV : ((φ (post.[i - 1])) < (φ V))%Z) by (rewrite Hr; apply nth_P_in; exact Hk).
      destruct (lab.[post.[i - 1]] =? 0) eqn:Hr0.
      * apply eqb_true in Hr0.
        set (r := post.[i - 1]) in *.
        exists [r], (r :: Lb), r, (nz (i - 1)).
        assert (HrLb : ~ In r Lb).
        { intros F. pose proof (e_Lb _ _ _ _ _ _ D r HrV) as G. cbn [lb] in G. apply G in F. contradiction. }
        assert (Hc1 : (φ (c + 1)) = ((φ c) + 1)%Z) by (apply phi_add1; lia).
        assert (Hc1nz : c + 1 <> 0) by (intros F; apply (f_equal to_Z) in F; rewrite Hc1 in F; change (φ 0) with 0%Z in F; pose proof (to_Z_bounded c); lia).
        assert (Hlab : forall v, lab.[r <- c + 1].[v] = if r =? v then c + 1 else lab.[v]).
        { intros v. destruct (r =? v) eqn:Ev.
          - apply eqb_true in Ev. subst v. apply get_same. rewrite Lll. exact HrV.
          - apply eqb_false in Ev. apply get_other. exact Ev. }
        assert (Hold : forall v, ((φ v) < (φ V))%Z -> ((φ (lab.[v])) <= (φ c))%Z) by exact (e_lab _ _ _ _ _ _ D).
        (* the current component is complete *)
        assert (Hcomp_c : forall v w, ((φ v) < (φ V))%Z -> ((φ w) < (φ V))%Z -> (φ c) <> 0%Z -> lab.[v] = c ->
                   (lab.[w] = c <-> (R v w /\ R w v))).
        { intros v w Hv Hw Hc Hlv.
          destruct (e_S1 _ _ _ _ _ _ D v Hv Hlv Hc) as [V1 V2].
          split.
          - intros Hlw. destruct (e_S1 _ _ _ _ _ _ D w Hw Hlw Hc) as [W1 W2].
            split; eapply rt_trans; eassumption.
          - intros [M1 M2]. apply (complete_cc _ _ _ _ D Hc w); [| |exact Hw].
            + eapply rt_trans; [exact M2 | exact V1].
            + eapply rt_trans; [exact V2 | exact M1]. }
        split.
        -- constructor; cbn [lb sk sq ii cc].
           ++ rewrite len_set. exact Lll.
           ++ rewrite len_set. exact Lsk.
           ++ reflexivity.
           ++ change [r] with ([] ++ [r]). rewrite <- ofn_0.
              apply slice0_extend; [reflexivity | rewrite Lsk; simpl; lia].
           ++ lia.
           ++ lia.
           ++ intros v Hv. rewrite Hlab. destruct (r =? v); [lia|]. pose proof (Hold v Hv). lia.
           ++ constructor; [exact HrLb | exact (e_Lbnd _ _ _ _ _ _ D)].
           ++ intros v [Hv | Hv]; [subst; exact HrV | exact (e_Lbin _ _ _ _ _ _ D v Hv)].
           ++ intros v Hv. rewrite Hlab. destruct (r =? v) eqn:Ev.
              ** apply eqb_true in Ev. subst v. split; [intros _; left; reflexivity | intros _; exact Hc1nz].
              ** apply eqb_false in Ev. pose proof (e_Lb _ _ _ _ _ _ D v Hv) as G. cbn [lb] in G.
                 rewrite G. simpl. split; [tauto|]. intros [F | F]; [congruence | exact F].
           ++ intros k Hk'. rewrite Hlab. destruct (r =? nth k P 0) eqn:Ek; [exact Hc1nz|].
              apply eqb_false in Ek.
              destruct (Nat.eq_dec k (nz (i - 1))) as [Ek' | Ek'].
              ** subst k. exfalso. apply Ek. rewrite <- Hr. reflexivity.
              ** apply (e_P1 _ _ _ _ _ _ D). cbn [ii]. rewrite Hni in Ek'. rewrite Hni in Hk'. lia.
           ++ intros F. lia.
           ++ intros _. split; [exact Hr|]. split; [lia|]. rewrite Hlab.
              rewrite (proj2 (eqb_true r r) eq_refl). reflexivity.
           ++ intros v Hv Hl _. rewrite Hlab in Hl. destruct (r =? v) eqn:Ev.
              ** apply eqb_true in Ev. subst v. split; apply rt_refl.
              ** exfalso. pose proof (Hold v Hv). rewrite Hl, Hc1 in H. lia.
           ++ intros v Hv Hl _ Hp. rewrite Hlab in Hl. destruct (r =? v) eqn:Ev.
              ** apply eqb_true in Ev. subst v. exfalso. apply Hp. left. reflexivity.
              ** exfalso. pose proof (Hold v Hv). rewrite Hl, Hc1 in H. lia.
           ++ constructor; [intros []|constructor].
           ++ intros v [Hv | []]. subst v. split; [exact HrV|]. rewrite Hlab.
              rewrite (proj2 (eqb_true r r) eq_refl). reflexivity.
           ++ intros v w Hv Hw Hlv Hlt. rewrite !Hlab in *. rewrite Hc1 in Hlt.
              destruct (r =? v) eqn:Ev; [lia|]. apply eqb_false in Ev.
              assert (Hcases : ((φ (lab.[v])) < (φ c))%Z \/ (lab.[v] = c /\ (φ c) <> 0%Z)).
              { pose proof (Hold v Hv). destruct (Z.eq_dec (φ (lab.[v])) (φ c)) as [E' | E'].
                - right. split; [apply phi_eq; exact E'|]. intros F. rewrite F in E'.
                  apply Hlv. apply phi_eq. rewrite E'. reflexivity.
                - left. lia. }
              destruct (r =? w) eqn:Ew.
              ** apply eqb_true in Ew. subst w. split.
                 --- intros F. exfalso. rewrite <- F in Hlt. lia.
                 --- intros Hm. exfalso. destruct Hcases as [Lt | [Eq Hc]].
                     +++ pose proof (proj2 (e_S4 _ _ _ _ _ _ D v r Hv HrV Hlv Lt) Hm) as F.
                         cbn [lb] in F. rewrite Hr0 in F. apply Hlv. symmetry. exact F.
                     +++ pose proof (proj2 (Hcomp_c v r Hv HrV Hc Eq) Hm) as F.
                         rewrite Hr0 in F. apply Hc. rewrite <- F. reflexivity.
              ** destruct Hcases as [Lt | [Eq Hc]].
                 --- exact (e_S4 _ _ _ _ _ _ D v w Hv Hw Hlv Lt).
                 --- rewrite Eq. exact (Hcomp_c v w Hv Hw Hc Eq).
        -- unfold Phi2. cbn [ii List.length]. rewrite Hi1. lia.
      * apply eqb_false in Hr0. exists [], Lb, rC, pr.
        destruct D as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18].
        cbn [lb sk sq ii cc] in *.
        split.
        -- constructor; cbn [lb sk sq ii cc]; try assumption.
           ++ lia.
           ++ lia.
           ++ intros k Hk'. destruct (Nat.eq_dec k (nz (i - 1))) as [Ek | Ek].
              ** subst k. rewrite <- Hr. exact Hr0.
              ** apply A11. rewrite Hni in Ek, Hk'. unfold nz in *. lia.
           ++ intros F. destruct (A13 F) as (B1 & B2 & B3). split; [exact B1|]. split; [|exact B3].
              rewrite Hni. lia.
        -- unfold Phi2. cbn [ii]. rewrite Hi1. lia.
    + rewrite ltb_false in Hi. split; [reflexivity|]. change (φ 0) with 0%Z in Hi.
      pose proof (to_Z_bounded i). lia.
Qed.


Lemma phi2_pos : forall s Sk Lb rC pr, D2core s Sk Lb rC pr Sk ->
  (Sk <> [] \/ (0 < (φ (ii s)))%Z) -> (1 <= Phi2 s Sk Lb)%Z.
Proof.
  intros s Sk Lb rC pr D H. pose proof (d2_size _ _ _ _ _ _ D). pose proof (to_Z_bounded (ii s)).
  unfold Phi2. destruct H as [H | H]; [|lia]. destruct Sk; [congruence|]. simpl List.length. lia.
Qed.

Lemma assign_spec : forall bound z steps s Sk Lb rC pr (H : Acc (Zwf 0) (gap bound steps)),
  gap bound steps = z -> D2core s Sk Lb rC pr Sk -> ((φ steps) + Phi2 s Sk Lb <= (φ bound))%Z ->
  exists Lbf rCf prf, D2core (assign roff radj post s bound steps H) [] Lbf rCf prf [] /\
                      (φ (ii (assign roff radj post s bound steps H))) = 0%Z.
Proof.
  intros bound z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros steps s Sk Lb rC pr H Hz D Hb. destruct H as [Hacc]. cbn [assign].
  destruct (bdec (steps <? bound)) as [Hlt | Hge].
  - pose proof (asg_step_spec s Sk Lb rC pr D) as Hs.
    destruct (asg_step roff radj post s) as [s' |] eqn:Es.
    + destruct Hs as (Sk' & Lb' & rC' & pr' & D' & Hph).
      destruct (step_le bound steps Hlt) as [E1 E2]. gen_acc.
      apply (IH (gap bound (steps + 1)) ltac:(unfold Zwf, gap in *; lia) (steps + 1) s' Sk' Lb' rC' pr' Hn eq_refl D').
      lia.
    + destruct Hs as [-> Hr]. exists Lb, rC, pr. split; [exact D | exact Hr].
  - rewrite ltb_false in Hge.
    destruct Sk as [|a Sk].
    + destruct (Z.eq_dec (φ (ii s)) 0) as [Hi | Hi].
      * exists Lb, rC, pr. split; [exact D | exact Hi].
      * exfalso. pose proof (to_Z_bounded (ii s)).
        assert (Hp : (0 < (φ (ii s)))%Z) by lia.
        pose proof (phi2_pos s [] Lb rC pr D (or_intror Hp)). lia.
    + exfalso. assert (Hne : a :: Sk <> []) by discriminate.
      pose proof (phi2_pos s (a :: Sk) Lb rC pr D (or_introl Hne)). lia.
Qed.

Lemma pass2_final : forall s Lb rC pr, D2core s [] Lb rC pr [] -> (φ (ii s)) = 0%Z ->
  (forall v, ((φ v) < (φ V))%Z -> (lb s).[v] <> 0 /\ ((φ ((lb s).[v])) <= (φ (cc s)))%Z) /\
  (forall v w, ((φ v) < (φ V))%Z -> ((φ w) < (φ V))%Z -> ((lb s).[v] = (lb s).[w] <-> (R v w /\ R w v))) /\
  ((φ (cc s)) <= (φ V))%Z.
Proof.
  intros s Lb rC pr D Hi.
  assert (Hlab : forall v, ((φ v) < (φ V))%Z -> (lb s).[v] <> 0).
  { intros v Hv. apply HPin in Hv. apply In_nth with (d := 0) in Hv as (k & Hk & <-).
    apply (e_P1 _ _ _ _ _ _ D). unfold nz at 1. rewrite Hi. rewrite HPl in Hk. lia. }
  split; [intros v Hv; split; [exact (Hlab v Hv) | exact (e_lab _ _ _ _ _ _ D v Hv)]|].
  split; [|pose proof (e_cc _ _ _ _ _ _ D); pose proof (to_Z_bounded (ii s)); lia].
  intros v w Hv Hw.
  pose proof (e_lab _ _ _ _ _ _ D v Hv) as Hle.
  destruct (Z.eq_dec (φ ((lb s).[v])) (φ (cc s))) as [Eq | Ne].
  - apply phi_eq in Eq.
    assert (Hc : (φ (cc s)) <> 0%Z).
    { intros F. apply (Hlab v Hv). rewrite Eq. apply phi_eq. rewrite F. reflexivity. }
    destruct (e_S1 _ _ _ _ _ _ D v Hv Eq Hc) as [V1 V2]. split.
    + intros Hvw. rewrite Eq in Hvw. destruct (e_S1 _ _ _ _ _ _ D w Hw (eq_sym Hvw) Hc) as [W1 W2].
      split; eapply rt_trans; eassumption.
    + intros [M1 M2]. rewrite Eq. symmetry. apply (complete_cc _ _ _ _ D Hc w); [| |exact Hw].
      * eapply rt_trans; [exact M2 | exact V1].
      * eapply rt_trans; [exact V2 | exact M1].
  - assert (Hlt : ((φ ((lb s).[v])) < (φ (cc s)))%Z) by lia.
    rewrite <- (e_S4 _ _ _ _ _ _ D v w Hv Hw (Hlab v Hv) Hlt). split; intros; symmetry; assumption.
Qed.

Lemma pass2_init : D2core (D2 (PArray.make V 0) (PArray.make V 0) 0 V 0) [] [] 0 0%nat [].
Proof.
  pose proof (to_Z_bounded V) as BV.
  constructor; cbn [lb sk sq ii cc]; change (φ 0) with 0%Z.
  all: solve
    [ apply len_make; lia
    | reflexivity
    | lia
    | constructor
    | intros v []
    | intros v _; rewrite get_mk; change (φ 0) with 0%Z; lia
    | intros v _; rewrite get_mk; split; [intros F; exfalso; apply F; reflexivity | intros []]
    | intros k Hk; unfold nz in Hk; lia
    | intros _; split; [reflexivity|]; intros v _; apply get_mk
    | intros F; exfalso; apply F; reflexivity
    | intros v _ _ F; exfalso; apply F; reflexivity
    | intros v w _ _ F; exfalso; apply F; apply get_mk ].
Qed.

Lemma pass2 :
  let sf := assign roff radj post (D2 (PArray.make V 0) (PArray.make V 0) 0 V 0)
              (3 * V + 1) 0 (Zwf_well_founded 0 (gap (3 * V + 1) 0)) in
  (forall v, ((φ v) < (φ V))%Z -> (lb sf).[v] <> 0 /\ ((φ ((lb sf).[v])) <= (φ (cc sf)))%Z) /\
  (forall v w, ((φ v) < (φ V))%Z -> ((φ w) < (φ V))%Z -> ((lb sf).[v] = (lb sf).[w] <-> (R v w /\ R w v))) /\
  ((φ (cc sf)) <= (φ V))%Z.
Proof.
  intros sf.
  destruct (assign_spec (3 * V + 1) _ 0 _ [] [] 0 0%nat (Zwf_well_founded 0 (gap (3 * V + 1) 0))
              eq_refl pass2_init) as (Lbf & rCf & prf & Df & Hi).
  - unfold Phi2. cbn [ii List.length]. change (φ 0) with 0%Z.
    assert ((φ (3 * V + 1)) = 3 * (φ V) + 1)%Z by sia. lia.
  - exact (pass2_final _ _ _ _ Df Hi).
Qed.

End Pass2.

(* ------------------------------------------------------------------ *)
(* Phase 5 proofs: merge sort                                          *)
(* ------------------------------------------------------------------ *)

Definition sl (a : array int) (lo hi : int) : list int :=
  slice a (φ lo) (Z.to_nat ((φ hi) - (φ lo))).

Lemma slice_cons : forall a lo n,
  slice a lo (S n) = a.[of_Z lo] :: slice a (lo + 1) n.
Proof.
  intros a lo n. unfold slice. simpl. rewrite Z.add_0_r. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros k. f_equal. f_equal. lia.
Qed.

Lemma slice_app : forall a lo n1 n2,
  slice a lo (n1 + n2) = slice a lo n1 ++ slice a (lo + Z.of_nat n1) n2.
Proof.
  intros a lo n1 n2. induction n2 as [|n2 IH].
  - rewrite Nat.add_0_r. unfold slice at 3. simpl. rewrite app_nil_r. reflexivity.
  - rewrite Nat.add_succ_r, !slice_S, IH, <- app_assoc. f_equal. f_equal. f_equal.
    f_equal. lia.
Qed.

Lemma sl_split : forall a lo mid hi, ((φ lo) <= (φ mid) <= (φ hi))%Z ->
  sl a lo hi = sl a lo mid ++ sl a mid hi.
Proof.
  intros a lo mid hi H. unfold sl.
  replace (Z.to_nat ((φ hi) - (φ lo))) with (Z.to_nat ((φ mid) - (φ lo)) + Z.to_nat ((φ hi) - (φ mid)))%nat by lia.
  rewrite slice_app. f_equal. f_equal. lia.
Qed.

Lemma sl_cons : forall a i hi, ((φ i) < (φ hi))%Z ->
  sl a i hi = a.[i] :: sl a (i + 1) hi.
Proof.
  intros a i hi H. unfold sl.
  replace (Z.to_nat ((φ hi) - (φ i))) with (S (Z.to_nat ((φ hi) - (φ (i + 1))))) by (rewrite (phi_add1_lt i hi H); lia).
  rewrite slice_cons. rewrite of_to_Z. f_equal. f_equal. rewrite (phi_add1_lt i hi H). reflexivity.
Qed.

Lemma sl_empty : forall a i hi, ((φ hi) <= (φ i))%Z -> sl a i hi = [].
Proof. intros a i hi H. unfold sl. replace (Z.to_nat ((φ hi) - (φ i))) with 0%nat by lia. reflexivity. Qed.

Lemma sl_ext : forall a b lo hi, (forall q, ((φ lo) <= (φ q) < (φ hi))%Z -> a.[q] = b.[q]) ->
  sl a lo hi = sl b lo hi.
Proof.
  intros a b lo hi H. unfold sl. apply slice_ext. intros k Hk. apply H.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  rewrite of_Z_spec, Z.mod_small; [lia|]. lia.
Qed.

Section MsortProof.
Variable le : int -> int -> bool.
Hypothesis le_total : forall a b, le a b = true \/ le b a = true.
Hypothesis le_trans : forall a b c, le a b = true -> le b c = true -> le a c = true.

Definition lep (a b : int) : Prop := le a b = true.

Fixpoint lmerge (l1 : list int) : list int -> list int :=
  match l1 with
  | [] => fun l2 => l2
  | x :: l1' => fix inner (l2 : list int) : list int :=
      match l2 with
      | [] => l1
      | y :: l2' => if le x y then x :: lmerge l1' l2 else y :: inner l2'
      end
  end.

Lemma lmerge_nil_r : forall l, lmerge l [] = l.
Proof. intros [|x l]; reflexivity. Qed.

Lemma lmerge_cc : forall x l1 y l2, lmerge (x :: l1) (y :: l2) =
  if le x y then x :: lmerge l1 (y :: l2) else y :: lmerge (x :: l1) l2.
Proof. reflexivity. Qed.

Lemma lmerge_perm : forall l1 l2, Permutation (lmerge l1 l2) (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH1]; intros l2; [reflexivity|].
  induction l2 as [|y l2 IH2]; [rewrite lmerge_nil_r, app_nil_r; reflexivity|].
  rewrite lmerge_cc. destruct (le x y).
  - simpl. constructor. apply IH1.
  - eapply perm_trans; [apply perm_skip; exact IH2|].
    exact (Permutation_middle (x :: l1) l2 y).
Qed.

Lemma lmerge_hd : forall a l1 l2, HdRel lep a l1 -> HdRel lep a l2 -> HdRel lep a (lmerge l1 l2).
Proof.
  intros a [|x l1] [|y l2] H1 H2; try assumption.
  rewrite lmerge_cc. destruct (le x y); constructor.
  - inversion H1; assumption.
  - inversion H2; assumption.
Qed.

Lemma lmerge_sorted : forall l1 l2, Sorted lep l1 -> Sorted lep l2 -> Sorted lep (lmerge l1 l2).
Proof.
  induction l1 as [|x l1 IH1]; intros l2 S1 S2; [exact S2|].
  induction l2 as [|y l2 IH2]; [rewrite lmerge_nil_r; exact S1|].
  rewrite lmerge_cc. destruct (le x y) eqn:Exy.
  - apply Sorted_inv in S1 as [S1 H1]. constructor; [apply IH1; assumption|].
    apply lmerge_hd; [exact H1 | constructor; exact Exy].
  - apply Sorted_inv in S2 as [S2 H2]. constructor; [apply IH2; assumption|].
    apply lmerge_hd; [constructor | exact H2].
    destruct (le_total x y) as [F | F]; [congruence | exact F].
Qed.

Lemma merge_loop_spec : forall a lo mid hi,
  ((φ lo) <= (φ mid) <= (φ hi))%Z -> ((φ hi) <= (φ (PArray.length a)))%Z ->
  forall z i j k t (H : Acc (Zwf 0) (gap hi k)), gap hi k = z ->
  ((φ lo) <= (φ i) <= (φ mid))%Z -> ((φ mid) <= (φ j) <= (φ hi))%Z ->
  (φ k) = ((φ lo) + ((φ i) - (φ lo)) + ((φ j) - (φ mid)))%Z ->
  PArray.length t = PArray.length a ->
  sl t lo k ++ lmerge (sl a i mid) (sl a j hi) = lmerge (sl a lo mid) (sl a mid hi) ->
  PArray.length (merge_loop le a t mid hi i j k H) = PArray.length a /\
  sl (merge_loop le a t mid hi i j k H) lo hi = lmerge (sl a lo mid) (sl a mid hi).
Proof.
  intros a lo mid hi Hlmh Hha z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j k t H Hz Hi Hj Hk Ht Hinv. destruct H as [Hacc]. cbn [merge_loop].
  destruct (bdec (k <? hi)) as [Hlt | Hge].
  - destruct (step_le hi k Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    assert (Hsl : forall v, sl t.[k <- v] lo (k + 1) = sl t lo k ++ [v]).
    { intros v. unfold sl. rewrite E1.
      replace (Z.to_nat ((φ k) + 1 - (φ lo))) with (S (Z.to_nat ((φ k) - (φ lo)))) by lia.
      rewrite slice_S. rewrite slice_set_out; [| apply to_Z_bounded | pose proof (len_bound t); lia | lia].
      f_equal. f_equal. replace ((φ lo) + Z.of_nat (Z.to_nat ((φ k) - (φ lo))))%Z with (φ k) by lia.
      rewrite of_to_Z. apply get_same. lia. }
    destruct ((i <? mid) && ((hi <=? j) || le a.[i] a.[j])) eqn:Ec.
    + apply Bool.andb_true_iff in Ec as [Ei Ec]. rewrite ltb_true in Ei.
      apply (IH (gap hi (k + 1)) ltac:(unfold Zwf, gap in *; lia) (i + 1) j (k + 1) _ Hn eq_refl).
      * rewrite (phi_add1_lt i mid Ei). lia.
      * lia.
      * rewrite (phi_add1_lt i mid Ei). lia.
      * rewrite len_set. exact Ht.
      * rewrite Hsl, <- app_assoc. rewrite <- Hinv. f_equal.
        rewrite (sl_cons a i mid Ei). simpl app.
        apply Bool.orb_true_iff in Ec as [Ec | Ec].
        -- rewrite leb_spec in Ec. rewrite (sl_empty a j hi) by lia. rewrite !lmerge_nil_r. reflexivity.
        -- destruct (Z.lt_ge_cases (φ j) (φ hi)) as [Lj | Gj].
           ++ rewrite (sl_cons a j hi Lj). rewrite lmerge_cc. rewrite Ec. reflexivity.
           ++ rewrite (sl_empty a j hi) by lia. rewrite !lmerge_nil_r. reflexivity.
    + assert (Lj : ((φ j) < (φ hi))%Z).
      { apply Bool.andb_false_iff in Ec as [Ec | Ec].
        - rewrite ltb_false in Ec. lia.
        - apply Bool.orb_false_iff in Ec as [Ec _]. rewrite <- Bool.not_true_iff_false, leb_spec in Ec. lia. }
      apply (IH (gap hi (k + 1)) ltac:(unfold Zwf, gap in *; lia) i (j + 1) (k + 1) _ Hn eq_refl).
      * lia.
      * rewrite (phi_add1_lt j hi Lj). lia.
      * rewrite (phi_add1_lt j hi Lj). lia.
      * rewrite len_set. exact Ht.
      * rewrite Hsl, <- app_assoc. rewrite <- Hinv. f_equal.
        rewrite (sl_cons a j hi Lj). simpl app.
        apply Bool.andb_false_iff in Ec as [Ec | Ec].
        -- rewrite ltb_false in Ec. rewrite (sl_empty a i mid) by lia. reflexivity.
        -- apply Bool.orb_false_iff in Ec as [_ Ec].
           destruct (Z.lt_ge_cases (φ i) (φ mid)) as [Li | Gi].
           ++ rewrite (sl_cons a i mid Li). rewrite lmerge_cc. rewrite Ec. reflexivity.
           ++ rewrite (sl_empty a i mid) by lia. reflexivity.
  - rewrite ltb_false in Hge. assert (Ekh : (φ k) = (φ hi)) by lia.
    assert (Ei : (φ i) = (φ mid)) by lia. assert (Ej : (φ j) = (φ hi)) by lia.
    split; [exact Ht|]. rewrite <- Hinv.
    rewrite (sl_empty a i mid) by lia. rewrite (sl_empty a j hi) by lia. simpl. rewrite app_nil_r.
    apply phi_eq in Ekh. subst k. reflexivity.
Qed.

Lemma copy_back_spec : forall t hi, forall z k a (H : Acc (Zwf 0) (gap hi k)), gap hi k = z ->
  ((φ hi) <= (φ (PArray.length a)))%Z ->
  PArray.length (copy_back t a hi k H) = PArray.length a /\
  (forall q, ((φ q) < (φ k) \/ (φ hi) <= (φ q))%Z -> (copy_back t a hi k H).[q] = a.[q]) /\
  (forall q, ((φ k) <= (φ q) < (φ hi))%Z -> (copy_back t a hi k H).[q] = t.[q]).
Proof.
  intros t hi z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k a H Hz Ha. destruct H as [Hacc]. cbn [copy_back].
  destruct (bdec (k <? hi)) as [Hlt | Hge].
  - destruct (step_le hi k Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    destruct (IH (gap hi (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) a.[k <- t.[k]] Hn eq_refl
                ltac:(rewrite len_set; exact Ha)) as (A1 & A2 & A3).
    split; [rewrite A1, len_set; reflexivity|]. split.
    + intros q Hq. rewrite A2 by lia. apply get_other_phi. lia.
    + intros q Hq. destruct (Z.eq_dec (φ q) (φ k)) as [Eq | Ne].
      * apply phi_eq in Eq. subst q. rewrite A2 by lia. apply get_same. lia.
      * apply A3. lia.
  - rewrite ltb_false in Hge. split; [reflexivity|]. split; [intros; reflexivity|]. intros q Hq. lia.
Qed.

Lemma sorted_short : forall l : list int, (List.length l <= 1)%nat -> Sorted lep l.
Proof. intros [|x [|y l]] H; simpl in H; try lia; repeat constructor. Qed.

Lemma msort_spec : forall z lo hi a t (H : Acc (Zwf 0) (gap hi lo)), gap hi lo = z ->
  ((φ lo) <= (φ hi) <= (φ (PArray.length a)))%Z -> PArray.length t = PArray.length a ->
  PArray.length (fst (msort le a t lo hi H)) = PArray.length a /\
  PArray.length (snd (msort le a t lo hi H)) = PArray.length a /\
  (forall q, ((φ q) < (φ lo) \/ (φ hi) <= (φ q))%Z -> (fst (msort le a t lo hi H)).[q] = a.[q]) /\
  Permutation (sl (fst (msort le a t lo hi H)) lo hi) (sl a lo hi) /\
  Sorted lep (sl (fst (msort le a t lo hi H)) lo hi).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi a t H Hz Hb Ht. destruct H as [Hacc]. cbn [msort].
  destruct (bdec (lo <? hi)) as [H1 | H1].
  - destruct (bdec (1 <? hi - lo)) as [H2 | H2].
    + set (A1 := Acc_inv (Acc_intro (gap hi lo) Hacc) (half_dec1 le lo hi H1 H2)).
      set (A2 := Acc_inv (Acc_intro (gap hi lo) Hacc) (half_dec2 le lo hi H1 H2)).
      pose proof (half_dec1 le lo hi H1 H2) as D1. pose proof (half_dec2 le lo hi H1 H2) as D2.
      clearbody A1 A2.
      set (mid := lo + (hi - lo) / 2) in *.
      assert (Hmid : ((φ lo) <= (φ mid) <= (φ hi))%Z) by (unfold Zwf, gap in D1, D2; lia).
      destruct (IH _ ltac:(rewrite <- Hz; exact D1) lo mid a t A1 eq_refl ltac:(lia) Ht)
        as (B1 & B2 & B3 & B4 & B5).
      set (r1 := msort le a t lo mid A1) in *.
      destruct (IH _ ltac:(rewrite <- Hz; exact D2) mid hi (fst r1) (snd r1) A2 eq_refl
                  ltac:(rewrite B1; lia) ltac:(rewrite B1, B2; reflexivity))
        as (C1 & C2 & C3 & C4 & C5).
      set (r2 := msort le (fst r1) (snd r1) mid hi A2) in *.
      destruct (merge_loop_spec (fst r2) lo mid hi Hmid ltac:(rewrite C1, B1; lia) _ lo mid lo (snd r2)
                  (Zwf_well_founded 0 (gap hi lo)) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite C2, C1; reflexivity)
                  ltac:(rewrite (sl_empty _ lo lo) by lia; reflexivity))
        as (M1 & M2).
      set (t3 := merge_loop le (fst r2) (snd r2) mid hi lo mid lo (Zwf_well_founded 0 (gap hi lo))) in *.
      destruct (copy_back_spec t3 hi _ lo (fst r2) (Zwf_well_founded 0 (gap hi lo)) eq_refl
                  ltac:(rewrite C1, B1; lia)) as (K1 & K2 & K3).
      cbn [fst snd].
      assert (Hsl2lo : sl (fst r2) lo mid = sl (fst r1) lo mid).
      { apply sl_ext. intros q Hq. apply C3. lia. }
      assert (Hsl1hi : sl (fst r1) mid hi = sl a mid hi).
      { apply sl_ext. intros q Hq. apply B3. lia. }
      assert (Hres : sl (copy_back t3 (fst r2) hi lo (Zwf_well_founded 0 (gap hi lo))) lo hi
                     = lmerge (sl (fst r2) lo mid) (sl (fst r2) mid hi)).
      { rewrite <- M2. apply sl_ext. intros q Hq. apply K3. exact Hq. }
      split; [rewrite K1, C1, B1; reflexivity|].
      split; [rewrite M1, C1, B1; reflexivity|].
      split.
      * intros q Hq. rewrite K2 by exact Hq. rewrite C3 by lia. apply B3. lia.
      * rewrite Hres. split.
        -- eapply perm_trans; [apply lmerge_perm|]. rewrite (sl_split a lo mid hi Hmid).
           apply Permutation_app; [rewrite Hsl2lo; exact B4 | rewrite <- Hsl1hi; exact C4].
        -- apply lmerge_sorted; [rewrite Hsl2lo; exact B5 | exact C5].
    + rewrite ltb_false in H2. cbn [fst snd].
      assert (Hl : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by (apply phi_sub; rewrite ltb_true in H1; lia).
      change (φ 1) with 1%Z in H2.
      split; [reflexivity|]. split; [exact Ht|]. split; [intros; reflexivity|]. split; [reflexivity|].
      apply sorted_short. unfold sl, slice. rewrite length_map, length_seq. lia.
  - rewrite ltb_false in H1. cbn [fst snd].
    split; [reflexivity|]. split; [exact Ht|]. split; [intros; reflexivity|]. split; [reflexivity|].
    rewrite sl_empty by lia. constructor.
Qed.

End MsortProof.

(* ------------------------------------------------------------------ *)
(* Phase 6 proofs: the output arrays                                   *)
(* ------------------------------------------------------------------ *)

Definition gview {A : Set} (a : array A) (n : nat) : list A :=
  map (fun k => a.[ofn k]) (seq 0 n).

Lemma gview_S : forall {A : Set} (a : array A) n, gview a (S n) = gview a n ++ [a.[ofn n]].
Proof. intros. unfold gview. rewrite seq_S, map_app. reflexivity. Qed.

Lemma gview_ext : forall {A : Set} (a b : array A) n,
  (forall k, (k < n)%nat -> a.[ofn k] = b.[ofn k]) -> gview a n = gview b n.
Proof. intros A a b n H. unfold gview. apply map_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia. Qed.

Lemma gview_extend : forall {A : Set} (a : array A) n v, (Z.of_nat n < (φ (PArray.length a)))%Z ->
  gview a.[ofn n <- v] (S n) = gview a n ++ [v].
Proof.
  intros A a n v H. rewrite gview_S. f_equal.
  - apply gview_ext. intros k Hk. apply get_other_phi.
    pose proof (to_Z_bounded (PArray.length a)).
    rewrite !phi_ofn by (rewrite wB_val; lia). lia.
  - f_equal. apply get_same. pose proof (to_Z_bounded (PArray.length a)).
    rewrite phi_ofn by (rewrite wB_val; lia). exact H.
Qed.

Lemma gview_length : forall {A : Set} (a : array A) n, List.length (gview a n) = n.
Proof. intros. unfold gview. rewrite length_map, length_seq. reflexivity. Qed.

Lemma slice0_gview : forall (a : array int) n, slice a 0 n = gview a n.
Proof. intros. unfold slice, gview. apply map_ext. intros k. rewrite Z.add_0_l. reflexivity. Qed.

Lemma iota_spec : forall n, ((φ n) <= 4194303)%Z ->
  forall z k a (H : Acc (Zwf 0) (gap n k)), gap n k = z -> ((φ k) <= (φ n))%Z ->
  PArray.length a = n -> (forall q, ((φ q) < (φ k))%Z -> a.[q] = q) ->
  PArray.length (iota_loop n k a H) = n /\ forall q, ((φ q) < (φ n))%Z -> (iota_loop n k a H).[q] = q.
Proof.
  intros n Hn z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k a H Hz Hk Ha Hq. destruct H as [Hacc]. cbn [iota_loop].
  destruct (bdec (k <? n)) as [Hlt | Hge].
  - destruct (step_le n k Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    apply (IH (gap n (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ Hn0 eq_refl ltac:(lia)).
    + rewrite len_set. exact Ha.
    + intros q Hq'. destruct (Z.eq_dec (φ q) (φ k)) as [Eq | Ne].
      * apply phi_eq in Eq. subst q. apply get_same. lia.
      * rewrite get_other_phi by lia. apply Hq. lia.
  - rewrite ltb_false in Hge. split; [exact Ha|]. intros q Hq'. apply Hq. lia.
Qed.

Lemma filter_le_length : forall {A} (f : A -> bool) l, (List.length (filter f l) <= List.length l)%nat.
Proof. intros A f l. induction l as [|a l IH]; simpl; [lia|]. destruct (f a); simpl; lia. Qed.

Section Emit.
Variables (names : array pstring) (lab csz boff badj byname : array int) (V : int).
Hypothesis HV : ((φ V) <= 4194302)%Z.

Definition pg (v : int) : bool := (1 <? csz.[lab.[v]]) && (badj.[boff.[lab.[v]]] =? v).
Definition pa (v : int) : bool := negb (1 <? csz.[lab.[v]]).

Lemma emit_spec : forall z k s (H : Acc (Zwf 0) (gap V k)), gap V k = z -> ((φ k) <= (φ V))%Z ->
  PArray.length (gord s) = V -> PArray.length (av s) = V ->
  (φ (gn s)) = Z.of_nat (List.length (filter pg (slice byname 0 (nz k)))) ->
  (φ (an s)) = Z.of_nat (List.length (filter pa (slice byname 0 (nz k)))) ->
  gview (gord s) (nz (gn s)) = map (fun v => lab.[v]) (filter pg (slice byname 0 (nz k))) ->
  gview (av s) (nz (an s)) = map (fun v => names.[v]) (filter pa (slice byname 0 (nz k))) ->
  let r := emit_loop names lab csz boff badj byname V k s H in
  PArray.length (gord r) = V /\ PArray.length (av r) = V /\
  (φ (gn r)) = Z.of_nat (List.length (filter pg (slice byname 0 (nz V)))) /\
  (φ (an r)) = Z.of_nat (List.length (filter pa (slice byname 0 (nz V)))) /\
  gview (gord r) (nz (gn r)) = map (fun v => lab.[v]) (filter pg (slice byname 0 (nz V))) /\
  gview (av r) (nz (an r)) = map (fun v => names.[v]) (filter pa (slice byname 0 (nz V))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k [go g a n] H Hz Hk L1 L2 G1 A1 G2 A2. destruct H as [Hacc]. cbn [emit_loop].
  cbn [gord gn av an] in *.
  destruct (bdec (k <? V)) as [Hlt | Hge].
  - destruct (step_le V k Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    assert (Hsl : slice byname 0 (nz (k + 1)) = slice byname 0 (nz k) ++ [byname.[k]]).
    { rewrite nz_add1 by lia. rewrite slice_S. f_equal. f_equal. f_equal.
      rewrite Z.add_0_l, nz_phi. apply of_to_Z. }
    pose proof (filter_le_length pg (slice byname 0 (nz k))) as Fg.
    pose proof (filter_le_length pa (slice byname 0 (nz k))) as Fa.
    rewrite slice0_length in Fg, Fa. pose proof (nz_phi k) as Nk.
    assert (Hpg : pg byname.[k] = ((1 <? csz.[lab.[byname.[k]]]) && (badj.[boff.[lab.[byname.[k]]]] =? byname.[k]))) by reflexivity.
    assert (Hpa : pa byname.[k] = negb (1 <? csz.[lab.[byname.[k]]])) by reflexivity.
    destruct (1 <? csz.[lab.[byname.[k]]]) eqn:Ec.
    + destruct (badj.[boff.[lab.[byname.[k]]]] =? byname.[k]) eqn:Eb.
      * apply (IH (gap V (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ Hn eq_refl ltac:(lia));
          cbn [gord gn av an]; rewrite ?Hsl, ?filter_app; cbn [filter]; rewrite ?Hpg, ?Hpa; cbn [negb andb];
          rewrite ?app_nil_r.
        -- rewrite len_set. exact L1.
        -- exact L2.
        -- rewrite length_app. simpl. rewrite phi_add1 by lia. lia.
        -- exact A1.
        -- assert (Eg : g = ofn (nz g)) by (rewrite ofn_nz; reflexivity).
           rewrite nz_add1 by lia. rewrite Eg at 1. rewrite gview_extend by (rewrite L1, nz_phi; lia).
           rewrite G2, map_app. reflexivity.
        -- exact A2.
      * apply (IH (gap V (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ Hn eq_refl ltac:(lia));
          cbn [gord gn av an]; rewrite ?Hsl, ?filter_app; cbn [filter]; rewrite ?Hpg, ?Hpa; cbn [negb andb];
          rewrite ?app_nil_r; assumption.
    + apply (IH (gap V (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ Hn eq_refl ltac:(lia));
        cbn [gord gn av an]; rewrite ?Hsl, ?filter_app; cbn [filter]; rewrite ?Hpg, ?Hpa; cbn [negb andb];
        rewrite ?app_nil_r.
      * exact L1.
      * rewrite len_set. exact L2.
      * exact G1.
      * rewrite length_app. simpl. rewrite phi_add1 by lia. lia.
      * exact G2.
      * assert (Ea : n = ofn (nz n)) by (rewrite ofn_nz; reflexivity).
        rewrite nz_add1 by lia. rewrite Ea at 1. rewrite gview_extend by (rewrite L2, nz_phi; lia).
        rewrite A2, map_app. reflexivity.
  - rewrite ltb_false in Hge. assert (k = V) by (apply phi_eq; lia). subst k. cbn zeta.
    cbn [gord gn av an]. repeat split; assumption.
Qed.

End Emit.

Lemma copy_spec : forall (src : array pstring) n,
  forall z k (dst : array pstring) (H : Acc (Zwf 0) (gap n k)), gap n k = z -> ((φ k) <= (φ n))%Z ->
  PArray.length dst = n ->
  (forall q, ((φ q) < (φ k))%Z -> dst.[q] = src.[q]) ->
  PArray.length (copy_loop src n k dst H) = n /\
  forall q, ((φ q) < (φ n))%Z -> (copy_loop src n k dst H).[q] = src.[q].
Proof.
  intros src n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k dst H Hz Hk Hl Hq. destruct H as [Hacc]. cbn [copy_loop].
  destruct (bdec (k <? n)) as [Hlt | Hge].
  - destruct (step_le n k Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    apply (IH (gap n (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ Hn eq_refl ltac:(lia)).
    + rewrite len_set. exact Hl.
    + intros q Hq'. destruct (Z.eq_dec (φ q) (φ k)) as [Eq | Ne].
      * apply phi_eq in Eq. subst q. apply get_same. lia.
      * rewrite get_other_phi by lia. apply Hq. lia.
  - rewrite ltb_false in Hge. split; [exact Hl|]. intros q Hq'. apply Hq. lia.
Qed.

Lemma inner_spec : forall (names : array pstring) (badj : array int) (st n : int),
  ((φ st) + (φ n) < wB)%Z ->
  forall z k g (H : Acc (Zwf 0) (gap n k)), gap n k = z -> ((φ k) <= (φ n))%Z ->
  PArray.length g = n ->
  (forall q, ((φ q) < (φ k))%Z -> g.[q] = names.[badj.[st + q]]) ->
  PArray.length (inner_loop names badj st n k g H) = n /\
  forall q, ((φ q) < (φ n))%Z -> (inner_loop names badj st n k g H).[q] = names.[badj.[st + q]].
Proof.
  intros names badj st n Hb z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k g H Hz Hk Hl Hq. destruct H as [Hacc]. cbn [inner_loop].
  destruct (bdec (k <? n)) as [Hlt | Hge].
  - destruct (step_le n k Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    apply (IH (gap n (k + 1)) ltac:(unfold Zwf, gap in *; lia) (k + 1) _ Hn eq_refl ltac:(lia)).
    + rewrite len_set. exact Hl.
    + intros q Hq'. destruct (Z.eq_dec (φ q) (φ k)) as [Eq | Ne].
      * apply phi_eq in Eq. subst q. apply get_same. lia.
      * rewrite get_other_phi by lia. apply Hq. lia.
  - rewrite ltb_false in Hge. split; [exact Hl|]. intros q Hq'. apply Hq. lia.
Qed.

Lemma group_arr_spec : forall names boff badj c,
  ((φ (boff.[c])) <= (φ (boff.[c + 1])) <= 4194303)%Z ->
  PArray.length (group_arr names boff badj c) = boff.[c + 1] - boff.[c] /\
  ((φ (boff.[c + 1] - boff.[c])) = (φ (boff.[c + 1])) - (φ (boff.[c])))%Z /\
  gview (group_arr names boff badj c) (nz (boff.[c + 1] - boff.[c]))
  = map (fun v => names.[v]) (slice badj (φ (boff.[c])) (nz (boff.[c + 1] - boff.[c]))).
Proof.
  intros names boff badj c Hb. unfold group_arr.
  assert (En : (φ (boff.[c + 1] - boff.[c])) = ((φ (boff.[c + 1])) - (φ (boff.[c])))%Z) by (apply phi_sub; lia).
  destruct (inner_spec names badj (boff.[c]) (boff.[c + 1] - boff.[c]) ltac:(rewrite En, wB_val; lia)
              _ 0 (PArray.make (boff.[c + 1] - boff.[c]) (PrimString.make 0 0))
              (Zwf_well_founded 0 (gap (boff.[c + 1] - boff.[c]) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(apply len_make; lia)
              ltac:(intros q Hq; change (φ 0) with 0%Z in Hq; pose proof (to_Z_bounded q); lia))
    as [I1 I2].
  split; [exact I1|]. split; [exact En|].
  unfold gview, slice. rewrite map_map. apply map_ext_in. intros k Hk. apply in_seq in Hk.
  pose proof (nz_phi (boff.[c + 1] - boff.[c])) as Nn. pose proof (to_Z_bounded (boff.[c])) as Bc.
  assert (Ek : (φ (ofn k)) = Z.of_nat k) by (apply phi_ofn; rewrite wB_val; lia).
  rewrite I2 by lia.
  f_equal. f_equal. apply phi_eq.
  rewrite phi_add by (rewrite Ek, wB_val; lia). rewrite Ek, of_Z_spec, Z.mod_small by (rewrite wB_val; lia).
  reflexivity.
Qed.

Lemma groups_spec : forall names boff badj gord G,
  forall z g out (H : Acc (Zwf 0) (gap G g)), gap G g = z -> ((φ g) <= (φ G))%Z ->
  PArray.length out = G ->
  (forall q, ((φ q) < (φ g))%Z -> out.[q] = group_arr names boff badj gord.[q]) ->
  PArray.length (groups_loop names boff badj gord G g out H) = G /\
  forall q, ((φ q) < (φ G))%Z -> (groups_loop names boff badj gord G g out H).[q] = group_arr names boff badj gord.[q].
Proof.
  intros names boff badj gord G z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros g out H Hz Hk Hl Hq. destruct H as [Hacc]. cbn [groups_loop].
  destruct (bdec (g <? G)) as [Hlt | Hge].
  - destruct (step_le G g Hlt) as [E1 E2]. gen_acc. rewrite ltb_true in Hlt.
    apply (IH (gap G (g + 1)) ltac:(unfold Zwf, gap in *; lia) (g + 1) _ Hn eq_refl ltac:(lia)).
    + rewrite len_set. exact Hl.
    + intros q Hq'. destruct (Z.eq_dec (φ q) (φ g)) as [Eq | Ne].
      * apply phi_eq in Eq. subst q. apply get_same. lia.
      * rewrite get_other_phi by lia. apply Hq. lia.
  - rewrite ltb_false in Hge. split; [exact Hl|]. intros q Hq'. apply Hq. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Strings: the math reading of a primitive string                     *)
(* ------------------------------------------------------------------ *)

Definition char_of (c : int) : Ascii.ascii := Ascii.ascii_of_N (Z.to_N (φ c)).
Definition to_math (s : pstring) : String.string :=
  String.string_of_list_ascii (map char_of (PrimStringAxioms.to_list s)).

Lemma char_valid : forall s c, In c (PrimStringAxioms.to_list s) -> ((φ c) < 256)%Z.
Proof.
  intros s c Hc. pose proof (PrimStringAxioms.to_list_char63_valid s) as Hv.
  rewrite Forall_forall in Hv. specialize (Hv c Hc). unfold PrimStringAxioms.char63_valid in Hv.
  rewrite <- Hv. rewrite land_spec'. change (φ 255) with (Z.ones 8). rewrite Z.land_ones by lia.
  match goal with |- context [(?a mod ?b)%Z] => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) end.
  change (2 ^ 8)%Z with 256%Z in *. lia.
Qed.

Lemma string_len : forall l, String.length (String.string_of_list_ascii l) = List.length l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma string_get : forall l k, String.get k (String.string_of_list_ascii l) = nth_error l k.
Proof. induction l as [|a l IH]; intros [|k]; simpl; try reflexivity. apply IH. Qed.

Lemma N_char : forall c, ((φ c) < 256)%Z -> Ascii.N_of_ascii (char_of c) = Z.to_N (φ c).
Proof. intros c H. unfold char_of. apply Ascii.N_ascii_embedding. lia. Qed.

Lemma to_math_length : forall x, String.length (to_math x) = nz (PrimString.length x).
Proof.
  intros x. unfold to_math. rewrite string_len, length_map, <- PrimStringAxioms.length_spec. reflexivity.
Qed.

Lemma to_math_get : forall x k, (k < String.length (to_math x))%nat ->
  String.get k (to_math x) = Some (char_of (PrimString.get x (ofn k))).
Proof.
  intros x k Hk. pose proof Hk as Hk'. rewrite to_math_length in Hk'. unfold to_math. rewrite string_get.
  rewrite nth_error_map. rewrite PrimStringAxioms.get_spec.
  assert (Ek : Z.to_nat (φ (ofn k)) = k).
  { rewrite phi_ofn; [lia|]. pose proof (nz_phi (PrimString.length x)). rewrite wB_val. lia. }
  rewrite Ek. rewrite nth_error_nth' with (d := 0); [reflexivity|].
  rewrite <- PrimStringAxioms.length_spec. exact Hk'.
Qed.

Lemma get_valid : forall x k, (k < nz (PrimString.length x))%nat -> ((φ (PrimString.get x (ofn k))) < 256)%Z.
Proof.
  intros x k Hk. apply (char_valid x). rewrite PrimStringAxioms.get_spec.
  assert (Ek : Z.to_nat (φ (ofn k)) = k).
  { rewrite phi_ofn; [lia|]. pose proof (nz_phi (PrimString.length x)). rewrite wB_val. lia. }
  rewrite Ek. apply nth_In. rewrite <- PrimStringAxioms.length_spec. exact Hk.
Qed.

Lemma repr_self : forall x, repr x (to_math x).
Proof.
  intros x. split.
  - rewrite to_math_length. apply nz_phi.
  - intros k Hk. exists (char_of (PrimString.get x (ofn k))). split; [apply to_math_get; exact Hk|].
    unfold repr, repr_uint. rewrite N_char; [reflexivity|]. apply get_valid.
    rewrite to_math_length in Hk. exact Hk.
Qed.

Lemma string_ext : forall s t, String.length s = String.length t ->
  (forall k, (k < String.length s)%nat -> String.get k s = String.get k t) -> s = t.
Proof.
  induction s as [|a s IH]; intros [|b t] Hl Hg; simpl in *; try discriminate; [reflexivity|].
  pose proof (Hg 0%nat ltac:(lia)) as H0. simpl in H0. injection H0 as ->. f_equal.
  apply IH; [lia|]. intros k Hk. exact (Hg (S k) ltac:(lia)).
Qed.

Lemma repr_eq : forall x s, repr x s -> s = to_math x.
Proof.
  intros x s [Hl Hg]. apply string_ext.
  - rewrite to_math_length. unfold nz. lia.
  - intros k Hk. destruct (Hg k Hk) as (c & Hc & Hr). rewrite Hc.
    rewrite to_math_get by (rewrite to_math_length; unfold nz; lia). f_equal.
    unfold repr, repr_uint in Hr. rewrite <- (Ascii.ascii_N_embedding c). rewrite <- Hr.
    reflexivity.
Qed.

Lemma soa_inj : forall l1 l2, String.string_of_list_ascii l1 = String.string_of_list_ascii l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; simpl in H; try discriminate; [reflexivity|].
  injection H as -> H. f_equal. apply IH. exact H.
Qed.

Lemma map_char_inj : forall l1 l2, (forall c, In c l1 -> (φ c) < 256)%Z -> (forall c, In c l2 -> (φ c) < 256)%Z ->
  map char_of l1 = map char_of l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H1 H2 H; simpl in H; try discriminate; [reflexivity|].
  injection H as Hab H. f_equal.
  - apply (f_equal Ascii.N_of_ascii) in Hab.
    rewrite (N_char a) in Hab by (apply H1; left; reflexivity).
    rewrite (N_char b) in Hab by (apply H2; left; reflexivity).
    apply Z2N.inj in Hab; [|apply to_Z_bounded|apply to_Z_bounded]. apply phi_eq. exact Hab.
  - apply IH; [intros c Hc; apply H1; right; exact Hc | intros c Hc; apply H2; right; exact Hc | exact H].
Qed.

Lemma to_math_inj : forall x y, to_math x = to_math y -> x = y.
Proof.
  intros x y H. apply soa_inj in H. apply map_char_inj in H; [|apply char_valid | apply char_valid].
  apply PString.to_list_inj. exact H.
Qed.

Lemma compare_lists : forall l1 l2, (forall c, In c l1 -> (φ c) < 256)%Z -> (forall c, In c l2 -> (φ c) < 256)%Z ->
  String.compare (String.string_of_list_ascii (map char_of l1)) (String.string_of_list_ascii (map char_of l2))
  = list_compare PrimInt63.compare l1 l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H1 H2;
    cbn [map String.string_of_list_ascii String.compare list_compare]; try reflexivity.
  unfold Ascii.compare.
  rewrite (N_char a) by (apply H1; left; reflexivity).
  rewrite (N_char b) by (apply H2; left; reflexivity).
  rewrite Z2N.inj_compare by (apply to_Z_bounded). rewrite <- compare_spec.
  destruct (a ?= b); try reflexivity.
  apply IH; [intros c Hc; apply H1; right; exact Hc | intros c Hc; apply H2; right; exact Hc].
Qed.

Lemma to_math_compare : forall x y, String.compare (to_math x) (to_math y) = PrimString.compare x y.
Proof.
  intros x y. unfold to_math. rewrite PrimStringAxioms.compare_spec.
  apply compare_lists; apply char_valid.
Qed.

Lemma repr_arr_eq : forall (x : array pstring) (l : list String.string), repr x l ->
  l = map to_math (gview x (nz (PArray.length x))).
Proof.
  intros x l [Hl Hc]. apply nth_error_ext. intros k.
  unfold gview. rewrite !nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec k (nz (PArray.length x))) as [Hk | Hk].
  - assert (Hk' : (k < List.length l)%nat) by (pose proof (nz_phi (PArray.length x)); unfold nz in *; lia).
    destruct (Hc k Hk') as (m & Hm & Hr). rewrite Hm. simpl. f_equal.
    rewrite (repr_eq _ _ Hr). reflexivity.
  - apply nth_error_None. pose proof (nz_phi (PArray.length x)). unfold nz in *. lia.
Qed.

Lemma repr_arr_self : forall (x : array pstring), repr x (map to_math (gview x (nz (PArray.length x)))).
Proof.
  intros x. split.
  - rewrite length_map, gview_length. apply nz_phi.
  - intros k Hk. rewrite length_map, gview_length in Hk.
    exists (to_math x.[ofn k]). split.
    + unfold gview. rewrite nth_error_map, nth_error_map, nth_error_seq.
      destruct (Nat.ltb_spec k (nz (PArray.length x))); [reflexivity | lia].
    + apply repr_self.
Qed.

Lemma repr_nested_self : forall (g : array (array pstring)),
  repr g (map (fun a => map to_math (gview a (nz (PArray.length a)))) (gview g (nz (PArray.length g)))).
Proof.
  intros g. split.
  - rewrite length_map, gview_length. apply nz_phi.
  - intros k Hk. rewrite length_map, gview_length in Hk.
    exists (map to_math (gview g.[ofn k] (nz (PArray.length g.[ofn k])))). split.
    + unfold gview at 2. rewrite nth_error_map, nth_error_map, nth_error_seq.
      destruct (Nat.ltb_spec k (nz (PArray.length g))); [reflexivity | lia].
    + apply repr_arr_self.
Qed.

(* ------------------------------------------------------------------ *)
(* The answer, on the math side                                        *)
(* ------------------------------------------------------------------ *)

Lemma SS_filter : forall {A} (R : A -> A -> Prop) f l, StronglySorted R l -> StronglySorted R (filter f l).
Proof.
  intros A R f l H. induction H as [|a l Hs IH Hf]; simpl; [constructor|].
  destruct (f a); [|exact IH]. constructor; [exact IH|].
  rewrite Forall_forall in *. intros x Hx. apply filter_In in Hx as [Hx _]. apply Hf. exact Hx.
Qed.

Lemma SS_map_in : forall {A B} (R : A -> A -> Prop) (R' : B -> B -> Prop) (f : A -> B) l,
  (forall a b, In a l -> In b l -> R a b -> R' (f a) (f b)) ->
  StronglySorted R l -> StronglySorted R' (map f l).
Proof.
  intros A B R R' f l Hi H. induction H as [|a l Hs IH Hf]; simpl; [constructor|].
  constructor.
  - apply IH. intros x y Hx Hy. apply Hi; right; assumption.
  - rewrite Forall_forall in *. intros y Hy. apply in_map_iff in Hy as (b & <- & Hb).
    apply Hi; [left; reflexivity | right; exact Hb | apply Hf; exact Hb].
Qed.

Section Final.
Variables (src dst : list String.string) (V : int) (nm : int -> String.string)
          (E : int -> int -> Prop) (lab : int -> int) (BN : list int) (pg pa : int -> bool).

Notation R := (clos_refl_trans int E).

Definition eqlab (v : int) : int -> bool := fun w => lab w =? lab v.
Definition loopyv (u : int) : Prop := exists w, ((φ w) < (φ V))%Z /\ w <> u /\ lab w = lab u.

Hypothesis Hstreet : forall a b, street src dst a b <-> exists u v, E u v /\ a = nm u /\ b = nm v.
Hypothesis Hstore : forall a, store src dst a <-> exists v, ((φ v) < (φ V))%Z /\ a = nm v.
Hypothesis HEV : forall u v, E u v -> ((φ u) < (φ V))%Z /\ ((φ v) < (φ V))%Z.
Hypothesis Hinj : forall u v, ((φ u) < (φ V))%Z -> ((φ v) < (φ V))%Z -> nm u = nm v -> u = v.
Hypothesis Hlab : forall u v, ((φ u) < (φ V))%Z -> ((φ v) < (φ V))%Z -> (lab u = lab v <-> (R u v /\ R v u)).
Hypothesis HBN : forall v, In v BN <-> ((φ v) < (φ V))%Z.
Hypothesis HBNnd : NoDup BN.
Hypothesis HBNs : StronglySorted (fun u v => str_lt (nm u) (nm v)) BN.
Hypothesis Hpg : forall v, In v BN -> (pg v = true <-> (loopyv v /\ exists rest, filter (eqlab v) BN = v :: rest)).
Hypothesis Hpa : forall v, In v BN -> (pa v = true <-> ~ loopyv v).

Lemma reach_nm : forall a b, reaches src dst a b -> forall u, ((φ u) < (φ V))%Z -> a = nm u ->
  exists w, ((φ w) < (φ V))%Z /\ b = nm w /\ R u w.
Proof.
  intros a b H. apply clos_rt_rt1n in H. induction H as [a | a c b Hac Hcb IH]; intros u Hu Ha.
  - exists u. split; [exact Hu|]. split; [exact Ha | apply rt_refl].
  - apply Hstreet in Hac as (u' & v' & Euv & Ea & Ec).
    destruct (HEV u' v' Euv) as [Hu' Hv'].
    assert (u' = u) by (apply Hinj; [exact Hu' | exact Hu | congruence]). subst u'.
    destruct (IH v' Hv' Ec) as (w & Hw & Eb & Rvw).
    exists w. split; [exact Hw|]. split; [exact Eb|].
    eapply rt_trans; [apply rt_step; exact Euv | exact Rvw].
Qed.

Lemma R_reach : forall u w, R u w -> reaches src dst (nm u) (nm w).
Proof.
  intros u w H. induction H as [u w Huw | u | u v w _ IH1 _ IH2].
  - apply rt_step. apply Hstreet. exists u, w. auto.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma reach_store : forall a b, reaches src dst a b -> a <> b -> exists u, ((φ u) < (φ V))%Z /\ a = nm u.
Proof.
  intros a b H Hne. apply clos_rt_rt1n in H. destruct H as [| c z Hac _]; [contradiction|].
  apply Hstreet in Hac as (u & v & Euv & Ea & _). exists u. split; [exact (proj1 (HEV u v Euv)) | exact Ea].
Qed.

Lemma together_nm : forall u b, ((φ u) < (φ V))%Z ->
  (together src dst (nm u) b <-> exists w, ((φ w) < (φ V))%Z /\ b = nm w /\ lab w = lab u).
Proof.
  intros u b Hu. split.
  - intros [H1 H2]. destruct (reach_nm _ _ H1 u Hu eq_refl) as (w & Hw & Eb & Ruw).
    subst b. destruct (reach_nm _ _ H2 w Hw eq_refl) as (u' & Hu' & Eu & Rwu).
    assert (u' = u) by (apply Hinj; [exact Hu' | exact Hu | congruence]). subst u'.
    exists w. split; [exact Hw|]. split; [reflexivity|]. apply Hlab; [exact Hw | exact Hu | split; assumption].
  - intros (w & Hw & -> & Hl). apply (Hlab w u Hw Hu) in Hl as [R1 R2].
    split; apply R_reach; assumption.
Qed.

Lemma loopy_nm : forall a, loopy src dst a <-> exists u, ((φ u) < (φ V))%Z /\ a = nm u /\ loopyv u.
Proof.
  intros a. split.
  - intros (b & Hne & Ht). destruct (reach_store a b (proj1 Ht) (fun F => Hne (eq_sym F))) as (u & Hu & ->).
    apply (together_nm u b Hu) in Ht as (w & Hw & -> & Hl).
    exists u. split; [exact Hu|]. split; [reflexivity|]. exists w. split; [exact Hw|]. split; [|exact Hl].
    intros ->. apply Hne. reflexivity.
  - intros (u & Hu & -> & (w & Hw & Hne & Hl)). exists (nm w). split.
    + intros F. apply Hne. apply Hinj; [exact Hw | exact Hu | exact F].
    + apply (together_nm u (nm w) Hu). exists w. auto.
Qed.

Lemma in_eqlab : forall v w, In w (filter (eqlab v) BN) <-> ((φ w) < (φ V))%Z /\ lab w = lab v.
Proof.
  intros v w. rewrite filter_In, HBN. unfold eqlab. rewrite eqb_true. tauto.
Qed.

Lemma loopy_regions_math :
  loopy_regions_spec src dst
    (map (fun v => map nm (filter (eqlab v) BN)) (filter pg BN), map nm (filter pa BN)).
Proof.
  unfold loopy_regions_spec.
  assert (Hpg' : forall v, In v (filter pg BN) -> In v BN /\ loopyv v /\ exists rest, filter (eqlab v) BN = v :: rest).
  { intros v Hv. apply filter_In in Hv as [Hv Hp]. apply (Hpg v Hv) in Hp. tauto. }
  assert (Hsort : forall f, StronglySorted str_lt (map nm (filter f BN))).
  { intros f. apply (SS_map_in (fun u v => str_lt (nm u) (nm v))); [intros; assumption|].
    apply SS_filter. exact HBNs. }
  split; [|split; [|split; [|split]]].
  - intros g Hg. apply in_map_iff in Hg as (v & <- & Hv). destruct (Hpg' v Hv) as (HvB & Hlv & _).
    pose proof (proj1 (HBN v) HvB) as HvV.
    split; [|apply Hsort]. split.
    + destruct Hlv as (w & Hw & Hne & Hl).
      assert (Hinc : incl [v; w] (filter (eqlab v) BN)).
      { intros z [<- | [<- | []]]; apply in_eqlab; auto. }
      pose proof (NoDup_incl_length (l := [v; w]) ltac:(constructor; [intros [F | []]; congruence | constructor; [intros [] | constructor]]) Hinc) as HL.
      unfold len. rewrite length_map. simpl in HL. lia.
    + exists (nm v). intros b. rewrite (together_nm v b HvV). rewrite in_map_iff. split.
      * intros (w & <- & Hw). apply in_eqlab in Hw as [Hw Hl]. exists w. auto.
      * intros (w & Hw & -> & Hl). exists w. split; [reflexivity|]. apply in_eqlab. auto.
  - intros a Ha. apply loopy_nm in Ha as (u & Hu & -> & Hlu).
    assert (HuF : In u (filter (eqlab u) BN)) by (apply in_eqlab; auto).
    destruct (filter (eqlab u) BN) as [|h rest] eqn:Ef; [destruct HuF|].
    assert (Hh : In h (filter (eqlab u) BN)) by (rewrite Ef; left; reflexivity).
    apply in_eqlab in Hh as [HhV Hhl].
    assert (Esame : filter (eqlab h) BN = filter (eqlab u) BN).
    { apply filter_ext. intros z. unfold eqlab. rewrite Hhl. reflexivity. }
    assert (Hhpg : In h (filter pg BN)).
    { apply filter_In. split; [apply HBN; exact HhV|]. apply Hpg; [apply HBN; exact HhV|]. split.
      - destruct Hlu as (w & Hw & Hne & Hl).
        destruct (idec h u) as [-> | Hhu].
        + exists w. auto.
        + exists u. split; [exact Hu|]. split; [intros F; apply Hhu; symmetry; exact F | symmetry; exact Hhl].
      - exists rest. rewrite Esame. exact Ef. }
    exists (map nm (filter (eqlab h) BN)). split.
    + apply in_map_iff. exists h. auto.
    + rewrite Esame, Ef. apply in_map. exact HuF.
  - apply (SS_map_in (fun u v => str_lt (nm u) (nm v))).
    + intros v1 v2 H1 H2 Hlt. destruct (Hpg' v1 H1) as (_ & _ & r1 & E1).
      destruct (Hpg' v2 H2) as (_ & _ & r2 & E2). rewrite E1, E2. simpl. left. exact Hlt.
    + apply SS_filter. exact HBNs.
  - apply Hsort.
  - intros a. rewrite in_map_iff. split.
    + intros (v & <- & Hv). apply filter_In in Hv as [HvB Hp]. apply (Hpa v HvB) in Hp.
      pose proof (proj1 (HBN v) HvB) as HvV.
      split; [apply Hstore; exists v; auto|].
      intros Hl. apply loopy_nm in Hl as (u & Hu & Eu & Hlu).
      assert (u = v) by (apply Hinj; [exact Hu | exact HvV | congruence]). subst u. contradiction.
    + intros [Hs Hl]. apply Hstore in Hs as (v & HvV & ->). exists v. split; [reflexivity|].
      apply filter_In. split; [apply HBN; exact HvV|]. apply Hpa; [apply HBN; exact HvV|].
      intros Hlv. apply Hl. apply loopy_nm. exists v. auto.
Qed.

End Final.

(* ------------------------------------------------------------------ *)
(* Glue                                                                *)
(* ------------------------------------------------------------------ *)

Lemma Perm_filter : forall {A} (f : A -> bool) l l', Permutation l l' ->
  Permutation (filter f l) (filter f l').
Proof.
  intros A f l l' H. induction H as [| x l l' H IH | x y l | l l' l'' H1 IH1 H2 IH2]; simpl.
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; reflexivity.
  - eapply perm_trans; eassumption.
Qed.

Lemma filter_map_comm : forall {A B} (f : B -> bool) (g : A -> B) l,
  filter f (map g l) = map g (filter (fun x => f (g x)) l).
Proof.
  intros A B f g l. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f (g a)); simpl; rewrite IH; reflexivity.
Qed.

Lemma In_combine_nth : forall {A B} (l1 : list A) (l2 : list B) a b,
  In (a, b) (combine l1 l2) <-> exists k, nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros A B l1. induction l1 as [|x l1 IH]; intros [|y l2] a b; simpl.
  - split; [intros [] | intros (k & H & _); destruct k; discriminate].
  - split; [intros [] | intros (k & H & _); destruct k; discriminate].
  - split; [intros [] | intros (k & _ & H); destruct k; discriminate].
  - rewrite IH. split.
    + intros [H | (k & H1 & H2)].
      * injection H as -> ->. exists 0%nat. auto.
      * exists (S k). auto.
    + intros ([|k] & H1 & H2); simpl in *.
      * injection H1 as ->. injection H2 as ->. left. reflexivity.
      * right. exists k. auto.
Qed.

Lemma name_le_total : forall names a b, name_le names a b = true \/ name_le names b a = true.
Proof.
  intros names a b. unfold name_le.
  destruct (PrimString.compare names.[a] names.[b]) eqn:E; auto.
  right. rewrite PString.compare_antisym, E. reflexivity.
Qed.

Lemma name_le_trans : forall names a b c,
  name_le names a b = true -> name_le names b c = true -> name_le names a c = true.
Proof.
  intros names a b c. unfold name_le.
  destruct (PrimString.compare names.[a] names.[b]) eqn:E1; try discriminate;
  destruct (PrimString.compare names.[b] names.[c]) eqn:E2; try discriminate; intros _ _.
  - apply PString.compare_eq in E1, E2. rewrite E1, E2, PString.compare_refl. reflexivity.
  - apply PString.compare_eq in E1. rewrite E1, E2. reflexivity.
  - apply PString.compare_eq in E2. rewrite <- E2, E1. reflexivity.
  - rewrite (PString.compare_trans Lt _ _ _ E1 E2). reflexivity.
Qed.

Lemma SS_nodup_impl : forall {A} (R R' : A -> A -> Prop) l, NoDup l ->
  (forall a b, In a l -> In b l -> a <> b -> R a b -> R' a b) ->
  StronglySorted R l -> StronglySorted R' l.
Proof.
  intros A R R' l Hn Hi H. induction H as [|a l Hs IH Hf]; [constructor|].
  inversion Hn as [|a' l' Ha Hn']; subst. constructor.
  - apply IH; [exact Hn'|]. intros x y Hx Hy. apply Hi; right; assumption.
  - rewrite Forall_forall in *. intros y Hy. apply Hi; [left; reflexivity | right; exact Hy | |apply Hf; exact Hy].
    intros ->. contradiction.
Qed.

Lemma nth_error_mt : forall (x : array pstring) n k, (k < n)%nat ->
  nth_error (map to_math (gview x n)) k = Some (to_math x.[ofn k]).
Proof.
  intros x n k Hk. unfold gview. rewrite !nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec k n); [reflexivity | lia].
Qed.

Lemma nth_error_mt_inv : forall (x : array pstring) n k a,
  nth_error (map to_math (gview x n)) k = Some a -> (k < n)%nat /\ a = to_math x.[ofn k].
Proof.
  intros x n k a H. unfold gview in H. rewrite !nth_error_map, nth_error_seq in H.
  destruct (Nat.ltb_spec k n); [|discriminate]. simpl in H. injection H as <-. auto.
Qed.

Lemma len_filter_two : forall (l : list int) v, NoDup l -> In v l ->
  ((2 <= List.length l)%nat <-> exists w, In w l /\ w <> v).
Proof.
  intros l v Hn Hv. split.
  - intros H. destruct l as [|a [|b l]]; simpl in H; try lia.
    inversion Hn as [|a' l' Ha _]; subst.
    destruct (idec a v) as [-> | Hav].
    + exists b. split; [right; left; reflexivity|]. intros ->. apply Ha. left. reflexivity.
    + exists a. split; [left; reflexivity | exact Hav].
  - intros (w & Hw & Hne).
    assert (Hinc : incl [v; w] l) by (intros z [<- | [<- | []]]; assumption).
    pose proof (NoDup_incl_length (l := [v; w])
                  ltac:(constructor; [intros [F | []]; congruence | constructor; [intros [] | constructor]]) Hinc).
    simpl in H. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The main theorem                                                    *)
(* ------------------------------------------------------------------ *)

Theorem loopy_impl_correct : forall (src dst : list String.string) (x y : array pstring),
  valid_input src dst -> repr x src -> repr y dst ->
  exists o, repr (loopy_impl x y) o /\ loopy_regions_spec src dst o.
Proof.
  intros src dst x y Hv Hx Hy.
  pose proof (repr_arr_eq x src Hx) as Esrc. pose proof (repr_arr_eq y dst Hy) as Edst.
  assert (Lx : Z.of_nat (List.length src) = (φ (PArray.length x))) by exact (proj1 Hx).
  assert (Ly : Z.of_nat (List.length dst) = (φ (PArray.length y))) by exact (proj1 Hy).
  destruct Hv as [Vn Vl Vs Vd Vdist Vnr]. unfold len in Vn, Vl.
  assert (Hm : ((φ (PArray.length x)) <= 10000)%Z) by lia.
  pose proof (hash_phase x y Hm) as Hok.
  unfold loopy_impl. cbv zeta.
  set (m := PArray.length x) in *.
  assert (Hmy : nz (PArray.length y) = nz m) by (unfold nz; lia).
  set (r0 := idloop x y m 0 _ _ _ _) in *.
  set (st := fst (fst r0)) in *. set (is := snd (fst r0)) in *. set (id := snd r0) in *.
  set (V := hc st) in *. set (names := hn st) in *.
  destruct Hok as (Hinv & HcV & Lis & Lid & Hids & Hnm).
  destruct Hinv as (_ & Lnames & HcB & Hinj & _ & _ & _).
  fold V names in HcV, HcB, Hinj, Hids, Hnm, Lnames.
  assert (HV : ((φ V) <= 20000)%Z) by lia.
  assert (HVb : ((φ V) <= 4194302)%Z) by lia.
  set (E := fun u v => exists k, ((φ k) < (φ m))%Z /\ is.[k] = u /\ id.[k] = v).
  assert (HEV : forall u v, E u v -> ((φ u) < (φ V))%Z /\ ((φ v) < (φ V))%Z).
  { intros u v (k & Hk & <- & <-). destruct (Hids k Hk) as (A1 & _ & A3 & _). auto. }
  (* the two CSRs *)
  assert (Hes1 : forall k, ((φ k) < (φ m))%Z -> ((φ (is.[k])) < (φ V))%Z) by (intros k Hk; apply (Hids k Hk)).
  assert (Hes2 : forall k, ((φ k) < (φ m))%Z -> ((φ (id.[k])) < (φ V))%Z) by (intros k Hk; apply (Hids k Hk)).
  pose proof (csr_ok (fun k => is.[k]) (fun k => id.[k]) V m HVb ltac:(lia) Hes1) as Cg.
  pose proof (csr_ok (fun k => id.[k]) (fun k => is.[k]) V m HVb ltac:(lia) Hes2) as Cgt.
  set (g := csr V m (fun k => is.[k]) (fun k => id.[k])) in *.
  set (gt := csr V m (fun k => id.[k]) (fun k => is.[k])) in *.
  assert (Hoff1 : forall u, ((φ u) < (φ V))%Z -> ((φ ((fst g).[u])) <= (φ ((fst g).[u + 1])))%Z).
  { intros u Hu. destruct Cg as (_ & _ & C3 & _). destruct (C3 u Hu). lia. }
  assert (Hoff2 : forall u, ((φ u) < (φ V))%Z -> ((φ ((fst gt).[u])) <= (φ ((fst gt).[u + 1])))%Z).
  { intros u Hu. destruct Cgt as (_ & _ & C3 & _). destruct (C3 u Hu). lia. }
  assert (Hsound1 : forall u j, ((φ u) < (φ V))%Z -> ((φ ((fst g).[u])) <= (φ j) < (φ ((fst g).[u + 1])))%Z ->
                      E u ((snd g).[j])).
  { intros u j Hu Hj. destruct (csr_sound _ _ _ _ _ _ Cg ltac:(lia) u j Hu Hj) as (k & Hk & E1 & E2).
    exists k. auto. }
  assert (Hcomp1 : forall u v, E u v ->
                     exists j, ((φ ((fst g).[u])) <= (φ j) < (φ ((fst g).[u + 1])))%Z /\ (snd g).[j] = v).
  { intros u v (k & Hk & <- & <-). exact (csr_complete _ _ _ _ _ _ Cg Hes1 k Hk). }
  assert (Hsound2 : forall u j, ((φ u) < (φ V))%Z -> ((φ ((fst gt).[u])) <= (φ j) < (φ ((fst gt).[u + 1])))%Z ->
                      E ((snd gt).[j]) u).
  { intros u j Hu Hj. destruct (csr_sound _ _ _ _ _ _ Cgt ltac:(lia) u j Hu Hj) as (k & Hk & E1 & E2).
    exists k. auto. }
  assert (Hcomp2 : forall u v, E v u ->
                     exists j, ((φ ((fst gt).[u])) <= (φ j) < (φ ((fst gt).[u + 1])))%Z /\ (snd gt).[j] = v).
  { intros u v (k & Hk & <- & <-). exact (csr_complete _ _ _ _ _ _ Cgt Hes2 k Hk). }
  (* Kosaraju *)
  destruct (pass1 V (fst g) (snd g) E HVb Hoff1 Hsound1 Hcomp1 HEV) as (P & HPl & HPs & HPnd & HPin & HPf).
  set (post := dfs V (fst g) (snd g) _ _ _ _) in *.
  pose proof (pass2 V (fst gt) (snd gt) E P HVb Hoff2 Hsound2 Hcomp2 HEV HPl HPnd HPin HPf post HPs)
    as (Hl1 & Hl2 & HC).
  set (s2 := assign (fst gt) (snd gt) post _ _ _ _) in *.
  set (lab := lb s2) in *. set (C := cc s2) in *.
  assert (HC1 : (φ (C + 1)) = ((φ C) + 1)%Z) by (apply phi_add1; lia).
  assert (Hlabb : forall v, ((φ v) < (φ V))%Z -> ((φ (lab.[v])) < (φ (C + 1)))%Z).
  { intros v Hv. destruct (Hl1 v Hv). lia. }
  (* component sizes *)
  destruct (cnt_loop_spec (fun v => lab.[v]) (fun v => v) (C + 1) V ltac:(lia) Hlabb _ 0
              (PArray.make (C + 1) 0) (Zwf_well_founded 0 (gap V 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(apply len_make; lia)
              ltac:(intros u Hu; rewrite get_mk; reflexivity)) as [Cs1 Cs2].
  set (csz := cnt_loop (fun v => lab.[v]) V 0 (PArray.make (C + 1) 0) _) in *.
  (* the sort *)
  destruct (iota_spec V ltac:(lia) _ 0 (PArray.make V 0) (Zwf_well_founded 0 (gap V 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(apply len_make; lia)
              ltac:(intros q Hq; change (φ 0) with 0%Z in Hq; pose proof (to_Z_bounded q); lia))
    as [I1 I2].
  set (iota := iota_loop V 0 (PArray.make V 0) _) in *.
  destruct (msort_spec (name_le names) (name_le_total names) _ 0 V iota (PArray.make V 0)
              (Zwf_well_founded 0 (gap V 0)) eq_refl
              ltac:(rewrite I1; change (φ 0) with 0%Z; lia)
              ltac:(rewrite I1; apply len_make; lia)) as (M1 & M2 & M3 & M4 & M5).
  set (byname := fst (msort (name_le names) iota _ 0 V _)) in *.
  set (BN := slice byname 0 (nz V)).
  assert (EBN : sl byname 0 V = BN).
  { unfold sl, BN. change (φ 0) with 0%Z. rewrite Z.sub_0_r. reflexivity. }
  assert (Eiota : sl iota 0 V = map ofn (seq 0 (nz V))).
  { unfold sl. change (φ 0) with 0%Z. rewrite Z.sub_0_r. fold (nz V). rewrite slice0_gview.
    unfold gview. apply map_ext_in. intros k Hk. apply in_seq in Hk. apply I2.
    pose proof (nz_phi V). rewrite phi_ofn; [lia|]. rewrite wB_val. lia. }
  rewrite EBN, Eiota in M4. rewrite EBN in M5.
  assert (Hseq_nd : NoDup (map ofn (seq 0 (nz V)))).
  { apply NoDup_map_on; [apply seq_NoDup|]. intros a b Ha Hb E'.
    apply in_seq in Ha, Hb. pose proof (nz_phi V).
    apply (f_equal to_Z) in E'. rewrite !phi_ofn in E' by (rewrite wB_val; lia). lia. }
  assert (Hseq_in : forall v, In v (map ofn (seq 0 (nz V))) <-> ((φ v) < (φ V))%Z).
  { intros v. rewrite in_map_iff. split.
    - intros (k & <- & Hk). apply in_seq in Hk. pose proof (nz_phi V).
      rewrite phi_ofn; [lia|]. rewrite wB_val. lia.
    - intros Hv. exists (nz v). split; [apply ofn_nz|]. apply in_seq. unfold nz.
      pose proof (to_Z_bounded v). lia. }
  assert (HBN : forall v, In v BN <-> ((φ v) < (φ V))%Z).
  { intros v. rewrite <- Hseq_in. split; intros H; [exact (Permutation_in _ M4 H)|].
    exact (Permutation_in _ (Permutation_sym M4) H). }
  assert (HBNnd : NoDup BN) by exact (Permutation_NoDup (Permutation_sym M4) Hseq_nd).
  set (nm := fun v => to_math names.[v]).
  assert (HBNs : StronglySorted (fun u v => str_lt (nm u) (nm v)) BN).
  { apply (SS_nodup_impl (lep (name_le names))); [exact HBNnd| |].
    - intros a b Ha Hb Hne Hle. unfold str_lt, nm. rewrite to_math_compare.
      unfold lep, name_le in Hle.
      destruct (PrimString.compare names.[a] names.[b]) eqn:Ec; try discriminate; [|reflexivity].
      exfalso. apply Hne. apply PString.compare_eq in Ec.
      apply Hinj; [apply HBN; exact Ha | apply HBN; exact Hb | exact Ec].
    - apply Sorted_StronglySorted; [|exact M5].
      intros a b c. apply name_le_trans. }
  (* the buckets *)
  assert (Hbyn : forall k, ((φ k) < (φ V))%Z -> ((φ (byname.[k])) < (φ V))%Z).
  { intros k Hk. apply HBN. unfold BN. apply in_slice. exists (nz k). split; [unfold nz; pose proof (to_Z_bounded k); lia|].
    f_equal. rewrite Z.add_0_l, nz_phi. apply of_to_Z. }
  assert (Hes3 : forall k, ((φ k) < (φ V))%Z -> ((φ (lab.[byname.[k]])) < (φ (C + 1)))%Z)
    by (intros k Hk; apply Hlabb; apply Hbyn; exact Hk).
  pose proof (csr_ok (fun k => lab.[byname.[k]]) (fun k => byname.[k]) (C + 1) V ltac:(lia) ltac:(lia) Hes3)
    as Cb.
  set (b := csr (C + 1) V (fun k => lab.[byname.[k]]) (fun k => byname.[k])) in *.
  assert (Hbucket : forall c, outl (fun k => lab.[byname.[k]]) (fun k => byname.[k]) c (nz V)
                              = filter (fun w => lab.[w] =? c) BN).
  { intros c. unfold outl, BN. rewrite slice0_gview. unfold gview. rewrite filter_map_comm. reflexivity. }
  assert (Hcount : forall c, ((φ c) < (φ (C + 1)))%Z ->
                     (φ (csz.[c])) = Z.of_nat (List.length (filter (fun w => lab.[w] =? c) BN))).
  { intros c Hc. rewrite Cs2 by exact Hc. f_equal. unfold cntl.
    rewrite <- (length_map ofn).
    apply Permutation_length.
    assert (Em : map ofn (filter (sel (fun v => lab.[v]) c) (seq 0 (nz V)))
                 = filter (fun w => lab.[w] =? c) (map ofn (seq 0 (nz V))))
      by (rewrite filter_map_comm; reflexivity).
    rewrite Em. apply Perm_filter. apply Permutation_sym. exact M4. }
  (* the emission scan *)
  pose proof (emit_spec names lab csz (fst b) (snd b) byname V HVb _ 0
                (D3 (PArray.make V 0) 0 (PArray.make V empty_str) 0) (Zwf_well_founded 0 (gap V 0))
                eq_refl ltac:(change (φ 0) with 0%Z; lia) ltac:(apply len_make; lia)
                ltac:(apply len_make; lia) eq_refl eq_refl eq_refl eq_refl) as Hem.
  cbv zeta in Hem. fold BN in Hem.
  set (s3 := emit_loop names lab csz (fst b) (snd b) byname V 0 _ _) in *.
  destruct Hem as (Lg & La & Hgn & Han & Hgv & Hav).
  pose proof (filter_le_length (pg lab csz (fst b) (snd b)) BN) as Fg.
  pose proof (filter_le_length (pa lab csz) BN) as Fa.
  assert (LBN : List.length BN = nz V) by (unfold BN; apply slice0_length).
  rewrite LBN in Fg, Fa. pose proof (nz_phi V) as NV.
  (* the avoid array *)
  destruct (copy_spec (av s3) (an s3) _ 0 (PArray.make (an s3) empty_str)
              (Zwf_well_founded 0 (gap (an s3) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (an s3)); lia)
              ltac:(apply len_make; lia)
              ltac:(intros q Hq; change (φ 0) with 0%Z in Hq; pose proof (to_Z_bounded q); lia))
    as [A1 A2].
  set (avoid := copy_loop (av s3) (an s3) 0 _ _) in *.
  (* the groups array *)
  destruct (groups_spec names (fst b) (snd b) (gord s3) (gn s3) _ 0
              (PArray.make (gn s3) (PArray.make 0 empty_str)) (Zwf_well_founded 0 (gap (gn s3) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (gn s3)); lia)
              ltac:(apply len_make; lia)
              ltac:(intros q Hq; change (φ 0) with 0%Z in Hq; pose proof (to_Z_bounded q); lia))
    as [G1 G2].
  set (groups := groups_loop names (fst b) (snd b) (gord s3) (gn s3) 0 _ _) in *.
  (* the hypotheses of the math lemma *)
  assert (Hstreet : forall a b0, street src dst a b0 <-> exists u v, E u v /\ a = nm u /\ b0 = nm v).
  { intros a b0. unfold street. rewrite Esrc, Edst, Hmy, In_combine_nth. split.
    - intros (k & H1 & H2). apply nth_error_mt_inv in H1 as [Hk ->]. apply nth_error_mt_inv in H2 as [_ ->].
      assert (Hkk : ((φ (ofn k)) < (φ m))%Z).
      { pose proof (nz_phi m). rewrite phi_ofn; [lia | rewrite wB_val; lia]. }
      destruct (Hids _ Hkk) as (_ & N1 & _ & N2).
      exists (is.[ofn k]), (id.[ofn k]). split; [exists (ofn k); auto|]. unfold nm. rewrite N1, N2. auto.
    - intros (u & v & (k & Hk & <- & <-) & -> & ->). exists (nz k).
      assert (Hk' : (nz k < nz m)%nat) by (unfold nz; pose proof (to_Z_bounded k); lia).
      rewrite !nth_error_mt by exact Hk'. rewrite ofn_nz. destruct (Hids k Hk) as (_ & N1 & _ & N2).
      unfold nm. rewrite N1, N2. auto. }
  assert (Hstore : forall a, store src dst a <-> exists v, ((φ v) < (φ V))%Z /\ a = nm v).
  { intros a. unfold store. rewrite Esrc, Edst, Hmy. split.
    - intros [Ha | Ha]; apply In_nth_error in Ha as (k & Hk); apply nth_error_mt_inv in Hk as [Hk ->];
        (assert (Hkk : ((φ (ofn k)) < (φ m))%Z)
           by (pose proof (nz_phi m); rewrite phi_ofn; [lia | rewrite wB_val; lia]));
        destruct (Hids _ Hkk) as (B1 & N1 & B3 & N2).
      + exists (is.[ofn k]). split; [exact B1|]. unfold nm. rewrite N1. reflexivity.
      + exists (id.[ofn k]). split; [exact B3|]. unfold nm. rewrite N2. reflexivity.
    - intros (v & Hv & ->). destruct (Hnm v Hv) as (k & Hk & HN);
        assert (Hk' : (nz k < nz m)%nat) by (unfold nz; pose proof (to_Z_bounded k); lia).
      destruct HN as [N | N].
      + left. apply nth_error_In with (n := nz k). rewrite nth_error_mt by exact Hk'.
        rewrite ofn_nz. unfold nm. rewrite N. reflexivity.
      + right. apply nth_error_In with (n := nz k). rewrite nth_error_mt by exact Hk'.
        rewrite ofn_nz. unfold nm. rewrite N. reflexivity. }
  assert (Hinj' : forall u v, ((φ u) < (φ V))%Z -> ((φ v) < (φ V))%Z -> nm u = nm v -> u = v).
  { intros u v Hu Hv Huv. apply Hinj; [exact Hu | exact Hv | apply to_math_inj; exact Huv]. }
  destruct Cb as (Cb1 & Cb2 & Cb3 & Cb4).
  assert (Hpgpa : forall v, In v BN ->
            (pg lab csz (fst b) (snd b) v = true <->
               (loopyv V (fun v => lab.[v]) v /\
                exists rest, filter (eqlab (fun v => lab.[v]) v) BN = v :: rest)) /\
            (pa lab csz v = true <-> ~ loopyv V (fun v => lab.[v]) v)).
  { intros v HvB. pose proof (proj1 (HBN v) HvB) as HvV.
    assert (Hc : ((φ (lab.[v])) < (φ (C + 1)))%Z) by (apply Hlabb; exact HvV).
    assert (HvBB : In v (filter (eqlab (fun v => lab.[v]) v) BN)).
    { apply filter_In. split; [exact HvB|]. unfold eqlab. apply eqb_true. reflexivity. }
    assert (HBnd : NoDup (filter (eqlab (fun v => lab.[v]) v) BN)) by (apply NoDup_filter; exact HBNnd).
    assert (Hloop : loopyv V (fun v => lab.[v]) v <->
                    (2 <= List.length (filter (eqlab (fun v => lab.[v]) v) BN))%nat).
    { rewrite (len_filter_two _ v HBnd HvBB). unfold loopyv. split.
      - intros (w & Hw & Hne & Hl). exists w. split; [|exact Hne].
        apply filter_In. split; [apply HBN; exact Hw|]. unfold eqlab. apply eqb_true. exact Hl.
      - intros (w & Hw & Hne). apply filter_In in Hw as [Hw Hl]. unfold eqlab in Hl.
        apply eqb_true in Hl. exists w. split; [apply HBN; exact Hw|]. auto. }
    assert (Hcz : (φ (csz.[lab.[v]])) = Z.of_nat (List.length (filter (eqlab (fun v => lab.[v]) v) BN)))
      by exact (Hcount (lab.[v]) Hc).
    assert (Hsl : slice (snd b) (φ ((fst b).[lab.[v]])) (cntl (fun k => lab.[byname.[k]]) (lab.[v]) (nz V))
                  = filter (eqlab (fun v => lab.[v]) v) BN)
      by (rewrite Cb4 by exact Hc; rewrite Hbucket; reflexivity).
    assert (HlenB : cntl (fun k => lab.[byname.[k]]) (lab.[v]) (nz V)
                    = List.length (filter (eqlab (fun v => lab.[v]) v) BN))
      by (rewrite <- Hsl; unfold slice; rewrite length_map, length_seq; reflexivity).
    assert (Hhead : forall n, cntl (fun k => lab.[byname.[k]]) (lab.[v]) (nz V) = S n ->
              filter (eqlab (fun v => lab.[v]) v) BN
              = (snd b).[(fst b).[lab.[v]]] :: slice (snd b) ((φ ((fst b).[lab.[v]])) + 1) n).
    { intros n En. rewrite <- Hsl, En, slice_cons, of_to_Z. reflexivity. }
    split.
    - unfold pg. split.
      + intros Hp. apply Bool.andb_true_iff in Hp as [P1 P2]. rewrite ltb_true in P1.
        change (φ 1) with 1%Z in P1. apply eqb_true in P2.
        split; [apply Hloop; lia|].
        destruct (cntl (fun k => lab.[byname.[k]]) (lab.[v]) (nz V)) as [|n] eqn:En; [lia|].
        rewrite (Hhead n eq_refl), P2. eexists. reflexivity.
      + intros [Hl (rest & Hr)]. apply Bool.andb_true_iff. split.
        * rewrite ltb_true. change (φ 1) with 1%Z. apply Hloop in Hl. lia.
        * apply eqb_true.
          destruct (cntl (fun k => lab.[byname.[k]]) (lab.[v]) (nz V)) as [|n] eqn:En; [apply Hloop in Hl; lia|].
          rewrite (Hhead n eq_refl) in Hr. injection Hr as Hr _. exact Hr.
    - unfold pa. rewrite Hloop. split.
      + intros Hp F. rewrite Bool.negb_true_iff, ltb_false in Hp. change (φ 1) with 1%Z in Hp. lia.
      + intros F. rewrite Bool.negb_true_iff, ltb_false. change (φ 1) with 1%Z. lia. }
  (* the answer *)
  assert (Eav : map to_math (gview avoid (nz (PArray.length avoid))) = map nm (filter (pa lab csz) BN)).
  { rewrite A1. rewrite (gview_ext avoid (av s3)).
    - rewrite Hav, map_map. reflexivity.
    - intros k Hk. apply A2. pose proof (nz_phi (an s3)). rewrite phi_ofn; [lia | rewrite wB_val; lia]. }
  assert (Egr : map (fun a => map to_math (gview a (nz (PArray.length a)))) (gview groups (nz (PArray.length groups)))
                = map (fun v => map nm (filter (eqlab (fun v => lab.[v]) v) BN)) (filter (pg lab csz (fst b) (snd b)) BN)).
  { rewrite G1.
    assert (E1 : gview groups (nz (gn s3)) = map (group_arr names (fst b) (snd b)) (gview (gord s3) (nz (gn s3)))).
    { unfold gview. rewrite map_map. apply map_ext_in. intros k Hk. apply in_seq in Hk. apply G2.
      pose proof (nz_phi (gn s3)). rewrite phi_ofn; [lia | rewrite wB_val; lia]. }
    rewrite E1, Hgv, !map_map. apply map_ext_in. intros v Hv.
    apply filter_In in Hv as [HvB _]. pose proof (proj1 (HBN v) HvB) as HvV.
    assert (Hc : ((φ (lab.[v])) < (φ (C + 1)))%Z) by (apply Hlabb; exact HvV).
    destruct (Cb3 (lab.[v]) Hc) as [N1 N2].
    destruct (group_arr_spec names (fst b) (snd b) (lab.[v]) ltac:(pose proof (to_Z_bounded ((fst b).[lab.[v]])); lia))
      as (Q1 & Q2 & Q3).
    rewrite Q1, Q3.
    assert (En : nz ((fst b).[lab.[v] + 1] - (fst b).[lab.[v]]) = cntl (fun k => lab.[byname.[k]]) (lab.[v]) (nz V))
      by (unfold nz; rewrite Q2, N1, Z.add_simpl_l; apply Nat2Z.id).
    rewrite En, (Cb4 (lab.[v]) Hc), Hbucket, map_map. reflexivity. }
  exists (map (fun v => map nm (filter (eqlab (fun v => lab.[v]) v) BN)) (filter (pg lab csz (fst b) (snd b)) BN),
          map nm (filter (pa lab csz) BN)).
  split.
  - rewrite <- Egr, <- Eav. split; cbn [fst snd]; [apply repr_nested_self | apply repr_arr_self].
  - apply (loopy_regions_math src dst V nm E (fun v => lab.[v]) BN (pg lab csz (fst b) (snd b)) (pa lab csz)
             Hstreet Hstore HEV Hinj' (fun u v Hu Hv => Hl2 u v Hu Hv) HBN HBNs).
    + intros v Hv. exact (proj1 (Hpgpa v Hv)).
    + intros v Hv. exact (proj2 (Hpgpa v Hv)).
Qed.

Definition loopy_regions_correct :
  forall (src dst : list String.string) (x y : array PrimString.string),
  valid_input src dst -> repr x src -> repr y dst ->
  exists o : list (list String.string) * list String.string,
    repr (loopy_regions x y) o /\ loopy_regions_spec src dst o
  := loopy_impl_correct.
