(* Implementation of satisfiability (satisfiability.spec): exhaustive
   search over the 2^n assignments, each one a Uint63 bit mask.

   Code.  Each clause is first converted, once, into two bit masks: [pos]
   has bit i-1 set for every literal Xi of the clause, [neg] for every
   literal ~Xi.  They are stored in two flat arrays indexed by the clause
   number.  The search then runs t = 0 .. 2^n - 1 (variable Xi is bit i-1
   of t) and checks the clauses in order: clause k holds under t iff
   [pos.[k] land t <> 0] (a positive literal is true) or
   [neg.[k] land t <> neg.[k]] (a negative literal is false in t).  The
   first false clause ends the check of t, the first satisfying t ends the
   search.  No Z, no lists, no nat in the code.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof, as in template/polymul1.

   Proof.  The masks are characterised bit by bit (Z.testbit of their
   value: [mask_of]); a clause test under t is then [clause_true] under
   the assignment [vz t] (Xi := bit i-1 of t).  The search returns true
   iff some t < 2^n satisfies every clause; conversely every assignment v
   agrees on X1..Xn with the mask whose bit i-1 is v i ([mask_exists]),
   which is below 2^n, and the literals only mention X1..Xn. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The bit of variable Xv. *)
Definition bitof (v : int) : int := 1 << (v - 1).

(* The bit a literal contributes to the positive (s = true) or the
   negative (s = false) mask of its clause. *)
Definition lit_bits (s : bool) (l : literal uint) : int :=
  match l with
  | X v => if s then bitof v else 0
  | NotX v => if s then 0 else bitof v
  end.

(* acc lor the bits of the literals c.[i .. len-1]. *)
Fixpoint mask_loop (s : bool) (c : array (literal uint)) (len i acc : int)
    (H : Acc (Zwf 0) (gap len i)) {struct H} : int :=
  match bdec (i <? len) with
  | left Hi =>
      mask_loop s c len (i + 1) (acc lor lit_bits s c.[i])
        (Acc_inv H (dec_step len i Hi))
  | right _ => acc
  end.

Lemma mask_loop_eq : forall s c len i acc H,
  mask_loop s c len i acc H =
  match bdec (i <? len) with
  | left Hi =>
      mask_loop s c len (i + 1) (acc lor lit_bits s c.[i])
        (Acc_inv H (dec_step len i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition clause_mask (s : bool) (c : array (literal uint)) : int :=
  mask_loop s c (PArray.length c) 0 0
    (Zwf_well_founded 0 (gap (PArray.length c) 0)).

(* Cells k .. m-1 of r receive the mask of clause k. *)
Fixpoint fill_loop (s : bool) (y : array (array (literal uint))) (m k : int)
    (r : array int) (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk =>
      fill_loop s y m (k + 1) r.[k <- clause_mask s y.[k]]
        (Acc_inv H (dec_step m k Hk))
  | right _ => r
  end.

Lemma fill_loop_eq : forall s y m k r H,
  fill_loop s y m k r H =
  match bdec (k <? m) with
  | left Hk =>
      fill_loop s y m (k + 1) r.[k <- clause_mask s y.[k]]
        (Acc_inv H (dec_step m k Hk))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition masks (s : bool) (y : array (array (literal uint))) : array int :=
  fill_loop s y (PArray.length y) 0 (PArray.make (PArray.length y) 0)
    (Zwf_well_founded 0 (gap (PArray.length y) 0)).

(* The clause of masks p (positive) and q (negative) holds under t. *)
Definition clause_ok (t p q : int) : bool :=
  if (p land t) =? 0 then negb ((q land t) =? q) else true.

(* Clauses k .. m-1 all hold under t. *)
Fixpoint check_loop (pos neg : array int) (m k t : int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : bool :=
  match bdec (k <? m) with
  | left Hk =>
      if clause_ok t pos.[k] neg.[k]
      then check_loop pos neg m (k + 1) t (Acc_inv H (dec_step m k Hk))
      else false
  | right _ => true
  end.

Lemma check_loop_eq : forall pos neg m k t H,
  check_loop pos neg m k t H =
  match bdec (k <? m) with
  | left Hk =>
      if clause_ok t pos.[k] neg.[k]
      then check_loop pos neg m (k + 1) t (Acc_inv H (dec_step m k Hk))
      else false
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition check_all (pos neg : array int) (m t : int) : bool :=
  check_loop pos neg m 0 t (Zwf_well_founded 0 (gap m 0)).

(* Some t in [t0, lim) satisfies every clause. *)
Fixpoint search_loop (pos neg : array int) (m lim t : int)
    (H : Acc (Zwf 0) (gap lim t)) {struct H} : bool :=
  match bdec (t <? lim) with
  | left Ht =>
      if check_all pos neg m t then true
      else search_loop pos neg m lim (t + 1) (Acc_inv H (dec_step lim t Ht))
  | right _ => false
  end.

Lemma search_loop_eq : forall pos neg m lim t H,
  search_loop pos neg m lim t H =
  match bdec (t <? lim) with
  | left Ht =>
      if check_all pos neg m t then true
      else search_loop pos neg m lim (t + 1) (Acc_inv H (dec_step lim t Ht))
  | right _ => false
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition satisfiable_impl (n : int) (y : array (array (literal uint))) : bool :=
  let m := PArray.length y in
  let lim := 1 << n in
  search_loop (masks true y) (masks false y) m lim 0
    (Zwf_well_founded 0 (gap lim 0)).

(* ------------------------------------------------------------------ *)
(* Prop side                                                           *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

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

(* Reading a cell of an array through repr. *)
Lemma repr_array_get : forall {A M} `{Repr A M} (x : array A) (l : list M),
  repr x l -> forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  exists m, nth_error l (Z.to_nat (φ i)) = Some m /\ repr x.[i] m.
Proof.
  intros A M R x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  exists m. split; [exact Hm|].
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. exact Hr.
Qed.

Lemma repr_array_length : forall {A M} `{Repr A M} (x : array A) (l : list M),
  repr x l -> (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros A M R x l [Hl _]. symmetry. exact Hl. Qed.

(* --- bits ----------------------------------------------------------- *)

Lemma nz_bit : forall a : Z, (0 <= a)%Z -> a <> 0%Z ->
  exists j, Z.testbit a j = true.
Proof. intros a H1 H2. exists (Z.log2 a). apply Z.bit_log2. lia. Qed.

(* The bit index of variable i, and the assignment read off a mask. *)
Definition vz (z : Z) : N -> bool := fun i => Z.testbit z (Z.of_N i - 1).

(* The literal l puts bit j into the mask of sign s. *)
Definition lit_has (s : bool) (l : literal N) (j : Z) : Prop :=
  match l with
  | X i => s = true /\ (Z.of_N i - 1)%Z = j
  | NotX i => s = false /\ (Z.of_N i - 1)%Z = j
  end.

(* The mask value z holds exactly the bits of the literals of sign s of c. *)
Definition mask_of (s : bool) (z : Z) (c : list (literal N)) : Prop :=
  forall j, Z.testbit z j = true <-> exists l, In l c /\ lit_has s l j.

Lemma bitof_val : forall v : int, (1 <= (φ v) <= 20)%Z ->
  (φ (bitof v)) = (2 ^ ((φ v) - 1))%Z.
Proof.
  intros v Hv. unfold bitof. rewrite lsl_spec.
  assert (E : (φ (v - 1)) = ((φ v) - 1)%Z) by sia. rewrite E.
  change (φ 1) with 1%Z. rewrite Z.mul_1_l.
  apply Z.mod_small.
  assert (B : (2 ^ ((φ v) - 1) <= 2 ^ 19)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (P : (0 < 2 ^ ((φ v) - 1))%Z) by (apply Z.pow_pos_nonneg; lia).
  rewrite wB_val. lia.
Qed.

Lemma lit_bits_spec : forall s (lm : literal uint) (l : literal N),
  repr lm l -> (1 <= var l <= 20)%N ->
  forall j, Z.testbit (φ (lit_bits s lm)) j = true <-> lit_has s l j.
Proof.
  intros s lm l Hr Hv j.
  destruct lm as [a | a], l as [i | i]; simpl in Hr; try contradiction;
    change (Z.to_N (φ a) = i) in Hr; simpl in Hv |- *;
    pose proof (to_Z_bounded a) as Ba;
    (assert (Ea : (φ a) = Z.of_N i) by lia);
    destruct s; simpl.
  all: first [ change (φ 0) with 0%Z; rewrite Z.testbit_0_l;
               split; [discriminate | intros [? _]; discriminate]
             | rewrite bitof_val by lia; rewrite Z.pow2_bits_eqb by lia;
               rewrite Z.eqb_eq; split;
                 [intros; split; [reflexivity | lia] | intros [_ ?]; lia] ].
Qed.

Lemma mask_loop_spec : forall s (c : array (literal uint)) (cl : list (literal N)),
  repr c cl -> Forall (fun l => 1 <= var l <= 20)%N cl ->
  forall (z : Z) (i acc : int) (H : Acc (Zwf 0) (gap (PArray.length@{Set} c) i)),
  gap (PArray.length@{Set} c) i = z ->
  ((φ i) <= (φ (PArray.length@{Set} c)))%Z ->
  (forall j, Z.testbit (φ acc) j = true <->
     exists k l, (k < Z.to_nat (φ i))%nat /\ nth_error cl k = Some l /\ lit_has s l j) ->
  forall j, Z.testbit (φ (mask_loop s c (PArray.length@{Set} c) i acc H)) j = true <->
     exists k l, (k < List.length cl)%nat /\ nth_error cl k = Some l /\ lit_has s l j.
Proof.
  intros s c cl Hc Hf z.
  assert (Lc : (φ (PArray.length@{Set} c)) = Z.of_nat (List.length cl))
    by exact (repr_array_length c cl Hc).
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Hil Hacc.
  rewrite mask_loop_eq.
  destruct (bdec (i <? PArray.length@{Set} c)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (repr_array_get c cl Hc i ltac:(lia)) as (l & Hl & Hrl).
    assert (Hvl : (1 <= var l <= 20)%N).
    { rewrite Forall_forall in Hf. apply Hf. eapply nth_error_In. exact Hl. }
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + intros j. rewrite lor_spec', Z.lor_spec, orb_true_iff, Hacc.
      rewrite (lit_bits_spec s _ l Hrl Hvl j).
      rewrite Hi1, Z2Nat.inj_add by lia. simpl. split.
      * intros [(k & l' & Hk & Hn & Hh) | Hh].
        -- exists k, l'. repeat split; auto. lia.
        -- exists (Z.to_nat (φ i)), l. repeat split; auto. lia.
      * intros (k & l' & Hk & Hn & Hh).
        destruct (Nat.eq_dec k (Z.to_nat (φ i))) as [E | E].
        -- subst k. rewrite Hl in Hn. injection Hn as <-. right. exact Hh.
        -- left. exists k, l'. repeat split; auto. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    intros j. rewrite Hacc.
    replace (Z.to_nat (φ i)) with (List.length cl) by lia. reflexivity.
Qed.

Lemma clause_mask_spec : forall s (c : array (literal uint)) (cl : list (literal N)),
  repr c cl -> Forall (fun l => 1 <= var l <= 20)%N cl ->
  mask_of s (φ (clause_mask s c)) cl.
Proof.
  intros s c cl Hc Hf j. unfold clause_mask.
  etransitivity; [apply (mask_loop_spec s c cl Hc Hf _ 0 0 _ eq_refl) | ].
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded (PArray.length c)). lia.
  - intros j'. change (φ 0) with 0%Z. rewrite Z.testbit_0_l. simpl. split.
    + discriminate.
    + intros (k & l & Hk & _). lia.
  - split.
    + intros (k & l & _ & Hn & Hh). exists l. split; [|exact Hh].
      eapply nth_error_In. exact Hn.
    + intros (l & Hin & Hh). destruct (In_nth_error _ _ Hin) as [k Hk].
      exists k, l. repeat split; auto.
      apply nth_error_Some. rewrite Hk. discriminate.
Qed.

Lemma fill_loop_spec : forall s (y : array (array (literal uint)))
    (cls : list (list (literal N))),
  repr y cls -> Forall (Forall (fun l => 1 <= var l <= 20)%N) cls ->
  forall (z : Z) (k : int) (r : array int)
         (H : Acc (Zwf 0) (gap (PArray.length@{Set} y) k)),
  gap (PArray.length@{Set} y) k = z ->
  PArray.length r = PArray.length@{Set} y ->
  ((φ k) <= (φ (PArray.length@{Set} y)))%Z ->
  (forall k' : int, ((φ k') < (φ k))%Z -> forall c,
     nth_error cls (Z.to_nat (φ k')) = Some c -> mask_of s (φ (r.[k'])) c) ->
  let r' := fill_loop s y (PArray.length@{Set} y) k r H in
  PArray.length r' = PArray.length@{Set} y /\
  forall k' : int, ((φ k') < (φ (PArray.length@{Set} y)))%Z -> forall c,
     nth_error cls (Z.to_nat (φ k')) = Some c -> mask_of s (φ (r'.[k'])) c.
Proof.
  intros s y cls Hy Hf z.
  assert (Ly : (φ (PArray.length@{Set} y)) = Z.of_nat (List.length cls))
    by exact (repr_array_length y cls Hy).
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k r H Hz Hlen Hkl Hinv r'. subst r'.
  rewrite fill_loop_eq.
  destruct (bdec (k <? PArray.length@{Set} y)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + rewrite alength_set. exact Hlen.
    + lia.
    + intros k' Hk'' c Hc. rewrite Hk1 in Hk''.
      destruct (Z.eq_dec (φ k') (φ k)) as [E | E].
      * assert (k' = k) by (apply to_Z_inj; exact E). subst k'.
        rewrite aget_set_same by (rewrite Hlen; exact Hk).
        destruct (repr_array_get y cls Hy k ltac:(lia)) as (c' & Hc' & Hrc).
        rewrite Hc in Hc'. injection Hc' as <-.
        apply clause_mask_spec; [exact Hrc|].
        rewrite Forall_forall in Hf. apply Hf. eapply nth_error_In. exact Hc.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hinv; [lia | exact Hc].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    split; [exact Hlen|].
    intros k' Hk' c Hc. apply Hinv; [lia | exact Hc].
Qed.

Lemma masks_spec : forall s (y : array (array (literal uint)))
    (cls : list (list (literal N))),
  repr y cls -> Forall (Forall (fun l => 1 <= var l <= 20)%N) cls ->
  PArray.length (masks s y) = PArray.length@{Set} y /\
  forall k' : int, ((φ k') < (φ (PArray.length@{Set} y)))%Z -> forall c,
     nth_error cls (Z.to_nat (φ k')) = Some c -> mask_of s (φ ((masks s y).[k'])) c.
Proof.
  intros s y cls Hy Hf. unfold masks.
  apply (fill_loop_spec s y cls Hy Hf _ 0 _ _ eq_refl).
  - rewrite alength_make.
    destruct (PArray.length@{Set} y <=? PArray.max_length) eqn:E; [reflexivity|].
    exfalso.
    assert (B : (PArray.length@{Set} y <=? PArray.max_length) = true)
      by exact (leb_length _ y).
    rewrite B in E. discriminate.
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded (PArray.length@{Set} y)). lia.
  - intros k' Hk'. change (φ 0) with 0%Z in Hk'.
    pose proof (to_Z_bounded k'). lia.
Qed.

(* --- one clause under one mask ------------------------------------- *)

Lemma clause_ok_bits : forall t p q : int,
  clause_ok t p q = true <->
  exists j, (Z.testbit (φ p) j = true /\ Z.testbit (φ t) j = true) \/
            (Z.testbit (φ q) j = true /\ Z.testbit (φ t) j = false).
Proof.
  intros t p q. unfold clause_ok.
  pose proof (to_Z_bounded p) as Bp. pose proof (to_Z_bounded q) as Bq.
  pose proof (to_Z_bounded t) as Bt.
  destruct (p land t =? 0) eqn:E1.
  - rewrite Uint63.eqb_spec in E1.
    assert (Z1 : Z.land (φ p) (φ t) = 0%Z)
      by (rewrite <- land_spec', E1; reflexivity).
    rewrite negb_true_iff, Uint63.eqb_false_spec. split.
    + intros Hne.
      assert (Hd : Z.ldiff (φ q) (φ t) <> 0%Z).
      { intros Hd. apply Hne. apply to_Z_inj. rewrite land_spec'.
        apply Z.bits_inj. intros j.
        assert (Hj := f_equal (fun a => Z.testbit a j) Hd). simpl in Hj.
        rewrite Z.ldiff_spec, Z.testbit_0_l in Hj. rewrite Z.land_spec.
        destruct (Z.testbit (φ q) j), (Z.testbit (φ t) j); simpl in *;
          congruence. }
      destruct (nz_bit (Z.ldiff (φ q) (φ t)) ltac:(apply Z.ldiff_nonneg; left; lia) Hd) as [j Hj].
      rewrite Z.ldiff_spec, andb_true_iff, negb_true_iff in Hj.
      exists j. right. exact Hj.
    + intros [j [[H1 H2] | [H1 H2]]] Heq.
      * assert (Hj := f_equal (fun a => Z.testbit a j) Z1). simpl in Hj.
        rewrite Z.land_spec, H1, H2, Z.testbit_0_l in Hj. discriminate.
      * assert (Hj := f_equal (fun a => Z.testbit (φ a) j) Heq). simpl in Hj.
        rewrite land_spec', Z.land_spec, H1, H2 in Hj. discriminate.
  - split; [intros _ | reflexivity].
    rewrite Uint63.eqb_false_spec in E1.
    assert (Hd : Z.land (φ p) (φ t) <> 0%Z).
    { intros Hd. apply E1. apply to_Z_inj. rewrite land_spec', Hd. reflexivity. }
    destruct (nz_bit (Z.land (φ p) (φ t)) ltac:(apply Z.land_nonneg; left; lia) Hd) as [j Hj].
    rewrite Z.land_spec, andb_true_iff in Hj.
    exists j. left. exact Hj.
Qed.

Lemma clause_ok_spec : forall (t p q : int) (c : list (literal N)),
  mask_of true (φ p) c -> mask_of false (φ q) c ->
  clause_ok t p q = true <-> clause_true (vz (φ t)) c.
Proof.
  intros t p q c Hp Hq. rewrite clause_ok_bits. unfold clause_true. split.
  - intros [j [[H1 H2] | [H1 H2]]].
    + apply Hp in H1. destruct H1 as (l & Hin & Hh).
      exists l. split; [exact Hin|].
      destruct l as [i | i]; destruct Hh as [Hs Hj]; [|discriminate].
      simpl. unfold vz. rewrite Hj. exact H2.
    + apply Hq in H1. destruct H1 as (l & Hin & Hh).
      exists l. split; [exact Hin|].
      destruct l as [i | i]; destruct Hh as [Hs Hj]; [discriminate|].
      simpl. unfold vz. rewrite Hj, H2. reflexivity.
  - intros (l & Hin & Hl). destruct l as [i | i]; simpl in Hl; unfold vz in Hl.
    + exists (Z.of_N i - 1)%Z. left. split; [|exact Hl].
      apply Hp. exists (X i). split; [exact Hin|]. split; reflexivity.
    + exists (Z.of_N i - 1)%Z. right. split.
      * apply Hq. exists (NotX i). split; [exact Hin|]. split; reflexivity.
      * apply negb_true_iff. exact Hl.
Qed.

(* --- the check of all clauses ---------------------------------------- *)

Lemma check_loop_spec : forall (pos neg : array int) (m t : int) (z : Z)
    (k : int) (H : Acc (Zwf 0) (gap m k)),
  gap m k = z ->
  check_loop pos neg m k t H = true <->
  forall k' : int, ((φ k) <= (φ k') < (φ m))%Z -> clause_ok t pos.[k'] neg.[k'] = true.
Proof.
  intros pos neg m t z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k H Hz.
  rewrite check_loop_eq.
  destruct (bdec (k <? m)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    destruct (clause_ok t pos.[k] neg.[k]) eqn:Ec.
    + rewrite (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hk) (k + 1) _ eq_refl).
      rewrite Hk1. split.
      * intros Hall k' Hk''.
        destruct (Z.eq_dec (φ k') (φ k)) as [E | E].
        -- assert (k' = k) by (apply to_Z_inj; exact E). subst k'. exact Ec.
        -- apply Hall. lia.
      * intros Hall k' Hk''. apply Hall. lia.
    + split; [discriminate|]. intros Hall. rewrite <- Ec. apply Hall. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    split; [|reflexivity]. intros _ k' Hk'. lia.
Qed.

Lemma check_all_spec : forall (y : array (array (literal uint)))
    (cls : list (list (literal N))) (pos neg : array int) (t : int),
  repr y cls ->
  PArray.length pos = PArray.length@{Set} y -> PArray.length neg = PArray.length@{Set} y ->
  (forall k' : int, ((φ k') < (φ (PArray.length@{Set} y)))%Z -> forall c,
     nth_error cls (Z.to_nat (φ k')) = Some c -> mask_of true (φ (pos.[k'])) c) ->
  (forall k' : int, ((φ k') < (φ (PArray.length@{Set} y)))%Z -> forall c,
     nth_error cls (Z.to_nat (φ k')) = Some c -> mask_of false (φ (neg.[k'])) c) ->
  check_all pos neg (PArray.length@{Set} y) t = true <->
  Forall (clause_true (vz (φ t))) cls.
Proof.
  intros y cls pos neg t Hy Lp Ln Hp Hn.
  assert (Ly : (φ (PArray.length@{Set} y)) = Z.of_nat (List.length cls))
    by exact (repr_array_length y cls Hy).
  unfold check_all. rewrite (check_loop_spec _ _ _ _ _ 0 _ eq_refl).
  change (φ 0) with 0%Z. rewrite Forall_forall. split.
  - intros Hall c Hin.
    destruct (In_nth_error _ _ Hin) as [k Hk].
    assert (Hkl : (k < List.length cls)%nat)
      by (apply nth_error_Some; rewrite Hk; discriminate).
    assert (Ek : (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
    { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val.
      pose proof (alength_bound pos). lia. }
    assert (Hk2 : nth_error cls (Z.to_nat (φ (of_Z (Z.of_nat k)))) = Some c)
      by (rewrite Ek, Nat2Z.id; exact Hk).
    assert (Hkk : ((φ (of_Z (Z.of_nat k))) < (φ (PArray.length@{Set} y)))%Z) by lia.
    rewrite <- (clause_ok_spec t _ _ c (Hp _ Hkk c Hk2) (Hn _ Hkk c Hk2)).
    apply Hall. lia.
  - intros Hall k' Hk'.
    destruct (nth_error cls (Z.to_nat (φ k'))) as [c|] eqn:Hc.
    + rewrite (clause_ok_spec t _ _ c (Hp k' ltac:(lia) c Hc) (Hn k' ltac:(lia) c Hc)).
      apply Hall. eapply nth_error_In. exact Hc.
    + apply nth_error_None in Hc. lia.
Qed.

(* --- the search ------------------------------------------------------- *)

Lemma search_loop_spec : forall (pos neg : array int) (m lim : int) (z : Z)
    (t : int) (H : Acc (Zwf 0) (gap lim t)),
  gap lim t = z ->
  search_loop pos neg m lim t H = true <->
  exists u : int, ((φ t) <= (φ u) < (φ lim))%Z /\ check_all pos neg m u = true.
Proof.
  intros pos neg m lim z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t H Hz.
  rewrite search_loop_eq.
  destruct (bdec (t <? lim)) as [Ht | Ht].
  - pose proof Ht as Ht'. rewrite ltb_spec in Ht'.
    assert (Ht1 : (φ (t + 1)) = ((φ t) + 1)%Z) by sia.
    destruct (check_all pos neg m t) eqn:Ec.
    + split; [intros _ | reflexivity]. exists t. split; [lia | exact Ec].
    + rewrite (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Ht) (t + 1) _ eq_refl).
      rewrite Ht1. split.
      * intros (u & Hu & Hc). exists u. split; [lia | exact Hc].
      * intros (u & Hu & Hc).
        destruct (Z.eq_dec (φ u) (φ t)) as [E | E].
        -- assert (u = t) by (apply to_Z_inj; exact E). subst u. congruence.
        -- exists u. split; [lia | exact Hc].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Ht.
    split; [discriminate|]. intros (u & Hu & _). lia.
Qed.

(* --- every assignment is a mask on its first k variables ------------- *)

Lemma mask_exists : forall (k : nat) (v : N -> bool),
  exists z, (0 <= z < 2 ^ Z.of_nat k)%Z /\
  forall j, (0 <= j < Z.of_nat k)%Z -> Z.testbit z j = v (Z.to_N j + 1)%N.
Proof.
  induction k as [| k IH]; intros v.
  - exists 0%Z. split; [simpl; lia|]. intros j Hj. lia.
  - destruct (IH (fun i => v (i + 1)%N)) as (z & Hz & Hb).
    exists (2 * z + Z.b2z (v 1%N))%Z.
    assert (P : (2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k)%Z)
      by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
    split; [rewrite P; destruct (v 1%N); simpl Z.b2z; lia|].
    intros j Hj.
    destruct (Z.eq_dec j 0) as [E | E].
    + subst j. simpl. destruct (v 1%N); simpl.
      * apply Z.testbit_odd_0.
      * rewrite Z.add_0_r. apply Z.testbit_even_0.
    + replace j with (Z.succ (j - 1)) by lia.
      assert (Ej : (Z.to_N (Z.succ (j - 1)) + 1 = Z.to_N (j - 1) + 1 + 1)%N) by lia.
      rewrite Ej, <- (Hb (j - 1)%Z) by lia.
      destruct (v 1%N); simpl.
      * apply Z.testbit_odd_succ. lia.
      * rewrite Z.add_0_r. apply Z.testbit_even_succ. lia.
Qed.

(* Two assignments that agree on the variables of the clauses. *)
Lemma clauses_agree : forall (n : N) (v w : N -> bool) (cls : list (list (literal N))),
  Forall (Forall (fun l => 1 <= var l <= n)%N) cls ->
  (forall i, (1 <= i <= n)%N -> v i = w i) ->
  Forall (clause_true v) cls -> Forall (clause_true w) cls.
Proof.
  intros n v w cls Hf Hvw Hv.
  rewrite Forall_forall in Hf, Hv |- *. intros c Hc.
  destruct (Hv c Hc) as (l & Hin & Hl).
  exists l. split; [exact Hin|].
  pose proof (Hf c Hc) as Hfc. rewrite Forall_forall in Hfc.
  specialize (Hfc l Hin).
  destruct l as [i | i]; simpl in *; rewrite <- Hvw by exact Hfc; exact Hl.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

(* Bridge from the iff form to the spec's match on the bool. *)
Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P H; [exact (proj1 H eq_refl)|].
  intro p. discriminate (proj2 H p).
Qed.

Lemma satisfiable_impl_correct :
  forall (n : N) (clauses : list (list (literal N)))
         (x : uint) (y : array (array (literal uint))),
  valid_input n clauses -> repr x n -> repr y clauses ->
  exists b : bool, repr (satisfiable_impl x y) b /\ satisfiable_spec n clauses b.
Proof.
  intros n cls x y Hv Hx Hy.
  destruct Hv as [Hn _ Hvars].
  unfold repr, repr_uint in Hx.
  pose proof (to_Z_bounded x) as Bx.
  assert (Ex : (φ x) = Z.of_N n) by lia.
  assert (Hf20 : Forall (Forall (fun l => 1 <= var l <= 20)%N) cls).
  { eapply Forall_impl; [|exact Hvars]. intros c Hc.
    eapply Forall_impl; [|exact Hc]. simpl. intros l Hl. lia. }
  destruct (masks_spec true y cls Hy Hf20) as [Lp Hp].
  destruct (masks_spec false y cls Hy Hf20) as [Ln Hn'].
  assert (Hlim : (φ (1 << x)) = (2 ^ Z.of_N n)%Z).
  { rewrite lsl_spec, Ex. change (φ 1) with 1%Z. rewrite Z.mul_1_l.
    apply Z.mod_small.
    assert (B : (2 ^ Z.of_N n <= 2 ^ 20)%Z) by (apply Z.pow_le_mono_r; lia).
    assert (P : (0 < 2 ^ Z.of_N n)%Z) by (apply Z.pow_pos_nonneg; lia).
    rewrite wB_val. lia. }
  exists (satisfiable_impl x y). split; [reflexivity|].
  unfold satisfiable_spec, satisfiable_impl. cbv zeta.
  apply bool_match_of_iff.
  rewrite (search_loop_spec _ _ _ _ _ 0 _ eq_refl).
  change (φ 0) with 0%Z. rewrite Hlim. split.
  - intros (u & Hu & Hc). exists (vz (φ u)).
    exact (proj1 (check_all_spec y cls _ _ u Hy Lp Ln Hp Hn') Hc).
  - intros (v & Hsat).
    destruct (mask_exists (N.to_nat n) v) as (z & Hz & Hb).
    rewrite N_nat_Z in Hz, Hb.
    assert (Bz : (z < 2 ^ 20)%Z).
    { assert (B : (2 ^ Z.of_N n <= 2 ^ 20)%Z) by (apply Z.pow_le_mono_r; lia).
      lia. }
    assert (Ez : (φ (of_Z z)) = z).
    { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
    exists (of_Z z). rewrite Ez. split; [lia|].
    apply (proj2 (check_all_spec y cls _ _ (of_Z z) Hy Lp Ln Hp Hn')).
    rewrite Ez.
    apply (clauses_agree n v (vz z) cls Hvars); [|exact Hsat].
    intros i Hi. unfold vz. rewrite Hb by lia. f_equal. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition satisfiable : uint -> array (array (literal uint)) -> bool :=
  satisfiable_impl.

Definition satisfiable_correct :
  forall (n : N) (clauses : list (list (literal N)))
         (x : uint) (y : array (array (literal uint))),
  valid_input n clauses -> repr x n -> repr y clauses ->
  exists b : bool, repr (satisfiable x y) b /\ satisfiable_spec n clauses b
  := satisfiable_impl_correct.
