(* Implementation of oddmanout (oddmanout.spec): XOR fold.

   Code.  [odd_one a] folds [Uint63.lxor] over the cells of [a], left to
   right, into one [int] accumulator started at 0.  One [PArray.get] per
   cell, no [set], no allocation.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap n i)] proof, the shape of the template's loops.

   Proof.  On the math side, [xorl l = fold_left N.lxor l 0].  The loop
   computes [xorl l] (invariant over [skipn i l]); the key lemma
   [xorl_unique_odd] shows by strong induction on the length (peeling all
   occurrences of the head with [remove]) that when every value other than
   v has even multiplicity, [xorl l] is v or 0 according to the parity of
   v's multiplicity; [vi_one_alone] then gives [xorl l = v]. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
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

(* acc lxor a.[i] lxor ... lxor a.[n-1] *)
Fixpoint xor_loop (a : array int) (n i acc : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi => xor_loop a n (i + 1) (acc lxor a.[i]) (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.

Lemma xor_loop_eq : forall a n i acc H,
  xor_loop a n i acc H =
  match bdec (i <? n) with
  | left Hi => xor_loop a n (i + 1) (acc lxor a.[i]) (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition odd_one_impl (a : array uint) : uint :=
  xor_loop a (PArray.length a) 0 0 (Zwf_well_founded 0 (gap (PArray.length a) 0)).

(* ------------------------------------------------------------------ *)
(* Math side: the XOR of a list                                        *)
(* ------------------------------------------------------------------ *)

Definition xorl (l : list N) : N := fold_left N.lxor l 0%N.

Lemma fold_lxor_acc : forall l a,
  fold_left N.lxor l a = N.lxor a (xorl l).
Proof.
  unfold xorl. induction l as [| b t IH]; intros a; simpl.
  - rewrite N.lxor_0_r. reflexivity.
  - rewrite IH, (IH b), N.lxor_assoc. reflexivity.
Qed.

Lemma xorl_cons : forall b t, xorl (b :: t) = N.lxor b (xorl t).
Proof. intros b t. unfold xorl at 1. simpl. rewrite fold_lxor_acc. reflexivity. Qed.

Definition cnt (l : list N) (x : N) : nat := count_occ N.eq_dec l x.

Lemma xorl_remove : forall a l,
  xorl l = N.lxor (if Nat.odd (cnt l a) then a else 0%N) (xorl (remove N.eq_dec a l)).
Proof.
  intros a l. unfold cnt. induction l as [| b t IH].
  - reflexivity.
  - simpl. rewrite xorl_cons, IH.
    destruct (N.eq_dec b a) as [E | E]; destruct (N.eq_dec a b) as [E' | E'];
      try (exfalso; congruence).
    + subst b. rewrite Nat.odd_succ, <- Nat.negb_odd.
      destruct (Nat.odd (count_occ N.eq_dec t a)); simpl.
      * rewrite <- N.lxor_assoc, N.lxor_nilpotent, N.lxor_0_l. reflexivity.
      * reflexivity.
    + rewrite xorl_cons, <- !N.lxor_assoc, (N.lxor_comm b). reflexivity.
Qed.

Lemma cnt_remove_same : forall a l, cnt (remove N.eq_dec a l) a = 0%nat.
Proof.
  intros a l. unfold cnt. induction l as [| b t IH]; simpl; [reflexivity|].
  destruct (N.eq_dec a b) as [E | E]; [exact IH|].
  simpl. destruct (N.eq_dec b a); [congruence | exact IH].
Qed.

Lemma cnt_remove_other : forall a y l, y <> a ->
  cnt (remove N.eq_dec a l) y = cnt l y.
Proof.
  intros a y l Hy. unfold cnt. induction l as [| b t IH]; simpl; [reflexivity|].
  destruct (N.eq_dec a b) as [E | E].
  - subst b. destruct (N.eq_dec a y); [congruence | exact IH].
  - simpl. destruct (N.eq_dec b y); rewrite IH; reflexivity.
Qed.

Lemma odd_false_of_even : forall n, Nat.Even n -> Nat.odd n = false.
Proof.
  intros n H. rewrite <- Nat.negb_even. apply Nat.even_spec in H. rewrite H. reflexivity.
Qed.

Lemma xorl_unique_odd : forall l v,
  (forall y, y <> v -> Nat.Even (cnt l y)) ->
  xorl l = if Nat.odd (cnt l v) then v else 0%N.
Proof.
  intros l. remember (List.length l) as n eqn:Hn. revert l Hn.
  induction n as [n IH] using lt_wf_ind.
  intros l Hn v Hev.
  destruct l as [| a t].
  - reflexivity.
  - rewrite (xorl_remove a (a :: t)).
    set (l' := remove N.eq_dec a (a :: t)).
    assert (Hlt : (List.length l' < n)%nat).
    { subst n. apply remove_length_lt. left. reflexivity. }
    assert (Hev' : forall y, y <> v -> Nat.Even (cnt l' y)).
    { intros y Hy. destruct (N.eq_dec y a) as [E | E].
      - subst y. unfold l'. rewrite cnt_remove_same. exists 0%nat. reflexivity.
      - unfold l'. rewrite cnt_remove_other by exact E. apply Hev. exact Hy. }
    rewrite (IH (List.length l') Hlt l' eq_refl v Hev').
    destruct (N.eq_dec a v) as [E | E].
    + subst a. unfold l'. rewrite cnt_remove_same. simpl Nat.odd.
      rewrite N.lxor_0_r. reflexivity.
    + rewrite (odd_false_of_even _ (Hev a E)), N.lxor_0_l.
      unfold l'. rewrite cnt_remove_other by (intro F; apply E; symmetry; exact F).
      reflexivity.
Qed.

Lemma xorl_only_odd : forall l v, only_odd l v -> xorl l = v.
Proof.
  intros l v [Hodd Huniq].
  rewrite (xorl_unique_odd l v).
  - apply Nat.odd_spec in Hodd. unfold cnt. unfold occurrences in Hodd.
    rewrite Hodd. reflexivity.
  - intros y Hy. destruct (Nat.Even_or_Odd (cnt l y)) as [He | Ho]; [exact He|].
    exfalso. apply Hy. apply Huniq. exact Ho.
Qed.

(* ------------------------------------------------------------------ *)
(* Machine side                                                        *)
(* ------------------------------------------------------------------ *)

Lemma to_N_lxor : forall p q : int,
  Z.to_N (φ (p lxor q)) = N.lxor (Z.to_N (φ p)) (Z.to_N (φ q)).
Proof.
  intros p q. rewrite lxor_spec'.
  pose proof (to_Z_bounded p) as Bp. pose proof (to_Z_bounded q) as Bq.
  rewrite <- (Z2N.id (φ p)) at 1 by lia. rewrite <- (Z2N.id (φ q)) at 1 by lia.
  rewrite <- N2Z.inj_lxor, N2Z.id. reflexivity.
Qed.

Lemma skipn_cons_nth : forall (l : list N) k m,
  nth_error l k = Some m -> skipn k l = m :: skipn (S k) l.
Proof.
  induction l as [| b t IH]; intros k m H; destruct k; simpl in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma xor_loop_spec : forall (l : list N) (a : array uint), repr a l ->
  forall (z : Z) (i acc : int) (H : Acc (Zwf 0) (gap (PArray.length a) i)),
  gap (PArray.length a) i = z ->
  ((φ i) <= (φ (PArray.length a)))%Z ->
  Z.to_N (φ (xor_loop a (PArray.length a) i acc H))
  = fold_left N.lxor (skipn (Z.to_nat (φ i)) l) (Z.to_N (φ acc)).
Proof.
  intros l a [Hl Hc] z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Hi.
  rewrite xor_loop_eq.
  destruct (bdec (i <? PArray.length a)) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
    unfold repr, repr_uint in Hr.
    assert (Ei : Uint63.of_nat (Z.to_nat (φ i)) = i).
    { unfold Uint63.of_nat. rewrite Z2Nat.id by lia. apply of_to_Z. }
    rewrite Ei in Hr.
    rewrite (IH (gap (PArray.length a) (i + 1))); [ | rewrite <- Hz; apply dec_step; exact Hlt
                                                 | reflexivity | lia ].
    rewrite (skipn_cons_nth l _ m Hm). simpl.
    rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by lia.
    rewrite to_N_lxor. f_equal. f_equal. exact Hr.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    assert (E : Z.to_nat (φ i) = List.length l) by lia.
    rewrite E, skipn_all. reflexivity.
Qed.

Lemma odd_one_impl_correct : forall (l : list N) (a : array uint),
  valid_input l -> repr a l ->
  exists x : N, repr (odd_one_impl a) x /\ odd_one_spec l x.
Proof.
  intros l a Hv Ha.
  assert (X : Z.to_N (φ (odd_one_impl a)) = xorl l).
  { unfold odd_one_impl.
  pose proof (xor_loop_spec l a Ha _ 0 0
    (Zwf_well_founded 0 (gap (PArray.length a) 0)) eq_refl
    ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (PArray.length a)); lia)) as E.
  exact (eq_trans E eq_refl). }
  destruct Hv as [_ _ [v Hov]].
  exists (xorl l). split; [exact X|].
  rewrite (xorl_only_odd l v Hov). exact Hov.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition odd_one : array uint -> uint := odd_one_impl.

Definition odd_one_correct : forall (l : list N) (a : array uint),
  valid_input l -> repr a l ->
  exists x : N, repr (odd_one a) x /\ odd_one_spec l x
  := odd_one_impl_correct.
