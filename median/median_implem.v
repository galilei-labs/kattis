(* Implementation of median (median.spec): randomized selection
   (CLRS 9.2) in place on one flat copy of the input.

   Code.  [median x] copies x, then [sel] selects position k = n / 2:
   on the range [lo, hi) holding k it draws a pivot value x = y.[p], p in
   [lo, hi) from a 63-bit linear congruential generator, and runs two
   Lomuto passes ([part]): the first moves the cells < x to the front of
   [lo, hi) (boundary i), the second the cells <= x to the front of
   [i, hi) (boundary m), so [lo, i) < x, [i, m) = x, [m, hi) > x.  It
   recurses into [lo, i) or [m, hi), whichever holds k, and stops when k
   falls in [i, m) (the three-way split keeps inputs with many equal
   values linear).  For odd n the answer is y.[k]; for even n the lower
   middle element is the maximum of the left part [0, k) ([maxl]), and the
   answer is (w + u) / 2 computed as of_uint63 (w + u) / 2. in floats,
   exact (w + u <= 2*10^9 < 2^53, and halving is exact).  All indices and
   values are Uint63 ints; no Z, no nat in the code.

   Termination: every loop recurses on an erased [Acc (Zwf 0) (gap _ _)]
   proof, as in template/polymul1; [sel]'s two recursive calls are guarded
   by tests (i < hi, lo < m) that the proof shows always true.

   Proof.  The cells are read on the math side as [cell y t : N]; [seg]
   is the list of a range of cells.  A swap permutes the range
   ([perm_tau]: a transposition of positions); [part_spec] keeps the range
   a permutation of itself and the rest untouched; [sel_spec] keeps the
   invariant that every cell left of lo is <= every cell from lo on, and
   every cell left of hi <= every cell from hi on, and ends with position
   k having nothing larger before it and nothing smaller after it.  [kth]
   turns this into "position k of the sorted permutation" by counting the
   cells < v and <= v ([sorted_nth], [cnt_perm]).  For even n, swapping
   the maximum of [0, k) into position k-1 gives the same property at
   k - 1. *)

From Median.spec Require Import Prelude.
From StdGalilei Require Import repr repr_float.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Stdlib Require Import Sorted Permutation ZifyUint63 Lia Lra Zwf.
From Stdlib Require Import FinFun.
From Flocq Require Core.Core.
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
  intros m i H. rewrite Uint63.ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_left : forall lo hi i : int,
  (lo <? hi) = true -> (i <? hi) = true -> Zwf 0 (gap i lo) (gap hi lo).
Proof.
  intros lo hi i H1 H2. rewrite Uint63.ltb_spec in H1, H2. unfold Zwf, gap. lia.
Qed.

Lemma dec_right : forall lo hi m : int,
  (lo <? hi) = true -> (lo <? m) = true -> Zwf 0 (gap hi m) (gap hi lo).
Proof.
  intros lo hi m H1 H2. rewrite Uint63.ltb_spec in H1, H2. unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* y with cell j set to v (= y.[j]) and cell i to y.[j]'s former partner:
   the exchange of cells i and j, both reads before the writes. *)
Definition swap_with (y : array int) (i j v : int) : array int :=
  let w := y.[i] in y.[i <- v].[j <- w].

(* the partition test: v < x (strict) or v <= x *)
Definition tst (strict : bool) (x v : int) : bool :=
  if strict then v <? x else v <=? x.

(* Lomuto partition of the cells [j, hi) given that [i0, i) pass the test
   and [i, j) fail it: returns the array and the boundary i'. *)
Fixpoint part (strict : bool) (x hi : int) (y : array int) (i j : int)
    (H : Acc (Zwf 0) (gap hi j)) {struct H} : array int * int :=
  match bdec (j <? hi) with
  | left Hj =>
      let v := y.[j] in
      if tst strict x v
      then part strict x hi (swap_with y i j v) (i + 1) (j + 1)
             (Acc_inv H (dec_step hi j Hj))
      else part strict x hi y i (j + 1) (Acc_inv H (dec_step hi j Hj))
  | right _ => (y, i)
  end.

Lemma part_eq : forall strict x hi y i j H,
  part strict x hi y i j H =
  match bdec (j <? hi) with
  | left Hj =>
      let v := y.[j] in
      if tst strict x v
      then part strict x hi (swap_with y i j v) (i + 1) (j + 1)
             (Acc_inv H (dec_step hi j Hj))
      else part strict x hi y i (j + 1) (Acc_inv H (dec_step hi j Hj))
  | right _ => (y, i)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the pseudo-random generator: a 63-bit linear congruential step *)
Definition lcg (s : int) : int := s * 6364136223846793005 + 1442695040888963407.

(* Select position k inside [lo, hi): a random pivot x of [lo, hi), then
   two Lomuto passes split [lo, hi) into < x, = x, > x; recurse into the
   side holding k, stop when k falls among the cells equal to x. *)
Fixpoint sel (k : int) (y : array int) (lo hi seed : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int :=
  match bdec (lo <? hi) with
  | left Hlh =>
      let s := lcg seed in
      let x := y.[lo + (s >> 17) mod (hi - lo)] in
      let (y1, i) := part true x hi y lo lo (Zwf_well_founded 0 (gap hi lo)) in
      let (y2, m) := part false x hi y1 i i (Zwf_well_founded 0 (gap hi i)) in
      if k <? i then
        match bdec (i <? hi) with
        | left Hi => sel k y2 lo i s (Acc_inv H (dec_left lo hi i Hlh Hi))
        | right _ => y2
        end
      else if k <? m then y2
      else
        match bdec (lo <? m) with
        | left Hm => sel k y2 m hi s (Acc_inv H (dec_right lo hi m Hlh Hm))
        | right _ => y2
        end
  | right _ => y
  end.

Lemma sel_eq : forall k y lo hi seed H,
  sel k y lo hi seed H =
  match bdec (lo <? hi) with
  | left Hlh =>
      let s := lcg seed in
      let x := y.[lo + (s >> 17) mod (hi - lo)] in
      let (y1, i) := part true x hi y lo lo (Zwf_well_founded 0 (gap hi lo)) in
      let (y2, m) := part false x hi y1 i i (Zwf_well_founded 0 (gap hi i)) in
      if k <? i then
        match bdec (i <? hi) with
        | left Hi => sel k y2 lo i s (Acc_inv H (dec_left lo hi i Hlh Hi))
        | right _ => y2
        end
      else if k <? m then y2
      else
        match bdec (lo <? m) with
        | left Hm => sel k y2 m hi s (Acc_inv H (dec_right lo hi m Hlh Hm))
        | right _ => y2
        end
  | right _ => y
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the maximum of acc and the cells [j, k) *)
Fixpoint maxl (y : array int) (k j acc : int)
    (H : Acc (Zwf 0) (gap k j)) {struct H} : int :=
  match bdec (j <? k) with
  | left Hj =>
      let v := y.[j] in
      maxl y k (j + 1) (if acc <? v then v else acc) (Acc_inv H (dec_step k j Hj))
  | right _ => acc
  end.

Lemma maxl_eq : forall y k j acc H,
  maxl y k j acc H =
  match bdec (j <? k) with
  | left Hj =>
      let v := y.[j] in
      maxl y k (j + 1) (if acc <? v then v else acc) (Acc_inv H (dec_step k j Hj))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition seed0 : int := 88172645463325252.

Definition median_impl (x : array uint) : float :=
  let n := PArray.length x in
  let k := n / 2 in
  let y := sel k (PArray.copy x) 0 n seed0 (Zwf_well_founded 0 (gap n 0)) in
  let u := y.[k] in
  if n mod 2 =? 1 then of_uint63 u
  else
    let w := maxl y k 1 y.[0] (Zwf_well_founded 0 (gap k 1)) in
    (of_uint63 (w + u) / of_uint63 2)%float.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite Uint63.leb_spec in H. exact H.
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

Lemma aget_copy : forall (t : array int) (i : int), (PArray.copy t).[i] = t.[i].
Proof. intros t i. exact (get_copy int t i). Qed.

Lemma alength_copy : forall (t : array int), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros t. exact (length_copy int t). Qed.

Definition nn (i : int) : nat := Z.to_nat (φ i).

Lemma nn_spec : forall i : int, Z.of_nat (nn i) = (φ i).
Proof. intros i. unfold nn. pose proof (to_Z_bounded i). lia. Qed.

Lemma of_nat_to_Z : forall t : nat, (Z.of_nat t < wB)%Z ->
  (φ (Uint63.of_nat t)) = Z.of_nat t.
Proof. intros t H. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma of_nat_nn : forall i : int, Uint63.of_nat (nn i) = i.
Proof.
  intros i. apply to_Z_inj. pose proof (to_Z_bounded i).
  rewrite of_nat_to_Z; unfold nn; lia.
Qed.

(* the math reading of cell t of a working array *)
Definition cell (y : array int) (t : nat) : N := Z.to_N (φ (y.[Uint63.of_nat t])).

(* the cells [lo, lo + len) *)
Definition seg (y : array int) (lo len : nat) : list N := map (cell y) (seq lo len).

(* the transposition of a and b *)
Definition tau (a b t : nat) : nat :=
  if Nat.eqb t b then a else if Nat.eqb t a then b else t.

Ltac eqbs :=
  repeat (match goal with |- context [Nat.eqb ?x ?y] =>
            is_var x; destruct (Nat.eqb_spec x y) end;
          simpl).

Lemma tau_invol : forall a b t, tau a b (tau a b t) = t.
Proof. intros a b t. unfold tau. eqbs; lia. Qed.

Lemma swap_length : forall (y : array int) i j v,
  PArray.length (swap_with y i j v) = PArray.length y.
Proof. intros. unfold swap_with. rewrite !alength_set. reflexivity. Qed.

Lemma swap_cell : forall (y : array int) (i j : int) (t : nat),
  ((φ i) < (φ (PArray.length y)))%Z -> ((φ j) < (φ (PArray.length y)))%Z ->
  (Z.of_nat t < (φ (PArray.length y)))%Z ->
  cell (swap_with y i j y.[j]) t = cell y (tau (nn i) (nn j) t).
Proof.
  intros y i j t Hi Hj Ht. unfold cell, swap_with, tau.
  pose proof (alength_bound y). pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  assert (Et : (φ (Uint63.of_nat t)) = Z.of_nat t) by (apply of_nat_to_Z; rewrite wB_val; lia).
  destruct (Nat.eqb_spec t (nn j)) as [E | E].
  - subst t. rewrite !of_nat_nn. rewrite aget_set_same; [reflexivity |].
    rewrite alength_set, Uint63.ltb_spec. lia.
  - rewrite aget_set_other by (intro F; apply E; unfold nn; rewrite F; lia).
    destruct (Nat.eqb_spec t (nn i)) as [E' | E'].
    + subst t. rewrite !of_nat_nn. rewrite aget_set_same; [reflexivity |].
      rewrite Uint63.ltb_spec. lia.
    + rewrite aget_set_other by (intro F; apply E'; unfold nn; rewrite F; lia).
      reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Segments and permutations                                           *)
(* ------------------------------------------------------------------ *)

Lemma perm_tau : forall (g : nat -> N) lo len a b,
  (lo <= a < lo + len)%nat -> (lo <= b < lo + len)%nat ->
  Permutation (map g (seq lo len)) (map (fun t => g (tau a b t)) (seq lo len)).
Proof.
  intros g lo len a b Ha Hb.
  rewrite <- (map_map (tau a b) g). apply Permutation_map.
  apply NoDup_Permutation.
  - apply seq_NoDup.
  - apply Injective_map_NoDup; [| apply seq_NoDup].
    intros x y E. rewrite <- (tau_invol a b x), <- (tau_invol a b y), E. reflexivity.
  - intros t. rewrite in_map_iff, in_seq. split.
    + intros Ht. exists (tau a b t). rewrite tau_invol. split; [reflexivity |].
      apply in_seq. unfold tau. eqbs; lia.
    + intros [s [<- Hs]]. rewrite in_seq in Hs. unfold tau. eqbs; lia.
Qed.

Lemma seg_app : forall y lo l1 l2,
  seg y lo (l1 + l2) = seg y lo l1 ++ seg y (lo + l1) l2.
Proof. intros. unfold seg. rewrite seq_app, map_app. reflexivity. Qed.

Lemma seg_ext : forall y z lo len,
  (forall t, (lo <= t < lo + len)%nat -> cell y t = cell z t) ->
  seg y lo len = seg z lo len.
Proof.
  intros y z lo len H. unfold seg. apply map_ext_in.
  intros t Ht. apply in_seq in Ht. apply H. lia.
Qed.

Lemma in_seg : forall v y lo len,
  In v (seg y lo len) <-> exists t, (lo <= t < lo + len)%nat /\ cell y t = v.
Proof.
  intros v y lo len. unfold seg. rewrite in_map_iff. split.
  - intros [t [H1 H2]]. exists t. rewrite in_seq in H2. split; [lia | exact H1].
  - intros [t [H1 H2]]. exists t. rewrite in_seq. split; [exact H2 | lia].
Qed.

(* a value of a permuted segment is a value of the original one *)
Lemma perm_cell : forall y0 y lo len t,
  Permutation (seg y0 lo len) (seg y lo len) -> (lo <= t < lo + len)%nat ->
  exists t', (lo <= t' < lo + len)%nat /\ cell y t = cell y0 t'.
Proof.
  intros y0 y lo len t Hp Ht.
  assert (Hin : In (cell y t) (seg y lo len)) by (apply in_seg; exists t; auto).
  apply (Permutation_in _ (Permutation_sym Hp)) in Hin.
  apply in_seg in Hin. destruct Hin as [t' [H1 H2]]. exists t'. auto.
Qed.

(* a permutation of [lo, hi) leaving the rest of [L, R) alone permutes [L, R) *)
Lemma perm_widen : forall y0 y L R lo hi,
  (L <= lo <= hi)%nat -> (hi <= R)%nat ->
  Permutation (seg y0 lo (hi - lo)) (seg y lo (hi - lo)) ->
  (forall t, (L <= t < R)%nat -> (t < lo \/ hi <= t)%nat -> cell y t = cell y0 t) ->
  Permutation (seg y0 L (R - L)) (seg y L (R - L)).
Proof.
  intros y0 y L R lo hi H1 H2 Hp Hout.
  replace (R - L)%nat with ((lo - L) + ((hi - lo) + (R - hi)))%nat by lia.
  rewrite !seg_app.
  rewrite (seg_ext y0 y L (lo - L)) by (intros t Ht; symmetry; apply Hout; lia).
  apply Permutation_app_head.
  replace (L + (lo - L))%nat with lo by lia.
  rewrite (seg_ext y0 y (lo + (hi - lo)) (R - hi))
    by (intros t Ht; symmetry; apply Hout; lia).
  apply Permutation_app_tail. exact Hp.
Qed.

(* ------------------------------------------------------------------ *)
(* The partition pass                                                  *)
(* ------------------------------------------------------------------ *)

Definition ptst (strict : bool) (X c : N) : bool :=
  if strict then (c <? X)%N else (c <=? X)%N.

Lemma tst_ptst : forall strict x v,
  tst strict x v = ptst strict (Z.to_N (φ x)) (Z.to_N (φ v)).
Proof.
  intros strict x v. pose proof (to_Z_bounded x). pose proof (to_Z_bounded v).
  unfold tst, ptst. destruct strict; apply Bool.eq_iff_eq_true.
  - rewrite Uint63.ltb_spec, N.ltb_lt. lia.
  - rewrite Uint63.leb_spec, N.leb_le. lia.
Qed.

Definition part_post (strict : bool) (x hi : int) (y0 : array int) (l : nat)
    (r : array int * int) : Prop :=
  let (y', i') := r in
  PArray.length y' = PArray.length y0 /\ (l <= nn i' <= nn hi)%nat /\
  Permutation (seg y0 l (nn hi - l)) (seg y' l (nn hi - l)) /\
  (forall t, (Z.of_nat t < (φ (PArray.length y0)))%Z -> (t < l \/ nn hi <= t)%nat ->
     cell y' t = cell y0 t) /\
  (forall t, (l <= t < nn i')%nat -> ptst strict (Z.to_N (φ x)) (cell y' t) = true) /\
  (forall t, (nn i' <= t < nn hi)%nat -> ptst strict (Z.to_N (φ x)) (cell y' t) = false).

Lemma part_spec : forall (strict : bool) (x hi : int) (y0 : array int) (l : nat),
  ((φ hi) <= (φ (PArray.length y0)))%Z ->
  forall (z : Z) (y : array int) (i j : int) (H : Acc (Zwf 0) (gap hi j)),
  gap hi j = z ->
  PArray.length y = PArray.length y0 ->
  (l <= nn i <= nn j)%nat -> ((φ j) <= (φ hi))%Z ->
  Permutation (seg y0 l (nn hi - l)) (seg y l (nn hi - l)) ->
  (forall t, (Z.of_nat t < (φ (PArray.length y0)))%Z -> (t < l \/ nn hi <= t)%nat ->
     cell y t = cell y0 t) ->
  (forall t, (l <= t < nn i)%nat -> ptst strict (Z.to_N (φ x)) (cell y t) = true) ->
  (forall t, (nn i <= t < nn j)%nat -> ptst strict (Z.to_N (φ x)) (cell y t) = false) ->
  part_post strict x hi y0 l (part strict x hi y i j H).
Proof.
  intros strict x hi y0 l Hhi z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros y i j H Hz Hlen Hij Hjh Hp Hout Hlt Hge.
  rewrite part_eq.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j). pose proof (to_Z_bounded hi).
  pose proof (alength_bound y0).
  destruct (bdec (j <? hi)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite Uint63.ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    cbv zeta.
    destruct (tst strict x y.[j]) eqn:T.
    + assert (T' : ptst strict (Z.to_N (φ x)) (cell y (nn j)) = _)
        by (unfold cell; rewrite of_nat_nn, <- tst_ptst; exact T); clear T; rename T' into T.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (unfold nn in Hij; sia).
      assert (Hsw : forall t, (Z.of_nat t < (φ (PArray.length y0)))%Z ->
                cell (swap_with y i j y.[j]) t = cell y (tau (nn i) (nn j) t)).
      { intros t Ht. apply swap_cell; rewrite Hlen; unfold nn in Hij; lia. }
      apply (IH (gap hi (j + 1))).
      * rewrite <- Hz. apply dec_step. exact Hj.
      * reflexivity.
      * rewrite swap_length. exact Hlen.
      * unfold nn in *. rewrite Hi1, Hj1. lia.
      * lia.
      * eapply Permutation_trans; [exact Hp |].
        unfold seg at 2. rewrite (map_ext_in _ (fun t => cell y (tau (nn i) (nn j) t))).
        -- apply perm_tau; unfold nn in *; lia.
        -- intros t Ht. apply in_seq in Ht. apply Hsw. unfold nn in *; lia.
      * intros t Ht Hto. rewrite Hsw by exact Ht. rewrite <- (Hout t Ht Hto).
        f_equal. unfold tau. unfold nn in *. eqbs; lia.
      * intros t Ht. rewrite Hsw by (unfold nn in *; lia).
        unfold tau. unfold nn in *. rewrite Hi1 in Ht.
        destruct (Nat.eqb_spec t (Z.to_nat (φ j))) as [E1 | E1]; simpl.
        -- subst t. replace (Z.to_nat (φ i)) with (Z.to_nat (φ j)) by lia. exact T.
        -- destruct (Nat.eqb_spec t (Z.to_nat (φ i))) as [E2 | E2]; simpl.
           ++ exact T.
           ++ apply Hlt. lia.
      * intros t Ht. rewrite Hsw by (unfold nn in *; lia).
        unfold tau. unfold nn in *. rewrite Hi1, Hj1 in Ht.
        destruct (Nat.eqb_spec t (Z.to_nat (φ j))) as [E1 | E1]; simpl.
        -- apply Hge. lia.
        -- destruct (Nat.eqb_spec t (Z.to_nat (φ i))) as [E2 | E2]; simpl.
           ++ lia.
           ++ apply Hge. lia.
    + assert (T' : ptst strict (Z.to_N (φ x)) (cell y (nn j)) = _)
        by (unfold cell; rewrite of_nat_nn, <- tst_ptst; exact T); clear T; rename T' into T.
      apply (IH (gap hi (j + 1))).
      * rewrite <- Hz. apply dec_step. exact Hj.
      * reflexivity.
      * exact Hlen.
      * unfold nn in *. rewrite Hj1. lia.
      * lia.
      * exact Hp.
      * exact Hout.
      * exact Hlt.
      * intros t Ht. unfold nn in Ht. rewrite Hj1 in Ht.
        destruct (Nat.eq_dec t (nn j)) as [E1 | E1].
        -- subst t. exact T.
        -- apply Hge. unfold nn in *. lia.
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hj.
    assert (E : nn j = nn hi) by (unfold nn; lia).
    unfold part_post. rewrite E in Hge.
    repeat split; auto; lia.
Qed.

Lemma ptst_lt : forall X c, ptst true X c = true -> (c < X)%N.
Proof. intros X c H. apply N.ltb_lt. exact H. Qed.
Lemma ptst_ge : forall X c, ptst true X c = false -> (X <= c)%N.
Proof. intros X c H. apply N.ltb_ge. exact H. Qed.
Lemma ptst_le : forall X c, ptst false X c = true -> (c <= X)%N.
Proof. intros X c H. apply N.leb_le. exact H. Qed.
Lemma ptst_gt : forall X c, ptst false X c = false -> (X < c)%N.
Proof. intros X c H. apply N.leb_gt. exact H. Qed.

(* ------------------------------------------------------------------ *)
(* The selection loop                                                  *)
(* ------------------------------------------------------------------ *)

(* every cell left of lo is at most every cell from lo on *)
Definition linv (y : array int) (n lo : nat) : Prop :=
  forall s t, (s < lo)%nat -> (lo <= t < n)%nat -> (cell y s <= cell y t)%N.

(* every cell left of hi is at most every cell from hi on *)
Definition rinv (y : array int) (n hi : nat) : Prop :=
  forall s t, (s < hi)%nat -> (hi <= t < n)%nat -> (cell y s <= cell y t)%N.

(* permuting [li, hh) keeps both invariants *)
Lemma transport : forall y y2 n li hh,
  (li <= hh <= n)%nat ->
  Permutation (seg y li (hh - li)) (seg y2 li (hh - li)) ->
  (forall t, (t < n)%nat -> (t < li \/ hh <= t)%nat -> cell y2 t = cell y t) ->
  linv y n li -> rinv y n hh -> linv y2 n li /\ rinv y2 n hh.
Proof.
  intros y y2 n li hh Hb Hp Hout HL HR.
  assert (Hin : forall t, (li <= t < hh)%nat ->
            exists t', (li <= t' < hh)%nat /\ cell y2 t = cell y t').
  { intros t Ht. destruct (perm_cell y y2 li (hh - li) t Hp ltac:(lia)) as [t' [A B]].
    exists t'. split; [lia | exact B]. }
  split.
  - intros s t Hs Ht. rewrite (Hout s) by lia.
    destruct (Nat.lt_ge_cases t hh).
    + destruct (Hin t ltac:(lia)) as [t' [A B]]. rewrite B. apply HL; lia.
    + rewrite (Hout t) by lia. apply HL; lia.
  - intros s t Hs Ht. rewrite (Hout t) by lia.
    destruct (Nat.lt_ge_cases s li).
    + rewrite (Hout s) by lia. apply HR; lia.
    + destruct (Hin s ltac:(lia)) as [s' [A B]]. rewrite B. apply HR; lia.
Qed.

Definition sel_post (k : int) (y0 y : array int) : Prop :=
  PArray.length y = PArray.length y0 /\
  Permutation (seg y0 0 (nn (PArray.length y0))) (seg y 0 (nn (PArray.length y0))) /\
  (forall s, (s < nn k)%nat -> (cell y s <= cell y (nn k))%N) /\
  (forall t, (nn k < t < nn (PArray.length y0))%nat -> (cell y (nn k) <= cell y t)%N).

Lemma sel_spec : forall (k : int) (y0 : array int) (z : Z) (y : array int)
    (lo hi seed : int) (H : Acc (Zwf 0) (gap hi lo)),
  gap hi lo = z ->
  PArray.length y = PArray.length y0 ->
  Permutation (seg y0 0 (nn (PArray.length y0))) (seg y 0 (nn (PArray.length y0))) ->
  ((φ lo) <= (φ k) < (φ hi))%Z -> ((φ hi) <= (φ (PArray.length y0)))%Z ->
  linv y (nn (PArray.length y0)) (nn lo) -> rinv y (nn (PArray.length y0)) (nn hi) ->
  sel_post k y0 (sel k y lo hi seed H).
Proof.
  intros k y0 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros y lo hi seed H Hz Hlen Hperm Hk Hhi HL HR.
  rewrite sel_eq.
  pose proof (alength_bound y0).
  pose proof (nn_spec lo). pose proof (nn_spec hi). pose proof (nn_spec k).
  pose proof (nn_spec (PArray.length y0)).
  set (n := nn (PArray.length y0)) in *.
  destruct (bdec (lo <? hi)) as [Hlh | Hlh];
    [| exfalso; rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hlh; lia].
  cbv zeta.
  assert (Hpr : forall r, ((φ lo) <= (φ (lo + r mod (hi - lo))) < (φ hi))%Z) by (intros r; sia).
  set (p := lo + (lcg seed >> 17) mod (hi - lo)).
  pose proof (Hpr (lcg seed >> 17)) as Hp. fold p in Hp.
  pose proof (nn_spec p).
  set (x := y.[p]).
  set (X := Z.to_N (φ x)).
  assert (HX : cell y (nn p) = X) by (unfold cell, X, x; rewrite of_nat_nn; reflexivity).
  pose proof (part_spec true x hi y (nn lo) ltac:(rewrite Hlen; lia) _ y lo lo
     (Zwf_well_founded 0 (gap hi lo)) eq_refl eq_refl ltac:(lia) ltac:(lia)
     (Permutation_refl _) (fun _ _ _ => eq_refl)
     ltac:(intros; exfalso; lia) ltac:(intros; exfalso; lia)) as P1.
  destruct (part true x hi y lo lo (Zwf_well_founded 0 (gap hi lo))) as [y1 i] eqn:E1.
  unfold part_post in P1. destruct P1 as (L1 & B1 & Pm1 & O1 & Lt1 & Ge1).
  pose proof (nn_spec i).
  assert (Hi_hi : ((φ i) <= (φ hi))%Z) by lia.
  pose proof (part_spec false x hi y1 (nn i) ltac:(rewrite L1, Hlen; lia) _ y1 i i
     (Zwf_well_founded 0 (gap hi i)) eq_refl eq_refl ltac:(lia) Hi_hi
     (Permutation_refl _) (fun _ _ _ => eq_refl)
     ltac:(intros; exfalso; lia) ltac:(intros; exfalso; lia)) as P2.
  destruct (part false x hi y1 i i (Zwf_well_founded 0 (gap hi i))) as [y2 m] eqn:E2.
  unfold part_post in P2. destruct P2 as (L2 & B2 & Pm2 & O2 & Le2 & Gt2).
  pose proof (nn_spec m).
  assert (Hlen2 : PArray.length y2 = PArray.length y0) by (rewrite L2, L1; exact Hlen).
  assert (O : forall t, (t < n)%nat -> (t < nn lo \/ nn hi <= t)%nat -> cell y2 t = cell y t).
  { intros t Ht Hto. rewrite O2 by (rewrite ?L1, ?Hlen; lia).
    apply O1; [rewrite ?Hlen; lia | exact Hto]. }
  assert (Pm : Permutation (seg y (nn lo) (nn hi - nn lo)) (seg y2 (nn lo) (nn hi - nn lo))).
  { eapply Permutation_trans; [exact Pm1 |].
    apply (perm_widen y1 y2 (nn lo) (nn hi) (nn i) (nn hi)); [lia | lia | exact Pm2 |].
    intros t Ht Hto. apply O2; [rewrite ?L1, ?Hlen; lia | exact Hto]. }
  assert (Pall : Permutation (seg y0 0 n) (seg y2 0 n)).
  { eapply Permutation_trans; [exact Hperm |].
    rewrite <- (Nat.sub_0_r n).
    apply (perm_widen y y2 0 n (nn lo) (nn hi)); [lia | lia | exact Pm |].
    intros t Ht Hto. apply O; lia. }
  destruct (transport y y2 n (nn lo) (nn hi) ltac:(lia) Pm O HL HR) as [HL2 HR2].
  assert (F1 : forall t, (nn lo <= t < nn i)%nat -> (cell y2 t < X)%N).
  { intros t Ht. rewrite O2 by (rewrite ?L1, ?Hlen; lia). apply ptst_lt, Lt1. exact Ht. }
  assert (F2 : forall t, (nn i <= t < nn hi)%nat -> (X <= cell y2 t)%N).
  { intros t Ht.
    destruct (perm_cell y1 y2 (nn i) (nn hi - nn i) t Pm2 ltac:(lia)) as [t' [A B]].
    rewrite B. apply ptst_ge, Ge1. lia. }
  assert (F3 : forall t, (nn i <= t < nn m)%nat -> (cell y2 t <= X)%N)
    by (intros t Ht; apply ptst_le, Le2; exact Ht).
  assert (F4 : forall t, (nn m <= t < nn hi)%nat -> (X < cell y2 t)%N)
    by (intros t Ht; apply ptst_gt, Gt2; exact Ht).
  assert (Him : (nn i < nn m)%nat).
  { assert (Hin : In X (seg y (nn lo) (nn hi - nn lo)))
      by (apply in_seg; exists (nn p); split; [lia | exact HX]).
    apply (Permutation_in _ Pm) in Hin. apply in_seg in Hin. destruct Hin as [t [A B]].
    destruct (Nat.lt_ge_cases t (nn i)) as [C | C]; [specialize (F1 t ltac:(lia)); lia |].
    destruct (Nat.lt_ge_cases t (nn m)) as [D | D]; [lia |].
    specialize (F4 t ltac:(lia)). lia. }
  destruct (k <? i) eqn:Eki.
  - rewrite Uint63.ltb_spec in Eki.
    destruct (bdec (i <? hi)) as [Hih | Hih];
      [| exfalso; rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hih; lia].
    apply (IH (gap i lo)).
    + rewrite <- Hz. apply dec_left; assumption.
    + reflexivity.
    + exact Hlen2.
    + exact Pall.
    + lia.
    + lia.
    + exact HL2.
    + intros s t Hs Ht.
      destruct (Nat.lt_ge_cases t (nn hi)) as [C | C]; [| apply HR2; lia].
      destruct (Nat.lt_ge_cases s (nn lo)) as [D | D]; [apply HL2; lia |].
      specialize (F1 s ltac:(lia)). specialize (F2 t ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Eki.
    destruct (k <? m) eqn:Ekm.
    + rewrite Uint63.ltb_spec in Ekm.
      unfold sel_post. fold n.
      assert (Ck : cell y2 (nn k) = X)
        by (specialize (F2 (nn k) ltac:(lia)); specialize (F3 (nn k) ltac:(lia)); lia).
      split; [exact Hlen2 |]. split; [exact Pall |]. split.
      * intros s Hs. rewrite Ck.
        destruct (Nat.lt_ge_cases s (nn lo)) as [D | D]; [rewrite <- Ck; apply HL2; lia |].
        destruct (Nat.lt_ge_cases s (nn i)) as [C | C];
          [specialize (F1 s ltac:(lia)); lia |].
        apply F3; lia.
      * intros t Ht. rewrite Ck.
        destruct (Nat.lt_ge_cases t (nn hi)) as [D | D]; [| rewrite <- Ck; apply HR2; lia].
        destruct (Nat.lt_ge_cases t (nn m)) as [C | C];
          [apply F2; lia | specialize (F4 t ltac:(lia)); lia].
    + rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Ekm.
      destruct (bdec (lo <? m)) as [Hlm | Hlm];
        [| exfalso; rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hlm; lia].
      apply (IH (gap hi m)).
      * rewrite <- Hz. apply dec_right; assumption.
      * reflexivity.
      * exact Hlen2.
      * exact Pall.
      * lia.
      * lia.
      * intros s t Hs Ht.
        destruct (Nat.lt_ge_cases t (nn hi)) as [C | C]; [| apply HR2; lia].
        specialize (F4 t ltac:(lia)).
        destruct (Nat.lt_ge_cases s (nn lo)) as [D | D]; [apply HL2; lia |].
        destruct (Nat.lt_ge_cases s (nn i)) as [E | E];
          [specialize (F1 s ltac:(lia)); lia | specialize (F3 s ltac:(lia)); lia].
      * exact HR2.
Qed.

(* ------------------------------------------------------------------ *)
(* The maximum scan                                                    *)
(* ------------------------------------------------------------------ *)

Lemma maxl_spec : forall (y : array int) (k : int),
  ((φ k) <= (φ (PArray.length y)))%Z ->
  forall (z : Z) (j acc : int) (H : Acc (Zwf 0) (gap k j)),
  gap k j = z -> ((φ j) <= (φ k))%Z ->
  (exists j0, (j0 < nn j)%nat /\ cell y j0 = Z.to_N (φ acc)) ->
  (forall s, (s < nn j)%nat -> (cell y s <= Z.to_N (φ acc))%N) ->
  (exists j0, (j0 < nn k)%nat /\ cell y j0 = Z.to_N (φ (maxl y k j acc H))) /\
  (forall s, (s < nn k)%nat -> (cell y s <= Z.to_N (φ (maxl y k j acc H)))%N).
Proof.
  intros y k Hk z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j acc H Hz Hj Hex Hall.
  rewrite maxl_eq.
  pose proof (nn_spec j). pose proof (nn_spec k). pose proof (alength_bound y).
  destruct (bdec (j <? k)) as [Hjk | Hjk].
  - pose proof Hjk as Hjk'. rewrite Uint63.ltb_spec in Hjk'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Hj1n : nn (j + 1) = S (nn j)) by (unfold nn; rewrite Hj1; lia).
    cbv zeta.
    assert (Cj : cell y (nn j) = Z.to_N (φ (y.[j]))) by (unfold cell; rewrite of_nat_nn; reflexivity).
    pose proof (to_Z_bounded acc). pose proof (to_Z_bounded (y.[j])).
    apply (IH (gap k (j + 1))).
    + rewrite <- Hz. apply dec_step. exact Hjk.
    + reflexivity.
    + lia.
    + destruct (acc <? y.[j]) eqn:E.
      * exists (nn j). split; [lia | exact Cj].
      * destruct Hex as [j0 [A B]]. exists j0. split; [lia | exact B].
    + intros s Hs. rewrite Hj1n in Hs.
      destruct (acc <? y.[j]) eqn:E;
        [rewrite Uint63.ltb_spec in E | rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E];
        (destruct (Nat.eq_dec s (nn j)) as [Es | Es];
         [subst s; rewrite Cj; lia | specialize (Hall s ltac:(lia)); lia]).
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hjk.
    assert (E : nn j = nn k) by (unfold nn; lia).
    rewrite <- E. split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Order statistics on lists                                           *)
(* ------------------------------------------------------------------ *)

Definition cnt (f : N -> bool) (l : list N) : nat := List.length (filter f l).

Lemma cnt_perm : forall f l l', Permutation l l' -> cnt f l = cnt f l'.
Proof.
  intros f l l' H. unfold cnt.
  induction H; simpl; try (destruct (f x)); try (destruct (f y)); simpl; lia.
Qed.

Lemma cnt_app : forall f l l', cnt f (l ++ l') = (cnt f l + cnt f l')%nat.
Proof. intros. unfold cnt. rewrite filter_app, length_app. reflexivity. Qed.

Lemma cnt_le_length : forall f l, (cnt f l <= List.length l)%nat.
Proof.
  intros f l. unfold cnt. induction l as [| c l IH]; simpl; [lia |].
  destruct (f c); simpl; lia.
Qed.

Lemma cnt_none : forall f l, Forall (fun c => f c = false) l -> cnt f l = 0%nat.
Proof.
  intros f l H. unfold cnt. induction H as [| c l Hc _ IH]; simpl; [reflexivity |].
  rewrite Hc. exact IH.
Qed.

Lemma cnt_all : forall f l, Forall (fun c => f c = true) l -> cnt f l = List.length l.
Proof.
  intros f l H. unfold cnt. induction H as [| c l Hc _ IH]; simpl; [reflexivity |].
  rewrite Hc. simpl. rewrite IH. reflexivity.
Qed.

(* in a sorted list, position k holds v when fewer than k+1 cells are
   below v and more than k are at most v *)
Lemma sorted_nth : forall l k v, Sorted N.le l ->
  (cnt (fun c => (c <? v)%N) l <= k)%nat ->
  (k < cnt (fun c => (c <=? v)%N) l)%nat ->
  nth k l 0%N = v.
Proof.
  induction l as [| x t IH]; intros k v Hs H1 H2.
  - unfold cnt in H2. simpl in H2. lia.
  - pose proof (Sorted_extends (fun a b c => N.le_trans a b c) Hs) as Hf.
    apply Sorted_inv in Hs. destruct Hs as [Hs _].
    unfold cnt in H1, H2. simpl in H1, H2.
    destruct (N.ltb_spec x v) as [Hxv | Hxv].
    + replace (x <=? v)%N with true in H2 by (symmetry; apply N.leb_le; lia).
      simpl in H1, H2. destruct k as [| k]; [lia |]. simpl.
      apply IH; [exact Hs | unfold cnt; lia | unfold cnt; lia].
    + destruct (N.leb_spec x v) as [Hxv' | Hxv'].
      * assert (x = v) by lia. subst x.
        destruct k as [| k]; [reflexivity |]. simpl.
        simpl in H2. apply IH; [exact Hs | |].
        -- rewrite cnt_none; [lia |].
           eapply Forall_impl; [| exact Hf]. intros c Hc. apply N.ltb_ge. exact Hc.
        -- unfold cnt. lia.
      * exfalso.
        assert (Z0 : cnt (fun c => (c <=? v)%N) t = 0%nat).
        { apply cnt_none. eapply Forall_impl; [| exact Hf].
          intros c Hc. apply N.leb_gt. lia. }
        unfold cnt in Z0. lia.
Qed.

(* a position k with nothing larger before it and nothing smaller after it
   holds the k-th smallest element *)
Lemma kth : forall m l k, Permutation m l -> Sorted N.le l -> (k < List.length m)%nat ->
  (forall s, (s < k)%nat -> (nth s m 0 <= nth k m 0)%N) ->
  (forall t, (k < t < List.length m)%nat -> (nth k m 0 <= nth t m 0)%N) ->
  nth k l 0%N = nth k m 0%N.
Proof.
  intros m l k Hp Hs Hk H1 H2.
  destruct (nth_split m 0%N Hk) as [A [B [Em La]]].
  remember (nth k m 0%N) as v eqn:Ev.
  assert (FA : forall c, In c A -> (c <= v)%N).
  { intros c Hc. apply In_nth with (d := 0%N) in Hc. destruct Hc as [s [Hs1 Hs2]].
    rewrite <- Hs2. pose proof (H1 s ltac:(lia)) as Hc.
    rewrite Em, app_nth1 in Hc by exact Hs1. exact Hc. }
  assert (FB : forall c, In c B -> (v <= c)%N).
  { intros c Hc. apply In_nth with (d := 0%N) in Hc. destruct Hc as [s [Hs1 Hs2]].
    assert (Hl : List.length m = (List.length A + S (List.length B))%nat)
      by (rewrite Em, length_app; reflexivity).
    pose proof (H2 (k + S s)%nat ltac:(lia)) as Hc.
    rewrite Em in Hc.
    rewrite app_nth2 in Hc by lia.
    replace (k + S s - List.length A)%nat with (S s) in Hc by lia.
    simpl in Hc. rewrite Hs2 in Hc. exact Hc. }
  apply sorted_nth; [exact Hs | |]; rewrite <- (cnt_perm _ _ _ Hp); rewrite Em, cnt_app.
  - rewrite (cnt_none _ (v :: B)); [pose proof (cnt_le_length (fun c => (c <? v)%N) A); lia |].
    constructor; [apply N.ltb_irrefl |].
    apply Forall_forall. intros c Hc. apply N.ltb_ge. apply FB. exact Hc.
  - rewrite (cnt_all _ A); [| apply Forall_forall; intros c Hc; apply N.leb_le, FA, Hc].
    unfold cnt. simpl. rewrite N.leb_refl. simpl. lia.
Qed.

Lemma map_seq_nth : forall (g : nat -> N) lo len t d, (t < len)%nat ->
  nth t (map g (seq lo len)) d = g (lo + t)%nat.
Proof.
  intros g lo len t d Ht.
  rewrite (nth_indep _ d (g 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma seg_length : forall y lo len, List.length (seg y lo len) = len.
Proof. intros. unfold seg. rewrite length_map, length_seq. reflexivity. Qed.

Lemma tau_b : forall a b, tau a b b = a.
Proof. intros a b. unfold tau. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma tau_a : forall a b, a <> b -> tau a b a = b.
Proof.
  intros a b H. unfold tau. destruct (Nat.eqb_spec a b); [contradiction |].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma tau_other : forall a b t, t <> a -> t <> b -> tau a b t = t.
Proof.
  intros a b t H1 H2. unfold tau.
  destruct (Nat.eqb_spec t b); [contradiction |]. destruct (Nat.eqb_spec t a); [contradiction |].
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the input                                                   *)
(* ------------------------------------------------------------------ *)

Lemma repr_len : forall (x : array uint) (a : list N), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_seg : forall (x : array uint) (a : list N), repr x a ->
  a = seg x 0 (List.length a).
Proof.
  intros x a [_ Hc]. apply nth_error_ext. intros t.
  unfold seg. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec t (List.length a)) as [Ht | Ht].
  - destruct (Hc t Ht) as [v [E R]]. rewrite E. simpl. f_equal. symmetry. exact R.
  - apply nth_error_None. exact Ht.
Qed.

(* ------------------------------------------------------------------ *)
(* The float result                                                    *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Lemma bpow_big : forall z : Z, (0 <= z <= 2 * 10 ^ 9)%Z ->
  Rabs (IZR z / 2) < Raux.bpow Zaux.radix2 1024.
Proof.
  intros z Hz. assert (0 <= IZR z) by (apply IZR_le; lia).
  rewrite Rabs_right by lra.
  change (Raux.bpow Zaux.radix2 1024) with (IZR (Z.pow_pos 2 1024)).
  assert (IZR z < IZR (Z.pow_pos 2 1024))
    by (apply IZR_lt; change (Z.pow_pos 2 1024) with (2 ^ 1024)%Z; lia).
  lra.
Qed.

Lemma half_exact : forall z : Z, (0 <= z <= 2 * 10 ^ 9)%Z -> rnd (IZR z / 2) = IZR z / 2.
Proof.
  intros z Hz. apply rnd_exact. apply FLT.generic_format_FLT.
  apply (FLT.FLT_spec _ _ _ _ (Defs.Float Zaux.radix2 z (-1))).
  - unfold Defs.F2R. simpl. lra.
  - simpl. lia.
  - simpl. lia.
Qed.

Local Close Scope R_scope.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma median_impl_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a -> exists r : R, repr (median_impl x) r /\ median_spec a r.
Proof.
  intros a x Hv Hr.
  destruct Hv as [Hn Hb]. unfold len in Hn.
  pose proof (repr_len x a Hr) as Hl.
  pose proof (repr_seg x a Hr) as Ha.
  set (nN := List.length a) in *.
  set (n := PArray.length x) in *.
  pose proof (alength_bound x) as Bx.
  assert (Hnn : nn n = nN) by (unfold nn; lia).
  set (y0 := PArray.copy x).
  assert (L0 : @PArray.length int y0 = n) by exact (alength_copy x).
  assert (C0 : forall t, cell y0 t = cell x t)
    by (intros t; unfold cell, y0; rewrite aget_copy; reflexivity).
  assert (Hk : (φ (n / 2)) = ((φ n) / 2)%Z) by sia.
  pose proof (sel_spec (n / 2) y0 _ y0 0 n seed0 (Zwf_well_founded 0 (gap n 0)) eq_refl eq_refl
     (Permutation_refl _) ltac:(change (φ 0) with 0%Z; sia) ltac:(rewrite L0; lia)
     ltac:(intros s t Hs; exfalso; change (nn 0) with 0%nat in Hs; lia)
     ltac:(intros s t Hs Ht; exfalso; rewrite L0 in Ht; lia)) as HS.
  unfold median_impl. fold n. fold y0.
  set (Y := sel (n / 2) y0 0 n seed0 (Zwf_well_founded 0 (gap n 0))) in *.
  change (exists r : R,
    repr (if n mod 2 =? 1 then of_uint63 (Y.[n / 2])
          else (of_uint63 (maxl Y (n / 2) 1 (Y.[0]) (Zwf_well_founded 0 (gap (n / 2) 1))
                           + Y.[n / 2]) / of_uint63 2)%float) r /\ median_spec a r).
  destruct HS as (LY & PY & SY1 & SY2).
  rewrite L0, Hnn in PY, SY2.
  rewrite L0 in LY.
  assert (Pa : Permutation a (seg Y 0 nN)).
  { rewrite (seg_ext y0 x) in PY by (intros; apply C0). rewrite <- Ha in PY. exact PY. }
  set (kk := nn (n / 2)) in *.
  assert (Hkk : Z.of_nat kk = ((φ n) / 2)%Z) by (unfold kk; rewrite nn_spec; exact Hk).
  assert (Hkk2 : (2 * Z.of_nat kk <= Z.of_nat nN <= 2 * Z.of_nat kk + 1)%Z)
    by (rewrite Hkk, <- Hl; sia).
  assert (Bd : forall t, (t < nN)%nat -> (cell Y t <= 10 ^ 9)%N).
  { intros t Ht.
    assert (Hin : In (cell Y t) a).
    { apply (Permutation_in _ (Permutation_sym Pa)). apply in_seg. exists t. split; [lia | reflexivity]. }
    rewrite Forall_forall in Hb. apply Hb. exact Hin. }
  assert (NY : forall t, (t < nN)%nat -> nth t (seg Y 0 nN) 0%N = cell Y t)
    by (intros t Ht; unfold seg; apply map_seq_nth; exact Ht).
  assert (KU : forall l, Permutation a l -> Sorted N.le l -> nth kk l 0%N = cell Y kk).
  { intros l Hpl Hsl. rewrite <- NY by lia. apply kth.
    - eapply Permutation_trans; [apply Permutation_sym; exact Pa | exact Hpl].
    - exact Hsl.
    - rewrite seg_length. lia.
    - intros s Hs. rewrite !NY by lia. apply SY1. exact Hs.
    - intros t Ht. rewrite seg_length in Ht. rewrite !NY by lia. apply SY2. lia. }
  assert (Ll : forall l, Permutation a l -> len l = N.of_nat nN)
    by (intros l Hpl; unfold len; rewrite <- (Permutation_length Hpl); reflexivity).
  assert (CU : Z.of_N (cell Y kk) = (φ (Y.[n / 2]))).
  { unfold cell, kk. rewrite of_nat_nn. pose proof (to_Z_bounded (Y.[n / 2])). lia. }
  pose proof (Bd kk ltac:(lia)) as BU.
  destruct (n mod 2 =? 1) eqn:Eo.
  - (* n odd *)
    rewrite Uint63.eqb_spec in Eo.
    exists (IZR (Z.of_N (cell Y kk))). split.
    + rewrite CU. apply repr_of_uint63_exact. lia.
    + intros l Hpl Hsl. unfold median_of_sorted. rewrite (Ll l Hpl).
      assert (Od : N.odd (N.of_nat nN) = true)
        by (apply N.odd_spec; exists (N.of_nat kk); sia).
      rewrite Od. unfold elem.
      replace (N.to_nat (N.of_nat nN / 2)) with kk by sia.
      rewrite (KU l Hpl Hsl). reflexivity.
  - (* n even *)
    rewrite Uint63.eqb_false_spec in Eo.
    assert (Hk1 : (1 <= kk)%nat) by sia.
    pose proof (maxl_spec Y (n / 2) ltac:(rewrite LY; sia) _ 1 (Y.[0])
       (Zwf_well_founded 0 (gap (n / 2) 1)) eq_refl
       ltac:(change (φ 1) with 1%Z; lia)
       ltac:(exists 0%nat; split; [change (nn 1) with 1%nat; lia | reflexivity])
       ltac:(intros s Hs; change (nn 1) with 1%nat in Hs;
             assert (s = 0%nat) by lia; subst s; apply N.le_refl)) as HM.
    set (w := maxl Y (n / 2) 1 (Y.[0]) (Zwf_well_founded 0 (gap (n / 2) 1))) in *.
    fold kk in HM.
    destruct HM as [[jm [Hjm Cjm]] Hmax].
    pose proof (Bd jm ltac:(lia)) as BW.
    assert (CW : Z.of_N (cell Y jm) = (φ w))
      by (rewrite Cjm; pose proof (to_Z_bounded w); lia).
    assert (Hsum : (φ (w + Y.[n / 2])) = ((φ w) + (φ (Y.[n / 2])))%Z) by sia.
    assert (KL : forall l, Permutation a l -> Sorted N.le l -> nth (kk - 1) l 0%N = cell Y jm).
    { intros l Hpl Hsl.
      set (M' := map (fun t => cell Y (tau jm (kk - 1) t)) (seq 0 nN)).
      assert (Pm' : Permutation (seg Y 0 nN) M') by (apply perm_tau; lia).
      assert (NM : forall t, (t < nN)%nat -> nth t M' 0%N = cell Y (tau jm (kk - 1) t))
        by (intros t Ht; unfold M'; apply map_seq_nth; exact Ht).
      assert (LM : List.length M' = nN) by (unfold M'; rewrite length_map, length_seq; reflexivity).
      transitivity (nth (kk - 1) M' 0%N).
      - apply kth.
        + eapply Permutation_trans; [apply Permutation_sym; exact Pm' |].
          eapply Permutation_trans; [apply Permutation_sym; exact Pa | exact Hpl].
        + exact Hsl.
        + lia.
        + intros s Hs. rewrite !NM by lia. rewrite tau_b, Cjm.
          destruct (Nat.eq_dec s jm) as [E | E].
          * subst s. destruct (Nat.eq_dec jm (kk - 1)) as [E' | E'].
            -- rewrite E', tau_b. rewrite <- E', Cjm. apply N.le_refl.
            -- rewrite tau_a by exact E'. apply Hmax. lia.
          * rewrite tau_other by lia. apply Hmax. lia.
        + intros t Ht. rewrite !NM by lia. rewrite tau_b, tau_other by lia.
          destruct (Nat.eq_dec t kk) as [E | E].
          * subst t. apply SY1. exact Hjm.
          * apply N.le_trans with (cell Y kk); [apply SY1; exact Hjm | apply SY2; lia].
      - rewrite NM by lia. rewrite tau_b. reflexivity. }
    exists (IZR (φ (w + Y.[n / 2])) / 2)%R. split.
    + pose proof (repr_of_uint63_exact (w + Y.[n / 2]) ltac:(lia)) as R1.
      pose proof (repr_of_uint63_exact 2 eq_refl) as R2.
      change (φ 2) with 2%Z in R2.
      rewrite <- (half_exact (φ (w + Y.[n / 2]))) by lia.
      apply repr_div; [exact R1 | exact R2 | lra |].
      rewrite half_exact by lia. apply bpow_big. lia.
    + intros l Hpl Hsl. unfold median_of_sorted. rewrite (Ll l Hpl).
      destruct (N.odd (N.of_nat nN)) eqn:Od;
        [exfalso; apply N.odd_spec in Od; destruct Od as [q Hq]; sia |].
      unfold elem.
      replace (N.to_nat (N.of_nat nN / 2)) with kk by sia.
      replace (N.to_nat (N.of_nat nN / 2 - 1)) with (kk - 1)%nat by sia.
      rewrite (KU l Hpl Hsl), (KL l Hpl Hsl), CU, CW, Hsum, plus_IZR.
      reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition median : array uint -> float := median_impl.

Definition median_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists r : R, repr (median x) r /\ median_spec a r
  := median_impl_correct.
