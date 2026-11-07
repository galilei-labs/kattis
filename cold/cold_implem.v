(* Implementation of cold (cold.spec): count the negative temperatures.

   Code.  [count_negatives x] is one left-to-right scan over the indices
   0 .. |x|-1 with an [int] accumulator: each cell is read once with
   [PArray.get] and tested with the signed comparison [Sint63.ltb x.[i] 0];
   the accumulator is incremented on a hit.  Nothing is allocated.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap n i)] proof, as in template/polymul1.

   Proof.  Invariant: after i steps the accumulator is the number of
   negative entries of [firstn i l].  At i = |l| this is [filter is_negative l],
   whose length is at most 100 < 2^63, so the word represents it. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
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

(* acc + the number of negative cells among x.[i], ..., x.[n-1]. *)
Fixpoint count_loop (x : array int) (n i acc : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      count_loop x n (i + 1)
        (if Sint63.ltb x.[i] 0 then acc + 1 else acc)
        (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.

Lemma count_loop_eq : forall x n i acc H,
  count_loop x n i acc H =
  match bdec (i <? n) with
  | left Hi =>
      count_loop x n (i + 1)
        (if Sint63.ltb x.[i] 0 then acc + 1 else acc)
        (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition count_negatives_impl (x : array sint) : uint :=
  let n := PArray.length x in
  count_loop x n 0 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Prop side                                                           *)
(* ------------------------------------------------------------------ *)

(* The number of negative entries among the first k of l. *)
Definition cnt (l : list Z) (k : nat) : Z :=
  Z.of_nat (List.length (filter is_negative (firstn k l))).

Lemma cnt_step : forall (l : list Z) (k : nat) (t : Z),
  nth_error l k = Some t ->
  cnt l (S k) = (cnt l k + if is_negative t then 1 else 0)%Z.
Proof.
  intros l k t Ht. unfold cnt.
  assert (Hk : (k < List.length l)%nat) by (apply nth_error_Some; congruence).
  pose proof (firstn_skipn_middle k l Ht) as E.
  assert (F : firstn (S k) l = firstn k l ++ [t]).
  { rewrite <- E at 1. rewrite firstn_app, length_firstn.
    replace (S k - Nat.min k (List.length l))%nat with 1%nat by lia.
    rewrite firstn_all2 by (rewrite length_firstn; lia). reflexivity. }
  rewrite F, filter_app, length_app. simpl.
  destruct (is_negative t); simpl; lia.
Qed.

Lemma cnt_le : forall (l : list Z) (k : nat), (cnt l k <= Z.of_nat k)%Z.
Proof.
  intros l k. unfold cnt.
  pose proof (filter_length_le is_negative (firstn k l)).
  pose proof (firstn_le_length k l).
  lia.
Qed.

(* Reading an in-bounds cell of an array representing l. *)
Lemma repr_get : forall (x : array sint) (l : list Z), repr x l ->
  forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  nth_error l (Z.to_nat (φ i)) = Some (Sint63.to_Z x.[i]).
Proof.
  intros x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hm, Hr. reflexivity.
Qed.

Lemma count_loop_spec : forall (l : list Z) (x : array sint),
  repr x l ->
  forall (n : int), (φ n) = Z.of_nat (List.length l) ->
  forall (z : Z) (i acc : int) (H : Acc (Zwf 0) (gap n i)),
  gap n i = z ->
  ((φ i) <= (φ n))%Z ->
  (φ acc) = cnt l (Z.to_nat (φ i)) ->
  (φ (count_loop x n i acc H)) = cnt l (List.length l).
Proof.
  intros l x Hx n Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Hin Hacc.
  rewrite count_loop_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded n) as Bn.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    pose proof (repr_get x l Hx i ltac:(lia)) as Hg.
    pose proof (cnt_step l _ _ Hg) as Hs.
    pose proof (cnt_le l (Z.to_nat (φ i))) as Hle.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by lia. rewrite Hs.
      unfold is_negative.
      rewrite Z2Nat.id in Hle by lia.
      (* the cell in the code and the cell in [repr_get] differ by their
         universe instance, so [lia] sees two atoms: bridge with [exact] *)
      lazymatch goal with |- context [if ltsb ?v 0 then _ else _] =>
        destruct (ltsb v 0) eqn:E; pose proof (Sint63.ltb_spec v 0) as Sp end.
      all: lazymatch goal with |- context [if (?w <? 0)%Z then _ else _] =>
        destruct (Z.ltb_spec w 0) end.
      all: change (Sint63.to_Z 0) with 0%Z in Sp.
      * rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; lia.
      * apply Sp in E. rewrite Z.compare_lt_iff in E.
        exfalso. apply (Z.lt_irrefl 0).
        eapply Z.le_lt_trans; [exact H0 | exact E].
      * exfalso. rewrite <- Bool.not_true_iff_false in E.
        apply E, Sp, Z.compare_lt_iff. exact H0.
      * lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    replace (List.length l) with (Z.to_nat (φ i)) by lia. exact Hacc.
Qed.

Lemma count_negatives_impl_correct : forall (l : list Z) (x : array sint),
  valid_input l -> repr x l ->
  exists c : N, repr (count_negatives_impl x) c /\ count_negatives_spec l c.
Proof.
  intros l x _ Hx.
  exists (len (filter is_negative l)). split; [| reflexivity].
  assert (Hn : (φ (PArray.length x)) = Z.of_nat (List.length l)).
  { destruct Hx as [Hl _]. symmetry. exact Hl. }
  unfold repr, repr_uint, count_negatives_impl.
  (* [repr_array]'s [PArray.length] is at another universe instance *)
  assert (Hn' : (φ (PArray.length@{Set} x)) = Z.of_nat (List.length l)) by exact Hn.
  rewrite (count_loop_spec l x Hx (PArray.length@{Set} x) Hn' _ 0 0 _ eq_refl).
  - unfold cnt, len. rewrite firstn_all. lia.
  - change (φ 0) with 0%Z. lia.
  - change (φ 0) with 0%Z. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition count_negatives : array sint -> uint := count_negatives_impl.

Definition count_negatives_correct : forall (l : list Z) (x : array sint),
  valid_input l -> repr x l ->
  exists c : N, repr (count_negatives x) c /\ count_negatives_spec l c
  := count_negatives_impl_correct.
