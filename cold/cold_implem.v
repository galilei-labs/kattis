(* Implementation of cold (cold.spec): count the strictly negative
   entries of an array of signed words.

   Code.  [count_loop x n i acc] scans the indices i .. n-1 of x once, left
   to right, adding 1 to the Uint63 accumulator whenever the cell is below
   zero under the signed comparison [Sint63.ltb].  Nothing is allocated,
   each cell is read once.  No Z, no nat in the extracted code.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap n i)] proof, as in template/polymul1. *)

From Cold.spec Require Import Prelude.
From StdGalilei Require Import repr.
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

(* acc + the number of negative cells among x.[i] .. x.[n-1]. *)
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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec in H. exact H.
Qed.

(* Reading an in-bounds cell of an array representing l. *)
Lemma repr_get : forall (x : array sint) (l : list Z), repr x l ->
  forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  Sint63.to_Z x.[i] = nth (Z.to_nat (φ i)) l 0%Z.
Proof.
  intros x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hr.
  symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array sint) (l : list Z), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros x l [Hl _]. symmetry. exact Hl. Qed.

Lemma firstn_S_nth : forall (l : list Z) (k : nat), (k < List.length l)%nat ->
  firstn (S k) l = firstn k l ++ [nth k l 0%Z].
Proof.
  induction l as [| a l IH]; intros k Hk; simpl in Hk; [lia|].
  destruct k as [| k]; [reflexivity|].
  change (firstn (S (S k)) (a :: l)) with (a :: firstn (S k) l).
  rewrite IH by lia. reflexivity.
Qed.

Definition cnt (l : list Z) (k : nat) : Z :=
  Z.of_nat (List.length (filter is_negative (firstn k l))).

Lemma cnt_le : forall l k, (cnt l k <= Z.of_nat k)%Z.
Proof.
  intros l k. unfold cnt.
  pose proof (filter_length_le is_negative (firstn k l)) as H1.
  pose proof (firstn_le_length k l) as H2.
  lia.
Qed.

Lemma cnt_S : forall l k, (k < List.length l)%nat ->
  cnt l (S k) = (cnt l k + if is_negative (nth k l 0%Z) then 1 else 0)%Z.
Proof.
  intros l k Hk. unfold cnt.
  rewrite firstn_S_nth by exact Hk.
  rewrite filter_app, length_app. simpl.
  destruct (is_negative (nth k l 0%Z)); simpl; lia.
Qed.

(* The scanning loop. *)
Lemma count_loop_spec : forall (l : list Z) (x : array sint),
  repr x l ->
  forall (z : Z) (i acc : int) (H : Acc (Zwf 0) (gap (PArray.length x) i)),
  gap (PArray.length x) i = z ->
  ((φ i) <= (φ (PArray.length x)))%Z ->
  (φ acc) = cnt l (Z.to_nat (φ i)) ->
  (φ (count_loop x (PArray.length x) i acc H)) = cnt l (List.length l).
Proof.
  intros l x Hx z.
  pose proof (repr_length x l Hx) as Lx.
  pose proof (alength_bound x) as Bx.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Hin Hacc.
  rewrite count_loop_eq.
  destruct (bdec (i <? PArray.length x)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    pose proof (cnt_le l (Z.to_nat (φ i))) as Hle.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by lia.
      rewrite cnt_S by lia.
      pose proof (repr_get x l Hx i ltac:(lia)) as E.
      unfold is_negative. rewrite <- E.
      lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:C end.
      * apply Sint63.ltb_spec in C. change (Sint63.to_Z 0) with 0%Z in C.
        apply Z.compare_lt_iff in C.
        replace (Sint63.to_Z x.[i] <? 0)%Z with true by (symmetry; apply Z.ltb_lt; exact C).
        rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; lia.
      * rewrite <- Bool.not_true_iff_false, Sint63.ltb_spec in C.
        change (Sint63.to_Z 0) with 0%Z in C.
        rewrite Z.compare_lt_iff in C.
        lazymatch goal with |- context [if (?a <? 0)%Z then _ else _] =>
          destruct (Z.ltb_spec a 0) as [N | N] end;
          [exfalso; apply C; exact N | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    replace (List.length l) with (Z.to_nat (φ i)) by lia. exact Hacc.
Qed.

Lemma count_negatives_impl_correct : forall (l : list Z) (x : array sint),
  valid_input l -> repr x l ->
  exists c : N, repr (count_negatives_impl x) c /\ count_negatives_spec l c.
Proof.
  intros l x _ Hx.
  exists (len (filter is_negative l)). split; [| reflexivity].
  unfold repr, repr_uint, count_negatives_impl, len.
  pose proof (count_loop_spec l x Hx _ 0 0
                (Zwf_well_founded 0 (gap (PArray.length x) 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (PArray.length x)); lia)
                eq_refl) as E.
  unfold cnt in E. rewrite firstn_all in E.
  lazymatch goal with |- Z.to_N (to_Z ?t) = _ =>
    replace (to_Z t) with (Z.of_nat (List.length (filter is_negative l)))
      by (symmetry; exact E) end.
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition count_negatives : array sint -> uint := count_negatives_impl.

Definition count_negatives_correct : forall (l : list Z) (x : array sint),
  valid_input l -> repr x l ->
  exists c : N, repr (count_negatives x) c /\ count_negatives_spec l c
  := count_negatives_impl_correct.
