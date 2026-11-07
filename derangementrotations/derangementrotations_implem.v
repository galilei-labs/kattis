From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation Znumtheory Bool.
Import ListNotations.

Unset Lia Cache.

Local Notation length := List.length (only parsing).

(* ================================================================== *)
(* Generic list counting                                               *)
(* ================================================================== *)

Open Scope nat_scope.

Lemma filter_len_compl {A} (f : A -> bool) (l : list A) :
  length (filter f l) + length (filter (fun x => negb (f x)) l) = length l.
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. destruct (f a); simpl; lia. Qed.

Lemma nodup_same_length {A} (l l' : list A) :
  NoDup l -> NoDup l' -> (forall z, In z l <-> In z l') -> length l = length l'.
Proof.
  intros H1 H2 H. apply Nat.le_antisymm; apply NoDup_incl_length; auto;
    intros z; apply H.
Qed.

Lemma has_count_unique {A} (P : A -> Prop) c c' :
  has_count P c -> has_count P c' -> c = c'.
Proof.
  intros (L & HL & HP & <-) (L' & HL' & HP' & <-). unfold len. f_equal.
  apply nodup_same_length; auto. intros z. rewrite HP, HP'. tauto.
Qed.

Lemma length_flat_map' {A B} (f : A -> list B) (l : list A) :
  length (flat_map f l) = list_sum (map (fun a => length (f a)) l).
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite length_app, IH. reflexivity. Qed.

Lemma list_sum_const {A} (c : nat) (l : list A) :
  list_sum (map (fun _ => c) l) = length l * c.
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma NoDup_flat_map_inj {A B} (f : A -> list B) (l : list A) :
  NoDup l -> (forall a, In a l -> NoDup (f a)) ->
  (forall a a' y, In a l -> In a' l -> In y (f a) -> In y (f a') -> a = a') ->
  NoDup (flat_map f l).
Proof.
  induction l as [|a l IH]; intros Hl Hf Hd; simpl; [constructor|].
  inversion Hl as [|a0 l0 Hna Hl0]; subst. apply NoDup_app.
  - apply Hf; left; auto.
  - apply IH; auto.
    + intros; apply Hf; right; auto.
    + intros a1 a2 y H1 H2 H3 H4. eapply Hd; eauto; right; auto.
  - intros y Hy Hy'. apply in_flat_map in Hy' as (a' & Ha' & Hy').
    assert (a = a') by (eapply (Hd a a' y); eauto; [left; auto | right; auto]).
    subst. contradiction.
Qed.

Lemma forallb_false_ex {A} (f : A -> bool) (l : list A) :
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  induction l as [|a l IH]; simpl; [discriminate|]. intros H.
  destruct (f a) eqn:E; simpl in H.
  - destruct (IH H) as (x & Hx & Hf). exists x; auto.
  - exists a; auto.
Qed.

(* ================================================================== *)
(* Bool lists : all of them, the non-constant ones                     *)
(* ================================================================== *)

Fixpoint allb (g : nat) : list (list bool) :=
  match g with
  | 0 => [[]]
  | S g => map (cons false) (allb g) ++ map (cons true) (allb g)
  end.

Lemma allb_In : forall g bl, In bl (allb g) <-> length bl = g.
Proof.
  induction g as [|g IH]; intros bl; simpl.
  - destruct bl; simpl; split; intros H; try discriminate; auto.
    destruct H as [H|[]]; discriminate.
  - rewrite in_app_iff, !in_map_iff. split.
    + intros [(b & <- & Hb)|(b & <- & Hb)]; simpl; rewrite (proj1 (IH b) Hb); reflexivity.
    + destruct bl as [|[|] bl]; simpl; intros H; try discriminate; injection H as H.
      * right. exists bl. rewrite IH. auto.
      * left. exists bl. rewrite IH. auto.
Qed.

Lemma allb_NoDup : forall g, NoDup (allb g).
Proof.
  induction g as [|g IH]; simpl.
  - constructor; [intros []|constructor].
  - apply NoDup_app.
    + apply NoDup_map_NoDup_ForallPairs; [|exact IH].
      intros a b _ _ H. injection H; auto.
    + apply NoDup_map_NoDup_ForallPairs; [|exact IH].
      intros a b _ _ H. injection H; auto.
    + intros a H1 H2. apply in_map_iff in H1 as (b1 & <- & _).
      apply in_map_iff in H2 as (b2 & H2 & _). discriminate.
Qed.

Lemma allb_length : forall g, length (allb g) = 2 ^ g.
Proof.
  induction g as [|g IH]; simpl; [reflexivity|].
  rewrite length_app, !length_map, IH. lia.
Qed.

Definition nonconst (bl : list bool) : bool :=
  existsb (fun b => b) bl && existsb negb bl.

Definition B (g : nat) : list (list bool) := filter nonconst (allb g).

Lemma existsb_id_false : forall bl, existsb (fun b => b) bl = false ->
  bl = repeat false (length bl).
Proof.
  induction bl as [|b bl IH]; simpl; [reflexivity|]. intros H.
  apply orb_false_iff in H as [-> H]. rewrite (IH H) at 1. reflexivity.
Qed.

Lemma existsb_negb_false : forall bl, existsb negb bl = false ->
  bl = repeat true (length bl).
Proof.
  induction bl as [|b bl IH]; simpl; [reflexivity|]. intros H.
  apply orb_false_iff in H as [H1 H]. destruct b; [|discriminate].
  rewrite (IH H) at 1. reflexivity.
Qed.

Lemma existsb_repeat : forall (f : bool -> bool) b g,
  f b = false -> existsb f (repeat b g) = false.
Proof. intros f b g H. induction g; simpl; [reflexivity|]. rewrite H, IHg. reflexivity. Qed.

Lemma B_length : forall g, 1 <= g -> length (B g) = 2 ^ g - 2.
Proof.
  intros g Hg. unfold B.
  pose proof (filter_len_compl nonconst (allb g)) as H.
  rewrite allb_length in H.
  assert (H2 : length (filter (fun x => negb (nonconst x)) (allb g))
               = length [repeat true g; repeat false g]).
  { apply nodup_same_length.
    - apply NoDup_filter, allb_NoDup.
    - constructor; [|constructor; [intros []|constructor]].
      intros [E|[]]. destruct g; [lia|]. discriminate.
    - intros z. rewrite filter_In, allb_In. simpl. split.
      + intros [Hl Hn]. unfold nonconst in Hn.
        destruct (existsb (fun b => b) z) eqn:E1, (existsb negb z) eqn:E2;
          try discriminate.
        * left. rewrite (existsb_negb_false z E2), Hl. reflexivity.
        * right; left. rewrite (existsb_id_false z E1), Hl. reflexivity.
        * right; left. rewrite (existsb_id_false z E1), Hl. reflexivity.
      + intros [<-|[<-|[]]]; rewrite repeat_length; split; auto; unfold nonconst.
        * rewrite (existsb_repeat negb true g eq_refl). rewrite andb_false_r. reflexivity.
        * rewrite (existsb_repeat (fun b => b) false g eq_refl). reflexivity. }
  simpl in H2. lia.
Qed.

Lemma B_In : forall g bl, In bl (B g) <->
  length bl = g /\
  (exists r, r < g /\ nth r bl false = true) /\
  (exists r, r < g /\ nth r bl false = false).
Proof.
  intros g bl. unfold B. rewrite filter_In, allb_In. unfold nonconst.
  rewrite andb_true_iff, !existsb_exists. split.
  - intros [Hl [(b1 & Hb1 & E1) (b2 & Hb2 & E2)]]. subst g. split; [reflexivity|]. split.
    + apply In_nth with (d := false) in Hb1 as (r & Hr & Hn). exists r. subst. auto.
    + apply In_nth with (d := false) in Hb2 as (r & Hr & Hn). exists r.
      destruct b2; [discriminate|]. subst. auto.
  - intros [Hl [(r1 & Hr1 & E1) (r2 & Hr2 & E2)]]. split; [exact Hl|]. split.
    + exists true. split; [|reflexivity]. rewrite <- E1. apply nth_In. lia.
    + exists false. split; [|reflexivity]. rewrite <- E2. apply nth_In. lia.
Qed.

(* ================================================================== *)
(* Permutations of {1..n}, their offsets and their rotations          *)
(* ================================================================== *)

Section Comb.

Variable n : nat.
Hypothesis Hn : 3 <= n.

(* subtraction and addition modulo n, on arguments below n *)
Definition subm (a b : nat) : nat := if b <=? a then a - b else a + n - b.
Definition addm (a b : nat) : nat := if a + b <? n then a + b else a + b - n.

Ltac cmp := repeat match goal with
  | |- context [?a <=? ?b] =>
      let E := fresh "E" in destruct (a <=? b) eqn:E;
      [apply Nat.leb_le in E | apply Nat.leb_gt in E]
  | |- context [?a <? ?b] =>
      let E := fresh "E" in destruct (a <? b) eqn:E;
      [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]
  | H : context [?a <=? ?b] |- _ =>
      let E := fresh "E" in destruct (a <=? b) eqn:E;
      [apply Nat.leb_le in E | apply Nat.leb_gt in E]
  | H : context [?a <? ?b] |- _ =>
      let E := fresh "E" in destruct (a <? b) eqn:E;
      [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]
  end.
Ltac sm := unfold subm, addm in *; cmp; lia.

Lemma subm_lt : forall a b, a < n -> b <= n -> subm a b < n.
Proof. intros. sm. Qed.

Lemma iota_eq : iota (N.of_nat n) = map N.of_nat (seq 1 n).
Proof. unfold iota. rewrite Nat2N.id. reflexivity. Qed.

Lemma In_iota : forall a, In a (iota (N.of_nat n)) <->
  exists k, 1 <= k <= n /\ a = N.of_nat k.
Proof.
  intros a. rewrite iota_eq, in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia|reflexivity].
  - intros (k & Hk & ->). exists k. split; [reflexivity|]. apply in_seq. lia.
Qed.

Lemma NoDup_iota : NoDup (iota (N.of_nat n)).
Proof.
  rewrite iota_eq. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros a b _ _ H. apply Nat2N.inj. exact H.
Qed.

Lemma length_iota : length (iota (N.of_nat n)) = n.
Proof. rewrite iota_eq, length_map, length_seq. reflexivity. Qed.

Lemma der_iff : forall l, derangement (N.of_nat n) l <->
  is_perm (N.of_nat n) l /\
  forall i, i < length l -> nth i l 0%N <> N.of_nat (S i).
Proof.
  intros l. unfold derangement. split; intros [Hp H]; split; auto; intros i Hi.
  - specialize (H (N.of_nat i)). rewrite Nat2N.id in H.
    replace (N.of_nat (S i)) with (N.of_nat i + 1)%N by lia.
    apply H. unfold len. lia.
  - unfold len in Hi.
    replace (i + 1)%N with (N.of_nat (S (N.to_nat i))) by lia.
    apply H. lia.
Qed.

Section Perm.

Variable D : list N.
Hypothesis HD : is_perm (N.of_nat n) D.

Lemma D_length : length D = n.
Proof. rewrite (Permutation_length HD). apply length_iota. Qed.

Lemma D_NoDup : NoDup D.
Proof. apply (Permutation_NoDup (Permutation_sym HD)), NoDup_iota. Qed.

(* the 0-based value at position j *)
Definition v (j : nat) : nat := N.to_nat (nth j D 0%N) - 1.

Lemma v_spec : forall j, j < n -> nth j D 0%N = N.of_nat (S (v j)) /\ v j < n.
Proof.
  intros j Hj. unfold v.
  assert (H : In (nth j D 0%N) (iota (N.of_nat n))).
  { apply (Permutation_in _ HD), nth_In. rewrite D_length. exact Hj. }
  apply In_iota in H as (k & Hk & ->). rewrite Nat2N.id. split; [f_equal; lia|lia].
Qed.

Lemma v_inj : forall j j', j < n -> j' < n -> v j = v j' -> j = j'.
Proof.
  intros j j' Hj Hj' H.
  apply (proj1 (NoDup_nth D 0%N) D_NoDup); rewrite ?D_length; auto.
  rewrite (proj1 (v_spec j Hj)), (proj1 (v_spec j' Hj')), H. reflexivity.
Qed.

(* the offset of position j : rotation s moves value v j onto position j - s *)
Definition e (j : nat) : nat := subm j (v j).

Lemma e_lt : forall j, j < n -> e j < n.
Proof. intros j Hj. pose proof (v_spec j Hj). unfold e. sm. Qed.

Lemma v_of_e : forall j, j < n -> v j = subm j (e j).
Proof. intros j Hj. pose proof (v_spec j Hj). unfold e. sm. Qed.

Definition good (s : nat) : bool :=
  forallb (fun j => negb (e j =? s)) (seq 0 n).

Lemma good_spec : forall s, good s = true <-> forall j, j < n -> e j <> s.
Proof.
  intros s. unfold good. rewrite forallb_forall. split.
  - intros H j Hj E. specialize (H j). rewrite in_seq in H.
    rewrite E, Nat.eqb_refl in H. simpl in H. discriminate (H ltac:(lia)).
  - intros H j Hj. apply in_seq in Hj. apply negb_true_iff, Nat.eqb_neq, H. lia.
Qed.

Lemma rot_eq : forall s, s < n ->
  rotation D (N.of_nat (S s)) = skipn s D ++ firstn s D.
Proof.
  intros s Hs. unfold rotation.
  replace (N.to_nat (N.of_nat (S s) - 1)) with s by lia. reflexivity.
Qed.

Lemma rot_nth : forall s i, s < n -> i < n ->
  nth i (rotation D (N.of_nat (S s))) 0%N = nth (addm i s) D 0%N.
Proof.
  intros s i Hs Hi. rewrite rot_eq by exact Hs.
  destruct (Nat.lt_ge_cases i (length (skipn s D))) as [H|H].
  - rewrite app_nth1 by exact H. rewrite nth_skipn.
    rewrite length_skipn, D_length in H. f_equal. sm.
  - rewrite app_nth2 by exact H. rewrite nth_firstn.
    rewrite length_skipn, D_length in *. cmp; [|lia]. f_equal. sm.
Qed.

Lemma rot_perm : forall s, s < n -> is_perm (N.of_nat n) (rotation D (N.of_nat (S s))).
Proof.
  intros s Hs. rewrite rot_eq by exact Hs. unfold is_perm.
  eapply Permutation_trans; [apply Permutation_app_comm|].
  rewrite firstn_skipn. exact HD.
Qed.

Lemma rot_length : forall s, s < n -> length (rotation D (N.of_nat (S s))) = n.
Proof.
  intros s Hs. rewrite (Permutation_length (rot_perm s Hs)). apply length_iota.
Qed.

Lemma rot_der : forall s, s < n ->
  (derangement (N.of_nat n) (rotation D (N.of_nat (S s))) <-> good s = true).
Proof.
  intros s Hs. rewrite der_iff, good_spec, rot_length by exact Hs. split.
  - intros [_ H] j Hj E.
    pose proof (v_spec j Hj) as [Hv Hvl].
    apply (H (subm j s)); [apply subm_lt; lia|].
    rewrite rot_nth by (try apply subm_lt; lia).
    replace (addm (subm j s) s) with j by sm.
    rewrite Hv. f_equal. f_equal. unfold e in E. sm.
  - intros H. split; [apply rot_perm; exact Hs|]. intros i Hi Heq.
    rewrite rot_nth in Heq by lia.
    assert (Hj : addm i s < n) by sm.
    pose proof (v_spec (addm i s) Hj) as [Hv Hvl].
    rewrite Hv in Heq. apply Nat2N.inj in Heq. injection Heq as Heq.
    apply (H (addm i s) Hj). unfold e. rewrite Heq. sm.
Qed.

Lemma f_count : has_count (fun q => is_rotation_of D q /\ derangement (N.of_nat n) q)
  (N.of_nat (length (filter good (seq 0 n)))).
Proof.
  exists (map (fun s => rotation D (N.of_nat (S s))) (filter good (seq 0 n))).
  split; [|split].
  - apply NoDup_map_NoDup_ForallPairs; [|apply NoDup_filter, seq_NoDup].
    intros s s' Hs Hs' E.
    apply filter_In in Hs as [Hs _]. apply filter_In in Hs' as [Hs' _].
    apply in_seq in Hs. apply in_seq in Hs'.
    assert (E0 : nth 0 (rotation D (N.of_nat (S s))) 0%N
                 = nth 0 (rotation D (N.of_nat (S s'))) 0%N) by (rewrite E; reflexivity).
    rewrite !rot_nth in E0 by lia.
    replace (addm 0 s) with s in E0 by sm. replace (addm 0 s') with s' in E0 by sm.
    apply (proj1 (NoDup_nth D 0%N) D_NoDup); rewrite ?D_length; auto; lia.
  - intros q. rewrite in_map_iff. split.
    + intros (s & <- & Hs). apply filter_In in Hs as [Hs Hg]. apply in_seq in Hs.
      split.
      * exists (N.of_nat (S s)). split; [|reflexivity]. unfold len. rewrite D_length. lia.
      * apply rot_der; [lia|exact Hg].
    + intros [(k & Hk & ->) Hd]. unfold len in Hk. rewrite D_length in Hk.
      exists (N.to_nat k - 1).
      replace (N.of_nat (S (N.to_nat k - 1))) with k in * by lia.
      split; [reflexivity|]. apply filter_In. split; [apply in_seq; lia|].
      apply (rot_der (N.to_nat k - 1)); [lia|].
      replace (N.of_nat (S (N.to_nat k - 1))) with k by lia. exact Hd.
  - unfold len. rewrite length_map. reflexivity.
Qed.

End Perm.

(* ================================================================== *)
(* The counted derangements, built from (x, d, bl)                    *)
(* ================================================================== *)

Definition gg (d : nat) : nat := Nat.gcd d n.

Lemma gg_pos : forall d, 1 <= gg d.
Proof.
  intros d. unfold gg. destruct (Nat.gcd d n) eqn:E; [|lia].
  apply Nat.gcd_eq_0 in E. lia.
Qed.

Lemma gg_le : forall d, gg d <= n.
Proof. intros d. apply Nat.divide_pos_le; [lia|apply Nat.gcd_divide_r]. Qed.

(* the offset of position j : x, or x + d on the classes modulo gg d that bl marks *)
Definition off (x d : nat) (bl : list bool) (j : nat) : nat :=
  if nth (j mod gg d) bl false then x + d else x.

Definition sg (x d : nat) (bl : list bool) (j : nat) : nat := subm j (off x d bl j).

Definition build (x d : nat) (bl : list bool) : list N :=
  map (fun j => N.of_nat (S (sg x d bl j))) (seq 0 n).

Definition L : list (list N) :=
  flat_map (fun d => flat_map (fun x => map (build x d) (B (gg d)))
                              (seq 1 (n - 1 - d)))
           (seq 1 (n - 2)).

Lemma L_In : forall D, In D L <->
  exists d x bl, 1 <= d /\ 1 <= x /\ x + d <= n - 1 /\ In bl (B (gg d)) /\
                 D = build x d bl.
Proof.
  intros D. unfold L. rewrite in_flat_map. split.
  - intros (d & Hd & H). apply in_flat_map in H as (x & Hx & H).
    apply in_map_iff in H as (bl & <- & Hbl). apply in_seq in Hd. apply in_seq in Hx.
    exists d, x, bl. repeat split; auto; lia.
  - intros (d & x & bl & H1 & H2 & H3 & H4 & ->). exists d.
    split; [apply in_seq; lia|]. apply in_flat_map. exists x.
    split; [apply in_seq; lia|]. apply in_map_iff. exists bl. auto.
Qed.

Lemma build_nth : forall x d bl j, j < n ->
  nth j (build x d bl) 0%N = N.of_nat (S (sg x d bl j)).
Proof.
  intros x d bl j Hj. unfold build.
  rewrite nth_indep with (d' := N.of_nat (S (sg x d bl 0)))
    by (rewrite length_map, length_seq; exact Hj).
  change (N.of_nat (S (sg x d bl 0))) with ((fun j => N.of_nat (S (sg x d bl j))) 0).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma build_length : forall x d bl, length (build x d bl) = n.
Proof. intros. unfold build. rewrite length_map, length_seq. reflexivity. Qed.

Section Build.

Variables (x d : nat) (bl : list bool).
Hypotheses (Hd : 1 <= d) (Hx : 1 <= x) (Hxd : x + d <= n - 1).

Lemma off_cases : forall j, off x d bl j = x \/ off x d bl j = x + d.
Proof. intros j. unfold off. destruct (nth _ bl false); auto. Qed.

Lemma sg_lt : forall j, j < n -> sg x d bl j < n.
Proof. intros j Hj. unfold sg. destruct (off_cases j) as [-> | ->]; sm. Qed.

Lemma subm_sg : forall j, j < n -> subm j (sg x d bl j) = off x d bl j.
Proof. intros j Hj. unfold sg. destruct (off_cases j) as [-> | ->]; sm. Qed.

Lemma mod_shift : forall j j', j < n -> j' < n ->
  (j' = j + d \/ j' + n = j + d) -> j' mod gg d = j mod gg d.
Proof.
  intros j j' Hj Hj' H.
  assert (Hkd : Nat.divide (gg d) d) by apply Nat.gcd_divide_l.
  assert (Hkn : Nat.divide (gg d) n) by apply Nat.gcd_divide_r.
  set (g := gg d) in *. destruct Hkd as [kd Ekd]. destruct Hkn as [kn Ekn].
  destruct H as [H|H].
  - subst j'. rewrite Ekd, Nat.Div0.mod_add. reflexivity.
  - rewrite <- (Nat.Div0.mod_add j' kn g), <- Ekn, H, Ekd, Nat.Div0.mod_add. reflexivity.
Qed.

Lemma sg_inj : forall j j', j < n -> j' < n -> sg x d bl j = sg x d bl j' -> j = j'.
Proof.
  intros j j' Hj Hj' H. unfold sg, off in H.
  destruct (nth (j mod gg d) bl false) eqn:E1, (nth (j' mod gg d) bl false) eqn:E2;
    try sm.
  - assert (Hm : j mod gg d = j' mod gg d) by (apply mod_shift; auto; sm).
    rewrite Hm, E2 in E1. discriminate.
  - assert (Hm : j' mod gg d = j mod gg d) by (apply mod_shift; auto; sm).
    rewrite Hm, E1 in E2. discriminate.
Qed.

Lemma build_perm : is_perm (N.of_nat n) (build x d bl).
Proof.
  unfold is_perm. apply NoDup_Permutation_bis.
  - unfold build. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros j j' Hj Hj' H. apply in_seq in Hj. apply in_seq in Hj'.
    apply Nat2N.inj in H. injection H as H. apply sg_inj; auto; lia.
  - rewrite length_iota, build_length. lia.
  - intros a Ha. unfold build in Ha. apply in_map_iff in Ha as (j & <- & Hj).
    apply in_seq in Hj. apply In_iota. exists (S (sg x d bl j)).
    pose proof (sg_lt j ltac:(lia)). split; [lia|reflexivity].
Qed.

Lemma build_v : forall j, j < n -> v (build x d bl) j = sg x d bl j.
Proof. intros j Hj. unfold v. rewrite build_nth by exact Hj. lia. Qed.

Lemma build_e : forall j, j < n -> e (build x d bl) j = off x d bl j.
Proof. intros j Hj. unfold e. rewrite build_v by exact Hj. apply subm_sg. exact Hj. Qed.

Hypothesis Hbl : In bl (B (gg d)).

Lemma bl_true : exists j, j < n /\ off x d bl j = x + d.
Proof.
  apply B_In in Hbl as (_ & (r & Hr & E) & _). pose proof (gg_le d).
  exists r. split; [lia|]. unfold off. rewrite Nat.mod_small, E by lia. reflexivity.
Qed.

Lemma bl_false : exists j, j < n /\ off x d bl j = x.
Proof.
  apply B_In in Hbl as (_ & _ & (r & Hr & E)). pose proof (gg_le d).
  exists r. split; [lia|]. unfold off. rewrite Nat.mod_small, E by lia. reflexivity.
Qed.

Lemma build_counted : counted (N.of_nat n) (build x d bl).
Proof.
  split.
  - apply der_iff. split; [apply build_perm|]. rewrite build_length.
    intros i Hi E. rewrite build_nth in E by exact Hi.
    apply Nat2N.inj in E. injection E as E. unfold sg in E.
    destruct (off_cases i) as [H|H]; rewrite H in E; sm.
  - pose proof (f_count _ build_perm) as Hc. unfold f_is.
    replace (N.of_nat n - 2)%N with (N.of_nat (length (filter (good (build x d bl)) (seq 0 n)))).
    { exact Hc. }
    pose proof (filter_len_compl (good (build x d bl)) (seq 0 n)) as H.
    rewrite length_seq in H.
    assert (H2 : length (filter (fun s => negb (good (build x d bl) s)) (seq 0 n))
                 = length [x; x + d]).
    { apply nodup_same_length.
      - apply NoDup_filter, seq_NoDup.
      - constructor; [intros [E|[]]; lia|constructor; [intros []|constructor]].
      - intros s. rewrite filter_In, in_seq, negb_true_iff. simpl. split.
        + intros [Hs Hg].
          destruct (Nat.eq_dec s x); [left; auto|]. destruct (Nat.eq_dec s (x + d)); [right; left; auto|].
          exfalso. assert (Hg' : good (build x d bl) s = true); [|congruence].
          apply (proj2 (good_spec _ s)). intros j Hj.
          rewrite build_e by exact Hj. destruct (off_cases j) as [-> | ->]; auto.
        + intros [<-|[<-|[]]]; (split; [lia|]);
            apply not_true_iff_false; rewrite good_spec;
            intros Hg.
          * destruct bl_false as (j & Hj & E). apply (Hg j Hj). rewrite build_e; auto.
          * destruct bl_true as (j & Hj & E). apply (Hg j Hj). rewrite build_e; auto. }
    simpl in H2. lia.
Qed.

End Build.

Lemma build_inj : forall x d bl x' d' bl',
  1 <= d -> 1 <= x -> x + d <= n - 1 -> In bl (B (gg d)) ->
  1 <= d' -> 1 <= x' -> x' + d' <= n - 1 -> In bl' (B (gg d')) ->
  build x d bl = build x' d' bl' -> x = x' /\ d = d' /\ bl = bl'.
Proof.
  intros x d bl x' d' bl' Hd Hx Hxd Hbl Hd' Hx' Hxd' Hbl' E.
  assert (Ho : forall j, j < n -> off x d bl j = off x' d' bl' j).
  { intros j Hj. rewrite <- (subm_sg x d bl Hd Hx Hxd j Hj),
                         <- (subm_sg x' d' bl' Hd' Hx' Hxd' j Hj).
    f_equal. pose proof (build_nth x d bl j Hj) as E1.
    pose proof (build_nth x' d' bl' j Hj) as E2. rewrite E in E1. rewrite E1 in E2.
    apply Nat2N.inj in E2. injection E2 as E2. exact E2. }
  destruct (bl_true x d bl Hd Hx Hxd Hbl) as (j1 & Hj1 & E1).
  destruct (bl_false x d bl Hd Hx Hxd Hbl) as (j0 & Hj0 & E0).
  destruct (bl_true x' d' bl' Hd' Hx' Hxd' Hbl') as (j1' & Hj1' & E1').
  destruct (bl_false x' d' bl' Hd' Hx' Hxd' Hbl') as (j0' & Hj0' & E0').
  pose proof (Ho j1 Hj1). pose proof (Ho j0 Hj0).
  pose proof (Ho j1' Hj1'). pose proof (Ho j0' Hj0').
  destruct (off_cases x d bl j1'), (off_cases x d bl j0'),
           (off_cases x' d' bl' j1), (off_cases x' d' bl' j0); try lia.
  all: assert (x = x' /\ d = d') as [<- <-] by lia; split; [reflexivity|split; [reflexivity|]].
  all: apply B_In in Hbl as (Hl & _ & _); apply B_In in Hbl' as (Hl' & _ & _).
  all: apply nth_ext with (d := false) (d' := false); [congruence|].
  all: intros r Hr; rewrite Hl in Hr; pose proof (gg_le d);
       pose proof (Ho r ltac:(lia)) as Hr'; unfold off in Hr';
       rewrite Nat.mod_small in Hr' by lia;
       destruct (nth r bl false), (nth r bl' false); auto; lia.
Qed.

Lemma L_NoDup : NoDup L.
Proof.
  unfold L. apply NoDup_flat_map_inj; [apply seq_NoDup| |].
  - intros d Hd. apply in_seq in Hd. apply NoDup_flat_map_inj; [apply seq_NoDup| |].
    + intros x Hx. apply in_seq in Hx.
      apply NoDup_map_NoDup_ForallPairs; [|apply NoDup_filter, allb_NoDup].
      intros bl bl' H1 H2 E. apply (build_inj x d bl x d bl'); auto; lia.
    + intros x x' D Hx Hx' H1 H2. apply in_seq in Hx. apply in_seq in Hx'.
      apply in_map_iff in H1 as (bl & <- & H1). apply in_map_iff in H2 as (bl' & E & H2).
      symmetry in E. apply (build_inj x d bl x' d bl'); auto; lia.
  - intros d d' D Hd Hd' H1 H2. apply in_seq in Hd. apply in_seq in Hd'.
    apply in_flat_map in H1 as (x & Hx & H1). apply in_flat_map in H2 as (x' & Hx' & H2).
    apply in_seq in Hx. apply in_seq in Hx'.
    apply in_map_iff in H1 as (bl & <- & H1). apply in_map_iff in H2 as (bl' & E & H2).
    symmetry in E. apply (build_inj x d bl x' d' bl'); auto; lia.
Qed.

Definition term (d : nat) : nat := (n - 1 - d) * (2 ^ gg d - 2).

Lemma L_length : length L = list_sum (map term (seq 1 (n - 2))).
Proof.
  unfold L. rewrite length_flat_map'. f_equal. apply map_ext. intros d.
  rewrite length_flat_map'.
  erewrite map_ext; [|intros x; rewrite length_map, B_length by apply gg_pos; reflexivity].
  rewrite list_sum_const, length_seq. reflexivity.
Qed.

(* ================================================================== *)
(* Every counted derangement is built                                  *)
(* ================================================================== *)

Lemma subm_mod : forall a b, a < n -> 1 <= b <= n -> subm a b = (a + (n - b)) mod n.
Proof.
  intros a b Ha Hb. unfold subm. cmp.
  - replace (a + (n - b)) with ((a - b) + 1 * n) by lia.
    rewrite Nat.Div0.mod_add, Nat.mod_small by lia. reflexivity.
  - rewrite Nat.mod_small by lia. lia.
Qed.

Section Complete.

Variable D : list N.
Hypothesis HD : is_perm (N.of_nat n) D.
Variables x y : nat.
Hypotheses (Hxy : x < y) (Hx1 : 1 <= x) (Hyn : y < n).
Hypothesis Hcases : forall j, j < n -> e D j = x \/ e D j = y.
Hypothesis Hex : exists j, j < n /\ e D j = x.
Hypothesis Hey : exists j, j < n /\ e D j = y.

Definition bb (j : nat) : bool := e D j =? y.

Lemma shift_closed : forall j, j < n -> bb j = true -> bb (subm j (y - x)) = true.
Proof.
  intros j Hj H. unfold bb in *. apply Nat.eqb_eq in H. apply Nat.eqb_eq.
  assert (Hj' : subm j (y - x) < n) by sm.
  destruct (Hcases _ Hj') as [E|E]; [|exact E]. exfalso.
  pose proof (v_of_e D HD j Hj) as V. pose proof (v_of_e D HD _ Hj') as V'.
  rewrite H in V. rewrite E in V'.
  assert (Hv : v D (subm j (y - x)) = v D j) by (rewrite V, V'; sm).
  apply (v_inj D HD) in Hv; auto. sm.
Qed.

Fixpoint iterS (t j : nat) : nat :=
  match t with 0 => j | S t => subm (iterS t j) (y - x) end.

Lemma iter_lt : forall t j, j < n -> iterS t j < n.
Proof. induction t as [|t IH]; intros j Hj; simpl; [exact Hj|]. apply subm_lt; [apply IH; exact Hj|lia]. Qed.

Lemma iter_closed : forall t j, j < n -> bb j = true -> bb (iterS t j) = true.
Proof.
  induction t as [|t IH]; intros j Hj H; simpl; [exact H|].
  apply shift_closed; [apply iter_lt; exact Hj|apply IH; auto].
Qed.

Lemma iter_mod : forall t j, j < n -> iterS t j = (j + t * (n - (y - x))) mod n.
Proof.
  induction t as [|t IH]; intros j Hj; simpl.
  - rewrite Nat.add_0_r, Nat.mod_small by exact Hj. reflexivity.
  - rewrite IH by exact Hj. rewrite subm_mod by (try apply Nat.mod_upper_bound; lia).
    rewrite Nat.Div0.add_mod_idemp_l. f_equal. lia.
Qed.

Lemma class_inv : forall j j', j < n -> j' < n ->
  j mod gg (y - x) = j' mod gg (y - x) -> bb j = true -> bb j' = true.
Proof.
  intros j j' Hj Hj' Hm H.
  assert (Hg : Nat.gcd (n - (y - x)) n = gg (y - x)).
  { unfold gg. apply Nat.gcd_unique.
    - apply Nat.divide_sub_r; [apply Nat.gcd_divide_r|apply Nat.gcd_divide_l].
    - apply Nat.gcd_divide_r.
    - intros q Hq1 Hq2. apply Nat.gcd_greatest; [|exact Hq2].
      replace (y - x) with (n - (n - (y - x))) by lia.
      apply Nat.divide_sub_r; auto. }
  destruct (Nat.gcd_bezout_pos (n - (y - x)) n ltac:(lia)) as (u & w & Hu).
  rewrite Hg in Hu.
  pose proof (gg_pos (y - x)) as Hg1.
  set (g := gg (y - x)) in *.
  assert (Hdiv : Nat.divide g (n + j' - j)).
  { pose proof (Nat.div_mod_eq j g) as Dj. pose proof (Nat.div_mod_eq j' g) as Dj'.
    replace (n + j' - j) with ((n + g * (j' / g)) - g * (j / g)) by lia.
    apply Nat.divide_sub_r; [apply Nat.divide_add_r; [apply Nat.gcd_divide_r|]|];
      apply Nat.divide_factor_l. }
  destruct Hdiv as [c Hc].
  assert (Hit : iterS (c * u) j = j').
  { rewrite iter_mod by exact Hj.
    assert (Eq : j + c * u * (n - (y - x)) = j' + (c * w + 1) * n).
    { rewrite <- Nat.mul_assoc, Hu, Nat.mul_add_distr_l, <- Hc. nia. }
    rewrite Eq, Nat.Div0.mod_add, Nat.mod_small by exact Hj'. reflexivity. }
  rewrite <- Hit. apply iter_closed; auto.
Qed.

Lemma nth_bl : forall j, j < n ->
  nth (j mod gg (y - x)) (map bb (seq 0 (gg (y - x)))) false = bb j.
Proof.
  intros j Hj. pose proof (gg_pos (y - x)). pose proof (gg_le (y - x)).
  assert (Hr : j mod gg (y - x) < gg (y - x)) by (apply Nat.mod_upper_bound; lia).
  rewrite nth_indep with (d' := bb 0) by (rewrite length_map, length_seq; exact Hr).
  rewrite map_nth, seq_nth by exact Hr. simpl.
  assert (Hmm : j mod gg (y - x) = (j mod gg (y - x)) mod gg (y - x))
    by (rewrite Nat.Div0.mod_mod; reflexivity).
  destruct (bb j) eqn:E1, (bb (j mod gg (y - x))) eqn:E2; auto.
  - assert (bb (j mod gg (y - x)) = true); [|congruence].
    apply (class_inv j); auto; lia.
  - assert (bb j = true); [|congruence].
    apply (class_inv (j mod gg (y - x))); auto; lia.
Qed.

Lemma complete : In D L.
Proof.
  pose proof (gg_pos (y - x)). pose proof (gg_le (y - x)).
  apply L_In. exists (y - x), x, (map bb (seq 0 (gg (y - x)))).
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  - apply B_In. split; [rewrite length_map, length_seq; reflexivity|]. split.
    + destruct Hey as (j & Hj & E). exists (j mod gg (y - x)).
      split; [apply Nat.mod_upper_bound; lia|]. rewrite nth_bl by exact Hj.
      unfold bb. rewrite E. apply Nat.eqb_refl.
    + destruct Hex as (j & Hj & E). exists (j mod gg (y - x)).
      split; [apply Nat.mod_upper_bound; lia|]. rewrite nth_bl by exact Hj.
      unfold bb. rewrite E. apply Nat.eqb_neq. lia.
  - apply nth_ext with (d := 0%N) (d' := 0%N).
    + rewrite build_length. apply (D_length D HD).
    + intros j Hj. rewrite (D_length D HD) in Hj.
      rewrite build_nth by exact Hj. rewrite (proj1 (v_spec D HD j Hj)).
      f_equal. f_equal. unfold sg, off. rewrite nth_bl by exact Hj.
      rewrite (v_of_e D HD j Hj). unfold bb.
      destruct (Hcases j Hj) as [E|E]; rewrite E.
      * destruct (Nat.eqb_spec x y); [lia|reflexivity].
      * rewrite Nat.eqb_refl. f_equal. lia.
Qed.

End Complete.

Theorem count_correct :
  has_count (counted (N.of_nat n)) (N.of_nat (list_sum (map term (seq 1 (n - 2))))).
Proof.
  exists L. split; [apply L_NoDup|split; [|unfold len; rewrite L_length; reflexivity]].
  intros D. split.
  - intros H. apply L_In in H as (d & x & bl & H1 & H2 & H3 & H4 & ->).
    apply build_counted; auto.
  - intros [Hder Hf]. unfold f_is in Hf.
    pose proof (proj1 (der_iff D) Hder) as [HD Hfix].
    rewrite (D_length D HD) in Hfix.
    assert (He0 : forall j, j < n -> e D j <> 0).
    { intros j Hj E. pose proof (v_spec D HD j Hj) as [V Vl].
      apply (Hfix j Hj). rewrite V. f_equal. f_equal. unfold e in E. sm. }
    pose proof (has_count_unique _ _ _ Hf (f_count D HD)) as Hc.
    pose proof (filter_len_compl (good D) (seq 0 n)) as Hlen.
    rewrite length_seq in Hlen.
    assert (HB : forall s, In s (filter (fun s => negb (good D s)) (seq 0 n)) <->
                           s < n /\ exists j, j < n /\ e D j = s).
    { intros s. rewrite filter_In, in_seq, negb_true_iff. split.
      - intros [Hs Hg]. split; [lia|]. unfold good in Hg.
        apply forallb_false_ex in Hg as (j & Hj & Hj2). apply in_seq in Hj.
        exists j. split; [lia|]. apply negb_false_iff, Nat.eqb_eq in Hj2. exact Hj2.
      - intros [Hs (j & Hj & E)]. split; [lia|]. apply not_true_iff_false.
        rewrite good_spec. intros H. exact (H j Hj E). }
    assert (HBn : NoDup (filter (fun s => negb (good D s)) (seq 0 n)))
      by (apply NoDup_filter, seq_NoDup).
    remember (filter (fun s => negb (good D s)) (seq 0 n)) as Bad eqn:EBad.
    destruct Bad as [|s1 [|s2 [|s3 l]]]; simpl in Hlen; try lia.
    apply NoDup_cons_iff in HBn as [Hn12 _]. simpl in Hn12.
    assert (Hcs : forall j, j < n -> e D j = s1 \/ e D j = s2).
    { intros j Hj. assert (Hi : In (e D j) [s1; s2])
        by (apply HB; split; [apply (e_lt D HD j Hj)|exists j; auto]).
      simpl in Hi. intuition. }
    destruct (proj1 (HB s1) (or_introl eq_refl)) as [Hs1 (j1 & Hj1 & E1)].
    destruct (proj1 (HB s2) (or_intror (or_introl eq_refl))) as [Hs2 (j2 & Hj2 & E2)].
    pose proof (He0 j1 Hj1). pose proof (He0 j2 Hj2).
    destruct (Nat.lt_ge_cases s1 s2).
    + apply (complete D HD s1 s2); try lia; eauto.
    + apply (complete D HD s2 s1); try lia; eauto.
      intros j Hj. destruct (Hcs j Hj); auto.
Qed.

End Comb.

Close Scope nat_scope.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Lemma nz_pos : forall b : int, (b =? 0) = false -> (0 < (φ b))%Z.
Proof.
  intros b H. rewrite <- not_true_iff_false, Uint63.eqb_spec in H.
  pose proof (to_Z_bounded b). assert ((φ b) <> 0%Z); [|lia].
  intros E. apply H. apply to_Z_inj. rewrite E. reflexivity.
Qed.

(* Euclid's gcd, on the erased measure φ b *)
Lemma gcd_dec : forall a b : int, (b =? 0) = false -> Zwf 0 (φ (a mod b)) (φ b).
Proof.
  intros a b H. pose proof (nz_pos b H). pose proof (to_Z_bounded a).
  unfold Zwf. rewrite mod_spec. pose proof (Z.mod_pos_bound (φ a) (φ b)). lia.
Qed.

Fixpoint gcd_loop (a b : int) (H : Acc (Zwf 0) (φ b)) {struct H} : int :=
  match bdec (b =? 0) with
  | left _ => a
  | right Hb => gcd_loop b (a mod b) (Acc_inv H (gcd_dec a b Hb))
  end.

Lemma gcd_loop_eq : forall a b H, gcd_loop a b H =
  match bdec (b =? 0) with
  | left _ => a
  | right Hb => gcd_loop b (a mod b) (Acc_inv H (gcd_dec a b Hb))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition gcd63 (a b : int) : int := gcd_loop a b (Zwf_well_founded 0 (φ b)).

(* acc * base ^ e modulo p, by squaring, on the erased measure φ e *)
Lemma half_dec : forall e : int, (e =? 0) = false -> Zwf 0 (φ (e / 2)) (φ e).
Proof.
  intros e H. pose proof (nz_pos e H). unfold Zwf. rewrite div_spec.
  change (φ 2) with 2%Z. split; [lia|apply Z.div_lt; lia].
Qed.

Fixpoint pow_loop (p base e acc : int) (H : Acc (Zwf 0) (φ e)) {struct H} : int :=
  match bdec (e =? 0) with
  | left _ => acc
  | right He =>
      pow_loop p ((base * base) mod p) (e / 2)
        (if e mod 2 =? 0 then acc else (acc * base) mod p)
        (Acc_inv H (half_dec e He))
  end.

Lemma pow_loop_eq : forall p base e acc H, pow_loop p base e acc H =
  match bdec (e =? 0) with
  | left _ => acc
  | right He =>
      pow_loop p ((base * base) mod p) (e / 2)
        (if e mod 2 =? 0 then acc else (acc * base) mod p)
        (Acc_inv H (half_dec e He))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition pow2mod (p g : int) : int := pow_loop p 2 g 1 (Zwf_well_founded 0 (φ g)).

(* the main loop : d = 1 .. n - 2, m = n - 1 *)
Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Fixpoint sum_loop (n m p d acc : int) (H : Acc (Zwf 0) (gap m d)) {struct H} : int :=
  match bdec (d <? m) with
  | left Hd =>
      sum_loop n m p (d + 1)
        ((acc + ((m - d) * ((pow2mod p (gcd63 d n) + p - 2) mod p)) mod p) mod p)
        (Acc_inv H (dec_step m d Hd))
  | right _ => acc
  end.

Lemma sum_loop_eq : forall n m p d acc H, sum_loop n m p d acc H =
  match bdec (d <? m) with
  | left Hd =>
      sum_loop n m p (d + 1)
        ((acc + ((m - d) * ((pow2mod p (gcd63 d n) + p - 2) mod p)) mod p) mod p)
        (Acc_inv H (dec_step m d Hd))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition derangement_rotations_impl (n p : uint) : uint :=
  sum_loop n (n - 1) p 1 0 (Zwf_well_founded 0 (gap (n - 1) 1)).

(* ================================================================== *)
(* Correctness of the program                                          *)
(* ================================================================== *)

Lemma gcd_loop_spec : forall z (a b : int) H, (φ b) = z ->
  (φ (gcd_loop a b H)) = Z.of_nat (Nat.gcd (Z.to_nat (φ a)) (Z.to_nat (φ b))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a b H Hz. rewrite gcd_loop_eq.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  destruct (bdec (b =? 0)) as [Hb|Hb].
  - apply Uint63.eqb_spec in Hb. subst b. change (φ 0) with 0%Z. simpl.
    rewrite Nat.gcd_0_r. lia.
  - pose proof (nz_pos b Hb).
    rewrite (IH (φ (a mod b))) with (H := Acc_inv H (gcd_dec a b Hb));
      [| rewrite <- Hz; apply gcd_dec; exact Hb | reflexivity].
    rewrite mod_spec, Z2Nat.inj_mod by lia.
    rewrite Nat.gcd_comm, Nat.Lcm0.gcd_mod, Nat.gcd_comm. reflexivity.
Qed.

Lemma gcd63_spec : forall a b : int,
  (φ (gcd63 a b)) = Z.of_nat (Nat.gcd (Z.to_nat (φ a)) (Z.to_nat (φ b))).
Proof. intros. apply (gcd_loop_spec (φ b)). reflexivity. Qed.

Lemma pow_step : forall P A Bs E : Z, (0 < P)%Z -> (0 <= E)%Z ->
  (((if (E mod 2 =? 0)%Z then A else (A * Bs) mod P) * ((Bs * Bs) mod P) ^ (E / 2)) mod P
  = (A * Bs ^ E) mod P)%Z.
Proof.
  intros P A Bs E HP HE.
  rewrite <- Z.mul_mod_idemp_r, <- Zpow_facts.Zpower_mod, Z.mul_mod_idemp_r by lia.
  assert (HE2 : (E = 2 * (E / 2) + E mod 2)%Z) by (apply Z.div_mod; lia).
  assert (Hpow : (Bs ^ E = (Bs * Bs) ^ (E / 2) * Bs ^ (E mod 2))%Z).
  { pose proof (Z.mod_pos_bound E 2 ltac:(lia)).
    assert (0 <= E / 2)%Z by (apply Z.div_pos; lia).
    rewrite HE2 at 1. rewrite Z.pow_add_r, Z.pow_mul_r, Z.pow_2_r by lia. reflexivity. }
  rewrite Hpow.
  pose proof (Z.mod_pos_bound E 2 ltac:(lia)).
  destruct (Z.eqb_spec (E mod 2) 0) as [E0|E0].
  - rewrite E0. f_equal. simpl. ring.
  - assert (E1 : (E mod 2 = 1)%Z) by lia. rewrite E1, Z.mul_mod_idemp_l by lia.
    f_equal. rewrite Z.pow_1_r. ring.
Qed.

Lemma pow_loop_spec : forall (p : int), (2 <= (φ p) < 2 ^ 31)%Z ->
  forall z (base e acc : int) H, (φ e) = z ->
  (0 <= (φ base) < (φ p))%Z -> (0 <= (φ acc) < (φ p))%Z ->
  (φ (pow_loop p base e acc H)) = (((φ acc) * (φ base) ^ (φ e)) mod (φ p))%Z.
Proof.
  intros p Hp z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros base e acc H Hz Hb Ha. rewrite pow_loop_eq.
  pose proof (to_Z_bounded e).
  destruct (bdec (e =? 0)) as [He|He].
  - apply Uint63.eqb_spec in He. subst e. change (φ 0) with 0%Z.
    rewrite Z.pow_0_r, Z.mul_1_r, Z.mod_small by lia. reflexivity.
  - pose proof (nz_pos e He).
    assert (Hbb : (φ ((base * base) mod p)) = (((φ base) * (φ base)) mod (φ p))%Z).
    { rewrite mod_spec, mul_spec, (Z.mod_small _ wB); [reflexivity|].
      change wB with (2 ^ 63)%Z. nia. }
    assert (Hacc : (φ (if e mod 2 =? 0 then acc else (acc * base) mod p))
                   = (if ((φ e) mod 2 =? 0)%Z then (φ acc) else ((φ acc) * (φ base)) mod (φ p))%Z).
    { assert (Hm : (φ (e mod 2)) = ((φ e) mod 2)%Z) by (rewrite mod_spec; reflexivity).
      destruct (e mod 2 =? 0) eqn:E1; destruct ((φ e) mod 2 =? 0)%Z eqn:E2.
      - reflexivity.
      - apply Uint63.eqb_spec in E1. rewrite E1 in Hm. change (φ 0) with 0%Z in Hm.
        apply Z.eqb_neq in E2. lia.
      - apply Z.eqb_eq in E2. rewrite <- not_true_iff_false, Uint63.eqb_spec in E1.
        exfalso. apply E1. apply to_Z_inj. rewrite Hm, E2. reflexivity.
      - rewrite mod_spec, mul_spec, (Z.mod_small _ wB); [reflexivity|].
        change wB with (2 ^ 63)%Z. nia. }
    rewrite (IH (φ (e / 2))) with (H := Acc_inv H (half_dec e He));
      [| rewrite <- Hz; apply half_dec; exact He | reflexivity | | ].
    + rewrite Hacc, Hbb, div_spec. change (φ 2) with 2%Z.
      apply pow_step; lia.
    + rewrite Hbb. pose proof (Z.mod_pos_bound ((φ base) * (φ base)) (φ p)). lia.
    + rewrite Hacc. destruct ((φ e) mod 2 =? 0)%Z; [lia|].
      pose proof (Z.mod_pos_bound ((φ acc) * (φ base)) (φ p)). lia.
Qed.

Lemma pow2mod_spec : forall p g : int, (2 < (φ p) < 2 ^ 31)%Z ->
  (φ (pow2mod p g)) = ((2 ^ (φ g)) mod (φ p))%Z.
Proof.
  intros p g Hp. unfold pow2mod.
  rewrite (pow_loop_spec p ltac:(lia) (φ g)); [| reflexivity | change (φ 2) with 2%Z; lia
                                                | change (φ 1) with 1%Z; lia].
  change (φ 1) with 1%Z. change (φ 2) with 2%Z. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma step_arith : forall P A S M X : Z, (0 < P)%Z -> A = (S mod P)%Z ->
  ((A + (M * ((X mod P + P - 2) mod P)) mod P) mod P = (S + M * (X - 2)) mod P)%Z.
Proof.
  intros P A S M X HP ->.
  rewrite Z.add_mod_idemp_l, Z.mul_mod_idemp_r, Z.add_mod_idemp_r by lia.
  rewrite (Zmod_eq_full X P) by lia.
  replace (S + M * (X - X / P * P + P - 2))%Z
    with ((S + M * (X - 2)) + (M * (1 - X / P)) * P)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Lemma sub_small : forall a b : int, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof.
  intros a b H. rewrite sub_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia.
Qed.

Lemma add_small : forall a b : int, ((φ a) + (φ b) < 2 ^ 62)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof.
  intros a b H. rewrite add_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  change wB with 9223372036854775808%Z in *. lia.
Qed.

Lemma mul_small : forall a b : int, ((φ a) * (φ b) < 2 ^ 62)%Z -> (φ (a * b)) = ((φ a) * (φ b))%Z.
Proof.
  intros a b H. rewrite mul_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  change wB with 9223372036854775808%Z in *. nia.
Qed.

(* an equation lia does not look into *)
Definition hidden_eq (a b : Z) : Prop := a = b.
Lemma hide_eq : forall a b : Z, a = b -> hidden_eq a b.
Proof. intros a b H. exact H. Qed.

Lemma sum_loop_spec : forall (nn : nat) (n m p : int),
  (φ n) = Z.of_nat nn -> (3 <= nn)%nat -> ((φ n) <= 1000000)%Z -> (φ m) = ((φ n) - 1)%Z ->
  (100000000 <= (φ p) <= 1000000007)%Z ->
  forall z (d acc : int) H, gap m d = z -> (1 <= (φ d) <= (φ m))%Z ->
  (φ acc) = (Z.of_nat (list_sum (map (term nn) (seq 1 (Z.to_nat (φ d) - 1)))) mod (φ p))%Z ->
  (φ (sum_loop n m p d acc H))
  = (Z.of_nat (list_sum (map (term nn) (seq 1 (nn - 2)))) mod (φ p))%Z.
Proof.
  intros nn n m p Hn Hnn Hn6 Hm Hp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d acc H Hz Hd Hacc. rewrite sum_loop_eq.
  assert (Hacc_b : (0 <= (φ acc) < (φ p))%Z) by (rewrite Hacc; apply Z.mod_pos_bound; lia).
  apply hide_eq in Hacc.
  destruct (bdec (d <? m)) as [Hdm|Hdm].
  - pose proof Hdm as Hlt. rewrite ltb_spec in Hlt.
    set (k := Z.to_nat (φ d)) in *.
    assert (Hk : (φ d) = Z.of_nat k) by (unfold k; lia).
    assert (Hd1 : (φ (d + 1)) = ((φ d) + 1)%Z).
    { rewrite add_spec. change (φ 1) with 1%Z. change wB with 9223372036854775808%Z.
      pose proof (to_Z_bounded m) as Bm. apply Z.mod_small. clear - Hlt Bm Hd. lia. }
    assert (Hg : (φ (gcd63 d n)) = Z.of_nat (Nat.gcd k nn)).
    { rewrite gcd63_spec. fold k. rewrite Hn, Nat2Z.id. reflexivity. }
    set (G := Nat.gcd k nn) in *.
    assert (HG1 : (1 <= G)%nat).
    { unfold G. destruct (Nat.gcd k nn) eqn:E; [|lia]. apply Nat.gcd_eq_0 in E. lia. }
    remember (2 ^ Z.of_nat G)%Z as X eqn:EX.
    assert (Hpw : (φ (pow2mod p (gcd63 d n))) = (X mod (φ p))%Z)
      by (rewrite pow2mod_spec, Hg, EX by (clear - Hp; lia); reflexivity).
    pose proof (Z.mod_pos_bound X (φ p) ltac:(clear - Hp; lia)) as HXb.
    remember (X mod (φ p))%Z as Xm eqn:EXm.
    assert (Ht : (φ ((pow2mod p (gcd63 d n) + p - 2) mod p))
                 = ((Xm + (φ p) - 2) mod (φ p))%Z).
    { assert (E1 : (φ (pow2mod p (gcd63 d n) + p)) = (Xm + (φ p))%Z)
        by (rewrite add_small; [rewrite Hpw; reflexivity|rewrite Hpw; clear - Hp HXb; lia]).
      assert (E2 : (φ (pow2mod p (gcd63 d n) + p - 2)) = (Xm + (φ p) - 2)%Z)
        by (rewrite sub_small; [rewrite E1; reflexivity
                               |rewrite E1; change (φ 2) with 2%Z; clear - Hp HXb; lia]).
      rewrite mod_spec, E2. reflexivity. }
    remember ((Xm + (φ p) - 2) mod (φ p))%Z as T eqn:ET.
    assert (HT : (0 <= T < (φ p))%Z)
      by (rewrite ET; apply Z.mod_pos_bound; clear - Hp; lia).
    assert (Hmd : (φ (m - d)) = ((φ m) - (φ d))%Z) by (apply sub_small; clear - Hlt; lia).
    assert (Hprod : (φ (((m - d) * ((pow2mod p (gcd63 d n) + p - 2) mod p)) mod p))
                    = ((((φ m) - (φ d)) * T) mod (φ p))%Z).
    { rewrite mod_spec, mul_small; [rewrite Hmd, Ht; reflexivity|].
      rewrite ?Hmd, ?Ht. clear - Hd Hlt Hm Hn6 HT Hp. nia. }
    pose proof (Z.mod_pos_bound (((φ m) - (φ d)) * T) (φ p) ltac:(clear - Hp; lia)) as HPb.
    remember ((((φ m) - (φ d)) * T) mod (φ p))%Z as P eqn:EP.
    assert (Hnew : (φ ((acc + ((m - d) * ((pow2mod p (gcd63 d n) + p - 2) mod p)) mod p) mod p))
                   = (((φ acc) + P) mod (φ p))%Z).
    { rewrite mod_spec, add_small; [rewrite Hprod; reflexivity|].
      rewrite ?Hprod. clear - Hacc_b HPb Hp. lia. }
    rewrite (IH (gap m (d + 1))) with (H := Acc_inv H (dec_step m d Hdm));
      [reflexivity | rewrite <- Hz; apply dec_step; exact Hdm | reflexivity
      | rewrite Hd1; clear - Hd Hlt; lia | ].
    rewrite Hnew, Hd1.
    replace (Z.to_nat ((φ d) + 1) - 1)%nat with (S (k - 1)) by (clear - Hk Hd; lia).
    rewrite seq_S, map_app, list_sum_app. simpl list_sum.
    replace (S (k - 1)) with k by (clear - Hk Hd; lia).
    assert (Hterm : Z.of_nat (term nn k) = (((φ m) - (φ d)) * (X - 2))%Z).
    { unfold term, gg. fold G.
      assert (H2 : (2 <= 2 ^ G)%nat)
        by (change 2%nat with (2 ^ 1)%nat at 1; apply Nat.pow_le_mono_r; clear - HG1; lia).
      rewrite Nat2Z.inj_mul, !Nat2Z.inj_sub by (clear - Hk Hm Hn Hlt Hd H2; lia).
      rewrite Nat2Z.inj_pow.
      rewrite EX. f_equal; clear - Hk Hm Hn Hlt Hd; lia. }
    rewrite Nat.add_0_r, Nat2Z.inj_add, Hterm.
    rewrite EP, ET, EXm. apply step_arith; [clear - Hp; lia|].
    unfold hidden_eq in Hacc. rewrite Hacc. reflexivity.
  - rewrite <- not_true_iff_false, ltb_spec in Hdm.
    unfold hidden_eq in Hacc. rewrite Hacc.
    replace (Z.to_nat (φ d) - 1)%nat with (nn - 2)%nat by (clear - Hdm Hd Hm Hn Hnn; lia).
    reflexivity.
Qed.

Lemma derangement_rotations_impl_correct : forall (n p : N) (x y : uint),
  valid_input n p -> repr x n -> repr y p ->
  exists o : N, repr (derangement_rotations_impl x y) o /\
                derangement_rotations_spec n p o.
Proof.
  intros n p x y [Hvn Hvp _] Hx Hy.
  change (10 ^ 6)%N with 1000000%N in Hvn.
  change (10 ^ 8)%N with 100000000%N in Hvp.
  change (10 ^ 9 + 7)%N with 1000000007%N in Hvp.
  unfold repr, repr_uint in Hx, Hy.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
  assert (Ex : (φ x) = Z.of_N n) by lia.
  assert (Ey : (φ y) = Z.of_N p) by lia.
  set (nn := N.to_nat n).
  set (S := list_sum (map (term nn) (seq 1 (nn - 2)))).
  exists (N.of_nat S mod p)%N. split.
  - unfold repr, repr_uint, derangement_rotations_impl.
    rewrite (sum_loop_spec nn x (x - 1) y) with (z := gap (x - 1) 1).
    + fold S. rewrite Ey, <- nat_N_Z, <- N2Z.inj_mod, N2Z.id. reflexivity.
    + unfold nn. lia.
    + unfold nn. lia.
    + lia.
    + rewrite sub_spec, Z.mod_small; change (φ 1) with 1%Z; [reflexivity|lia].
    + lia.
    + reflexivity.
    + assert ((φ (x - 1)) = ((φ x) - 1)%Z)
        by (rewrite sub_spec, Z.mod_small; change (φ 1) with 1%Z; [reflexivity|lia]).
      change (φ 1) with 1%Z. lia.
    + change (φ 0) with 0%Z. change (φ 1) with 1%Z. simpl.
      rewrite Z.mod_0_l by lia. reflexivity.
  - exists (N.of_nat S). split; [|reflexivity].
    pose proof (count_correct nn ltac:(unfold nn; lia)) as C.
    unfold nn in C. rewrite N2Nat.id in C. exact C.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition derangement_rotations : uint -> uint -> uint := derangement_rotations_impl.

Definition derangement_rotations_correct : forall (n p : N) (x y : uint),
  valid_input n p -> repr x n -> repr y p ->
  exists o : N, repr (derangement_rotations x y) o /\
                derangement_rotations_spec n p o
  := derangement_rotations_impl_correct.
