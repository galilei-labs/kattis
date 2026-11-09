(* Correctness proofs for bst_implem.v. *)
(* Implementation of bst (bst.spec): the depth counter of an unbalanced
   binary search tree, computed online with a red-black tree.

   Code.  The keys inserted so far are held in a red-black tree (an
   inductive tree, insertion in the Okasaki style, [lbal]/[rbal] on the
   side of the descent).  For the new key y, one descent [around] finds its
   predecessor p and successor s in the set, with the sentinels 0 (no
   predecessor) and N+1 (no successor).  The flat table [d], indexed by
   key (size N+2), holds depth+1 of every inserted key and 0 elsewhere
   (the sentinels included), so the new key's depth+1 is
   1 + max d.[p] d.[s]: in the statement's tree the new key hangs below
   whichever of p and s is deeper (theorem [key_depth]).  The counter is a
   uint; the answers go into one array threaded linearly.

   Termination: the red-black functions recurse structurally on the tree;
   the main loop on an erased [Acc (Zwf 0) (gap n j)] proof, the
   template's device.  No nat, no Z in the code. *)

From Bst.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Bst Require Export bst_implem.
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

Lemma loop_eq : forall x n j t d c o H,
  loop x n j t d c o H =
  match bdec (j <? n) with
  | left Hj =>
      let y := x.[j] in
      let ps := around y t 0 (n + 1) in
      let e := 1 + imax d.[fst ps] d.[snd ps] in
      let c' := c + e - 1 in
      loop x n (j + 1) (rb_insert y t) d.[y <- e] c' o.[j <- c']
        (Acc_inv H (dec_step n j Hj))
  | right _ => o
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the statement's tree                                     *)
(* ------------------------------------------------------------------ *)

Local Open Scope N_scope.

Fixpoint In_tree (x : N) (t : tree) : Prop :=
  match t with
  | Leaf => False
  | Node l z r => In_tree x l \/ x = z \/ In_tree x r
  end.

Fixpoint sbst (t : tree) : Prop :=
  match t with
  | Leaf => True
  | Node l z r => sbst l /\ sbst r /\ (forall x, In_tree x l -> x < z)
                  /\ (forall x, In_tree x r -> z < x)
  end.

(* Membership along the search path. *)
Fixpoint memb (x : N) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node l z r => if x <? z then memb x l else if z <? x then memb x r else true
  end.

(* depth + 1 of a key of t, 0 for a non-key. *)
Definition E (t : tree) (x : N) : N := if memb x t then N.succ (depth x t) else 0.

Lemma memb_In : forall t x, sbst t -> (memb x t = true <-> In_tree x t).
Proof.
  induction t as [|l IHl z r IHr]; intros x Hb; simpl.
  - split; [discriminate | tauto].
  - simpl in Hb. destruct Hb as (Hbl & Hbr & Hlz & Hzr).
    destruct (N.ltb_spec x z) as [Hxz|Hxz].
    + rewrite IHl by assumption. split; [tauto|].
      intros [H|[H|H]]; [exact H | lia | apply Hzr in H; lia].
    + destruct (N.ltb_spec z x) as [Hzx|Hzx].
      * rewrite IHr by assumption. split; [tauto|].
        intros [H|[H|H]]; [apply Hlz in H; lia | lia | exact H].
      * split; [intros _; right; left; lia | reflexivity].
Qed.

Lemma insert_In : forall t x y, In_tree x (insert y t) <-> x = y \/ In_tree x t.
Proof.
  induction t as [|l IHl z r IHr]; intros x y; simpl.
  - tauto.
  - destruct (N.ltb_spec y z); simpl; [rewrite IHl; tauto|].
    destruct (N.ltb_spec z y); simpl; [rewrite IHr; tauto|].
    assert (y = z) by lia. subst. tauto.
Qed.

Lemma insert_sbst : forall t y, sbst t -> sbst (insert y t).
Proof.
  induction t as [|l IHl z r IHr]; intros y Hb; simpl.
  - repeat split; intros x [].
  - simpl in Hb. destruct Hb as (Hbl & Hbr & Hlz & Hzr).
    destruct (N.ltb_spec y z); simpl.
    + repeat split; auto. intros x Hx. apply insert_In in Hx.
      destruct Hx as [->|Hx]; auto.
    + destruct (N.ltb_spec z y); simpl.
      * repeat split; auto. intros x Hx. apply insert_In in Hx.
        destruct Hx as [->|Hx]; auto; lia.
      * repeat split; auto.
Qed.

Lemma memb_insert_other : forall t x y, x <> y -> memb x (insert y t) = memb x t.
Proof.
  intros t x y Hxy. induction t as [|l IHl z r IHr]; simpl.
  - destruct (N.ltb_spec x y); [reflexivity|].
    destruct (N.ltb_spec y x); [reflexivity|]. lia.
  - destruct (N.ltb_spec y z); simpl.
    + destruct (N.ltb_spec x z); [exact IHl | reflexivity].
    + destruct (N.ltb_spec z y); simpl; [|reflexivity].
      destruct (N.ltb_spec x z); [reflexivity|].
      destruct (N.ltb_spec z x); [exact IHr | reflexivity].
Qed.

Lemma depth_insert_other : forall t x y, x <> y -> memb x t = true ->
  depth x (insert y t) = depth x t.
Proof.
  intros t x y Hxy. induction t as [|l IHl z r IHr]; simpl; intros Hm.
  - discriminate.
  - destruct (N.ltb_spec y z); simpl.
    + destruct (N.ltb_spec x z); [rewrite IHl by exact Hm; reflexivity | reflexivity].
    + destruct (N.ltb_spec z y); simpl; [|reflexivity].
      destruct (N.ltb_spec x z); [reflexivity|].
      destruct (N.ltb_spec z x); [rewrite IHr by exact Hm; reflexivity | reflexivity].
Qed.

Lemma memb_insert_self : forall t y, memb y (insert y t) = true.
Proof.
  induction t as [|l IHl z r IHr]; intros y; simpl.
  - rewrite N.ltb_irrefl. reflexivity.
  - destruct (N.ltb_spec y z) as [H|H]; simpl.
    + rewrite (proj2 (N.ltb_lt y z) H). apply IHl.
    + destruct (N.ltb_spec z y) as [H'|H']; simpl.
      * rewrite (proj2 (N.ltb_ge y z) H), (proj2 (N.ltb_lt z y) H'). apply IHr.
      * rewrite (proj2 (N.ltb_ge y z) H), (proj2 (N.ltb_ge z y) H'). reflexivity.
Qed.

Lemma E_insert_other : forall t x y, x <> y -> E (insert y t) x = E t x.
Proof.
  intros t x y Hxy. unfold E. rewrite memb_insert_other by exact Hxy.
  destruct (memb x t) eqn:Hm; [|reflexivity].
  rewrite depth_insert_other by assumption. reflexivity.
Qed.

Lemma E_insert_self : forall t y, E (insert y t) y = N.succ (depth y (insert y t)).
Proof. intros t y. unfold E. rewrite memb_insert_self. reflexivity. Qed.

Lemma fold_In : forall l t x,
  In_tree x (fold_left (fun t y => insert y t) l t) <-> In x l \/ In_tree x t.
Proof.
  induction l as [|y l IH]; intros t x; simpl; [tauto|].
  assert (Hs : forall a b : N, a = b <-> b = a) by (split; auto).
  rewrite IH, insert_In, (Hs x y). tauto.
Qed.

Lemma tree_of_In : forall l x, In_tree x (tree_of l) <-> In x l.
Proof. intros l x. unfold tree_of. rewrite fold_In. simpl. tauto. Qed.

Lemma fold_sbst : forall l t, sbst t ->
  sbst (fold_left (fun t y => insert y t) l t).
Proof.
  induction l as [|y l IH]; intros t Ht; simpl; [exact Ht|].
  apply IH, insert_sbst, Ht.
Qed.

Lemma tree_of_sbst : forall l, sbst (tree_of l).
Proof. intros l. apply fold_sbst. exact I. Qed.

(* E at a node, for a key left / right of the root. *)
Lemma E_left : forall l z r x, x < z ->
  E (Node l z r) x = if memb x l then N.succ (E l x) else 0.
Proof.
  intros l z r x H. unfold E. simpl. rewrite (proj2 (N.ltb_lt x z) H).
  destruct (memb x l); reflexivity.
Qed.

Lemma E_right : forall l z r x, z < x ->
  E (Node l z r) x = if memb x r then N.succ (E r x) else 0.
Proof.
  intros l z r x H. unfold E. simpl.
  rewrite (proj2 (N.ltb_ge x z) ltac:(lia)), (proj2 (N.ltb_lt z x) H).
  destruct (memb x r); reflexivity.
Qed.

Lemma E_root : forall l z r, E (Node l z r) z = 1.
Proof. intros l z r. unfold E. simpl. rewrite N.ltb_irrefl. reflexivity. Qed.

Lemma E_not : forall t x, memb x t = false -> E t x = 0.
Proof. intros t x H. unfold E. rewrite H. reflexivity. Qed.

Lemma E_pos : forall t x, memb x t = true -> E t x = N.succ (depth x t).
Proof. intros t x H. unfold E. rewrite H. reflexivity. Qed.

Lemma classic_in : forall x t, In_tree x t \/ ~ In_tree x t.
Proof.
  intros x t. induction t as [|l IHl z r IHr]; simpl; [tauto|].
  destruct IHl, IHr, (N.eq_dec x z); tauto.
Qed.

(* The new key hangs below the deeper of its predecessor p and its
   successor s (0 / N+1 or any non-key standing for "none"). *)
Theorem key_depth : forall t y p s,
  sbst t -> ~ In_tree y t -> p < y < s ->
  (forall x, In_tree x t -> x <= p \/ s <= x) ->
  (~ In_tree p t -> forall x, In_tree x t -> y < x) ->
  (~ In_tree s t -> forall x, In_tree x t -> x < y) ->
  depth y (insert y t) = N.max (E t p) (E t s).
Proof.
  induction t as [|l IHl z r IHr]; intros y p s Hb Hy Hps H2 H3 H4.
  - unfold E. simpl. rewrite N.ltb_irrefl. reflexivity.
  - pose proof Hb as Hb'. simpl in Hb'. destruct Hb' as (Hbl & Hbr & Hlz & Hzr).
    simpl in Hy.
    assert (Hzt : In_tree z (Node l z r)) by (simpl; tauto).
    destruct (N.lt_trichotomy y z) as [Hyz|[Hyz|Hyz]]; [ | exfalso; tauto | ].
    + (* y < z: the new key goes left *)
      simpl. rewrite (proj2 (N.ltb_lt y z) Hyz). simpl.
      rewrite (proj2 (N.ltb_lt y z) Hyz).
      assert (Hsz : s <= z) by (destruct (H2 z Hzt); lia).
      assert (Hpl : In_tree p (Node l z r) -> In_tree p l).
      { simpl. intros [H|[H|H]]; [exact H | lia | apply Hzr in H; lia]. }
      assert (H3l : ~ In_tree p l -> forall x, In_tree x l -> y < x).
      { intros Hp x Hx. apply H3; [tauto | simpl; tauto]. }
      rewrite (E_left l z r p) by lia.
      destruct (N.eq_dec s z) as [Esz|Esz].
      * subst s. rewrite E_root.
        assert (Hzl : ~ In_tree z l) by (intro H; apply Hlz in H; lia).
        rewrite (IHl y p z Hbl ltac:(tauto) ltac:(lia)
          ltac:(intros x Hx; apply H2; simpl; tauto) H3l
          ltac:(intros _ x Hx; destruct (H2 x ltac:(simpl; tauto)) as [H|H];
                  [lia | apply Hlz in Hx; lia])).
        rewrite (E_not l z) by (destruct (memb z l) eqn:M; [|reflexivity];
                                apply memb_In in M; tauto).
        destruct (memb p l) eqn:M; [rewrite (E_pos l p M) | rewrite (E_not l p M)]; lia.
      * assert (Hst : In_tree s (Node l z r)).
        { destruct (classic_in s (Node l z r)) as [H|H]; [exact H|].
          exfalso. specialize (H4 H z Hzt). lia. }
        assert (Hsl : In_tree s l).
        { simpl in Hst. destruct Hst as [H|[H|H]]; [exact H | lia | apply Hzr in H; lia]. }
        rewrite (E_left l z r s) by lia.
        rewrite (IHl y p s Hbl ltac:(tauto) ltac:(lia)
          ltac:(intros x Hx; apply H2; simpl; tauto) H3l
          ltac:(intros H; exfalso; exact (H Hsl))).
        rewrite (proj2 (memb_In l s Hbl) Hsl), (E_pos l s (proj2 (memb_In l s Hbl) Hsl)).
        destruct (memb p l) eqn:M; [rewrite (E_pos l p M) | rewrite (E_not l p M)]; lia.
    + (* z < y: the new key goes right *)
      simpl. rewrite (proj2 (N.ltb_ge y z) ltac:(lia)), (proj2 (N.ltb_lt z y) Hyz). simpl.
      rewrite (proj2 (N.ltb_ge y z) ltac:(lia)), (proj2 (N.ltb_lt z y) Hyz).
      assert (Hpz : z <= p) by (destruct (H2 z Hzt); lia).
      assert (Hsr : In_tree s (Node l z r) -> In_tree s r).
      { simpl. intros [H|[H|H]]; [apply Hlz in H; lia | lia | exact H]. }
      assert (H4r : ~ In_tree s r -> forall x, In_tree x r -> x < y).
      { intros Hs x Hx. apply H4; [tauto | simpl; tauto]. }
      rewrite (E_right l z r s) by lia.
      destruct (N.eq_dec p z) as [Epz|Epz].
      * subst p. rewrite E_root.
        assert (Hzr' : ~ In_tree z r) by (intro H; apply Hzr in H; lia).
        rewrite (IHr y z s Hbr ltac:(tauto) ltac:(lia)
          ltac:(intros x Hx; apply H2; simpl; tauto)
          ltac:(intros _ x Hx; destruct (H2 x ltac:(simpl; tauto)) as [H|H];
                  [apply Hzr in Hx; lia | lia]) H4r).
        rewrite (E_not r z) by (destruct (memb z r) eqn:M; [|reflexivity];
                                apply memb_In in M; tauto).
        destruct (memb s r) eqn:M; [rewrite (E_pos r s M) | rewrite (E_not r s M)]; lia.
      * assert (Hpt : In_tree p (Node l z r)).
        { destruct (classic_in p (Node l z r)) as [H|H]; [exact H|].
          exfalso. specialize (H3 H z Hzt). lia. }
        assert (Hpr : In_tree p r).
        { simpl in Hpt. destruct Hpt as [H|[H|H]]; [apply Hlz in H; lia | lia | exact H]. }
        rewrite (E_right l z r p) by lia.
        rewrite (IHr y p s Hbr ltac:(tauto) ltac:(lia)
          ltac:(intros x Hx; apply H2; simpl; tauto)
          ltac:(intros H; exfalso; exact (H Hpr)) H4r).
        rewrite (proj2 (memb_In r p Hbr) Hpr), (E_pos r p (proj2 (memb_In r p Hbr) Hpr)).
        destruct (memb s r) eqn:M; [rewrite (E_pos r s M) | rewrite (E_not r s M)]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the red-black tree                                       *)
(* ------------------------------------------------------------------ *)

(* A machine key read as a number. *)
Definition toN (k : int) : N := Z.to_N (φ k).

Lemma ltb_toN : forall u v : int, (u <? v)%uint63 = (toN u <? toN v).
Proof.
  intros u v. unfold toN. pose proof (to_Z_bounded u). pose proof (to_Z_bounded v).
  destruct (Uint63.ltb u v) eqn:Hl; symmetry.
  - rewrite ltb_spec in Hl. apply N.ltb_lt. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hl. apply N.ltb_ge. lia.
Qed.

Lemma toN_inj : forall u v : int, toN u = toN v -> u = v.
Proof.
  intros u v H. unfold toN in H. pose proof (to_Z_bounded u). pose proof (to_Z_bounded v).
  apply to_Z_inj. lia.
Qed.

(* The keys, in order. *)
Fixpoint elems (t : rbt) : list N :=
  match t with
  | RE => []
  | RN _ l k r => elems l ++ toN k :: elems r
  end.

Definition ordR (t : rbt) : Prop := StronglySorted N.lt (elems t).

Lemma SS_split : forall L1 k L2,
  StronglySorted N.lt (L1 ++ k :: L2) <->
  StronglySorted N.lt L1 /\ StronglySorted N.lt L2 /\
  (forall z, In z L1 -> z < k) /\ (forall z, In z L2 -> k < z).
Proof.
  induction L1 as [|a L1 IH]; intros k L2; simpl.
  - split.
    + intros H. apply StronglySorted_inv in H. destruct H as [H1 H2].
      rewrite Forall_forall in H2.
      repeat split; auto. constructor. intros z [].
    + intros (_ & H1 & _ & H2). constructor; [exact H1|]. apply Forall_forall, H2.
  - split.
    + intros H. apply StronglySorted_inv in H. destruct H as [H1 H2].
      apply IH in H1. destruct H1 as (S1 & S2 & F1 & F2).
      rewrite Forall_forall in H2.
      assert (Hak : a < k) by (apply H2, in_or_app; simpl; tauto).
      repeat split; auto.
      * constructor; [exact S1|]. apply Forall_forall. intros z Hz.
        apply H2, in_or_app. tauto.
      * intros z [<-|Hz]; auto.
    + intros (S1 & S2 & F1 & F2).
      apply StronglySorted_inv in S1. destruct S1 as [S1 G1].
      rewrite Forall_forall in G1.
      assert (Hak : a < k) by (apply F1; tauto).
      constructor.
      * apply IH. repeat split; auto.
      * apply Forall_forall. intros z Hz. apply in_app_or in Hz.
        destruct Hz as [Hz|[<-|Hz]]; auto. apply F2 in Hz. lia.
Qed.

Lemma ordR_node : forall c l k r, ordR (RN c l k r) <->
  ordR l /\ ordR r /\ (forall z, In z (elems l) -> z < toN k) /\
  (forall z, In z (elems r) -> toN k < z).
Proof. intros. unfold ordR. simpl. apply SS_split. Qed.

Ltac crush_match :=
  repeat match goal with |- context [match ?t with _ => _ end] => destruct t end.

Lemma lbal_elems : forall l k r, elems (lbal l k r) = elems l ++ toN k :: elems r.
Proof.
  intros l k r. unfold lbal. crush_match; simpl;
    repeat (rewrite <- app_assoc; simpl); reflexivity.
Qed.

Lemma rbal_elems : forall l k r, elems (rbal l k r) = elems l ++ toN k :: elems r.
Proof.
  intros l k r. unfold rbal. crush_match; simpl;
    repeat (rewrite <- app_assoc; simpl); reflexivity.
Qed.

Lemma rb_ins_spec : forall y t,
  (forall z, In z (elems (rb_ins y t)) <-> z = toN y \/ In z (elems t)) /\
  (ordR t -> ordR (rb_ins y t)).
Proof.
  intros y t. induction t as [|c l IHl k r IHr]; simpl.
  - split; [intros z; simpl; split; intros H; destruct H as [H|H]; auto; contradiction|].
    intros _. unfold ordR. simpl. constructor; constructor.
  - destruct IHl as [IHl1 IHl2]. destruct IHr as [IHr1 IHr2].
    destruct (y <? k)%uint63 eqn:Hyk.
    + rewrite ltb_toN, N.ltb_lt in Hyk.
      assert (Hel : elems (match c with
                           | Red => RN Red (rb_ins y l) k r
                           | Black => lbal (rb_ins y l) k r end)
                    = elems (rb_ins y l) ++ toN k :: elems r)
        by (destruct c; [reflexivity | apply lbal_elems]).
      split.
      * intros z. rewrite Hel, !in_app_iff, IHl1. simpl. tauto.
      * intros Ho. unfold ordR in *. rewrite Hel. simpl in Ho.
        apply SS_split in Ho. destruct Ho as (S1 & S2 & F1 & F2).
        apply SS_split. repeat split; auto.
        intros z Hz. apply IHl1 in Hz. destruct Hz as [->|Hz]; auto.
    + destruct (k <? y)%uint63 eqn:Hky.
      * rewrite ltb_toN, N.ltb_lt in Hky.
        assert (Hel : elems (match c with
                             | Red => RN Red l k (rb_ins y r)
                             | Black => rbal l k (rb_ins y r) end)
                      = elems l ++ toN k :: elems (rb_ins y r))
          by (destruct c; [reflexivity | apply rbal_elems]).
        split.
        -- intros z. rewrite Hel, !in_app_iff. simpl. rewrite IHr1. tauto.
        -- intros Ho. unfold ordR in *. rewrite Hel. simpl in Ho.
           apply SS_split in Ho. destruct Ho as (S1 & S2 & F1 & F2).
           apply SS_split. repeat split; auto.
           intros z Hz. apply IHr1 in Hz. destruct Hz as [->|Hz]; auto.
      * rewrite ltb_toN, N.ltb_ge in Hyk, Hky.
        assert (E : toN y = toN k) by lia.
        split; [|auto].
        intros z. simpl. rewrite in_app_iff. simpl. rewrite E.
        split; [tauto|]. intros [->|H]; tauto.
Qed.

Lemma rb_insert_spec : forall y t, ordR t ->
  ordR (rb_insert y t) /\
  (forall z, In z (elems (rb_insert y t)) <-> z = toN y \/ In z (elems t)).
Proof.
  intros y t Ho. destruct (rb_ins_spec y t) as [H1 H2].
  assert (Hm : forall u, elems (make_black u) = elems u) by (destruct u; reflexivity).
  unfold rb_insert, ordR in *. rewrite Hm. split; [apply H2, Ho | exact H1].
Qed.

Lemma around_spec : forall t y p s p' s',
  ordR t -> ~ In (toN y) (elems t) ->
  toN p < toN y < toN s ->
  (forall z, In z (elems t) -> toN p < z < toN s) ->
  around y t p s = (p', s') ->
  toN p' < toN y < toN s' /\
  (p' = p \/ In (toN p') (elems t)) /\
  (s' = s \/ In (toN s') (elems t)) /\
  (forall z, In z (elems t) -> z <= toN p' \/ toN s' <= z).
Proof.
  induction t as [|c l IHl k r IHr]; intros y p s p' s' Ho Hy Hps Hin Ha; simpl in Ha.
  - injection Ha as <- <-. repeat split; auto; try lia. intros z [].
  - apply ordR_node in Ho. destruct Ho as (Ol & Or & Fl & Fr).
    simpl in Hy, Hin. rewrite in_app_iff in Hy. simpl in Hy.
    destruct (y <? k)%uint63 eqn:Hyk.
    + rewrite ltb_toN, N.ltb_lt in Hyk.
      destruct (IHl y p k p' s' Ol ltac:(tauto) ltac:(lia)
                  ltac:(intros z Hz; split;
                          [apply (Hin z ltac:(apply in_or_app; tauto)) | apply Fl, Hz])
                  Ha) as (B & P & S & G).
      simpl. repeat split; try lia.
      * destruct P as [P|P]; [left; exact P | right; apply in_or_app; tauto].
      * destruct S as [->|S]; right; apply in_or_app; simpl; tauto.
      * intros z Hz. apply in_app_or in Hz. simpl in Hz.
        assert (Hsk : toN s' <= toN k)
          by (destruct S as [->|S]; [lia | apply Fl in S; lia]).
        destruct Hz as [Hz|[<-|Hz]]; [apply G, Hz | lia | apply Fr in Hz; lia].
    + rewrite ltb_toN, N.ltb_ge in Hyk.
      assert (Hky : toN k < toN y)
        by (destruct (N.eq_dec (toN k) (toN y)) as [E|E]; [exfalso; tauto | lia]).
      destruct (IHr y k s p' s' Or ltac:(tauto) ltac:(lia)
                  ltac:(intros z Hz; split;
                          [apply Fr, Hz | apply (Hin z ltac:(apply in_or_app; simpl; tauto))])
                  Ha) as (B & P & S & G).
      simpl. repeat split; try lia.
      * destruct P as [->|P]; right; apply in_or_app; simpl; tauto.
      * destruct S as [S|S]; [left; exact S | right; apply in_or_app; simpl; tauto].
      * intros z Hz. apply in_app_or in Hz. simpl in Hz.
        assert (Hpk : toN k <= toN p')
          by (destruct P as [->|P]; [lia | apply Fr in P; lia]).
        destruct Hz as [Hz|[<-|Hz]]; [apply Fl in Hz; lia | lia | apply G, Hz].
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: lists and the input                                      *)
(* ------------------------------------------------------------------ *)

Lemma firstn_snoc : forall (l : list N) j, (j < List.length l)%nat ->
  firstn (S j) l = firstn j l ++ [nth j l 0].
Proof.
  induction l as [|a l IH]; intros j Hj; simpl in Hj; [lia|].
  destruct j as [|j]; [reflexivity|].
  change (firstn (S (S j)) (a :: l)) with (a :: firstn (S j) l).
  rewrite IH by lia. reflexivity.
Qed.

Lemma tree_of_snoc : forall l y, tree_of (l ++ [y]) = insert y (tree_of l).
Proof. intros l y. unfold tree_of. rewrite fold_left_app. reflexivity. Qed.

Lemma nodup_nth_firstn : forall (l : list N) j, NoDup l -> (j < List.length l)%nat ->
  ~ In (nth j l 0) (firstn j l).
Proof.
  induction l as [|a l IH]; intros j Hd Hj; simpl in Hj; [lia|].
  apply NoDup_cons_iff in Hd. destruct Hd as [Ha Hd].
  destruct j as [|j]; simpl; [tauto|].
  intros [H|H].
  - apply Ha. rewrite H. apply nth_In. lia.
  - exact (IH j Hd ltac:(lia) H).
Qed.

Lemma in_firstn' : forall (l : list N) j w, In w (firstn j l) -> In w l.
Proof.
  intros l j w H. rewrite <- (firstn_skipn j l). apply in_or_app. left. exact H.
Qed.

Local Close Scope N_scope.

(* Reading an in-bounds cell of an array representing a. *)
Lemma repr_get : forall (x : array uint) (a : list N), repr x a ->
  forall i : int, ((φ i) < Z.of_nat (List.length a))%Z ->
  toN x.[i] = nth (Z.to_nat (φ i)) a 0%N.
Proof.
  intros x a [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. unfold toN. rewrite Hr.
  symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array uint) (a : list N), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

(* ------------------------------------------------------------------ *)
(* The main loop                                                       *)
(* ------------------------------------------------------------------ *)

Lemma loop_spec : forall (a : list N) (x : array uint), valid_input a -> repr x a ->
  forall n : int, (φ n) = Z.of_nat (List.length a) ->
  forall (z : Z) (j : int) (t : rbt) (d : array int) (c : int) (o : array int)
         (H : Acc (Zwf 0) (gap n j)) (T : tree),
  gap n j = z ->
  ((φ j) <= (φ n))%Z ->
  T = tree_of (firstn (Z.to_nat (φ j)) a) ->
  ordR t -> (forall w, In w (elems t) <-> In_tree w T) ->
  (φ (PArray.length d)) = ((φ n) + 2)%Z ->
  (forall i : int, ((φ i) <= (φ n) + 1)%Z ->
     toN d.[i] = E T (toN i) /\ ((φ (d.[i])) <= (φ j))%Z) ->
  toN c = counter a (Z.to_nat (φ j)) -> ((φ c) <= (φ j) * (φ j))%Z ->
  PArray.length o = n ->
  (forall k : int, ((φ k) < (φ j))%Z -> toN o.[k] = counter a (Z.to_nat (φ k) + 1)) ->
  PArray.length (loop x n j t d c o H) = n /\
  forall k : int, ((φ k) < (φ n))%Z ->
    toN (loop x n j t d c o H).[k] = counter a (Z.to_nat (φ k) + 1).
Proof.
  intros a x Hv Hx n Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j t d c o H T Hz Hjn HT Ho Hset Hdl Hd Hc Hcb Hol Hoc.
  pose proof Hv as Hv'. destruct Hv' as [Hvn Hvr Hvd]. unfold len in Hvn.
  rewrite Forall_forall in Hvr.
  rewrite loop_eq.
  destruct (bdec (j <? n)) as [Hj | Hj].
  2: { rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
       split; [exact Hol|]. intros k Hk. apply Hoc. lia. }
  pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
  pose proof (to_Z_bounded j) as Bj.
  assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
  assert (Hn1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  set (jn := Z.to_nat (φ j)) in *.
  assert (Hjn' : (jn < List.length a)%nat) by lia.
  assert (HSj : Z.to_nat (φ (j + 1)) = S jn) by lia.
  set (y := x.[j]).
  assert (Hy : toN y = nth jn a 0%N) by exact (repr_get x a Hx j ltac:(lia)).
  assert (HyR : (1 <= toN y <= N.of_nat (List.length a))%N)
    by (rewrite Hy; apply Hvr, nth_In; exact Hjn').
  assert (HTb : sbst T) by (rewrite HT; apply tree_of_sbst).
  assert (HyT : ~ In_tree (toN y) T)
    by (rewrite HT, tree_of_In, Hy; apply nodup_nth_firstn; auto).
  assert (HTr : forall w, In_tree w T -> (1 <= w <= N.of_nat (List.length a))%N)
    by (intros w Hw; rewrite HT, tree_of_In in Hw; apply Hvr, (in_firstn' _ jn), Hw).
  assert (HT' : insert (toN y) T = tree_of (firstn (S jn) a))
    by (rewrite firstn_snoc, tree_of_snoc, <- HT, Hy by exact Hjn'; reflexivity).
  cbv zeta.
  destruct (around y t 0 (n + 1)) as [p s] eqn:Hps.
  cbn [fst snd].
  destruct (around_spec t y 0 (n + 1) p s Ho ltac:(rewrite Hset; exact HyT)
              ltac:(unfold toN in *; change (φ 0) with 0%Z; lia)
              ltac:(intros w Hw; apply Hset, HTr in Hw; unfold toN in *;
                    change (φ 0) with 0%Z; lia)
              Hps) as (B & HP & HS & G).
  assert (Hp : ((φ p) <= (φ n) + 1)%Z).
  { destruct HP as [->|HP']; [change (φ 0) with 0%Z; lia|].
    apply Hset, HTr in HP'. unfold toN in HP'. pose proof (to_Z_bounded p). lia. }
  assert (Hs : ((φ s) <= (φ n) + 1)%Z).
  { destruct HS as [->|HS']; [lia|].
    apply Hset, HTr in HS'. unfold toN in HS'. pose proof (to_Z_bounded s). lia. }
  destruct (Hd p Hp) as [Dp Bp]. destruct (Hd s Hs) as [Ds Bs].
  pose proof (to_Z_bounded d.[p]) as Bdp. pose proof (to_Z_bounded d.[s]) as Bds.
  set (e := 1 + imax d.[p] d.[s]).
  assert (He : (φ e) = (1 + Z.max (φ (d.[p])) (φ (d.[s])))%Z).
  { unfold e, imax. destruct (d.[p] <? d.[s]) eqn:Hc';
      [rewrite ltb_spec in Hc' | rewrite <- Bool.not_true_iff_false, ltb_spec in Hc'];
      sia. }
  assert (Hkey : depth (toN y) (insert (toN y) T) = N.max (E T (toN p)) (E T (toN s))).
  { apply key_depth; auto.
    - intros w Hw. apply G, Hset, Hw.
    - intros Hnp w Hw. destruct HP as [Ep|HP']; [| exfalso; apply Hnp, Hset, HP'].
      subst p. pose proof (HTr w Hw). destruct (G w (proj2 (Hset w) Hw)) as [Q|Q];
        unfold toN in *; change (φ 0) with 0%Z in *; lia.
    - intros Hns w Hw. destruct HS as [Es|HS']; [| exfalso; apply Hns, Hset, HS'].
      subst s. pose proof (HTr w Hw). destruct (G w (proj2 (Hset w) Hw)) as [Q|Q];
        unfold toN in *; lia. }
  assert (Hj3 : ((φ j) <= 300000)%Z) by lia.
  assert (Hjj : ((φ j) * (φ j) <= 300000 * 300000)%Z)
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (Hcs : ((φ c) <= 90000000000)%Z) by lia.
  pose proof (to_Z_bounded c) as Bc.
  assert (Hce : (φ (c + e - 1)) = ((φ c) + (φ e) - 1)%Z) by sia.
  assert (Hc' : toN (c + e - 1) = counter a (S jn)).
  { simpl counter. unfold placed_depth, Prelude.get. rewrite Nat2N.id, Nat.add_1_r.
    rewrite <- HT', <- Hy, Hkey, <- Dp, <- Ds, <- Hc.
    unfold toN. rewrite Hce, He. clear - Bc Bdp Bds. lia. }
  apply (IH (gap n (j + 1))) with (T := insert (toN y) T).
  - rewrite <- Hz. apply dec_step. exact Hj.
  - reflexivity.
  - lia.
  - rewrite HSj. exact HT'.
  - exact (proj1 (rb_insert_spec y t Ho)).
  - intros w. rewrite (proj2 (rb_insert_spec y t Ho)), Hset, insert_In. tauto.
  - rewrite alength_set. exact Hdl.
  - intros i Hi. destruct (Z.eq_dec (φ i) (φ y)) as [Ei|Ei].
    + assert (i = y) by (apply to_Z_inj; exact Ei). subst i.
      rewrite aget_set_same by (rewrite ltb_spec, Hdl; unfold toN in HyR; lia).
      split.
      * rewrite E_insert_self, Hkey, <- Dp, <- Ds. unfold toN. rewrite He.
        clear - Bdp Bds. lia.
      * rewrite He, Hj1. lia.
    + rewrite aget_set_other by (intro F; apply Ei; rewrite F; reflexivity).
      destruct (Hd i Hi) as [D1 D2]. split; [|lia].
      rewrite E_insert_other; [exact D1|].
      intro F. apply Ei. apply toN_inj in F. rewrite F. reflexivity.
  - rewrite HSj. exact Hc'.
  - rewrite Hce, He, Hj1.
    assert (Hsq : (((φ j) + 1) * ((φ j) + 1) = (φ j) * (φ j) + 2 * (φ j) + 1)%Z) by ring.
    rewrite Hsq. lia.
  - rewrite alength_set. exact Hol.
  - intros k Hk. rewrite Hj1 in Hk. destruct (Z.eq_dec (φ k) (φ j)) as [Ek|Ek].
    + assert (k = j) by (apply to_Z_inj; exact Ek). subst k.
      rewrite aget_set_same by (rewrite ltb_spec, Hol; exact Hj').
      rewrite Nat.add_1_r. exact Hc'.
    + rewrite aget_set_other by (intro F; apply Ek; rewrite F; reflexivity).
      apply Hoc. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The output                                                          *)
(* ------------------------------------------------------------------ *)

Definition out_list (a : list N) : list N :=
  map (fun k => counter a (k + 1)) (seq 0 (List.length a)).

Lemma out_correct : forall (a : list N) (r : array@{Set} uint) (n : int),
  (φ n) = Z.of_nat (List.length a) ->
  PArray.length@{Set} r = n ->
  (forall k : int, ((φ k) < (φ n))%Z ->
     toN (PArray.get@{Set} r k) = counter a (Z.to_nat (φ k) + 1)) ->
  repr r (out_list a) /\ bst_spec a (out_list a).
Proof.
  intros a r n Hn Hrl0 Hrc0.
  assert (Hrl : PArray.length@{repr_array.u0} r = n) by exact Hrl0.
  assert (Hrc : forall k : int, ((φ k) < (φ n))%Z ->
     toN (PArray.get@{repr_array.u0} r k) = counter a (Z.to_nat (φ k) + 1))
    by exact Hrc0.
  clear Hrl0 Hrc0.
  assert (Hlen : List.length (out_list a) = List.length a).
  { unfold out_list. rewrite length_map, length_seq. reflexivity. }
  assert (Hnth : forall k, (k < List.length a)%nat ->
            nth_error (out_list a) k = Some (counter a (k + 1))).
  { intros k Hk. unfold out_list. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec k (List.length a)); [reflexivity | lia]. }
  pose proof (to_Z_bounded n) as Bn.
  split.
  - split.
    + rewrite Hlen, Hrl, Hn. reflexivity.
    + intros k Hk. rewrite Hlen in Hk.
      exists (counter a (k + 1)). split; [apply Hnth; exact Hk|].
      unfold repr, repr_uint.
      assert (Hk' : (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
      { rewrite of_Z_spec. apply Z.mod_small. lia. }
      change (Uint63.of_nat k) with (of_Z (Z.of_nat k)).
      pose proof (Hrc (of_Z (Z.of_nat k)) ltac:(rewrite Hk'; lia)) as R.
      unfold toN in R. rewrite R, Hk', Nat2Z.id. reflexivity.
  - split.
    + unfold len. rewrite Hlen. reflexivity.
    + intros k Hk. unfold len in Hk. rewrite Hlen in Hk. unfold Prelude.get.
      apply nth_error_nth. apply Hnth. lia.
Qed.

Lemma bst_impl_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists c : list N, repr (bst_impl x) c /\ bst_spec a c.
Proof.
  intros a x Hv Hx.
  pose proof Hv as Hv'. destruct Hv' as [Hvn _ _]. unfold len in Hvn.
  pose proof (repr_length x a Hx) as Lx.
  exists (out_list a).
  unfold bst_impl.
  set (n := PArray.length x) in *.
  pose proof (to_Z_bounded n) as Bn.
  assert (Hmd : (φ (PArray.length (PArray.make (n + 2) (0 : int)))) = ((φ n) + 2)%Z).
  { rewrite alength_make.
    replace (n + 2 <=? PArray.max_length) with true;
      [sia | symmetry; rewrite leb_spec, max_length_val; sia]. }
  assert (Hmo : PArray.length (PArray.make n (0 : int)) = n).
  { rewrite alength_make.
    replace (n <=? PArray.max_length) with true;
      [reflexivity | symmetry; rewrite leb_spec, max_length_val; lia]. }
  destruct (loop_spec a x Hv Hx n Lx _ 0 RE (PArray.make (n + 2) 0) 0
              (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) Leaf eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              eq_refl
              ltac:(constructor)
              ltac:(intros w; simpl; tauto)
              Hmd
              ltac:(intros i Hi; rewrite aget_make; split; reflexivity)
              eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              Hmo
              ltac:(intros k Hk; change (φ 0) with 0%Z in Hk;
                    pose proof (to_Z_bounded k); lia))
    as [Hrl Hrc].
  exact (out_correct a _ n Lx Hrl Hrc).
Qed.

Definition bst_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists c : list N, repr (bst x) c /\ bst_spec a c
  := bst_impl_correct.
