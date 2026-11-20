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
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.
Elpi complexity sumbool.
Elpi complexity bdec.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.
Arguments gap : simpl never.

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

Inductive color : Type := Red | Black.
Elpi complexity color.

Inductive rbt : Type :=
| RE : rbt
| RN : color -> rbt -> int -> rbt -> rbt.
Elpi complexity rbt.

(* Okasaki's balance, the red-red violation being on the left. *)
Definition lbal (l : rbt) (k : int) (r : rbt) : rbt :=
  match l with
  | RN Red (RN Red a x b) y c => RN Red (RN Black a x b) y (RN Black c k r)
  | RN Red a x (RN Red b y c) => RN Red (RN Black a x b) y (RN Black c k r)
  | _ => RN Black l k r
  end.
Elpi complexity lbal.
Arguments lbal_cost : simpl never.

(* The same, the violation being on the right. *)
Definition rbal (l : rbt) (k : int) (r : rbt) : rbt :=
  match r with
  | RN Red (RN Red b y c) z d => RN Red (RN Black l k b) y (RN Black c z d)
  | RN Red b y (RN Red c z d) => RN Red (RN Black l k b) y (RN Black c z d)
  | _ => RN Black l k r
  end.
Elpi complexity rbal.
Arguments rbal_cost : simpl never.

Fixpoint rb_ins (y : int) (t : rbt) : rbt :=
  match t with
  | RE => RN Red RE y RE
  | RN c l k r =>
      if y <? k then
        match c with
        | Red => RN Red (rb_ins y l) k r
        | Black => lbal (rb_ins y l) k r
        end
      else if k <? y then
        match c with
        | Red => RN Red l k (rb_ins y r)
        | Black => rbal l k (rb_ins y r)
        end
      else t
  end.
Elpi complexity rb_ins.
Arguments rb_ins_cost : simpl never.

Definition make_black (t : rbt) : rbt :=
  match t with
  | RE => RE
  | RN _ l k r => RN Black l k r
  end.
Elpi complexity make_black.
Arguments make_black_cost : simpl never.

Definition rb_insert (y : int) (t : rbt) : rbt := make_black (rb_ins y t).
Elpi complexity rb_insert.
Arguments rb_insert_cost : simpl never.

(* The predecessor and the successor of y among the keys of t, p and s
   being returned when t has none below / above y on the search path. *)
Fixpoint around (y : int) (t : rbt) (p s : int) : int * int :=
  match t with
  | RE => (p, s)
  | RN _ l k r => if y <? k then around y l p k else around y r k s
  end.
Elpi complexity around.
Arguments around_cost : simpl never.

Definition imax (u v : int) : int := if u <? v then v else u.
Elpi complexity imax.
Arguments imax_cost : simpl never.
Elpi complexity fst.
Elpi complexity snd.

(* Insertions j, j+1, ..., n-1. *)
Fixpoint loop (x : array uint) (n j : int) (t : rbt) (d : array int)
    (c : int) (o : array int) (H : Acc (Zwf 0) (gap n j)) {struct H}
    : array int :=
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

Elpi complexity loop.
Arguments loop_cost : simpl never.

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

Definition bst_impl (x : array uint) : array uint :=
  let n := PArray.length x in
  loop x n 0 RE (PArray.make (n + 2) 0) 0 (PArray.make n 0)
    (Zwf_well_founded 0 (gap n 0)).
Elpi complexity bst_impl.
Arguments bst_impl_cost : simpl never.

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
  In_tree x (tree_from l t) <-> In x l \/ In_tree x t.
Proof.
  induction l as [|y l IH]; intros t x; simpl; [tauto|].
  assert (Hs : forall a b : N, a = b <-> b = a) by (split; auto).
  rewrite IH, insert_In, (Hs x y). tauto.
Qed.

Lemma tree_of_In : forall l x, In_tree x (tree_of l) <-> In x l.
Proof. intros l x. unfold tree_of. rewrite fold_In. simpl. tauto. Qed.

Lemma fold_sbst : forall l t, sbst t ->
  sbst (tree_from l t).
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

Lemma tree_from_app : forall l r t,
  tree_from (l ++ r) t = tree_from r (tree_from l t).
Proof.
  induction l as [|x l IH]; intros r t; cbn [app tree_from].
  - reflexivity.
  - apply IH.
Qed.

Lemma tree_of_snoc : forall l y, tree_of (l ++ [y]) = insert y (tree_of l).
Proof. intros l y. unfold tree_of. rewrite tree_from_app. reflexivity. Qed.

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

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bst : array uint -> array uint := bst_impl.
Elpi complexity bst.

Definition bst_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists c : list N, repr (bst x) c /\ bst_spec a c
  := bst_impl_correct.

(* ------------------------------------------------------------------ *)
(* Complexity                                                          *)
(* ------------------------------------------------------------------ *)

(* The bound needs the depth of the red-black tree to be logarithmic:
   the red-black invariant (proof-only, the program is unchanged), kept
   by insertion (Okasaki's balance), bounds the height by twice the black
   height, itself at most log2 (size + 1); every insertion adds at most
   one node. *)

Local Open Scope nat_scope.

Fixpoint height (t : rbt) : nat :=
  match t with RE => 0 | RN _ l _ r => S (Nat.max (height l) (height r)) end.

Fixpoint tsize (t : rbt) : nat :=
  match t with RE => 0 | RN _ l _ r => S (tsize l + tsize r) end.

(* is_rb t c n: t is a red-black tree of black height n that may hang
   below a parent of colour c (a red parent wants a black or empty t). *)
Inductive is_rb : rbt -> color -> nat -> Prop :=
| IsRB_leaf c : is_rb RE c 0
| IsRB_r l k r n : is_rb l Red n -> is_rb r Red n -> is_rb (RN Red l k r) Black n
| IsRB_b c l k r n : is_rb l Black n -> is_rb r Black n -> is_rb (RN Black l k r) c (S n).

(* the same, a red-red violation allowed at the root *)
Inductive nearly_rb : rbt -> nat -> Prop :=
| nrRB_r l k r n : is_rb l Black n -> is_rb r Black n -> nearly_rb (RN Red l k r) n
| nrRB_b l k r n : is_rb l Black n -> is_rb r Black n -> nearly_rb (RN Black l k r) (S n).

Lemma is_rb_black : forall t n, is_rb t Red n -> is_rb t Black n.
Proof. intros t n H. inversion H; subst; constructor; auto. Qed.

Ltac inv_rb :=
  repeat match goal with
  | H : is_rb (RN _ _ _ _) _ _ |- _ => inversion H; clear H; subst
  | H : is_rb RE _ _ |- _ => inversion H; clear H; subst
  | H : nearly_rb _ _ |- _ => inversion H; clear H; subst
  end.

Ltac split_trees :=
  repeat match goal with
  | |- context [match ?t with RE => _ | RN _ _ _ _ => _ end] => destruct t
  | |- context [match ?c with Red => _ | Black => _ end] => destruct c
  end.

Lemma lbal_rb : forall l k r n, nearly_rb l n -> is_rb r Black n ->
  is_rb (lbal l k r) Black (S n).
Proof.
  intros l k r n Hl Hr. unfold lbal.
  inversion Hl; subst; split_trees; inv_rb;
    repeat (constructor; auto using is_rb_black).
Qed.

Lemma rbal_rb : forall l k r n, is_rb l Black n -> nearly_rb r n ->
  is_rb (rbal l k r) Black (S n).
Proof.
  intros l k r n Hl Hr. unfold rbal.
  inversion Hr; subst; split_trees; inv_rb;
    repeat (constructor; auto using is_rb_black).
Qed.

Lemma rb_black_nearly : forall t n, is_rb t Black n -> t <> RE -> nearly_rb t n.
Proof.
  intros t n H Ht. inversion H; subst; [congruence| |]; constructor; auto using is_rb_black.
Qed.

Lemma rb_ins_rb : forall y t,
  (forall n, is_rb t Red n -> is_rb (rb_ins y t) Black n) /\
  (forall n, is_rb t Black n -> nearly_rb (rb_ins y t) n).
Proof.
  intros y t. induction t as [|c l [IHl1 IHl2] k r [IHr1 IHr2]].
  - split; intros n H; inversion H; subst; simpl; repeat constructor.
  - simpl. destruct c.
    + split; intros n H; inversion H; subst.
      destruct (y <? k)%uint63; [|destruct (k <? y)%uint63];
        constructor; auto using is_rb_black.
    + assert (G : forall c n, is_rb (RN Black l k r) c n ->
                 is_rb (if (y <? k)%uint63 then lbal (rb_ins y l) k r
                        else if (k <? y)%uint63 then rbal l k (rb_ins y r)
                        else RN Black l k r) Black n).
      { intros c0 n H. inversion H; subst.
        destruct (y <? k)%uint63; [|destruct (k <? y)%uint63].
        - apply lbal_rb; auto.
        - apply rbal_rb; auto.
        - constructor; auto. }
      split; intros n H.
      * exact (G _ _ H).
      * apply rb_black_nearly; [exact (G _ _ H)|].
        destruct (y <? k)%uint63; [|destruct (k <? y)%uint63].
        -- unfold lbal. split_trees; discriminate.
        -- unfold rbal. split_trees; discriminate.
        -- discriminate.
Qed.

Lemma make_black_rb : forall t n, is_rb t Black n -> exists m, is_rb (make_black t) Red m.
Proof.
  intros t n H. inversion H; subst; simpl.
  - exists 0. constructor.
  - exists (S n). constructor; auto using is_rb_black.
  - exists (S n0). constructor; auto.
Qed.

Definition rb_inv (t : rbt) : Prop := exists n, is_rb t Red n.

Lemma rb_insert_inv : forall y t, rb_inv t -> rb_inv (rb_insert y t).
Proof.
  intros y t [n H]. unfold rb_insert.
  exact (make_black_rb _ _ (proj1 (rb_ins_rb y t) n H)).
Qed.

Lemma height_rb : forall t c n, is_rb t c n ->
  height t <= 2 * n + (match c with Red => 0 | Black => 1 end).
Proof.
  intros t c n H. induction H; simpl in *; try destruct c; lia.
Qed.

Lemma size_rb : forall t c n, is_rb t c n -> 2 ^ n <= tsize t + 1.
Proof.
  intros t c n H. induction H; simpl in *; lia.
Qed.

Lemma height_inv : forall t, rb_inv t -> height t <= 2 * Nat.log2 (tsize t + 1).
Proof.
  intros t [n H]. pose proof (height_rb _ _ _ H) as H1. simpl in H1.
  pose proof (size_rb _ _ _ H) as H2.
  apply Nat.log2_le_pow2 in H2; [lia|lia].
Qed.

Lemma tsize_lbal : forall l k r, tsize (lbal l k r) = S (tsize l + tsize r).
Proof. intros. unfold lbal. split_trees; simpl; lia. Qed.
Lemma tsize_rbal : forall l k r, tsize (rbal l k r) = S (tsize l + tsize r).
Proof. intros. unfold rbal. split_trees; simpl; lia. Qed.

Lemma tsize_rb_ins : forall y t, tsize (rb_ins y t) <= S (tsize t).
Proof.
  intros y t. induction t as [|c l IHl k r IHr]; simpl; [lia|].
  destruct (y <? k)%uint63; [|destruct (k <? y)%uint63]; destruct c;
    rewrite ?tsize_lbal, ?tsize_rbal; simpl; lia.
Qed.

Lemma tsize_rb_insert : forall y t, tsize (rb_insert y t) <= S (tsize t).
Proof.
  intros y t. unfold rb_insert. pose proof (tsize_rb_ins y t).
  destruct (rb_ins y t); simpl in *; lia.
Qed.

(* The cost lemmas, in the program's scope. *)
Local Open Scope uint63_scope.

Lemma around_time1 y yC t (tC : rbt_cost stepsCM t) :
  cost (extract (around_cost stepsCM y yC) t tC) = 1%nat.
Proof. unfold around_cost. destruct tC; cost_simpl; reflexivity. Qed.

Lemma around_time2 y yC t (tC : rbt_cost stepsCM t) p pC :
  cost (extract (extract (around_cost stepsCM y yC) t tC) p pC) = 0%nat.
Proof. unfold around_cost. destruct tC; cost_simpl; reflexivity. Qed.

Lemma around_time y yC t (tC : rbt_cost stepsCM t) p pC s sC :
  (cost (extract (extract (extract (around_cost stepsCM y yC) t tC) p pC) s sC)
    <= height t * 50 + 10)%nat.
Proof.
  unfold around_cost. revert p pC s sC. induction tC; intros p pC s sC; cost_simpl.
  - lia.
  - cost_destruct (y <? i); cost_simpl.
    + specialize (IHtC1 p pC i _C0). cost_simpl_in IHtC1.
      pose proof (around_time1 y yC r tC1) as H1. unfold around_cost in H1. cost_simpl_in H1.
      pose proof (around_time2 y yC r tC1 p pC) as H2. unfold around_cost in H2. cost_simpl_in H2.
      lia.
    + specialize (IHtC2 i _C0 s sC). cost_simpl_in IHtC2.
      pose proof (around_time1 y yC r0 tC2) as H1. unfold around_cost in H1. cost_simpl_in H1.
      pose proof (around_time2 y yC r0 tC2 i _C0) as H2. unfold around_cost in H2. cost_simpl_in H2.
      lia.
Qed.

Ltac crush_w r n :=
  cost_simpl; try lia;
  lazymatch n with
  | S ?m =>
    match goal with
    | w : color_cost _ _ |- _ => destruct w; crush_w r m
    | w : rbt_cost _ ?t |- _ => assert_fails (constr_eq t r); destruct w; crush_w r m
    end
  end.

Lemma lbal_time l lC k kC r rC :
  (cost (extract (extract (lbal_cost stepsCM l lC) k kC) r rC) <= 40)%nat.
Proof.
  unfold lbal_cost. crush_w r constr:(6%nat).
Qed.

Lemma rbal_time l lC k kC r rC :
  (cost (extract (extract (rbal_cost stepsCM l lC) k kC) r rC) <= 40)%nat.
Proof.
  unfold rbal_cost. crush_w l constr:(6%nat).
Qed.

Lemma lbal_time0 l lC : cost (lbal_cost stepsCM l lC) = 0%nat.
Proof. unfold lbal_cost. cost_simpl. reflexivity. Qed.
Lemma lbal_time1 l lC k kC : cost (extract (lbal_cost stepsCM l lC) k kC) = 0%nat.
Proof. unfold lbal_cost. cost_simpl. reflexivity. Qed.
Lemma rbal_time0 l lC : cost (rbal_cost stepsCM l lC) = 0%nat.
Proof. unfold rbal_cost. cost_simpl. reflexivity. Qed.
Lemma rbal_time1 l lC k kC : cost (extract (rbal_cost stepsCM l lC) k kC) = 0%nat.
Proof. unfold rbal_cost. cost_simpl. reflexivity. Qed.

Ltac bound_calls :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (lbal_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC =>
        pose proof (lbal_time a aC b bC c cC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (rbal_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC =>
        pose proof (rbal_time a aC b bC c cC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (lbal_cost stepsCM ?a ?aC) ?b ?bC =>
        change (@cost T X) with 0%nat
    | extract (rbal_cost stepsCM ?a ?aC) ?b ?bC =>
        change (@cost T X) with 0%nat
    | lbal_cost stepsCM ?a ?aC =>
        change (@cost T X) with 0%nat
    | rbal_cost stepsCM ?a ?aC =>
        change (@cost T X) with 0%nat
    end end.

Lemma rb_ins_time y yC t (tC : rbt_cost stepsCM t) :
  (cost (extract (rb_ins_cost stepsCM y yC) t tC) <= height t * 80 + 10)%nat.
Proof.
  unfold rb_ins_cost. induction tC; cost_simpl.
  - lia.
  - cost_simpl_in IHtC1. cost_simpl_in IHtC2.
    cost_destruct (y <? i); cost_simpl.
    + destruct _C; cost_simpl; bound_calls; lia.
    + cost_destruct (i <? y); cost_simpl.
      * destruct _C; cost_simpl; bound_calls; lia.
      * lia.
Qed.

Lemma make_black_time t tC : (cost (make_black_cost stepsCM t tC) <= 5)%nat.
Proof. unfold make_black_cost. destruct tC; cost_simpl; lia. Qed.

Lemma imax_time u uC v vC : (cost (extract (imax_cost stepsCM u uC) v vC) <= 10)%nat.
Proof. unfold imax_cost. cost_simpl. cost_destruct (u <? v); cost_simpl; lia. Qed.

Lemma rb_ins_time0 y yC : cost (rb_ins_cost stepsCM y yC) = 0%nat.
Proof. reflexivity. Qed.

Lemma rb_insert_time y yC t (tC : rbt_cost stepsCM t) :
  (cost (extract (rb_insert_cost stepsCM y yC) t tC) <= height t * 80 + 20)%nat.
Proof.
  unfold rb_insert_cost. cost_simpl.
  rewrite rb_ins_time0.
  pose proof (rb_ins_time y yC t tC).
  pose proof (make_black_time (rb_ins y t) (extract (extract (rb_ins_cost stepsCM y yC) t tC))).
  lia.
Qed.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. unfold bdec_cost. destruct w; cost_simpl; lia. Qed.

Ltac zero_partials :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch T with forall _, _ => change (@cost T X) with 0%nat end end.

Ltac bound_with X T lem :=
  let Hc := fresh "Hc" in
  pose proof lem as Hc; change (@cost T X) with (@cost T X) in Hc;
  revert Hc; generalize (@cost T X); intros ? Hc.

Ltac bound_loop_calls :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (around_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
        bound_with X T (around_time a aC b bC c cC d dC : (@cost T X <= _)%nat)
    | extract (extract (around_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC =>
        bound_with X T (around_time2 a aC b bC c cC : (@cost T X = _)%nat)
    | extract (around_cost stepsCM ?a ?aC) ?b ?bC =>
        bound_with X T (around_time1 a aC b bC : (@cost T X = _)%nat)
    | extract (rb_insert_cost stepsCM ?a ?aC) ?b ?bC =>
        bound_with X T (rb_insert_time a aC b bC : (@cost T X <= _)%nat)
    | extract (imax_cost stepsCM ?a ?aC) ?b ?bC =>
        bound_with X T (imax_time a aC b bC : (@cost T X <= _)%nat)
    | extract (extract (extract (set_cost _ _ _) _ _) _ _) _ _ =>
        change (@cost T X) with 1%nat
    end end.

Lemma loop_time x xC n nC j jC t tC d dC c cC o oC H HC (L : nat) :
  (forall t', rb_inv t' -> (tsize t' <= Z.to_nat (φ n))%nat -> (height t' <= L)%nat) ->
  rb_inv t -> (tsize t <= Z.to_nat (φ j))%nat ->
  (cost (extract (extract (extract (extract (extract (extract (extract (loop_cost stepsCM x xC) n nC) j jC) t tC) d dC) c cC) o oC) H HC)
     <= Z.to_nat (gap n j) * (L * 200 + 300) + 10)%nat.
Proof.
  intros HL. unfold loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC j jC t tC d dC c cC o oC H HC)] =>
    assert (HG : forall k j jC t tC d dC c cC o oC H HC, (Z.to_nat (gap n j) <= k)%nat ->
       rb_inv t -> (tsize t <= Z.to_nat (φ j))%nat ->
       (cost (G x xC n nC j jC t tC d dC c cC o oC H HC) <= k * (L * 200 + 300) + 10)%nat) end.
  { induction k as [|k IH]; intros j' jC' t' tC' d' dC' c' cC' o' oC' [g] HC' Hk Hinv Hsz;
      cost_simpl;
      pose proof (bdec_time (j' <? n) (bool_w (j' <? n))) as HB;
      cost_destruct (bdec (j' <? n)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
    - lia.
    - zero_partials.
      bound_loop_calls.
      match goal with |- context [extract (extract (extract (extract (around_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC)] =>
        set (W := extract (extract (extract (extract (around_cost stepsCM a aC) b bC) c cC) d dC)) end.
      clearbody W. revert W. generalize (around x.[j'] t' 0 (n + 1)) as o0. intros o0 W.
      destruct W as [p pC q qC]. cost_simpl. zero_partials. bound_loop_calls.
      match goal with |- context [@cost ?T (?G' x xC n nC (j' + 1)%uint63 ?w ?t2 ?tC2 ?d2 ?dC2 ?c2 ?cC2 ?o2 ?oC2 ?h ?e)] =>
        pose proof (IH (j' + 1)%uint63 w t2 tC2 d2 dC2 c2 cC2 o2 oC2 h e
          : _ -> _ -> _ -> (@cost T (G' x xC n nC (j' + 1)%uint63 w t2 tC2 d2 dC2 c2 cC2 o2 oC2 h e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' x xC n nC (j' + 1)%uint63 w t2 tC2 d2 dC2 c2 cC2 o2 oC2 h e)); intros ? HI end.
      clear IH.
      pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hj1 : φ (j' + 1) = (φ j' + 1)%Z) by (zify; Z.to_euclidean_division_equations; lia).
      pose proof (to_Z_bounded j') as Bj. pose proof (to_Z_bounded n) as Bn.
      change (to_nat j') with (Z.to_nat (φ j')) in Hsz.
      change (to_nat n) with (Z.to_nat (φ n)) in HL.
      specialize (HI ltac:(unfold gap in *; lia) (rb_insert_inv _ _ Hinv)).
      pose proof (tsize_rb_insert x.[j'] t') as Hs1.
      specialize (HI ltac:(change (to_nat (j' + 1)) with (Z.to_nat (φ (j' + 1))); lia)).
      pose proof (HL t' Hinv ltac:(lia)) as Hh.
      clear Hj1 Hk Hlt Bj Bn Hsz HL Hs1.
      remember (k * (L * 200 + 300))%nat as KM.
      lia.
    - lia. }
  intros Hinv Hsz.
  match goal with |- context [@cost ?T (?G x xC n nC j jC t tC d dC c cC o oC H HC)] =>
    exact (HG _ j jC t tC d dC c cC o oC H HC (le_n _) Hinv Hsz
           : (@cost T (G x xC n nC j jC t tC d dC c cC o oC H HC) <= _)%nat) end.
Qed.

Lemma height_bound (N : nat) : forall t, rb_inv t -> (tsize t <= N)%nat ->
  (height t <= 2 * Nat.log2 (N + 1))%nat.
Proof.
  intros t Hi Hs. pose proof (height_inv t Hi).
  pose proof (Nat.log2_le_mono (tsize t + 1) (N + 1) ltac:(lia)). lia.
Qed.

Lemma bst_impl_time x xC :
  (cost (bst_impl_cost stepsCM x xC) <= Z.to_nat (φ (PArray.length x)) * (2 * Nat.log2 (Z.to_nat (φ (PArray.length x)) + 1) * 200 + 300) + 100)%nat.
Proof.
  remember (Z.to_nat (φ (PArray.length x))) as N eqn:EN.
  remember (2 * Nat.log2 (N + 1))%nat as L eqn:EL.
  assert (HL : forall t', rb_inv t' -> (tsize t' <= Z.to_nat (φ (PArray.length x)))%nat -> (height t' <= L)%nat)
    by (subst; apply height_bound).
  assert (Hinv0 : rb_inv RE) by (exists 0%nat; constructor).
  assert (Hg : Z.to_nat (gap (PArray.length x) 0) = N) by (unfold gap; subst N; f_equal; change (φ 0) with 0%Z; lia).
  remember (N * (L * 200 + 300) + 100)%nat as R eqn:ER.
  unfold bst_impl_cost. cost_simpl. zero_partials.
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (make_cost _ _ _) _ _) _ _ => change (@cost T X) with 1%nat
    end end.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (extract (extract (extract (loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC =>
      bound_with X T (loop_time a aC b bC c cC d dC e eC f fC g gC h hC L HL Hinv0 (le_0_n _) : (@cost T X <= _)%nat)
    end end.
  rewrite Hg in Hc. subst R. clear -Hc.
  remember (N * (L * 200 + 300))%nat as M. lia.
Qed.

Lemma bst_time_concrete x :
  (cost1 bst_cost x <= (size x + 1) * (Nat.log2 (size x) + 1) * 1000 + 1000)%nat.
Proof.
  remember ((size x + 1) * (Nat.log2 (size x) + 1) * 1000 + 1000)%nat as R eqn:ER.
  unfold cost1, bst_cost. cost_simpl.
  match goal with |- context [@cost ?T ?X] =>
    pose proof (bst_impl_time x (witness x) : (@cost T X <= _)%nat) as H;
    revert H; generalize (@cost T X); intros C H end.
  change (Z.to_nat (φ (PArray.length x))) with (size x) in H.
  subst R. revert H. generalize (size x) as N. intros N H.
  pose proof (Nat.log2_succ_le N) as HS. replace (S N) with (N + 1)%nat in HS by lia.
  revert H HS. generalize (Nat.log2 (N + 1)) as A. generalize (Nat.log2 N) as G. intros G A H HS.
  assert (H1 : (N * (2 * A * 200 + 300) <= N * (G * 400 + 700))%nat) by (apply Nat.mul_le_mono_l; lia).
  assert (H2 : (N * (G * 400 + 700) <= (N + 1) * (G + 1) * 1000)%nat) by nia.
  lia.
Qed.

Theorem bst_time : exists c1 c2 : nat,
  forall (sequence : list N) (sequence_arr : array uint),
  valid_input sequence -> repr sequence_arr sequence ->
  (cost1 bst_cost sequence_arr <= c1 * ((size sequence_arr + 1) * (Nat.log2 (size sequence_arr) + 1)) + c2)%nat.
Proof.
  exists 1000%nat, 1000%nat. intros sequence sequence_arr _ _.
  pose proof (bst_time_concrete sequence_arr) as H.
  remember ((size sequence_arr + 1) * (Nat.log2 (size sequence_arr) + 1))%nat as P.
  lia.
Qed.
