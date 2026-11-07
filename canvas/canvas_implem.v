(* Implementation of canvas (canvas.spec): Huffman's greedy algorithm on
   a binary min-heap kept in one flat array (heapify, then pop the lightest
   group a, replace the next lightest b by a + b, add a + b to the total).
   Part A: trees and Huffman's exchange lemma; Part B: runs of the painting
   machine <-> trees over the canvasses; Part C: the program and its heap
   proofs.  Termination by erased Acc on Z measures; no nat, no Z in the
   extracted code. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  Permutation Bool.
Import ListNotations.

Unset Lia Cache.

(* ================================================================== *)
(* Part A.  Binary trees over leaf labels, their cost, Huffman's      *)
(* exchange lemma.                                                     *)
(* ================================================================== *)

Open Scope N_scope.

Inductive tree := Leaf (x : N) | Node (l r : tree).

Fixpoint leaves (t : tree) : list N :=
  match t with Leaf x => [x] | Node l r => leaves l ++ leaves r end.

Fixpoint sumL (l : list N) : N :=
  match l with [] => 0 | x :: r => x + sumL r end.

Definition wt (w : N -> N) (t : tree) : N := sumL (map w (leaves t)).

Fixpoint cost (w : N -> N) (t : tree) : N :=
  match t with
  | Leaf _ => 0
  | Node l r => wt w l + wt w r + cost w l + cost w r
  end.

Lemma sumL_app : forall l l', sumL (l ++ l') = sumL l + sumL l'.
Proof. induction l; intros; simpl; [lia | rewrite IHl; lia]. Qed.

Lemma sumL_perm : forall l l', Permutation l l' -> sumL l = sumL l'.
Proof. intros l l' H. induction H; simpl; lia. Qed.

Lemma leaves_nonempty : forall t, exists a, In a (leaves t).
Proof.
  induction t as [x | l [a Ha] r _]; simpl.
  - exists x. left. reflexivity.
  - exists a. apply in_or_app. left. exact Ha.
Qed.

Lemma wt_ext : forall w w' t, (forall x, In x (leaves t) -> w x = w' x) ->
  wt w t = wt w' t.
Proof. intros. unfold wt. f_equal. apply map_ext_in. auto. Qed.

Lemma cost_ext : forall w w' t, (forall x, In x (leaves t) -> w x = w' x) ->
  cost w t = cost w' t.
Proof.
  intros w w' t. induction t as [x | l IHl r IHr]; intros H; simpl; [reflexivity|].
  simpl in H.
  rewrite (wt_ext w w' l), (wt_ext w w' r), IHl, IHr; auto;
    intros; apply H; apply in_or_app; auto.
Qed.

Definition inb (x : N) (l : list N) : bool := existsb (N.eqb x) l.

Lemma inb_true : forall x l, inb x l = true <-> In x l.
Proof.
  intros x l. unfold inb. rewrite existsb_exists. split.
  - intros [y [Hy E]]. apply N.eqb_eq in E. subst. exact Hy.
  - intros H. exists x. split; [exact H | apply N.eqb_refl].
Qed.

Lemma inb_false : forall x l, ~ In x l -> inb x l = false.
Proof.
  intros x l H. destruct (inb x l) eqn:E; [|reflexivity].
  apply inb_true in E. contradiction.
Qed.

Fixpoint dep (t : tree) (x : N) : nat :=
  match t with
  | Leaf _ => O
  | Node l r => S (if inb x (leaves l) then dep l x else dep r x)
  end.

Fixpoint ht (t : tree) : nat :=
  match t with Leaf _ => O | Node l r => S (Nat.max (ht l) (ht r)) end.

Lemma dep_le_ht : forall t x, (dep t x <= ht t)%nat.
Proof.
  induction t as [y | l IHl r IHr]; intros x; simpl; [lia|].
  destruct (inb x (leaves l)); [specialize (IHl x) | specialize (IHr x)]; lia.
Qed.

Lemma NoDup_app_l : forall (l l' : list N), NoDup (l ++ l') -> NoDup l.
Proof.
  intros l l' H. induction l as [| a l IH]; [constructor|].
  inversion H; subst. constructor; [| apply IH; assumption].
  intro F. apply H2. apply in_or_app. left. exact F.
Qed.

Lemma NoDup_app_r : forall (l l' : list N), NoDup (l ++ l') -> NoDup l'.
Proof.
  intros l l' H. induction l as [| a l IH]; [exact H|].
  inversion H; subst. apply IH. assumption.
Qed.

Lemma NoDup_app_disj : forall (l l' : list N) x,
  NoDup (l ++ l') -> In x l -> In x l' -> False.
Proof.
  intros l l' x H. induction l as [| a l IH]; intros H1 H2; [destruct H1|].
  inversion H; subst. destruct H1 as [E | H1].
  - subst. apply H4. apply in_or_app. right. exact H2.
  - apply IH; assumption.
Qed.

(* Changing the weight of one leaf x. *)
Lemma sumL_change : forall (w w' : N -> N) l x,
  NoDup l -> In x l -> (forall z, z <> x -> w' z = w z) ->
  (Z.of_N (sumL (map w' l)) = Z.of_N (sumL (map w l)) + Z.of_N (w' x) - Z.of_N (w x))%Z.
Proof.
  intros w w' l x Hnd. induction l as [| a l IH]; intros Hin Hw; [destruct Hin|].
  inversion Hnd; subst. simpl. destruct Hin as [E | Hin].
  - subst a. rewrite (map_ext_in w' w l).
    + lia.
    + intros z Hz. apply Hw. intro F. subst. contradiction.
  - rewrite Hw by (intro F; subst; contradiction).
    rewrite N2Z.inj_add, N2Z.inj_add, IH by assumption. lia.
Qed.

Lemma sumL_same : forall (w w' : N -> N) l x,
  ~ In x l -> (forall z, z <> x -> w' z = w z) ->
  sumL (map w' l) = sumL (map w l).
Proof.
  intros. f_equal. apply map_ext_in. intros z Hz. apply H0.
  intro F. subst. contradiction.
Qed.

Lemma cost_change : forall (w w' : N -> N) t x,
  NoDup (leaves t) -> In x (leaves t) -> (forall z, z <> x -> w' z = w z) ->
  (Z.of_N (cost w' t) = Z.of_N (cost w t)
     + (Z.of_N (w' x) - Z.of_N (w x)) * Z.of_nat (dep t x))%Z.
Proof.
  intros w w' t x. induction t as [y | l IHl r IHr]; intros Hnd Hin Hw.
  - simpl. lia.
  - simpl in Hnd, Hin |- *.
    pose proof (NoDup_app_l _ _ Hnd) as Hl. pose proof (NoDup_app_r _ _ Hnd) as Hr.
    apply in_app_or in Hin. unfold wt.
    destruct Hin as [Hin | Hin].
    + rewrite (proj2 (inb_true x (leaves l)) Hin).
      assert (Hnr : ~ In x (leaves r)) by (intro F; exact (NoDup_app_disj _ _ _ Hnd Hin F)).
      rewrite (sumL_same w w' (leaves r) x Hnr Hw).
      rewrite (cost_ext w' w r) by (intros z Hz; apply Hw; intro F; subst; contradiction).
      rewrite !N2Z.inj_add.
      rewrite (sumL_change w w' (leaves l) x Hl Hin Hw), (IHl Hl Hin Hw).
      rewrite Zpos_P_of_succ_nat. ring.
    + assert (Hnl : ~ In x (leaves l)) by (intro F; exact (NoDup_app_disj _ _ _ Hnd F Hin)).
      rewrite (inb_false _ _ Hnl).
      rewrite (sumL_same w w' (leaves l) x Hnl Hw).
      rewrite (cost_ext w' w l) by (intros z Hz; apply Hw; intro F; subst; contradiction).
      rewrite !N2Z.inj_add.
      rewrite (sumL_change w w' (leaves r) x Hr Hin Hw), (IHr Hr Hin Hw).
      rewrite Zpos_P_of_succ_nat. ring.
Qed.

Definition upd (w : N -> N) (x v : N) : N -> N :=
  fun z => if N.eqb z x then v else w z.

Definition swp (w : N -> N) (x y : N) : N -> N := upd (upd w x (w y)) y (w x).

Lemma swp_x : forall w x y, swp w x y x = w y.
Proof.
  intros. unfold swp, upd. destruct (N.eqb_spec x y); [subst; reflexivity|].
  rewrite N.eqb_refl. reflexivity.
Qed.

Lemma swp_y : forall w x y, swp w x y y = w x.
Proof. intros. unfold swp, upd. rewrite N.eqb_refl. reflexivity. Qed.

Lemma swp_other : forall w x y z, z <> x -> z <> y -> swp w x y z = w z.
Proof.
  intros. unfold swp, upd.
  rewrite (proj2 (N.eqb_neq z y) H0), (proj2 (N.eqb_neq z x) H). reflexivity.
Qed.

(* Swapping the weights of x and y, the lighter going deeper, does not
   increase the cost. *)
Lemma cost_swap : forall w t x y,
  NoDup (leaves t) -> In x (leaves t) -> In y (leaves t) ->
  w x <= w y -> (dep t x <= dep t y)%nat ->
  cost (swp w x y) t <= cost w t.
Proof.
  intros w t x y Hnd Hx Hy Hw Hd.
  destruct (N.eq_dec x y) as [E | Hxy].
  - subst y. rewrite (cost_ext (swp w x x) w); [lia|].
    intros z _. unfold swp, upd. destruct (N.eqb_spec z x); subst; reflexivity.
  - set (w1 := upd w x (w y)).
    assert (E1 := cost_change w w1 t x Hnd Hx
                  ltac:(intros z Hz; unfold w1, upd; rewrite (proj2 (N.eqb_neq z x) Hz); reflexivity)).
    assert (E2 := cost_change w1 (swp w x y) t y Hnd Hy
                  ltac:(intros z Hz; unfold swp, upd; fold w1;
                        rewrite (proj2 (N.eqb_neq z y) Hz); reflexivity)).
    rewrite swp_y in E2.
    assert (Hw1x : w1 x = w y) by (unfold w1, upd; rewrite N.eqb_refl; reflexivity).
    assert (Hw1y : w1 y = w y)
      by (unfold w1, upd; rewrite (proj2 (N.eqb_neq y x) (fun F => Hxy (eq_sym F))); reflexivity).
    rewrite Hw1x in E1. rewrite Hw1y in E2.
    nia.
Qed.

Lemma perm_swap_mid : forall (A B C : list N) u v,
  Permutation (A ++ u :: B ++ v :: C) (A ++ v :: B ++ u :: C).
Proof.
  intros. apply Permutation_app_head.
  apply perm_trans with (v :: u :: B ++ C).
  - apply Permutation_sym. exact (Permutation_middle (u :: B) C v).
  - apply perm_skip. apply Permutation_middle.
Qed.

Lemma perm_swp_core : forall w (A B C : list N) x y,
  NoDup (A ++ x :: B ++ y :: C) ->
  Permutation (map (swp w x y) (A ++ x :: B ++ y :: C)) (map w (A ++ x :: B ++ y :: C)).
Proof.
  intros w A B C x y Hnd.
  pose proof (NoDup_remove_2 _ _ _ Hnd) as Nx.
  assert (Hnd' : NoDup ((A ++ x :: B) ++ y :: C)) by (rewrite <- app_assoc; exact Hnd).
  pose proof (NoDup_remove_2 _ _ _ Hnd') as Ny.
  assert (Ho : forall z, In z (A ++ B ++ C) -> swp w x y z = w z).
  { intros z Hz. apply swp_other.
    - intro E. subst. apply Nx. rewrite in_app_iff in Hz |- *.
      destruct Hz as [Hz | Hz]; [left; exact Hz|]. right. apply in_or_app.
      rewrite in_app_iff in Hz. destruct Hz as [Hz | Hz]; [left; exact Hz | right; right; exact Hz].
    - intro E. subst. apply Ny. rewrite !in_app_iff in Hz |- *. simpl.
      destruct Hz as [Hz | [Hz | Hz]]; auto. }
  rewrite !map_app. simpl. rewrite !map_app. simpl.
  rewrite swp_x, swp_y.
  rewrite (map_ext_in (swp w x y) w A) by (intros z Hz; apply Ho; apply in_or_app; left; exact Hz).
  rewrite (map_ext_in (swp w x y) w B)
    by (intros z Hz; apply Ho; apply in_or_app; right; apply in_or_app; left; exact Hz).
  rewrite (map_ext_in (swp w x y) w C)
    by (intros z Hz; apply Ho; apply in_or_app; right; apply in_or_app; right; exact Hz).
  apply perm_swap_mid.
Qed.

Lemma swp_sym : forall w x y z, swp w x y z = swp w y x z.
Proof.
  intros. unfold swp, upd.
  destruct (N.eqb_spec z y), (N.eqb_spec z x); subst; reflexivity.
Qed.

Lemma perm_swp : forall w l x y, NoDup l -> In x l -> In y l ->
  Permutation (map (swp w x y) l) (map w l).
Proof.
  intros w l x y Hnd Hx Hy.
  destruct (N.eq_dec x y) as [E | Hxy].
  - subst. rewrite (map_ext_in (swp w y y) w); [apply Permutation_refl|].
    intros z _. unfold swp, upd. destruct (N.eqb_spec z y); subst; reflexivity.
  - destruct (in_split x l Hx) as (A & D & ->).
    apply in_app_or in Hy. destruct Hy as [Hy | [Hy | Hy]].
    + destruct (in_split y A Hy) as (A1 & A2 & ->).
      rewrite <- app_assoc. simpl.
      rewrite (map_ext (swp w x y) (swp w y x)) by apply swp_sym.
      apply perm_swp_core. rewrite <- app_assoc in Hnd. exact Hnd.
    + subst. contradiction.
    + destruct (in_split y D Hy) as (D1 & D2 & ->).
      apply perm_swp_core. exact Hnd.
Qed.

(* One-hole contexts. *)
Inductive ctx := Hole | CL (c : ctx) (r : tree) | CR (l : tree) (c : ctx).

Fixpoint plug (C : ctx) (s : tree) : tree :=
  match C with
  | Hole => s
  | CL c r => Node (plug c s) r
  | CR l c => Node l (plug c s)
  end.

Fixpoint cdepth (C : ctx) : nat :=
  match C with Hole => O | CL c _ => S (cdepth c) | CR _ c => S (cdepth c) end.

Fixpoint cl (C : ctx) : list N :=
  match C with Hole => [] | CL c _ => cl c | CR l c => leaves l ++ cl c end.

Fixpoint cr (C : ctx) : list N :=
  match C with Hole => [] | CL c r => cr c ++ leaves r | CR _ c => cr c end.

Lemma leaves_plug : forall C s, leaves (plug C s) = cl C ++ leaves s ++ cr C.
Proof.
  induction C as [| c IH r | l c IH]; intros s; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite <- !app_assoc. reflexivity.
  - rewrite IH. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma cherry : forall t, (1 <= ht t)%nat ->
  exists C p q, t = plug C (Node (Leaf p) (Leaf q)) /\ S (cdepth C) = ht t.
Proof.
  induction t as [x | l IHl r IHr]; intros H; simpl in H; [lia|].
  destruct l as [a | l1 l2]; destruct r as [b | r1 r2].
  - exists Hole, a, b. split; reflexivity.
  - destruct IHr as (C & p & q & E & D); [simpl; lia|].
    exists (CR (Leaf a) C), p, q. split; [rewrite E; reflexivity|].
    simpl. simpl in D. lia.
  - destruct IHl as (C & p & q & E & D); [simpl; lia|].
    exists (CL C (Leaf b)), p, q. split; [rewrite E; reflexivity|].
    simpl. simpl in D. lia.
  - destruct (Nat.le_gt_cases (ht (Node r1 r2)) (ht (Node l1 l2))) as [Hc | Hc].
    + destruct IHl as (C & p & q & E & D); [simpl; lia|].
      exists (CL C (Node r1 r2)), p, q. split; [rewrite E; reflexivity|].
      simpl. simpl in D, Hc. lia.
    + destruct IHr as (C & p & q & E & D); [simpl; lia|].
      exists (CR (Node l1 l2) C), p, q. split; [rewrite E; reflexivity|].
      simpl. simpl in D, Hc. lia.
Qed.

Lemma dep_plug : forall C s x, NoDup (leaves (plug C s)) -> In x (leaves s) ->
  dep (plug C s) x = (cdepth C + dep s x)%nat.
Proof.
  induction C as [| c IH r | l c IH]; intros s x Hnd Hx; simpl; [reflexivity| |].
  - simpl in Hnd.
    assert (Hin : In x (leaves (plug c s)))
      by (rewrite leaves_plug; apply in_or_app; right; apply in_or_app; left; exact Hx).
    rewrite (proj2 (inb_true _ _) Hin). rewrite IH; [reflexivity | | exact Hx].
    exact (NoDup_app_l _ _ Hnd).
  - simpl in Hnd.
    assert (Hin : In x (leaves (plug c s)))
      by (rewrite leaves_plug; apply in_or_app; right; apply in_or_app; left; exact Hx).
    rewrite inb_false by (intro F; exact (NoDup_app_disj _ _ _ Hnd F Hin)).
    rewrite IH; [reflexivity | | exact Hx].
    exact (NoDup_app_r _ _ Hnd).
Qed.

Lemma wt_plug : forall w C s,
  wt w (plug C s) = sumL (map w (cl C)) + wt w s + sumL (map w (cr C)).
Proof.
  intros. unfold wt. rewrite leaves_plug, !map_app, !sumL_app. lia.
Qed.

Lemma cost_plug : forall C w w' s s',
  (forall x, In x (cl C ++ cr C) -> w x = w' x) -> wt w s = wt w' s' ->
  cost w (plug C s) + cost w' s' = cost w' (plug C s') + cost w s.
Proof.
  induction C as [| c IH r | l c IH]; intros w w' s s' Hext Hwt; simpl; [lia| |].
  - assert (Hr : forall x, In x (leaves r) -> w x = w' x)
      by (intros x Hx; apply Hext; simpl; apply in_or_app; right; apply in_or_app; right; exact Hx).
    assert (Hc : forall x, In x (cl c ++ cr c) -> w x = w' x).
    { intros x Hx; apply Hext; simpl. rewrite in_app_iff in Hx |- *.
      destruct Hx as [Hx | Hx]; [left; exact Hx | right; apply in_or_app; left; exact Hx]. }
    rewrite (wt_ext w w' r Hr), (cost_ext w w' r Hr).
    assert (Hp : wt w (plug c s) = wt w' (plug c s')).
    { rewrite !wt_plug, Hwt.
      rewrite (map_ext_in w w' (cl c)) by (intros; apply Hc; apply in_or_app; auto).
      rewrite (map_ext_in w w' (cr c)) by (intros; apply Hc; apply in_or_app; auto).
      reflexivity. }
    rewrite Hp. specialize (IH w w' s s' Hc Hwt). lia.
  - assert (Hr : forall x, In x (leaves l) -> w x = w' x)
      by (intros x Hx; apply Hext; simpl; rewrite <- app_assoc; apply in_or_app; left; exact Hx).
    assert (Hc : forall x, In x (cl c ++ cr c) -> w x = w' x).
    { intros x Hx; apply Hext; simpl. rewrite <- app_assoc. apply in_or_app. right. exact Hx. }
    rewrite (wt_ext w w' l Hr), (cost_ext w w' l Hr).
    assert (Hp : wt w (plug c s) = wt w' (plug c s')).
    { rewrite !wt_plug, Hwt.
      rewrite (map_ext_in w w' (cl c)) by (intros; apply Hc; apply in_or_app; auto).
      rewrite (map_ext_in w w' (cr c)) by (intros; apply Hc; apply in_or_app; auto).
      reflexivity. }
    rewrite Hp. specialize (IH w w' s s' Hc Hwt). lia.
Qed.

Lemma length_leaves_ht : forall t, ht t = O -> List.length (leaves t) = 1%nat.
Proof. intros [x | l r]; simpl; [reflexivity | discriminate]. Qed.

Lemma in_perm_cons : forall (l : list N) a R x, Permutation l (a :: R) -> In x l ->
  x = a \/ In x R.
Proof.
  intros. apply (Permutation_in x H) in H0. destruct H0; auto.
Qed.

(* Huffman's exchange lemma: in any tree over a :: b :: R, a and b the two
   smallest weights, merging a and b saves at least a + b. *)
Lemma huff_key : forall t w a b R,
  NoDup (leaves t) -> Permutation (map w (leaves t)) (a :: b :: R) ->
  (forall x, In x (b :: R) -> a <= x) -> (forall x, In x R -> b <= x) ->
  exists t' w', NoDup (leaves t') /\
    Permutation (map w' (leaves t')) ((a + b) :: R) /\
    cost w' t' + (a + b) <= cost w t.
Proof.
  intros t w a b R Hnd Hp Ha Hb.
  assert (Hht : (1 <= ht t)%nat).
  { destruct (Nat.eq_dec (ht t) 0) as [E | E]; [|lia].
    apply length_leaves_ht in E. apply Permutation_length in Hp.
    rewrite length_map, E in Hp. simpl in Hp. discriminate. }
  destruct (cherry t Hht) as (C & p & q & Et & Dt).
  rewrite Et in Hnd, Hp |- *.
  set (L := leaves (plug C (Node (Leaf p) (Leaf q)))) in *.
  assert (EL : L = cl C ++ p :: q :: cr C) by (unfold L; rewrite leaves_plug; reflexivity).
  assert (Hpq : p <> q).
  { intro E. subst q. rewrite EL in Hnd. apply NoDup_remove_2 in Hnd.
    apply Hnd. apply in_or_app. right. left. reflexivity. }
  assert (Hpin : In p L) by (rewrite EL; apply in_or_app; right; left; reflexivity).
  assert (Hqin : In q L) by (rewrite EL; apply in_or_app; right; right; left; reflexivity).
  assert (Dp : dep (plug C (Node (Leaf p) (Leaf q))) p = ht t).
  { rewrite dep_plug by (simpl; auto). simpl. rewrite N.eqb_refl. simpl. lia. }
  assert (Dq : dep (plug C (Node (Leaf p) (Leaf q))) q = ht t).
  { rewrite dep_plug by (simpl; auto). simpl.
    rewrite (proj2 (N.eqb_neq q p) (fun E => Hpq (eq_sym E))). simpl. lia. }
  assert (Hdmax : forall x, (dep (plug C (Node (Leaf p) (Leaf q))) x <= ht t)%nat)
    by (intros x; rewrite Et; apply dep_le_ht).
  (* step 1: a into p *)
  assert (Hai : In a (map w L)) by (apply (Permutation_in a (Permutation_sym Hp)); left; reflexivity).
  apply in_map_iff in Hai. destruct Hai as (i & Hwi & Hi).
  set (w1 := swp w i p).
  assert (C1 : cost w1 (plug C (Node (Leaf p) (Leaf q))) <= cost w (plug C (Node (Leaf p) (Leaf q)))).
  { apply cost_swap; auto.
    - rewrite Hwi. destruct (in_perm_cons _ _ _ (w p) Hp (in_map w L p Hpin)) as [E | E].
      + lia.
      + apply Ha. exact E.
    - rewrite Dp. apply Hdmax. }
  assert (P1 : Permutation (map w1 L) (a :: b :: R))
    by (eapply perm_trans; [apply perm_swp; auto | exact Hp]).
  assert (W1p : w1 p = a) by (unfold w1; rewrite swp_y; exact Hwi).
  (* step 2: b into q *)
  assert (P1' : Permutation (map w1 (cl C ++ q :: cr C)) (b :: R)).
  { rewrite EL, map_app in P1. simpl in P1. rewrite W1p in P1.
    apply Permutation_sym in P1. apply Permutation_cons_app_inv in P1.
    rewrite map_app. simpl. apply Permutation_sym. exact P1. }
  assert (Hbj : In b (map w1 (cl C ++ q :: cr C)))
    by (apply (Permutation_in b (Permutation_sym P1')); left; reflexivity).
  apply in_map_iff in Hbj. destruct Hbj as (j & Hwj & Hj).
  assert (HjL : In j L).
  { rewrite EL. rewrite in_app_iff in Hj |- *. simpl.
    destruct Hj as [Hj | [Hj | Hj]]; auto. }
  assert (Hjp : j <> p).
  { intro E. subst j. rewrite EL in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd.
    exact Hj. }
  set (w2 := swp w1 j q).
  assert (C2 : cost w2 (plug C (Node (Leaf p) (Leaf q))) <= cost w1 (plug C (Node (Leaf p) (Leaf q)))).
  { apply cost_swap; auto.
    - rewrite Hwj.
      assert (Hq1 : In (w1 q) (b :: R))
        by (apply (Permutation_in _ P1'); apply in_map; apply in_or_app; right; left; reflexivity).
      destruct Hq1 as [E | E]; [lia | apply Hb; exact E].
    - rewrite Dq. apply Hdmax. }
  assert (P2 : Permutation (map w2 L) (a :: b :: R))
    by (eapply perm_trans; [apply perm_swp; auto | exact P1]).
  assert (W2p : w2 p = a)
    by (unfold w2; rewrite swp_other by auto; exact W1p).
  assert (W2q : w2 q = b) by (unfold w2; rewrite swp_y; exact Hwj).
  (* merge the cherry *)
  set (w' := upd w2 p (a + b)).
  exists (plug C (Leaf p)), w'.
  assert (Hncl : forall x, In x (cl C ++ cr C) -> x <> p).
  { intros x Hx E. subst x. rewrite EL in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd.
    rewrite in_app_iff in Hx |- *. destruct Hx as [Hx | Hx]; [left; exact Hx|].
    right. right. exact Hx. }
  assert (Hw'e : forall x, In x (cl C ++ cr C) -> w2 x = w' x).
  { intros x Hx. unfold w', upd. rewrite (proj2 (N.eqb_neq x p) (Hncl x Hx)). reflexivity. }
  split; [|split].
  - rewrite leaves_plug. simpl. rewrite EL in Hnd.
    replace (cl C ++ p :: q :: cr C) with ((cl C ++ [p]) ++ q :: cr C) in Hnd
      by (rewrite <- app_assoc; reflexivity).
    apply NoDup_remove_1 in Hnd. rewrite <- app_assoc in Hnd. exact Hnd.
  - rewrite leaves_plug. simpl. rewrite map_app. simpl.
    assert (Ep : w' p = a + b) by (unfold w', upd; rewrite N.eqb_refl; reflexivity).
    rewrite Ep.
    rewrite <- (map_ext_in w2 w' (cl C)) by (intros; apply Hw'e; apply in_or_app; auto).
    rewrite <- (map_ext_in w2 w' (cr C)) by (intros; apply Hw'e; apply in_or_app; auto).
    rewrite EL, map_app in P2. simpl in P2. rewrite W2p, W2q in P2.
    apply Permutation_sym in P2. apply Permutation_cons_app_inv in P2.
    apply Permutation_cons_app_inv in P2.
    eapply perm_trans; [apply Permutation_sym; apply Permutation_middle|].
    apply perm_skip. apply Permutation_sym. exact P2.
  - assert (Ep : w' p = a + b) by (unfold w', upd; rewrite N.eqb_refl; reflexivity).
    assert (K := cost_plug C w2 w' (Node (Leaf p) (Leaf q)) (Leaf p) Hw'e
                  ltac:(unfold wt; simpl; rewrite Ep, W2p, W2q; lia)).
    simpl in K. unfold wt in K. simpl in K. rewrite W2p, W2q in K. lia.
Qed.

(* ================================================================== *)
(* Part B.  Runs of the machine and trees over the canvasses.         *)
(* ================================================================== *)

Definition rg (n : nat) : list N := map N.of_nat (seq 0 n).

Lemma in_rg : forall n j, In j (rg n) <-> j < N.of_nat n.
Proof.
  intros n j. unfold rg. rewrite in_map_iff. split.
  - intros [k [Ek Hk]]. apply in_seq in Hk. lia.
  - intros H. exists (N.to_nat j). split; [lia|]. apply in_seq. lia.
Qed.

Lemma NoDup_map_seq : forall n st, NoDup (map N.of_nat (seq st n)).
Proof.
  induction n as [| n IH]; intros st; simpl; constructor; [| apply IH].
  intros F. apply in_map_iff in F. destruct F as [k [Ek Hk]].
  apply in_seq in Hk. lia.
Qed.

Lemma NoDup_rg : forall n, NoDup (rg n).
Proof. intros. apply NoDup_map_seq. Qed.

Lemma rg_S : forall m, rg (S m) = rg m ++ [N.of_nat m].
Proof. intros. unfold rg. rewrite seq_S, map_app. reflexivity. Qed.

Lemma sum_below_filter : forall (P : N -> bool) (f : N -> N) m,
  sum_below (fun i => if P i then f i else 0) m = sumL (map f (filter P (rg m))).
Proof.
  intros P f m. induction m as [| m IH]; [reflexivity|].
  simpl sum_below. rewrite rg_S, filter_app, map_app, sumL_app, IH. simpl.
  destruct (P (N.of_nat m)); simpl; lia.
Qed.

Lemma count_below_filter : forall (P : N -> bool) n,
  count_below P n = N.of_nat (List.length (filter P (rg (N.to_nat n)))).
Proof.
  intros P n. unfold count_below. generalize (N.to_nat n). intros m.
  induction m as [| m IH]; [reflexivity|].
  simpl sum_below. rewrite rg_S, filter_app, length_app, IH. simpl.
  destruct (P (N.of_nat m)); simpl; lia.
Qed.

Definition ccond (n : nat) (c : colouring) (t : tree) : Prop :=
  forall i, In i (leaves t) -> forall j, j < N.of_nat n ->
    (c j = c i <-> In j (leaves t)).

Definition classes (n : nat) (c : colouring) (Fo : list tree) : Prop :=
  Permutation (concat (map leaves Fo)) (rg n) /\ forall t, In t Fo -> ccond n c t.

Definition costs (w : N -> N) (Fo : list tree) : N := sumL (map (cost w) Fo).

Lemma perm_concat : forall Fo Fo', Permutation Fo Fo' ->
  Permutation (concat (map leaves Fo)) (concat (map leaves Fo')).
Proof.
  intros Fo Fo' H. induction H; simpl.
  - apply Permutation_refl.
  - apply Permutation_app_head. exact IHPermutation.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - eapply perm_trans; eassumption.
Qed.

Lemma costs_perm : forall w Fo Fo', Permutation Fo Fo' -> costs w Fo = costs w Fo'.
Proof. intros. unfold costs. apply sumL_perm. apply Permutation_map. exact H. Qed.

Lemma in_concat_leaves : forall F t a, In t F -> In a (leaves t) ->
  In a (concat (map leaves F)).
Proof.
  intros F t a Ht Ha. apply in_concat. exists (leaves t). split; [apply in_map; exact Ht | exact Ha].
Qed.

Lemma extract : forall F j, In j (concat (map leaves F)) ->
  exists t F', Permutation F (t :: F') /\ In j (leaves t).
Proof.
  intros F j H. apply in_concat in H. destruct H as [l [Hl Hj]].
  apply in_map_iff in Hl. destruct Hl as [t [Et Ht]]. subst l.
  destruct (in_split t F Ht) as (A & B & ->).
  exists t, (A ++ B). split; [apply Permutation_sym; apply Permutation_middle | exact Hj].
Qed.

Lemma classes_lt : forall n c Fo t a, classes n c Fo -> In t Fo -> In a (leaves t) ->
  a < N.of_nat n.
Proof.
  intros n c Fo t a [Hp _] Ht Ha. apply in_rg.
  apply (Permutation_in _ Hp). exact (in_concat_leaves _ _ _ Ht Ha).
Qed.

(* --- lower bound: a run gives a tree --- *)

Lemma transfer : forall n c c' C X Y t,
  (forall j, j < N.of_nat n -> c j = C -> c' j = X \/ c' j = Y) ->
  (forall j, j < N.of_nat n -> c j <> C -> c' j = c j /\ c j <> X /\ c j <> Y) ->
  ccond n c' t ->
  (forall a, In a (leaves t) -> a < N.of_nat n /\ ~ (c' a = X \/ c' a = Y)) ->
  ccond n c t.
Proof.
  intros n c c' C X Y t H1 H2 Hc Ha i Hi j Hj.
  destruct (Ha i Hi) as [Hin Hxi].
  assert (Ci : c i <> C) by (intro E; apply Hxi; apply H1; assumption).
  destruct (H2 i Hin Ci) as [Ei _].
  split.
  - intros E.
    assert (Cj : c j <> C) by (rewrite E; exact Ci).
    destruct (H2 j Hj Cj) as [Ej _].
    apply (Hc i Hi j Hj). rewrite Ej, Ei. exact E.
  - intros Hjt.
    destruct (Ha j Hjt) as [_ Hxj].
    assert (Cj : c j <> C) by (intro E; apply Hxj; apply H1; assumption).
    destruct (H2 j Hj Cj) as [Ej _].
    apply (Hc i Hi j Hj) in Hjt. rewrite <- Ej, <- Ei. exact Hjt.
Qed.

Lemma assemble : forall n c c' C X Y tC F,
  (forall j, j < N.of_nat n -> c j = C -> c' j = X \/ c' j = Y) ->
  (forall j, j < N.of_nat n -> c j <> C -> c' j = c j /\ c j <> X /\ c j <> Y) ->
  Permutation (leaves tC ++ concat (map leaves F)) (rg n) ->
  (forall j, j < N.of_nat n -> (In j (leaves tC) <-> c' j = X \/ c' j = Y)) ->
  (forall t, In t F -> ccond n c' t) ->
  classes n c (tC :: F).
Proof.
  intros n c c' C X Y tC F H1 H2 Hp HtC HF.
  assert (HC : forall j, j < N.of_nat n -> (c j = C <-> c' j = X \/ c' j = Y)).
  { intros j Hj. split; [apply H1; exact Hj|].
    intros Hx. destruct (N.eq_dec (c j) C) as [E | E]; [exact E|].
    destruct (H2 j Hj E) as [Ej [NX NY]]. rewrite Ej in Hx. destruct Hx; contradiction. }
  assert (Hnd : NoDup (leaves tC ++ concat (map leaves F)))
    by (apply (Permutation_NoDup (Permutation_sym Hp)); apply NoDup_rg).
  assert (Hlt : forall a, In a (leaves tC ++ concat (map leaves F)) -> a < N.of_nat n)
    by (intros a Ha; apply in_rg; apply (Permutation_in _ Hp); exact Ha).
  split; [exact Hp|].
  intros t [Et | Ht].
  - subst t. intros i Hi j Hj.
    assert (Hin : i < N.of_nat n) by (apply Hlt; apply in_or_app; left; exact Hi).
    assert (Ci : c i = C) by (apply (HC i Hin); apply (HtC i Hin); exact Hi).
    rewrite Ci, (HC j Hj), (HtC j Hj). tauto.
  - apply (transfer n c c' C X Y t H1 H2 (HF t Ht)).
    intros a Ha.
    assert (Hac : In a (concat (map leaves F))) by exact (in_concat_leaves _ _ _ Ht Ha).
    assert (Han : a < N.of_nat n) by (apply Hlt; apply in_or_app; right; exact Hac).
    split; [exact Han|].
    intros Hx. apply (HtC a Han) in Hx.
    exact (NoDup_app_disj _ _ _ Hnd Hx Hac).
Qed.

Lemma tC_perm : forall n c c' C X Y tC,
  (forall j, j < N.of_nat n -> c j = C -> c' j = X \/ c' j = Y) ->
  (forall j, j < N.of_nat n -> c j <> C -> c' j = c j /\ c j <> X /\ c j <> Y) ->
  NoDup (leaves tC) -> (forall j, In j (leaves tC) -> j < N.of_nat n) ->
  (forall j, j < N.of_nat n -> (In j (leaves tC) <-> c' j = X \/ c' j = Y)) ->
  Permutation (leaves tC) (filter (fun i => c i =? C) (rg n)).
Proof.
  intros n c c' C X Y tC H1 H2 Hnd Hlt HtC.
  apply NoDup_Permutation; [exact Hnd | apply NoDup_filter; apply NoDup_rg |].
  intros x. rewrite filter_In, in_rg, N.eqb_eq. split.
  - intros Hx. pose proof (Hlt x Hx) as Hxn. split; [exact Hxn|].
    apply (HtC x Hxn) in Hx.
    destruct (N.eq_dec (c x) C) as [E | E]; [exact E|].
    destruct (H2 x Hxn E) as [Ex [NX NY]]. rewrite Ex in Hx. destruct Hx; contradiction.
  - intros [Hxn Ex]. apply (HtC x Hxn). apply H1; assumption.
Qed.

Lemma no_witness : forall (f : N -> N) n X, existsb (fun j => f j =? X) (rg n) = false ->
  forall j, j < N.of_nat n -> f j <> X.
Proof.
  intros f n X H j Hj E.
  assert (T : existsb (fun j => f j =? X) (rg n) = true).
  { apply existsb_exists. exists j. split; [apply in_rg; exact Hj | apply N.eqb_eq; exact E]. }
  rewrite H in T. discriminate.
Qed.

Lemma lower_step : forall n c c' C X Y Fo' (sz : N -> N),
  X <> Y ->
  (forall j, j < N.of_nat n -> c j = C -> c' j = X \/ c' j = Y) ->
  (forall j, j < N.of_nat n -> c j <> C -> c' j = c j /\ c j <> X /\ c j <> Y) ->
  classes n c' Fo' ->
  exists Fo, classes n c Fo /\
    costs sz Fo <= sumL (map sz (filter (fun i => c i =? C) (rg n))) + costs sz Fo'.
Proof.
  intros n c c' C X Y Fo' sz Hxy H1 H2 Hcl.
  pose proof Hcl as [Hp Hcc].
  assert (Hnd : NoDup (concat (map leaves Fo')))
    by (apply (Permutation_NoDup (Permutation_sym Hp)); apply NoDup_rg).
  destruct (existsb (fun j => c' j =? X) (rg n)) eqn:EX;
  destruct (existsb (fun j => c' j =? Y) (rg n)) eqn:EY.
  - (* both colours present *)
    apply existsb_exists in EX. destruct EX as [iX [HiX EiX]].
    apply existsb_exists in EY. destruct EY as [iY [HiY EiY]].
    apply N.eqb_eq in EiX, EiY. apply in_rg in HiX, HiY.
    destruct (extract Fo' iX (Permutation_in _ (Permutation_sym Hp) (proj2 (in_rg _ _) HiX)))
      as (tX & F1 & P1 & HtX).
    assert (CX : ccond n c' tX) by (apply Hcc; apply (Permutation_in _ (Permutation_sym P1)); left; reflexivity).
    assert (HiY' : In iY (concat (map leaves F1))).
    { assert (H : In iY (concat (map leaves (tX :: F1))))
        by (apply (Permutation_in _ (perm_concat _ _ P1)); apply (Permutation_in _ (Permutation_sym Hp));
            apply in_rg; exact HiY).
      simpl in H. apply in_app_or in H. destruct H as [H | H]; [|exact H].
      exfalso. apply (CX iX HtX iY HiY) in H. rewrite H, EiX in EiY. apply Hxy. exact EiY. }
    destruct (extract F1 iY HiY') as (tY & F2 & P2 & HtY).
    assert (P12 : Permutation Fo' (tX :: tY :: F2)) by (eapply perm_trans; [exact P1 | apply perm_skip; exact P2]).
    assert (CY : ccond n c' tY) by (apply Hcc; apply (Permutation_in _ (Permutation_sym P12)); right; left; reflexivity).
    assert (Hp' : Permutation (leaves (Node tX tY) ++ concat (map leaves F2)) (rg n)).
    { simpl. rewrite <- app_assoc. change (leaves tX ++ leaves tY ++ concat (map leaves F2))
        with (concat (map leaves (tX :: tY :: F2))).
      eapply perm_trans; [apply perm_concat; apply Permutation_sym; exact P12 | exact Hp]. }
    assert (Hnd' : NoDup (leaves (Node tX tY) ++ concat (map leaves F2)))
      by (apply (Permutation_NoDup (Permutation_sym Hp')); apply NoDup_rg).
    assert (Hiff : forall j, j < N.of_nat n -> (In j (leaves (Node tX tY)) <-> c' j = X \/ c' j = Y)).
    { intros j Hj. simpl. rewrite in_app_iff.
      rewrite <- (CX iX HtX j Hj), <- (CY iY HtY j Hj), EiX, EiY. tauto. }
    exists (Node tX tY :: F2). split.
    + apply (assemble n c c' C X Y); auto.
      intros t Ht. apply Hcc. apply (Permutation_in _ (Permutation_sym P12)). right. right. exact Ht.
    + assert (Pc : Permutation (leaves (Node tX tY)) (filter (fun i => c i =? C) (rg n))).
      { apply (tC_perm n c c' C X Y); auto.
        - exact (NoDup_app_l _ _ Hnd').
        - intros j Hj. apply in_rg. apply (Permutation_in _ Hp'). apply in_or_app. left. exact Hj. }
      rewrite <- (sumL_perm _ _ (Permutation_map sz Pc)).
      rewrite (costs_perm sz Fo' _ P12). unfold costs. simpl. unfold wt.
      rewrite map_app, sumL_app. lia.
  - (* only X *)
    apply existsb_exists in EX. destruct EX as [iX [HiX EiX]].
    apply N.eqb_eq in EiX. apply in_rg in HiX.
    pose proof (no_witness c' n Y EY) as NY.
    destruct (extract Fo' iX (Permutation_in _ (Permutation_sym Hp) (proj2 (in_rg _ _) HiX)))
      as (tX & F1 & P1 & HtX).
    assert (CX : ccond n c' tX) by (apply Hcc; apply (Permutation_in _ (Permutation_sym P1)); left; reflexivity).
    exists (tX :: F1). split.
    + apply (assemble n c c' C X Y); auto.
      * eapply perm_trans; [apply (perm_concat _ _ (Permutation_sym P1)) | exact Hp].
      * intros j Hj. rewrite <- (CX iX HtX j Hj), EiX.
        split; [tauto|]. intros [E | E]; [exact E | exfalso; exact (NY j Hj E)].
      * intros t Ht. apply Hcc. apply (Permutation_in _ (Permutation_sym P1)). right. exact Ht.
    + rewrite <- (costs_perm sz _ _ P1). lia.
  - (* only Y *)
    apply existsb_exists in EY. destruct EY as [iY [HiY EiY]].
    apply N.eqb_eq in EiY. apply in_rg in HiY.
    pose proof (no_witness c' n X EX) as NX.
    destruct (extract Fo' iY (Permutation_in _ (Permutation_sym Hp) (proj2 (in_rg _ _) HiY)))
      as (tY & F1 & P1 & HtY).
    assert (CY : ccond n c' tY) by (apply Hcc; apply (Permutation_in _ (Permutation_sym P1)); left; reflexivity).
    exists (tY :: F1). split.
    + apply (assemble n c c' C X Y); auto.
      * eapply perm_trans; [apply (perm_concat _ _ (Permutation_sym P1)) | exact Hp].
      * intros j Hj. rewrite <- (CY iY HtY j Hj), EiY.
        split; [tauto|]. intros [E | E]; [exfalso; exact (NX j Hj E) | exact E].
      * intros t Ht. apply Hcc. apply (Permutation_in _ (Permutation_sym P1)). right. exact Ht.
    + rewrite <- (costs_perm sz _ _ P1). lia.
  - (* neither *)
    pose proof (no_witness c' n X EX) as NX.
    pose proof (no_witness c' n Y EY) as NY.
    exists Fo'. split; [|lia].
    split; [exact Hp|].
    intros t Ht. apply (transfer n c c' C X Y t H1 H2 (Hcc t Ht)).
    intros a Ha. pose proof (classes_lt n c' Fo' t a Hcl Ht Ha) as Han.
    split; [exact Han|]. intros [E | E]; [exact (NX a Han E) | exact (NY a Han E)].
Qed.

Lemma concat_leaves_map_Leaf : forall l, concat (map leaves (map Leaf l)) = l.
Proof. induction l; simpl; [reflexivity | rewrite IHl; reflexivity]. Qed.

Lemma costs_map_Leaf : forall w l, costs w (map Leaf l) = 0.
Proof. intros w l. unfold costs. induction l; simpl; [reflexivity | exact IHl]. Qed.

Lemma paints_lower : forall s pos used c k, paints s pos used c k ->
  (forall i, i < len s -> used (c i)) ->
  exists Fo, classes (List.length s) c Fo /\ costs (Prelude.size s) Fo <= k.
Proof.
  intros s pos used c k H. induction H as [used c Hd | used c C F X Y k Hnd HF Hxy HX HY Hp IH];
    intros Hu.
  - exists (map Leaf (rg (List.length s))). split; [split|].
    + rewrite concat_leaves_map_Leaf. apply Permutation_refl.
    + intros t Ht. apply in_map_iff in Ht. destruct Ht as [i [Et Hi]]. subst t.
      intros i' Hi' j Hj. simpl in Hi'. destruct Hi' as [E | []]. subst i'.
      simpl. split.
      * intros E. destruct (N.eq_dec i j) as [D | D]; [left; exact D|].
        exfalso. apply in_rg in Hi. unfold len in Hd. exact (Hd j i Hj Hi (fun F => D (eq_sym F)) E).
      * intros [E | []]. subst. reflexivity.
    + rewrite costs_map_Leaf. lia.
  - destruct IH as [Fo' [Hcl Hc]].
    { intros i Hi. unfold repaint. destruct (c i =? C); [destruct (_ <? F)|]; auto. }
    destruct (lower_step (List.length s) c (repaint (len s) pos c C F X Y) C X Y Fo' (Prelude.size s) Hxy)
      as [Fo [HFo Hcost]]; [| | exact Hcl |].
    + intros j Hj E. unfold repaint. rewrite (proj2 (N.eqb_eq _ _) E).
      destruct (_ <? F); auto.
    + intros j Hj E. unfold repaint. rewrite (proj2 (N.eqb_neq _ _) E).
      split; [reflexivity|]. split; intro F'; [apply HX | apply HY]; rewrite <- F'; apply Hu; exact Hj.
    + exists Fo. split; [exact HFo|].
      unfold step_ink. rewrite sum_below_filter. lia.
Qed.

Lemma ink_lower : forall s k, 1 <= len s -> ink_spent s k ->
  exists t, Permutation (leaves t) (rg (List.length s)) /\ cost (Prelude.size s) t <= k.
Proof.
  intros s k Hn [pos [_ Hp]].
  destruct (paints_lower s pos _ _ _ Hp ltac:(intros; reflexivity)) as [Fo [[HP Hc] Hk]].
  unfold len in Hn.
  destruct Fo as [| t F].
  - simpl in HP. apply Permutation_length in HP. unfold rg in HP.
    rewrite length_map, length_seq in HP. simpl in HP. lia.
  - assert (Hall : forall j, j < N.of_nat (List.length s) -> In j (leaves t)).
    { destruct (leaves_nonempty t) as [a Ha]. intros j Hj.
      apply (Hc t (or_introl eq_refl) a Ha j Hj). reflexivity. }
    destruct F as [| t' F].
    + exists t. simpl in HP. rewrite app_nil_r in HP. split; [exact HP|].
      unfold costs in Hk. simpl in Hk. lia.
    + exfalso. destruct (leaves_nonempty t') as [a Ha].
      assert (Hnd : NoDup (concat (map leaves (t :: t' :: F))))
        by (apply (Permutation_NoDup (Permutation_sym HP)); apply NoDup_rg).
      simpl in Hnd.
      assert (Han : a < N.of_nat (List.length s)).
      { apply in_rg. apply (Permutation_in _ HP). simpl. apply in_or_app. right. apply in_or_app. left. exact Ha. }
      apply (NoDup_app_disj _ _ a Hnd (Hall a Han)). apply in_or_app. left. exact Ha.
Qed.

(* --- upper bound: a tree gives a run --- *)

Fixpoint ordered (pos : N -> N) (t : tree) : Prop :=
  match t with
  | Leaf _ => True
  | Node l r => ordered pos l /\ ordered pos r /\
      forall i j, In i (leaves l) -> In j (leaves r) -> pos i < pos j
  end.

Fixpoint nodes (t : tree) : nat :=
  match t with Leaf _ => O | Node l r => S (nodes l + nodes r) end.

Fixpoint nodesF (Fo : list tree) : nat :=
  match Fo with [] => O | t :: F => (nodes t + nodesF F)%nat end.

Lemma nodesF_app : forall A B, nodesF (A ++ B) = (nodesF A + nodesF B)%nat.
Proof. induction A; intros; simpl; [reflexivity | rewrite IHA; lia]. Qed.

Definition isNode (t : tree) : bool := match t with Leaf _ => false | Node _ _ => true end.

Lemma costs_leaves : forall w Fo, (forall t, In t Fo -> isNode t = false) -> costs w Fo = 0.
Proof.
  intros w Fo. unfold costs. induction Fo as [| t F IH]; intros H; simpl; [reflexivity|].
  destruct t as [x | l r]; [| discriminate (H _ (or_introl eq_refl))].
  simpl. apply IH. intros; apply H; right; assumption.
Qed.

Lemma paints_used_mono : forall s pos used c k, paints s pos used c k ->
  forall used' : N -> Prop, (forall z, used' z -> used z) -> paints s pos used' c k.
Proof.
  intros s pos used c k H. induction H as [used c Hd | used c C F X Y k Hnd HF Hxy HX HY Hp IH];
    intros used' Hu.
  - apply paints_done. exact Hd.
  - apply (paints_step _ _ _ _ C F X Y);
      [exact Hnd | exact HF | exact Hxy | intro H; apply HX; apply Hu; exact H
      | intro H; apply HY; apply Hu; exact H |].
    apply IH. intros z [Hz | Hz]; [left; apply Hu; exact Hz | right; exact Hz].
Qed.

Lemma paints_upper : forall s pos (m : nat) Fo c used bound,
  nodesF Fo = m ->
  classes (List.length s) c Fo ->
  (forall t, In t Fo -> ordered pos t) ->
  (forall z, used z -> z < bound) ->
  (forall i, i < len s -> c i < bound) ->
  paints s pos used c (costs (Prelude.size s) Fo).
Proof.
  intros s pos m. induction m as [m IH] using (well_founded_induction lt_wf).
  intros Fo c used bound Hm Hcl Hord Hused Hcb.
  set (n := List.length s) in *.
  assert (Hlen : len s = N.of_nat n) by reflexivity.
  pose proof Hcl as [Hp Hcc].
  assert (HndF : NoDup (concat (map leaves Fo)))
    by (apply (Permutation_NoDup (Permutation_sym Hp)); apply NoDup_rg).
  destruct (existsb isNode Fo) eqn:EN.
  2:{ (* only leaves left: all colours distinct *)
    assert (HL : forall t, In t Fo -> isNode t = false).
    { intros t Ht. destruct (isNode t) eqn:E; [|reflexivity].
      assert (T : existsb isNode Fo = true) by (apply existsb_exists; exists t; auto).
      rewrite EN in T. discriminate. }
    rewrite (costs_leaves _ _ HL). apply paints_done.
    intros i j Hi Hj Hij E. rewrite Hlen in Hi, Hj.
    destruct (extract Fo i (Permutation_in _ (Permutation_sym Hp) (proj2 (in_rg _ _) Hi)))
      as (t & F' & P & Ht).
    assert (Ht' : In t Fo) by (apply (Permutation_in _ (Permutation_sym P)); left; reflexivity).
    pose proof (HL t Ht') as Lt. destruct t as [a | l r]; [| discriminate].
    pose proof (proj1 (Hcc _ Ht' i Ht j Hj) (eq_sym E)) as Hj'.
    simpl in Ht, Hj'. destruct Ht as [Ht | []]. destruct Hj' as [Hj' | []]. subst.
    apply Hij. reflexivity. }
  apply existsb_exists in EN. destruct EN as [T [HT ET]].
  destruct T as [x | t1 t2]; [discriminate|].
  destruct (in_split _ _ HT) as (A & B & EFo).
  set (Fo1 := A ++ B).
  assert (HP : Permutation Fo (Node t1 t2 :: Fo1))
    by (rewrite EFo; apply Permutation_sym; apply Permutation_middle).
  assert (HndT : NoDup (leaves (Node t1 t2) ++ concat (map leaves Fo1))).
  { apply (Permutation_NoDup (perm_concat _ _ HP)). exact HndF. }
  assert (Hnd12 : NoDup (leaves t1 ++ leaves t2)) by exact (NoDup_app_l _ _ HndT).
  assert (Hlt : forall j, In j (leaves (Node t1 t2)) -> j < N.of_nat n)
    by (intros j Hj; exact (classes_lt _ _ _ _ _ Hcl HT Hj)).
  destruct (leaves_nonempty t1) as [i0 Hi0].
  destruct (leaves_nonempty t2) as [j0 Hj0].
  assert (Hi0T : In i0 (leaves (Node t1 t2))) by (simpl; apply in_or_app; left; exact Hi0).
  assert (Hj0T : In j0 (leaves (Node t1 t2))) by (simpl; apply in_or_app; right; exact Hj0).
  set (C := c i0).
  assert (HCT : forall j, j < N.of_nat n -> (c j = C <-> In j (leaves (Node t1 t2))))
    by (intros j Hj; exact (Hcc _ HT i0 Hi0T j Hj)).
  destruct (Hord _ HT) as [Ho1 [Ho2 Ho12]].
  set (F := N.of_nat (List.length (leaves t1))).
  set (X := bound). set (Y := bound + 1).
  assert (Pf : Permutation (filter (fun i => c i =? C) (rg n)) (leaves (Node t1 t2))).
  { apply NoDup_Permutation; [apply NoDup_filter; apply NoDup_rg | exact Hnd12 |].
    intros x. rewrite filter_In, in_rg, N.eqb_eq. split.
    - intros [Hx Ex]. apply (HCT x Hx). exact Ex.
    - intros Hx. pose proof (Hlt x Hx) as Hxn. split; [exact Hxn|]. apply (HCT x Hxn). exact Hx. }
  assert (LT1 : forall j, In j (leaves t1) -> left_of (len s) pos c C j < F).
  { intros j Hj. unfold left_of. rewrite count_below_filter, Hlen, Nat2N.id.
    destruct (in_split _ _ Hj) as (u & v & Euv).
    assert (Hinc : incl (filter (fun k => (c k =? C) && (pos k <? pos j)) (rg n)) (u ++ v)).
    { intros k Hk. apply filter_In in Hk. destruct Hk as [Hk Ek].
      apply andb_prop in Ek. destruct Ek as [Ek Pk].
      apply N.eqb_eq in Ek. apply N.ltb_lt in Pk. apply in_rg in Hk.
      apply (HCT k Hk) in Ek. simpl in Ek. apply in_app_or in Ek.
      destruct Ek as [Ek | Ek].
      - rewrite Euv in Ek. apply in_app_or in Ek. apply in_or_app.
        destruct Ek as [Ek | [Ek | Ek]]; auto. subst. lia.
      - pose proof (Ho12 j k Hj Ek). lia. }
    apply NoDup_incl_length in Hinc; [| apply NoDup_filter; apply NoDup_rg].
    unfold F. rewrite Euv. rewrite length_app in Hinc |- *. simpl. lia. }
  assert (LT2 : forall j, In j (leaves t2) -> F <= left_of (len s) pos c C j).
  { intros j Hj. unfold left_of. rewrite count_below_filter, Hlen, Nat2N.id.
    assert (Hinc : incl (leaves t1) (filter (fun k => (c k =? C) && (pos k <? pos j)) (rg n))).
    { intros k Hk. apply filter_In.
      assert (HkT : In k (leaves (Node t1 t2))) by (simpl; apply in_or_app; left; exact Hk).
      pose proof (Hlt k HkT) as Hkn. split; [apply in_rg; exact Hkn|].
      apply andb_true_intro. split.
      - apply N.eqb_eq. apply (HCT k Hkn). exact HkT.
      - apply N.ltb_lt. apply Ho12; assumption. }
    apply NoDup_incl_length in Hinc; [| exact (NoDup_app_l _ _ Hnd12)].
    unfold F. lia. }
  set (c' := repaint (len s) pos c C F X Y).
  assert (X1 : forall j, In j (leaves t1) -> c' j = X).
  { intros j Hj. unfold c', repaint.
    assert (HjT : In j (leaves (Node t1 t2))) by (simpl; apply in_or_app; left; exact Hj).
    rewrite (proj2 (N.eqb_eq _ _) (proj2 (HCT j (Hlt j HjT)) HjT)).
    rewrite (proj2 (N.ltb_lt _ _) (LT1 j Hj)). reflexivity. }
  assert (Y2 : forall j, In j (leaves t2) -> c' j = Y).
  { intros j Hj. unfold c', repaint.
    assert (HjT : In j (leaves (Node t1 t2))) by (simpl; apply in_or_app; right; exact Hj).
    rewrite (proj2 (N.eqb_eq _ _) (proj2 (HCT j (Hlt j HjT)) HjT)).
    rewrite (proj2 (N.ltb_ge _ _) (LT2 j Hj)). reflexivity. }
  assert (Z3 : forall j, j < N.of_nat n -> ~ In j (leaves (Node t1 t2)) -> c' j = c j /\ c j <> C).
  { intros j Hj Hn. assert (Cj : c j <> C) by (intro E; apply Hn; apply (HCT j Hj); exact E).
    split; [|exact Cj]. unfold c', repaint. rewrite (proj2 (N.eqb_neq _ _) Cj). reflexivity. }
  assert (Hcb' : forall j, j < N.of_nat n -> c' j < bound + 2).
  { intros j Hj. destruct (In_dec N.eq_dec j (leaves (Node t1 t2))) as [H | H].
    - simpl in H. apply in_app_or in H. destruct H as [H | H];
        [rewrite (X1 j H) | rewrite (Y2 j H)]; unfold X, Y; lia.
    - rewrite (proj1 (Z3 j Hj H)). rewrite <- Hlen in Hj. specialize (Hcb j Hj). lia. }
  assert (Hcl' : classes n c' (t1 :: t2 :: Fo1)).
  { split.
    - eapply perm_trans; [| exact Hp].
      eapply perm_trans; [| apply perm_concat; apply Permutation_sym; exact HP].
      simpl. rewrite app_assoc. apply Permutation_refl.
    - intros t Ht j' Hj' j Hj.
      destruct Ht as [Et | [Et | Ht]].
      + subst t. rewrite (X1 j' Hj'). split; [|apply X1].
        intros E. destruct (In_dec N.eq_dec j (leaves (Node t1 t2))) as [H | H].
        * simpl in H. apply in_app_or in H. destruct H as [H | H]; [exact H|].
          rewrite (Y2 j H) in E. unfold X, Y in E. lia.
        * exfalso. rewrite (proj1 (Z3 j Hj H)) in E. rewrite <- Hlen in Hj.
          specialize (Hcb j Hj). unfold X in E. lia.
      + subst t. rewrite (Y2 j' Hj'). split; [|apply Y2].
        intros E. destruct (In_dec N.eq_dec j (leaves (Node t1 t2))) as [H | H].
        * simpl in H. apply in_app_or in H. destruct H as [H | H]; [|exact H].
          rewrite (X1 j H) in E. unfold X, Y in E. lia.
        * exfalso. rewrite (proj1 (Z3 j Hj H)) in E. rewrite <- Hlen in Hj.
          specialize (Hcb j Hj). unfold Y in E. lia.
      + assert (Ht' : In t Fo) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact Ht).
        assert (Hj'c : In j' (concat (map leaves Fo1))) by exact (in_concat_leaves _ _ _ Ht Hj').
        assert (Hj'n : j' < N.of_nat n) by exact (classes_lt _ _ _ _ _ Hcl Ht' Hj').
        assert (Hj'T : ~ In j' (leaves (Node t1 t2)))
          by (intro F'; exact (NoDup_app_disj _ _ _ HndT F' Hj'c)).
        destruct (Z3 j' Hj'n Hj'T) as [E' _]. rewrite E'.
        assert (Hb' : c j' < bound) by (apply Hcb; rewrite Hlen; exact Hj'n).
        destruct (In_dec N.eq_dec j (leaves (Node t1 t2))) as [H | H].
        * split.
          -- intros E. exfalso. simpl in H. apply in_app_or in H.
             destruct H as [H | H]; [rewrite (X1 j H) in E | rewrite (Y2 j H) in E];
               unfold X, Y in E; lia.
          -- intros Hjt. exfalso.
             exact (NoDup_app_disj _ _ _ HndT H (in_concat_leaves _ _ _ Ht Hjt)).
        * rewrite (proj1 (Z3 j Hj H)). exact (Hcc t Ht' j' Hj' j Hj). }
  assert (Hrun : paints s pos (fun z => used z \/ z = X \/ z = Y) c'
                   (costs (Prelude.size s) (t1 :: t2 :: Fo1))).
  { apply (IH (nodesF (t1 :: t2 :: Fo1))) with (bound := bound + 2).
    - rewrite <- Hm, EFo, nodesF_app. simpl. unfold Fo1. rewrite nodesF_app. lia.
    - reflexivity.
    - exact Hcl'.
    - intros t [Et | [Et | Ht]]; [subst; exact Ho1 | subst; exact Ho2 |].
      apply Hord. apply (Permutation_in _ (Permutation_sym HP)). right. exact Ht.
    - intros z [Hz | [Hz | Hz]]; [specialize (Hused z Hz); lia | unfold X in Hz; lia | unfold Y in Hz; lia].
    - intros i Hi. rewrite Hlen in Hi. exact (Hcb' i Hi). }
  replace (costs (Prelude.size s) Fo)
    with (step_ink s c C + costs (Prelude.size s) (t1 :: t2 :: Fo1)).
  - apply (paints_step _ _ _ _ C F X Y); [| | unfold X, Y; lia | intro H; specialize (Hused X H); unfold X in *; lia
                         | intro H; specialize (Hused Y H); unfold Y in *; lia | exact Hrun].
    + intros Hd. apply (Hd i0 j0).
      * rewrite Hlen. apply Hlt. exact Hi0T.
      * rewrite Hlen. apply Hlt. exact Hj0T.
      * intro E. subst j0. exact (NoDup_app_disj _ _ _ Hnd12 Hi0 Hj0).
      * symmetry. apply (HCT j0 (Hlt j0 Hj0T)). exact Hj0T.
    + unfold count_colour. rewrite count_below_filter, Hlen, Nat2N.id.
      rewrite (Permutation_length Pf). simpl. rewrite length_app.
      unfold F. destruct (leaves t2) as [| ? ?]; [destruct Hj0 | simpl; lia].
  - rewrite (costs_perm _ _ _ HP). unfold step_ink. rewrite sum_below_filter.
    fold n. rewrite (sumL_perm _ _ (Permutation_map (Prelude.size s) Pf)).
    unfold costs. simpl. unfold wt. rewrite map_app, sumL_app. lia.
Qed.

(* --- the belt order of a tree: its leaves from left to right --- *)

Fixpoint idx (x : N) (l : list N) : N :=
  match l with [] => 0 | y :: r => if N.eqb x y then 0 else 1 + idx x r end.

Definition before (l : list N) (i j : N) : Prop :=
  exists u v, l = u ++ i :: v /\ In j v.

Lemma ordered_before : forall pos t,
  (forall i j, before (leaves t) i j -> pos i < pos j) -> ordered pos t.
Proof.
  intros pos t. induction t as [x | l IHl r IHr]; intros H; simpl; [exact I|].
  split; [|split].
  - apply IHl. intros i j (u & v & E & Hj). apply H. simpl.
    exists u, (v ++ leaves r). split; [rewrite E, <- app_assoc; reflexivity | apply in_or_app; left; exact Hj].
  - apply IHr. intros i j (u & v & E & Hj). apply H. simpl.
    exists (leaves l ++ u), v. split; [rewrite E, <- app_assoc; reflexivity | exact Hj].
  - intros i j Hi Hj. apply H. simpl. destruct (in_split _ _ Hi) as (u & v & E).
    exists u, (v ++ leaves r). split; [rewrite E, <- app_assoc; reflexivity | apply in_or_app; right; exact Hj].
Qed.

Lemma idx_before : forall l i j, NoDup l -> before l i j -> idx i l < idx j l.
Proof.
  intros l i j Hnd (u & v & E & Hj). subst l. revert Hnd.
  induction u as [| a u IH]; intros Hnd; cbn [idx app].
  - rewrite N.eqb_refl. inversion Hnd; subst.
    assert (D : j <> i) by (intro F; subst; contradiction).
    rewrite (proj2 (N.eqb_neq _ _) D). lia.
  - inversion Hnd; subst.
    assert (Di : i <> a) by (intro F; subst; apply H1; apply in_or_app; right; left; reflexivity).
    assert (Dj : j <> a) by (intro F; subst; apply H1; apply in_or_app; right; right; exact Hj).
    rewrite (proj2 (N.eqb_neq _ _) Di), (proj2 (N.eqb_neq _ _) Dj).
    specialize (IH H2). lia.
Qed.

Lemma idx_inj : forall l i j, In i l -> In j l -> idx i l = idx j l -> i = j.
Proof.
  induction l as [| y r IH]; intros i j Hi Hj E; [destruct Hi|]. cbn [idx] in E.
  destruct (N.eqb_spec i y) as [Ei | Ei], (N.eqb_spec j y) as [Ej | Ej].
  - subst. reflexivity.
  - lia.
  - lia.
  - destruct Hi as [Hi | Hi]; [subst; contradiction|].
    destruct Hj as [Hj | Hj]; [subst; contradiction|].
    apply IH; auto. lia.
Qed.

Lemma ink_upper : forall s t, Permutation (leaves t) (rg (List.length s)) ->
  ink_spent s (cost (Prelude.size s) t).
Proof.
  intros s t Hp.
  assert (Hnd : NoDup (leaves t)) by (apply (Permutation_NoDup (Permutation_sym Hp)); apply NoDup_rg).
  exists (fun i => idx i (leaves t)). split.
  - intros i j Hi Hj E. unfold len in Hi, Hj.
    apply (idx_inj (leaves t)); auto;
      apply (Permutation_in _ (Permutation_sym Hp)); apply in_rg; assumption.
  - replace (cost (Prelude.size s) t) with (costs (Prelude.size s) [t])
      by (unfold costs; simpl; lia).
    apply (paints_upper s _ (nodesF [t]) [t] _ _ 1); [reflexivity | | | |].
    + split.
      * simpl. rewrite app_nil_r. exact Hp.
      * intros t' [Et | []]. subst t'. intros i Hi j Hj. split; [|reflexivity].
        intros _. apply (Permutation_in _ (Permutation_sym Hp)). apply in_rg. exact Hj.
    + intros t' [Et | []]. subst t'. apply ordered_before.
      intros i j Hb. apply idx_before; assumption.
    + intros z Hz. rewrite Hz. unfold white. lia.
    + intros i _. unfold white. lia.
Qed.

(* The characterisation used by the main proof. *)
Lemma canvas_char : forall s r, valid_input s ->
  (exists t, Permutation (leaves t) (rg (List.length s)) /\ cost (Prelude.size s) t = r) ->
  (forall t, Permutation (leaves t) (rg (List.length s)) -> r <= cost (Prelude.size s) t) ->
  canvas_spec s r.
Proof.
  intros s r Hv [t [Ht Ec]] Hlow. split.
  - rewrite <- Ec. apply ink_upper. exact Ht.
  - intros k Hk. destruct Hv as [Hn _].
    destruct (ink_lower s k ltac:(lia) Hk) as [t' [Ht' Hc]].
    specialize (Hlow t' Ht'). lia.
Qed.

(* --- the invariants of the greedy loop, on the multiset M of the heap --- *)

(* Upper side: a forest whose weights are M, over all canvasses, of cost acc. *)
Definition UB (s M : list N) (acc : N) : Prop :=
  exists Fo, Permutation (map (wt (Prelude.size s)) Fo) M /\
    Permutation (concat (map leaves Fo)) (rg (List.length s)) /\
    costs (Prelude.size s) Fo = acc.

(* Lower side: every tree over s costs at least acc plus some tree over M. *)
Definition LB (s M : list N) (acc : N) : Prop :=
  forall t w, NoDup (leaves t) -> Permutation (map w (leaves t)) s ->
    exists t' w', NoDup (leaves t') /\ Permutation (map w' (leaves t')) M /\
      acc + cost w' t' <= cost w t.

Definition Final (s : list N) (r : N) : Prop :=
  (exists t, Permutation (leaves t) (rg (List.length s)) /\ cost (Prelude.size s) t = r) /\
  (forall t, Permutation (leaves t) (rg (List.length s)) -> r <= cost (Prelude.size s) t).

Lemma UB_perm : forall s M M' acc, Permutation M M' -> UB s M acc -> UB s M' acc.
Proof.
  intros s M M' acc P [Fo [H1 [H2 H3]]]. exists Fo. split; [|split]; auto.
  eapply perm_trans; eassumption.
Qed.

Lemma LB_perm : forall s M M' acc, Permutation M M' -> LB s M acc -> LB s M' acc.
Proof.
  intros s M M' acc P H t w H1 H2. destruct (H t w H1 H2) as (t' & w' & A & B & C).
  exists t', w'. split; [|split]; auto. eapply perm_trans; eassumption.
Qed.

Lemma perm_map_inv : forall (f : tree -> N) F a X, Permutation (map f F) (a :: X) ->
  exists t F', Permutation F (t :: F') /\ f t = a /\ Permutation (map f F') X.
Proof.
  intros f F a X H.
  assert (Ha : In a (map f F)) by (apply (Permutation_in _ (Permutation_sym H)); left; reflexivity).
  apply in_map_iff in Ha. destruct Ha as [t [Et Ht]].
  destruct (in_split _ _ Ht) as (A & B & ->).
  exists t, (A ++ B). split; [apply Permutation_sym; apply Permutation_middle|]. split; [exact Et|].
  rewrite map_app in H |- *. simpl in H. rewrite Et in H.
  apply Permutation_sym in H. apply Permutation_cons_app_inv in H. apply Permutation_sym. exact H.
Qed.

Lemma UB_step : forall s M acc a b R, UB s M acc -> Permutation M (a :: b :: R) ->
  UB s ((a + b) :: R) (acc + (a + b)).
Proof.
  intros s M acc a b R [Fo [H1 [H2 H3]]] P.
  destruct (perm_map_inv _ Fo a (b :: R) (perm_trans H1 P)) as (ta & F1 & Pa & Ea & Ha).
  destruct (perm_map_inv _ F1 b R Ha) as (tb & F2 & Pb & Eb & Hb).
  assert (P2 : Permutation Fo (ta :: tb :: F2)) by (eapply perm_trans; [exact Pa | apply perm_skip; exact Pb]).
  exists (Node ta tb :: F2). split; [|split].
  - simpl. unfold wt at 1. simpl. rewrite map_app, sumL_app. fold (wt (Prelude.size s) ta).
    fold (wt (Prelude.size s) tb). rewrite Ea, Eb. apply perm_skip. exact Hb.
  - eapply perm_trans; [| exact H2]. eapply perm_trans; [| apply perm_concat; apply Permutation_sym; exact P2].
    simpl. rewrite app_assoc. apply Permutation_refl.
  - rewrite <- H3, (costs_perm _ _ _ P2). unfold costs. simpl. rewrite Ea, Eb. lia.
Qed.

Lemma LB_step : forall s M acc a b R, LB s M acc -> Permutation M (a :: b :: R) ->
  (forall x, In x (b :: R) -> a <= x) -> (forall x, In x R -> b <= x) ->
  LB s ((a + b) :: R) (acc + (a + b)).
Proof.
  intros s M acc a b R H P Ha Hb t w H1 H2.
  destruct (H t w H1 H2) as (t' & w' & N' & P' & C').
  destruct (huff_key t' w' a b R N' (perm_trans P' P) Ha Hb) as (t'' & w'' & N'' & P'' & C'').
  exists t'', w''. split; [exact N''|]. split; [exact P''|]. lia.
Qed.

Lemma map_nth_seq_self : forall (l : list N) d,
  map (fun k => nth k l d) (seq 0 (List.length l)) = l.
Proof.
  induction l as [| a l IH]; intros d; [reflexivity|].
  simpl. f_equal. rewrite <- seq_shift, map_map. simpl. apply IH.
Qed.

Lemma map_size_rg : forall s, map (Prelude.size s) (rg (List.length s)) = s.
Proof.
  intros s. unfold rg. rewrite map_map.
  rewrite <- (map_nth_seq_self s 0) at 2. apply map_ext. intros k.
  unfold Prelude.size. rewrite Nat2N.id. reflexivity.
Qed.

Lemma Final_of : forall s r acc, UB s [r] acc -> LB s [r] acc -> Final s acc.
Proof.
  intros s r acc [Fo [H1 [H2 H3]]] HL. split.
  - destruct Fo as [| T [| T' F]].
    + apply Permutation_length in H1. discriminate.
    + exists T. simpl in H2. rewrite app_nil_r in H2. split; [exact H2|].
      rewrite <- H3. unfold costs. simpl. lia.
    + apply Permutation_length in H1. discriminate.
  - intros t Ht.
    assert (Nt : NoDup (leaves t)) by (apply (Permutation_NoDup (Permutation_sym Ht)); apply NoDup_rg).
    destruct (HL t (Prelude.size s) Nt) as (t' & w' & _ & P' & C').
    { rewrite <- (map_size_rg s) at 2. apply Permutation_map. exact Ht. }
    destruct t' as [x | l r'].
    + simpl in C'. lia.
    + apply Permutation_length in P'. simpl in P'. rewrite length_map, length_app in P'.
      destruct (leaves_nonempty l) as [u Hu]. destruct (leaves_nonempty r') as [v Hv].
      destruct (leaves l); [destruct Hu|]. destruct (leaves r'); [destruct Hv|].
      simpl in P'. lia.
Qed.

Lemma UB_init : forall s, UB s s 0.
Proof.
  intros s. exists (map Leaf (rg (List.length s))). split; [|split].
  - rewrite map_map. unfold wt. simpl.
    rewrite <- (map_size_rg s) at 2. rewrite (map_ext _ (Prelude.size s)) by (intros; lia).
    apply Permutation_refl.
  - rewrite concat_leaves_map_Leaf. apply Permutation_refl.
  - apply costs_map_Leaf.
Qed.

Lemma LB_init : forall s, LB s s 0.
Proof.
  intros s t w H1 H2. exists t, w. split; [exact H1|]. split; [exact H2|]. lia.
Qed.

Lemma sumL_bound : forall (l : list N) B, Forall (fun x => x <= B) l ->
  sumL l <= N.of_nat (List.length l) * B.
Proof.
  intros l B H. induction H; cbn [sumL List.length]; [lia|].
  rewrite Nat2N.inj_succ. nia.
Qed.

Lemma le_sumL : forall l x, In x l -> x <= sumL l.
Proof.
  induction l as [| a l IH]; intros x H; [destruct H|]. simpl.
  destruct H as [E | H]; [subst; lia | specialize (IH x H); lia].
Qed.

Close Scope N_scope.

(* ================================================================== *)
(* Part C.  The program: Huffman's greedy algorithm on a binary        *)
(* min-heap kept in one flat array.                                    *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition meas (i : int) : Z := (wB - (φ i))%Z.

Lemma dec_meas : forall b i m, (b && (i <? m)) = true -> Zwf 0 (meas m) (meas i).
Proof.
  intros b i m H. apply andb_prop in H. destruct H as [_ H].
  rewrite ltb_spec in H. pose proof (to_Z_bounded m). pose proof (to_Z_bounded i).
  unfold Zwf, meas. lia.
Qed.

Lemma dec_pred : forall j k, (j <? k) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros j k H. rewrite ltb_spec in H. pose proof (to_Z_bounded j).
  assert ((φ (k - 1)) = (φ k) - 1)%Z by sia. unfold Zwf. lia.
Qed.

(* Sift the value at i down the heap h.[0 .. sz-1]. *)
Fixpoint sift (h : array int) (sz i : int) (H : Acc (Zwf 0) (meas i)) {struct H}
    : array int :=
  let x := h.[i] in
  let l := 2 * i + 1 in
  if l <? sz then
    let yl := h.[l] in
    let r := l + 1 in
    if (r <? sz) && (h.[r] <? yl) then
      let yr := h.[r] in
      match bdec ((yr <? x) && (i <? r)) with
      | left Hd => sift (h.[i <- yr].[r <- x]) sz r (Acc_inv H (dec_meas _ i r Hd))
      | right _ => h
      end
    else
      match bdec ((yl <? x) && (i <? l)) with
      | left Hd => sift (h.[i <- yl].[l <- x]) sz l (Acc_inv H (dec_meas _ i l Hd))
      | right _ => h
      end
  else h.

Lemma sift_eq : forall h sz i H, sift h sz i H =
  let x := h.[i] in
  let l := 2 * i + 1 in
  if l <? sz then
    let yl := h.[l] in
    let r := l + 1 in
    if (r <? sz) && (h.[r] <? yl) then
      let yr := h.[r] in
      match bdec ((yr <? x) && (i <? r)) with
      | left Hd => sift (h.[i <- yr].[r <- x]) sz r (Acc_inv H (dec_meas _ i r Hd))
      | right _ => h
      end
    else
      match bdec ((yl <? x) && (i <? l)) with
      | left Hd => sift (h.[i <- yl].[l <- x]) sz l (Acc_inv H (dec_meas _ i l Hd))
      | right _ => h
      end
  else h.
Proof. intros. destruct H. reflexivity. Qed.

(* Heapify: sift k-1, k-2, ..., 0. *)
Fixpoint build (h : array int) (sz k : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : array int :=
  match bdec (0 <? k) with
  | left Hk => build (sift h sz (k - 1) (Zwf_well_founded 0 (meas (k - 1)))) sz (k - 1)
                 (Acc_inv H (dec_pred 0 k Hk))
  | right _ => h
  end.

Lemma build_eq : forall h sz k H, build h sz k H =
  match bdec (0 <? k) with
  | left Hk => build (sift h sz (k - 1) (Zwf_well_founded 0 (meas (k - 1)))) sz (k - 1)
                 (Acc_inv H (dec_pred 0 k Hk))
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The greedy loop: pop the lightest group a, replace the next lightest b
   by a + b, add a + b to the total. *)
Fixpoint huff (h : array int) (sz acc : int) (H : Acc (Zwf 0) (φ sz)) {struct H} : int :=
  match bdec (1 <? sz) with
  | left Hs =>
      let a := h.[0] in
      let sz1 := sz - 1 in
      let h1 := sift (h.[0 <- h.[sz1]]) sz1 0 (Zwf_well_founded 0 (meas 0)) in
      let b := h1.[0] in
      let h2 := sift (h1.[0 <- a + b]) sz1 0 (Zwf_well_founded 0 (meas 0)) in
      huff h2 sz1 (acc + (a + b)) (Acc_inv H (dec_pred 1 sz Hs))
  | right _ => acc
  end.

Lemma huff_eq : forall h sz acc H, huff h sz acc H =
  match bdec (1 <? sz) with
  | left Hs =>
      let a := h.[0] in
      let sz1 := sz - 1 in
      let h1 := sift (h.[0 <- h.[sz1]]) sz1 0 (Zwf_well_founded 0 (meas 0)) in
      let b := h1.[0] in
      let h2 := sift (h1.[0 <- a + b]) sz1 0 (Zwf_well_founded 0 (meas 0)) in
      huff h2 sz1 (acc + (a + b)) (Acc_inv H (dec_pred 1 sz Hs))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition canvas_impl (x : array uint) : uint :=
  let sz := PArray.length x in
  let h := build (PArray.copy x) sz (sz / 2) (Zwf_well_founded 0 (φ (sz / 2))) in
  huff h sz 0 (Zwf_well_founded 0 (φ sz)).

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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma rd2 : forall (h : array int) i m a b t,
  ((φ i) < (φ (PArray.length h)))%Z -> ((φ m) < (φ (PArray.length h)))%Z -> (φ i) <> (φ m) ->
  h.[i <- a].[m <- b].[t] =
    if Z.eqb (φ t) (φ m) then b else if Z.eqb (φ t) (φ i) then a else h.[t].
Proof.
  intros h i m a b t Hi Hm Hne. destruct (Z.eqb_spec (φ t) (φ m)) as [E | E].
  - assert (t = m) by (apply to_Z_inj; exact E). subst t.
    apply aget_set_same. rewrite alength_set. apply ltb_spec. exact Hm.
  - rewrite aget_set_other by (intro F; apply E; subst; reflexivity).
    destruct (Z.eqb_spec (φ t) (φ i)) as [E' | E'].
    + assert (t = i) by (apply to_Z_inj; exact E'). subst t.
      apply aget_set_same. apply ltb_spec. exact Hi.
    + apply aget_set_other. intro F; apply E'; subst; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The heap: order, contents                                           *)
(* ------------------------------------------------------------------ *)

(* k is a child of p: 2p + 1 <= k <= 2p + 2. *)

(* Heap order on the pairs whose parent is at least lo, except at hole j. *)
Definition HPx (h : array int) (sz lo j : int) : Prop :=
  forall p k : int, ((φ k) < (φ sz))%Z -> (2 * (φ p) + 1 <= (φ k) <= 2 * (φ p) + 2)%Z ->
    ((φ lo) <= (φ p))%Z -> (φ p) <> (φ j) -> ((φ (h.[p])) <= (φ (h.[k])))%Z.

(* The parent of the hole j is below the children of j. *)
Definition Grand (h : array int) (sz lo j : int) : Prop :=
  forall g k : int, (2 * (φ g) + 1 <= (φ j) <= 2 * (φ g) + 2)%Z -> ((φ lo) <= (φ g))%Z ->
    ((φ k) < (φ sz))%Z -> (2 * (φ j) + 1 <= (φ k) <= 2 * (φ j) + 2)%Z -> ((φ (h.[g])) <= (φ (h.[k])))%Z.

(* Heap order on the pairs whose parent is at least lo. *)
Definition HPf (h : array int) (sz lo : int) : Prop :=
  forall p k : int, ((φ k) < (φ sz))%Z -> (2 * (φ p) + 1 <= (φ k) <= 2 * (φ p) + 2)%Z ->
    ((φ lo) <= (φ p))%Z -> ((φ (h.[p])) <= (φ (h.[k])))%Z.

Lemma stop_ok : forall h sz lo i, HPx h sz lo i ->
  (forall k : int, ((φ k) < (φ sz))%Z -> (2 * (φ i) + 1 <= (φ k) <= 2 * (φ i) + 2)%Z ->
     ((φ (h.[i])) <= (φ (h.[k])))%Z) ->
  HPf h sz lo.
Proof.
  intros h sz lo i Hx Hc p k Hk Hp Hlo.
  destruct (Z.eq_dec (φ p) (φ i)) as [E | E].
  - assert (p = i) by (apply to_Z_inj; exact E). subst p. apply Hc; assumption.
  - apply Hx; assumption.
Qed.

Lemma swap_ok : forall (h : array int) sz lo i m,
  ((φ sz) <= (φ (PArray.length h)))%Z -> ((φ lo) <= (φ i))%Z -> ((φ m) < (φ sz))%Z ->
  (2 * (φ i) + 1 <= (φ m) <= 2 * (φ i) + 2)%Z ->
  HPx h sz lo i -> Grand h sz lo i ->
  ((φ (h.[m])) <= (φ (h.[i])))%Z ->
  (forall k : int, ((φ k) < (φ sz))%Z -> (2 * (φ i) + 1 <= (φ k) <= 2 * (φ i) + 2)%Z ->
     ((φ (h.[m])) <= (φ (h.[k])))%Z) ->
  HPx (h.[i <- h.[m]].[m <- h.[i]]) sz lo m /\ Grand (h.[i <- h.[m]].[m <- h.[i]]) sz lo m.
Proof.
  intros h sz lo i m Hsz Hlo Hm Hpar Hx Hg Hmi Hmin.
  pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded lo) as Blo.
  split.
  - intros p k Hk Hpk Hlop Hpm. pose proof (to_Z_bounded p).
    rewrite !(rd2 h i m) by lia.
    destruct (Z.eqb_spec (φ k) (φ m)); destruct (Z.eqb_spec (φ k) (φ i));
      destruct (Z.eqb_spec (φ p) (φ m)); destruct (Z.eqb_spec (φ p) (φ i)); try lia.
    + apply (Hg p m); lia.
    + apply Hmin; lia.
    + apply (Hx p k); lia.
  - intros g k Hgm Hlog Hk Hmk. pose proof (to_Z_bounded g).
    rewrite !(rd2 h i m) by lia.
    destruct (Z.eqb_spec (φ k) (φ m)); destruct (Z.eqb_spec (φ k) (φ i));
      destruct (Z.eqb_spec (φ g) (φ m)); destruct (Z.eqb_spec (φ g) (φ i)); try lia.
    apply (Hx m k); lia.
Qed.

Definition rd (h : array int) (k : N) : N := Z.to_N (φ (h.[of_Z (Z.of_N k)])).

Definition cont (h : array int) (sz : int) : list N := map (rd h) (rg (Z.to_nat (φ sz))).

Lemma phi_of_Z_N : forall k : N, (Z.of_N k < wB)%Z -> (φ (of_Z (Z.of_N k))) = Z.of_N k.
Proof. intros k H. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma cont_swap : forall (h : array int) sz i m,
  ((φ sz) <= (φ (PArray.length h)))%Z -> ((φ i) < (φ sz))%Z -> ((φ m) < (φ sz))%Z -> (φ i) <> (φ m) ->
  Permutation (cont (h.[i <- h.[m]].[m <- h.[i]]) sz) (cont h sz).
Proof.
  intros h sz i m Hsz Hi Hm Hne. unfold cont.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded m). pose proof (to_Z_bounded sz).
  rewrite (map_ext_in _ (swp (rd h) (Z.to_N (φ i)) (Z.to_N (φ m)))).
  - apply perm_swp; [apply NoDup_rg | apply in_rg; lia | apply in_rg; lia].
  - intros k Hk. apply in_rg in Hk.
    assert (Hk' : (φ (of_Z (Z.of_N k))) = Z.of_N k) by (apply phi_of_Z_N; lia).
    unfold rd at 1. rewrite (rd2 h i m) by lia. rewrite Hk'.
    unfold swp, upd.
    destruct (Z.eqb_spec (Z.of_N k) (φ m)); destruct (Z.eqb_spec (Z.of_N k) (φ i));
      destruct (N.eqb_spec k (Z.to_N (φ m))); destruct (N.eqb_spec k (Z.to_N (φ i))); try lia;
      unfold rd; rewrite ?Z2N.id by lia; rewrite ?of_to_Z; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* sift                                                                 *)
(* ------------------------------------------------------------------ *)

Lemma sift_spec : forall z (h : array int) sz i lo (H : Acc (Zwf 0) (meas i)),
  meas i = z ->
  ((φ sz) <= (φ (PArray.length h)))%Z -> ((φ lo) <= (φ i) < (φ sz))%Z ->
  HPx h sz lo i -> Grand h sz lo i ->
  PArray.length (sift h sz i H) = PArray.length h /\ HPf (sift h sz i H) sz lo /\
  Permutation (cont (sift h sz i H) sz) (cont h sz).
Proof.
  intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h sz i lo H Hz Hsz Hi Hx Hg.
  pose proof (alength_bound h) as Bh. pose proof (to_Z_bounded i) as Bi.
  pose proof (to_Z_bounded sz) as Bs. pose proof (to_Z_bounded lo) as Blo.
  assert (El : ((φ (2 * i + 1)) = 2 * (φ i) + 1)%Z) by sia.
  assert (Er : ((φ (2 * i + 1 + 1)) = 2 * (φ i) + 2)%Z) by sia.
  rewrite sift_eq. cbv zeta.
  destruct (2 * i + 1 <? sz) eqn:Cl.
  - rewrite ltb_spec in Cl.
    destruct ((2 * i + 1 + 1 <? sz) && (h.[2 * i + 1 + 1] <? h.[2 * i + 1])) eqn:Cr.
    + apply andb_prop in Cr. destruct Cr as [Cr1 Cr2]. rewrite ltb_spec in Cr1, Cr2.
      destruct (bdec ((h.[2 * i + 1 + 1] <? h.[i]) && (i <? 2 * i + 1 + 1))) as [Hd | Hd].
      * pose proof Hd as Hd'. apply andb_prop in Hd'. destruct Hd' as [Hd1 _].
        rewrite ltb_spec in Hd1.
        destruct (swap_ok h sz lo i (2 * i + 1 + 1) Hsz ltac:(lia) ltac:(lia) ltac:(lia) Hx Hg
                    ltac:(lia)) as [Hx' Hg'].
        { intros k Hk Hik.
          destruct (Z.eq_dec (φ k) (2 * (φ i) + 1)) as [E | E].
          - assert (k = 2 * i + 1) by (apply to_Z_inj; lia). subst k. lia.
          - assert (k = 2 * i + 1 + 1) by (apply to_Z_inj; lia). subst k. lia. }
        destruct (IH (meas (2 * i + 1 + 1)) ltac:(rewrite <- Hz; apply dec_meas with (b := h.[2 * i + 1 + 1] <? h.[i]); exact Hd)
                   (h.[i <- h.[2 * i + 1 + 1]].[2 * i + 1 + 1 <- h.[i]]) sz (2 * i + 1 + 1) lo
                   (Acc_inv H (dec_meas _ i (2 * i + 1 + 1) Hd)) eq_refl)
          as [L1 [P1 C1]].
        -- rewrite !alength_set. exact Hsz.
        -- lia.
        -- exact Hx'.
        -- exact Hg'.
        -- split; [rewrite L1, !alength_set; reflexivity|]. split; [exact P1|].
           eapply perm_trans; [exact C1 | apply cont_swap; lia].
      * assert (Hd2 : (h.[2 * i + 1 + 1] <? h.[i]) = false).
        { destruct (h.[2 * i + 1 + 1] <? h.[i]) eqn:E; [|reflexivity].
          rewrite (proj2 (ltb_spec i (2 * i + 1 + 1)) ltac:(lia)) in Hd. discriminate. }
        rewrite <- not_true_iff_false, ltb_spec in Hd2.
        split; [reflexivity|]. split; [|apply Permutation_refl].
        apply (stop_ok h sz lo i Hx).
        intros k Hk Hik.
        destruct (Z.eq_dec (φ k) (2 * (φ i) + 1)) as [E | E].
        -- assert (k = 2 * i + 1) by (apply to_Z_inj; lia). subst k. lia.
        -- assert (k = 2 * i + 1 + 1) by (apply to_Z_inj; lia). subst k. lia.
    + assert (Cr' : ((φ sz) <= 2 * (φ i) + 2 \/ (φ (h.[2 * i + 1])) <= (φ (h.[2 * i + 1 + 1])))%Z).
      { apply andb_false_iff in Cr. destruct Cr as [Cr | Cr];
          rewrite <- not_true_iff_false, ltb_spec in Cr; lia. }
      destruct (bdec ((h.[2 * i + 1] <? h.[i]) && (i <? 2 * i + 1))) as [Hd | Hd].
      * pose proof Hd as Hd'. apply andb_prop in Hd'. destruct Hd' as [Hd1 _].
        rewrite ltb_spec in Hd1.
        destruct (swap_ok h sz lo i (2 * i + 1) Hsz ltac:(lia) ltac:(lia) ltac:(lia) Hx Hg
                    ltac:(lia)) as [Hx' Hg'].
        { intros k Hk Hik.
          destruct (Z.eq_dec (φ k) (2 * (φ i) + 1)) as [E | E].
          - assert (k = 2 * i + 1) by (apply to_Z_inj; lia). subst k. lia.
          - assert (k = 2 * i + 1 + 1) by (apply to_Z_inj; lia). subst k. lia. }
        destruct (IH (meas (2 * i + 1)) ltac:(rewrite <- Hz; apply dec_meas with (b := h.[2 * i + 1] <? h.[i]); exact Hd)
                   (h.[i <- h.[2 * i + 1]].[2 * i + 1 <- h.[i]]) sz (2 * i + 1) lo
                   (Acc_inv H (dec_meas _ i (2 * i + 1) Hd)) eq_refl)
          as [L1 [P1 C1]].
        -- rewrite !alength_set. exact Hsz.
        -- lia.
        -- exact Hx'.
        -- exact Hg'.
        -- split; [rewrite L1, !alength_set; reflexivity|]. split; [exact P1|].
           eapply perm_trans; [exact C1 | apply cont_swap; lia].
      * assert (Hd2 : (h.[2 * i + 1] <? h.[i]) = false).
        { destruct (h.[2 * i + 1] <? h.[i]) eqn:E; [|reflexivity].
          rewrite (proj2 (ltb_spec i (2 * i + 1)) ltac:(lia)) in Hd. discriminate. }
        rewrite <- not_true_iff_false, ltb_spec in Hd2.
        split; [reflexivity|]. split; [|apply Permutation_refl].
        apply (stop_ok h sz lo i Hx).
        intros k Hk Hik.
        destruct (Z.eq_dec (φ k) (2 * (φ i) + 1)) as [E | E].
        -- assert (k = 2 * i + 1) by (apply to_Z_inj; lia). subst k. lia.
        -- assert (k = 2 * i + 1 + 1) by (apply to_Z_inj; lia). subst k. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Cl.
    split; [reflexivity|]. split; [|apply Permutation_refl].
    apply (stop_ok h sz lo i Hx). intros k Hk Hik. lia.
Qed.

Lemma root_min : forall h sz, HPf h sz 0 ->
  forall k, ((φ k) < (φ sz))%Z -> ((φ (h.[0])) <= (φ (h.[k])))%Z.
Proof.
  intros h sz Hh.
  assert (Hn : forall n : nat, forall k, Z.to_nat (φ k) = n -> ((φ k) < (φ sz))%Z ->
                 ((φ (h.[0])) <= (φ (h.[k])))%Z).
  { intro n. induction n as [n IH] using (well_founded_induction lt_wf).
    intros k Ek Hk. pose proof (to_Z_bounded k).
    destruct (Z.eq_dec (φ k) 0) as [E | E].
    - assert (k = 0) by (apply to_Z_inj; exact E). subst. lia.
    - assert (Ep : ((φ ((k - 1) / 2)) = ((φ k) - 1) / 2)%Z) by sia.
      assert (Hrel : (2 * (φ ((k - 1) / 2)) + 1 <= (φ k) <= 2 * (φ ((k - 1) / 2)) + 2)%Z)
        by (rewrite Ep; Z.to_euclidean_division_equations; lia).
      pose proof (Hh ((k - 1) / 2) k Hk Hrel ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded ((k - 1) / 2)); lia)).
      pose proof (IH (Z.to_nat (φ ((k - 1) / 2))) ltac:(lia) ((k - 1) / 2) eq_refl ltac:(lia)).
      lia. }
  intros k Hk. exact (Hn _ k eq_refl Hk).
Qed.

Lemma cont_min : forall h sz x, HPf h sz 0 -> In x (cont h sz) -> (rd h 0 <= x)%N.
Proof.
  intros h sz x Hh Hx. unfold cont in Hx. apply in_map_iff in Hx.
  destruct Hx as [k [Ek Hk]]. apply in_rg in Hk. subst x.
  pose proof (to_Z_bounded sz).
  assert (Hk' : (φ (of_Z (Z.of_N k))) = Z.of_N k) by (apply phi_of_Z_N; lia).
  pose proof (root_min h sz Hh (of_Z (Z.of_N k)) ltac:(lia)).
  unfold rd. change (of_Z (Z.of_N 0)) with 0. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* build                                                               *)
(* ------------------------------------------------------------------ *)

Lemma build_spec : forall z (h : array int) sz k (H : Acc (Zwf 0) (φ k)),
  (φ k) = z -> ((φ sz) <= (φ (PArray.length h)))%Z -> (2 * (φ k) <= (φ sz))%Z -> HPf h sz k ->
  PArray.length (build h sz k H) = PArray.length h /\ HPf (build h sz k H) sz 0 /\
  Permutation (cont (build h sz k H) sz) (cont h sz).
Proof.
  intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h sz k H Hz Hsz Hk Hh.
  pose proof (to_Z_bounded k). pose proof (to_Z_bounded sz).
  rewrite build_eq.
  destruct (bdec (0 <? k)) as [Hk0 | Hk0].
  - pose proof Hk0 as Hk0'. rewrite ltb_spec in Hk0'. change (φ 0) with 0%Z in Hk0'.
    assert (Ek : ((φ (k - 1)) = (φ k) - 1)%Z) by sia.
    destruct (sift_spec _ h sz (k - 1) (k - 1) (Zwf_well_founded 0 (meas (k - 1))) eq_refl Hsz
                ltac:(lia)) as [L1 [P1 C1]].
    { intros p q Hq Hpq Hlo Hne. apply Hh; lia. }
    { intros g q Hg Hlo. lia. }
    destruct (IH (φ (k - 1)) ltac:(rewrite <- Hz; apply dec_pred with (j := 0); exact Hk0)
                (sift h sz (k - 1) (Zwf_well_founded 0 (meas (k - 1)))) sz (k - 1)
                (Acc_inv H (dec_pred 0 k Hk0)) eq_refl) as [L2 [P2 C2]].
    + rewrite L1. exact Hsz.
    + lia.
    + exact P1.
    + split; [rewrite L2, L1; reflexivity|]. split; [exact P2|].
      eapply perm_trans; [exact C2 | exact C1].
  - rewrite <- not_true_iff_false, ltb_spec in Hk0. change (φ 0) with 0%Z in Hk0.
    assert (k = 0) by (apply to_Z_inj; change (φ 0) with 0%Z; lia). subst k.
    split; [reflexivity|]. split; [exact Hh | apply Permutation_refl].
Qed.

(* ------------------------------------------------------------------ *)
(* Contents under the root operations                                   *)
(* ------------------------------------------------------------------ *)

Lemma rg_S0 : forall m, rg (S m) = 0%N :: map N.of_nat (seq 1 m).
Proof. reflexivity. Qed.

Lemma set0_cont : forall (h : array int) (v sz : int),
  (1 <= (φ sz) <= (φ (PArray.length h)))%Z ->
  exists tl, cont h sz = rd h 0 :: tl /\ cont (h.[0 <- v]) sz = Z.to_N (φ v) :: tl.
Proof.
  intros h v sz Hsz. pose proof (to_Z_bounded sz). unfold cont.
  destruct (Z.to_nat (φ sz)) as [| m] eqn:Em; [lia|].
  rewrite rg_S0. simpl map.
  exists (map (rd h) (map N.of_nat (seq 1 m))). split; [reflexivity|]. f_equal.
  - unfold rd. change (of_Z (Z.of_N 0)) with 0.
    rewrite aget_set_same; [reflexivity|]. apply ltb_spec. change (φ 0) with 0%Z. lia.
  - apply map_ext_in. intros k Hk. apply in_map_iff in Hk. destruct Hk as [j [Ej Hj]].
    apply in_seq in Hj. subst k. unfold rd.
    rewrite aget_set_other; [reflexivity|].
    intro F. assert (G : (φ 0) = (φ (of_Z (Z.of_N (N.of_nat j))))) by (rewrite F; reflexivity).
    rewrite phi_of_Z_N in G by lia. change (φ 0) with 0%Z in G. lia.
Qed.

Lemma pop_cont : forall (h : array int) sz,
  (2 <= (φ sz) <= (φ (PArray.length h)))%Z ->
  Permutation (cont h sz) (rd h 0 :: cont (h.[0 <- h.[sz - 1]]) (sz - 1)).
Proof.
  intros h sz Hsz. pose proof (to_Z_bounded sz).
  assert (E1 : ((φ (sz - 1)) = (φ sz) - 1)%Z) by sia.
  destruct (set0_cont h (h.[sz - 1]) (sz - 1) ltac:(lia)) as [tl [T1 T2]].
  rewrite T2. unfold cont in T1 |- *.
  replace (Z.to_nat (φ sz)) with (S (Z.to_nat (φ (sz - 1)))) by lia.
  rewrite rg_S, map_app, T1. simpl.
  replace (rd h (N.of_nat (Z.to_nat (φ (sz - 1))))) with (Z.to_N (φ (h.[sz - 1]))).
  - apply perm_skip. apply Permutation_sym. apply Permutation_cons_append.
  - unfold rd.
    replace (of_Z (Z.of_N (N.of_nat (Z.to_nat (φ (sz - 1)))))) with (sz - 1); [reflexivity|].
    apply to_Z_inj. rewrite phi_of_Z_N by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The greedy loop                                                      *)
(* ------------------------------------------------------------------ *)

Lemma hpx_root : forall (h : array int) sz sz' v,
  HPf h sz 0 -> ((φ sz') <= (φ sz))%Z -> HPx (h.[0 <- v]) sz' 0 0.
Proof.
  intros h sz sz' v Hh Hs p k Hk Hpk Hlo Hp0.
  pose proof (to_Z_bounded p). change (φ 0) with 0%Z in *.
  rewrite !aget_set_other.
  - apply Hh; [lia | lia | change (φ 0) with 0%Z; lia].
  - intro F. rewrite <- F in Hpk. change (φ 0) with 0%Z in Hpk. lia.
  - intro F. apply Hp0. rewrite <- F. reflexivity.
Qed.

Lemma grand_root : forall (h : array int) sz, Grand h sz 0 0.
Proof.
  intros h sz g k Hg. pose proof (to_Z_bounded g). change (φ 0) with 0%Z in Hg. lia.
Qed.

Lemma huff_spec : forall s z (h : array int) sz acc (H : Acc (Zwf 0) (φ sz)) (accN : N),
  (φ sz) = z ->
  (1 <= (φ sz))%Z -> ((φ sz) <= (φ (PArray.length h)))%Z ->
  ((φ sz) <= Z.of_nat (List.length s))%Z -> (Z.of_nat (List.length s) <= 100000)%Z ->
  (Z.of_N (sumL s) <= 10000000000)%Z ->
  HPf h sz 0 -> sumL (cont h sz) = sumL s ->
  (φ acc) = Z.of_N accN ->
  (Z.of_N accN <= (Z.of_nat (List.length s) - (φ sz)) * Z.of_N (sumL s))%Z ->
  UB s (cont h sz) accN -> LB s (cont h sz) accN ->
  exists r, (φ (huff h sz acc H)) = Z.of_N r /\ Final s r.
Proof.
  intros s z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h sz acc H accN Hz H1 Hlen Hn Hn5 HS Hh Hsum Hacc Hb Hub Hlb.
  pose proof (to_Z_bounded sz). pose proof (to_Z_bounded acc).
  rewrite huff_eq.
  destruct (bdec (1 <? sz)) as [Hs | Hs].
  - pose proof Hs as Hs'. rewrite ltb_spec in Hs'. change (φ 1) with 1%Z in Hs'.
    cbv zeta.
    assert (E1 : ((φ (sz - 1)) = (φ sz) - 1)%Z) by sia.
    pose proof (pop_cont h sz ltac:(lia)) as PM.
    set (sz1 := sz - 1) in *.
    set (h0 := h.[0 <- h.[sz1]]) in *.
    assert (L0 : PArray.length h0 = PArray.length h) by apply alength_set.
    destruct (sift_spec _ h0 sz1 0 0 (Zwf_well_founded 0 (meas 0)) eq_refl
                ltac:(rewrite L0; lia) ltac:(change (φ 0) with 0%Z; lia)
                (hpx_root h sz sz1 _ Hh ltac:(lia)) (grand_root h0 sz1)) as [L1 [P1 C1]].
    set (h1 := sift h0 sz1 0 (Zwf_well_founded 0 (meas 0))) in *.
    set (a := h.[0]). set (b := h1.[0]).
    set (h1' := h1.[0 <- a + b]).
    assert (L1' : PArray.length h1' = PArray.length h) by (unfold h1'; rewrite alength_set, L1, L0; reflexivity).
    destruct (sift_spec _ h1' sz1 0 0 (Zwf_well_founded 0 (meas 0)) eq_refl
                ltac:(rewrite L1'; lia) ltac:(change (φ 0) with 0%Z; lia)
                (hpx_root h1 sz1 sz1 _ P1 ltac:(lia)) (grand_root h1' sz1)) as [L2 [P2 C2]].
    set (h2 := sift h1' sz1 0 (Zwf_well_founded 0 (meas 0))) in *.
    destruct (set0_cont h1 (a + b) sz1 ltac:(rewrite L1, L0; lia)) as [tl [T1 T2]].
    fold h1' in T2.
    set (a' := rd h 0) in *. set (b' := rd h1 0) in *.
    assert (Ea : (φ a) = Z.of_N a').
    { unfold a', rd, a. change (of_Z (Z.of_N 0)) with 0. pose proof (to_Z_bounded (h.[0])). lia. }
    assert (Eb : (φ b) = Z.of_N b').
    { unfold b', rd, b. change (of_Z (Z.of_N 0)) with 0. pose proof (to_Z_bounded (h1.[0])). lia. }
    assert (MP : Permutation (cont h sz) (a' :: b' :: tl)).
    { eapply perm_trans; [exact PM|]. apply perm_skip. rewrite <- T1. apply Permutation_sym. exact C1. }
    assert (Ha : forall y, In y (b' :: tl) -> (a' <= y)%N).
    { intros y Hy. apply (cont_min h sz y Hh). apply (Permutation_in _ (Permutation_sym MP)). right. exact Hy. }
    assert (Hbm : forall y, In y tl -> (b' <= y)%N).
    { intros y Hy. apply (cont_min h1 sz1 y P1). rewrite T1. right. exact Hy. }
    assert (Hsum' : sumL (cont h sz) = (a' + b' + sumL tl)%N)
      by (rewrite (sumL_perm _ _ MP); simpl; lia).
    assert (Eab : (φ (a + b)) = (Z.of_N a' + Z.of_N b')%Z).
    { rewrite add_spec, Ea, Eb. apply Z.mod_small. rewrite wB_val. lia. }
    assert (M2 : Permutation (cont h2 sz1) ((a' + b')%N :: tl)).
    { eapply perm_trans; [exact C2|]. rewrite T2.
      replace (Z.to_N (φ (a + b))) with (a' + b')%N by lia. apply Permutation_refl. }
    assert (Bacc : (Z.of_N accN + Z.of_N a' + Z.of_N b' <= (Z.of_nat (List.length s) - (φ sz1)) * Z.of_N (sumL s))%Z)
      by nia.
    assert (Bacc' : (Z.of_N accN + Z.of_N a' + Z.of_N b' < wB)%Z) by (rewrite wB_val; nia).
    destruct (IH (φ sz1) ltac:(rewrite <- Hz; apply dec_pred with (j := 1); exact Hs)
                h2 sz1 (acc + (a + b)) (Acc_inv H (dec_pred 1 sz Hs)) (accN + (a' + b'))%N eq_refl)
      as [r [Hr Fr]].
    + lia.
    + rewrite L2, L1'. lia.
    + lia.
    + exact Hn5.
    + exact HS.
    + exact P2.
    + rewrite (sumL_perm _ _ M2). simpl. lia.
    + rewrite add_spec, Hacc, Eab. rewrite Z.mod_small by lia. lia.
    + lia.
    + apply (UB_perm s _ _ _ (Permutation_sym M2)). apply (UB_step s (cont h sz)); assumption.
    + apply (LB_perm s _ _ _ (Permutation_sym M2)). apply (LB_step s (cont h sz)); assumption.
    + exists r. split; [exact Hr | exact Fr].
  - rewrite <- not_true_iff_false, ltb_spec in Hs. change (φ 1) with 1%Z in Hs.
    assert (C1 : cont h sz = [rd h 0]).
    { unfold cont. replace (Z.to_nat (φ sz)) with 1%nat by lia. reflexivity. }
    rewrite C1 in Hub, Hlb.
    exists accN. split; [exact Hacc|]. exact (Final_of s _ accN Hub Hlb).
Qed.

(* ------------------------------------------------------------------ *)
(* The main theorem                                                     *)
(* ------------------------------------------------------------------ *)

Lemma canvas_impl_correct : forall (s : list N) (x : array uint),
  valid_input s -> repr x s -> exists o : N, repr (canvas_impl x) o /\ canvas_spec s o.
Proof.
  intros s x Hv Hx. pose proof Hv as [Hn Hsz].
  unfold len in Hn.
  destruct Hx as [Hlx Hcx].
  assert (Lx : (φ (PArray.length x)) = Z.of_nat (List.length s)) by (symmetry; exact Hlx).
  assert (Cx : forall k, (k < List.length s)%nat ->
             Z.to_N (φ (x.[of_Z (Z.of_nat k)])) = nth k s 0%N).
  { intros k Hk. destruct (Hcx k Hk) as [m [Hm Hr]].
    rewrite (nth_error_nth s k 0%N Hm). exact Hr. }
  clear Hlx Hcx.
  assert (HS : (Z.of_N (sumL s) <= 10000000000)%Z).
  { pose proof (sumL_bound s 100000 (Forall_impl _ (fun x H => proj2 H) Hsz)). lia. }
  set (sz := PArray.length x) in *.
  set (h := PArray.copy x).
  assert (Lh : PArray.length h = sz) by exact (length_copy _ x).
  assert (Ch : cont h sz = s).
  { unfold cont. rewrite Lx, Nat2Z.id. rewrite <- (map_size_rg s) at 2.
    apply map_ext_in. intros k Hk. apply in_rg in Hk.
    unfold rd, h.
    transitivity (Z.to_N (φ (x.[of_Z (Z.of_N k)]))); [exact (f_equal (fun v : int => Z.to_N (φ v)) (get_copy _ x (of_Z (Z.of_N k))))|]. unfold Prelude.size.
    rewrite <- Cx by lia. rewrite N_nat_Z. reflexivity. }
  pose proof (to_Z_bounded sz).
  destruct (build_spec _ h sz (sz / 2) (Zwf_well_founded 0 (φ (sz / 2))) eq_refl
              ltac:(apply Z.eq_le_incl; f_equal; exact (eq_sym Lh)) ltac:(sia)) as [L0 [P0 C0]].
  { intros p k Hk Hpk Hlo. assert ((φ (sz / 2)) = (φ sz) / 2)%Z by sia. lia. }
  set (h0 := build h sz (sz / 2) (Zwf_well_founded 0 (φ (sz / 2)))) in *.
  rewrite Ch in C0.
  destruct (huff_spec s _ h0 sz 0 (Zwf_well_founded 0 (φ sz)) 0%N eq_refl)
    as [r [Hr Fr]].
  - lia.
  - apply Z.eq_le_incl. f_equal. exact (eq_sym (eq_trans L0 Lh)).
  - lia.
  - lia.
  - exact HS.
  - exact P0.
  - apply sumL_perm. exact C0.
  - reflexivity.
  - lia.
  - apply (UB_perm s s _ _ (Permutation_sym C0)). apply UB_init.
  - apply (LB_perm s s _ _ (Permutation_sym C0)). apply LB_init.
  - exists r. split.
    + unfold repr, repr_uint, canvas_impl. transitivity (Z.to_N (Z.of_N r)); [f_equal; exact Hr | apply N2Z.id].
    + destruct Fr as [Fu Fl]. apply canvas_char; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition canvas : array uint -> uint := canvas_impl.

Definition canvas_correct : forall (s : list N) (x : array uint),
  valid_input s -> repr x s -> exists o : N, repr (canvas x) o /\ canvas_spec s o
  := canvas_impl_correct.
