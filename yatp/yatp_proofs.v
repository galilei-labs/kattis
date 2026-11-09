(* Correctness proofs for yatp_implem.v. *)
(* Implementation of yatp (yatp.spec): centroid decomposition, a Li Chao
   tree per component (lines y = p_v * x + dist(c, v), queried at x = p_u).

   Code.  CSR adjacency built from the half-edges (counting sort); then the
   nodes r = 1..n in turn: while r is alive, a BFS from r over the alive
   nodes gives its component, subtree sizes along the BFS order give the
   centroid c, a BFS from c gives the distances d (with a consistency flag;
   a relaxation loop, never run on a tree, repairs d otherwise), the lines
   (p_v, d_v) of the component go into a Li Chao tree on the abscissae
   0..max p (stamped per round, never cleared), and every node u of the
   component takes best[u] := min(best[u], d_u + query(p_u)); c is removed.
   The answer is the sum of best[1..n].  Every loop is a Fixpoint on an
   erased Acc (Zwf 0) argument; no nat, N or Z in the extracted code.

   Proof.  Graph side over arbitrary walks (no acyclicity needed):
   invariant MI of the main loop -- best[u] is at most the cost of every
   walk from u that touches a removed node, and at least the cost of some
   walk from u; at the end every node is removed and shortcut turns the
   witness walk into a simple path.  See README.md, "Implementation". *)

From Yatp.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Yatp Require Export yatp_implem.
Open Scope uint63_scope.
Open Scope array_scope.


Lemma aget_oob : forall (t : array int) (i : int),
  (i <? PArray.length t) = false -> t.[i] = PArray.default t.
Proof. intros t i H. exact (get_out_of_bounds int t i H). Qed.

Lemma adefault_set : forall (t : array int) (i b : int), PArray.default t.[i <- b] = PArray.default t.
Proof. intros t i b. exact (default_set int t i b). Qed.

Lemma aget_set_le : forall (t : array int) (i j : int) (b : int),
  t.[i <- b].[j] = if (i =? j) && (i <? PArray.length t) then b else t.[j].
Proof.
  intros t i j b. destruct (i <? PArray.length t) eqn:B.
  - rewrite andb_true_r. apply aget_set; auto.
  - rewrite andb_false_r. destruct (i =? j) eqn:E.
    + rewrite Uint63.eqb_spec in E. subst j.
      assert (B' : (i <? PArray.length t.[i <- b]) = false) by (rewrite alength_set; exact B).
      rewrite (aget_oob _ i B'), adefault_set. symmetry. apply (aget_oob t i B).
    + rewrite eqb_false_spec in E. apply aget_set_other; auto.
Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma blength_make : forall (n : int) (b : bool),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make bool n b). Qed.

Lemma alength_make_small : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma blength_make_small : forall (n : int) (b : bool),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite blength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make int b n i). Qed.

Lemma bget_make : forall (n i : int) (b : bool), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make bool b n i). Qed.
Lemma ltb_false : forall a b : int, (a <? b) = false <-> ((φ b) <= (φ a))%Z.
Proof. intros. rewrite <- Bool.not_true_iff_false, ltb_spec. lia. Qed.
Lemma leb_true : forall a b : int, (a <=? b) = true <-> ((φ a) <= (φ b))%Z.
Proof. intros. apply leb_spec. Qed.
Lemma leb_false : forall a b : int, (a <=? b) = false <-> ((φ b) < (φ a))%Z.
Proof. intros. rewrite <- Bool.not_true_iff_false, leb_spec. lia. Qed.

Lemma int_eq_phi : forall a b : int, (φ a) = (φ b) -> a = b.
Proof. intros. apply to_Z_inj. auto. Qed.

Lemma phi_neq : forall a b : int, (φ a) <> (φ b) -> a <> b.
Proof. intros a b H E. subst. auto. Qed.

(* ================================================================== *)
(* Prop side                                                          *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Walks                                                               *)
(* ------------------------------------------------------------------ *)

Section Walks.
Variables eu ev ew : list N.

Definition wsum (ks : list N) : N := fold_right (fun k acc => (Prelude.get ew k + acc)%N) 0%N ks.

Lemma wsum_app : forall a b, wsum (a ++ b) = (wsum a + wsum b)%N.
Proof. induction a; intros b; simpl; [reflexivity|]. rewrite IHa. lia. Qed.

Lemma wsum_rev : forall a, wsum (rev a) = wsum a.
Proof. induction a; simpl; [reflexivity|]. rewrite wsum_app. simpl. lia. Qed.

Lemma joins_sym : forall k a b, joins eu ev k a b -> joins eu ev k b a.
Proof. unfold joins. intros k a b [H1 H2]. split; auto. tauto. Qed.

Lemma walk_nonnil : forall vs ks, walk eu ev vs ks -> vs <> [].
Proof. intros vs ks H. destruct H; discriminate. Qed.

Lemma walk_single : forall c ks, walk eu ev [c] ks -> ks = [].
Proof. intros c ks H. inversion H; auto. Qed.

Lemma walk_cons_inv : forall a b vs ks, walk eu ev (a :: b :: vs) ks ->
  exists k ks', ks = k :: ks' /\ joins eu ev k a b /\ walk eu ev (b :: vs) ks'.
Proof. intros a b vs ks H. inversion H as [| ? ? k ? ks0 ? ?]; subst. exists k, ks0. auto. Qed.

Lemma walk_app : forall vs1 c ks1 vs2 ks2,
  walk eu ev (vs1 ++ [c]) ks1 -> walk eu ev (c :: vs2) ks2 ->
  walk eu ev (vs1 ++ c :: vs2) (ks1 ++ ks2).
Proof.
  induction vs1 as [| a vs1 IH]; intros c ks1 vs2 ks2 H1 H2.
  - simpl in *. apply walk_single in H1. subst. exact H2.
  - destruct vs1 as [| b vs1'].
    + simpl in H1 |- *. destruct (walk_cons_inv _ _ _ _ H1) as (k & ks' & E & Hj & Hw).
      apply walk_single in Hw. subst. simpl. constructor; auto.
    + simpl in H1 |- *. destruct (walk_cons_inv _ _ _ _ H1) as (k & ks' & E & Hj & Hw).
      subst. simpl. constructor; auto. apply (IH c ks' vs2 ks2 Hw H2).
Qed.

Lemma walk_split : forall vs ks c, walk eu ev vs ks -> In c vs ->
  exists vs1 vs2 ks1 ks2, vs = vs1 ++ c :: vs2 /\ ks = ks1 ++ ks2 /\
    walk eu ev (vs1 ++ [c]) ks1 /\ walk eu ev (c :: vs2) ks2.
Proof.
  intros vs ks c H. induction H as [a | a b k vs ks Hj Hw IH]; intros Hin.
  - destruct Hin as [<- | []]. exists [], [], [], []. repeat split; constructor.
  - destruct Hin as [<- | Hin].
    + exists [], (b :: vs), [], (k :: ks). repeat split; [constructor | constructor; auto].
    + destruct (IH Hin) as (vs1 & vs2 & ks1 & ks2 & E1 & E2 & W1 & W2).
      exists (a :: vs1), vs2, (k :: ks1), ks2. rewrite E2. split; [rewrite E1; reflexivity|].
      split; [reflexivity|]. split; [|exact W2].
      destruct vs1 as [| b' vs1]; simpl in E1 |- *.
      * inversion E1; subst. constructor; auto.
      * inversion E1; subst. constructor; auto.
Qed.

Lemma walk_rev : forall vs ks, walk eu ev vs ks -> walk eu ev (rev vs) (rev ks).
Proof.
  intros vs ks H. induction H as [a | a b k vs ks Hj Hw IH]; [constructor|].
  simpl in IH |- *.
  replace ((rev vs ++ [b]) ++ [a]) with (rev vs ++ b :: [a]) by (rewrite <- app_assoc; reflexivity).
  apply walk_app; [exact IH | constructor; [apply joins_sym; auto | constructor]].
Qed.

(* last with a list whose head is known *)
Lemma last_cons_any : forall (vs : list N) a d1 d2, last (a :: vs) d1 = last (a :: vs) d2.
Proof.
  induction vs as [| b vs IH]; intros a d1 d2; [reflexivity|].
  change (last (b :: vs) d1 = last (b :: vs) d2). apply IH.
Qed.

Lemma last_app_cons : forall (vs1 vs2 : list N) c d, last (vs1 ++ c :: vs2) d = last (c :: vs2) d.
Proof.
  induction vs1; intros; simpl; [reflexivity|]. rewrite IHvs1.
  destruct (vs1 ++ c :: vs2) eqn:E; [destruct vs1; discriminate | reflexivity].
Qed.

Lemma last_app_single : forall (vs1 : list N) c d, last (vs1 ++ [c]) d = c.
Proof. intros. rewrite last_app_cons. reflexivity. Qed.

(* every walk shortens to a simple path with the same ends, no heavier *)
Lemma shortcut : forall vs ks, walk eu ev vs ks ->
  exists vs' ks', walk eu ev vs' ks' /\ hd_error vs' = hd_error vs /\
    (forall d, last vs' d = last vs d) /\ NoDup vs' /\ (wsum ks' <= wsum ks)%N.
Proof.
  intros vs ks H. induction H as [a | a b k vs ks Hj Hw IH].
  - exists [a], []. split; [apply walk_one|]. split; [reflexivity|]. split; [reflexivity|].
    split; [constructor; [intros []|constructor] | simpl; lia].
  - destruct IH as (vs' & ks' & W & Hh & Hl & ND & Hs).
    destruct (in_dec N.eq_dec a vs') as [Hin | Hin].
    + destruct (walk_split vs' ks' a W Hin) as (vs1 & vs2 & ks1 & ks2 & E1 & E2 & W1 & W2).
      exists (a :: vs2), ks2. repeat split; auto.
      * intros d. change (last (a :: b :: vs) d) with (last (b :: vs) d).
        rewrite <- Hl, E1, last_app_cons. reflexivity.
      * rewrite E1 in ND. apply NoDup_app_remove_l in ND. exact ND.
      * rewrite E2, wsum_app in Hs. simpl. lia.
    + exists (a :: vs'), (k :: ks'). destruct vs' as [| b' vs'']; [apply walk_nonnil in W; congruence|].
      simpl in Hh. inversion Hh; subst b'. repeat split.
      * constructor; auto.
      * intros d. change (last (a :: b :: vs'') d = last (a :: b :: vs) d).
        change (last (b :: vs'') d = last (b :: vs) d). apply Hl.
      * constructor; auto.
      * simpl. lia.
Qed.

(* a potential that no edge inside S can beat bounds every walk inside S *)
Lemma potential : forall (S : N -> Prop) (D : N -> Z),
  (forall k a b, joins eu ev k a b -> S a -> S b -> (D b <= D a + Z.of_N (Prelude.get ew k))%Z) ->
  forall vs ks, walk eu ev vs ks -> Forall S vs ->
  forall a d, hd_error vs = Some a -> (D (last vs d) <= D a + Z.of_N (wsum ks))%Z.
Proof.
  intros S D HD vs ks H. induction H as [x | x y k vs ks Hj Hw IH]; intros HS a d Ha.
  - simpl in Ha. inversion Ha; subst. simpl. lia.
  - simpl in Ha. inversion Ha; subst. inversion HS; subst. inversion H2; subst.
    pose proof (HD k a y Hj H1 H3).
    specialize (IH H2 y d eq_refl).
    change (last (a :: y :: vs) d) with (last (y :: vs) d).
    simpl wsum. lia.
Qed.

(* a set closed under the alive edges contains every alive walk it meets *)
Lemma closure_fwd : forall (C A : N -> Prop),
  (forall k a b, joins eu ev k a b -> C a -> A b -> C b) ->
  forall vs ks, walk eu ev vs ks -> Forall A vs ->
  forall a, hd_error vs = Some a -> C a -> Forall C vs.
Proof.
  intros C A HC vs ks H. induction H as [x | x y k vs ks Hj Hw IH]; intros HA a Ha Ca.
  - simpl in Ha. inversion Ha; subst. constructor; auto.
  - simpl in Ha. inversion Ha; subst. inversion HA; subst. inversion H2; subst.
    constructor; auto. apply (IH H2 y eq_refl). eapply HC; eauto.
Qed.

Lemma closure : forall (C A : N -> Prop),
  (forall k a b, joins eu ev k a b -> C a -> A b -> C b) ->
  forall vs ks, walk eu ev vs ks -> Forall A vs ->
  forall c, In c vs -> C c -> Forall C vs.
Proof.
  intros C A HC vs ks H HA c Hin Cc.
  destruct (walk_split vs ks c H Hin) as (vs1 & vs2 & ks1 & ks2 & E1 & E2 & W1 & W2).
  subst vs. apply Forall_app in HA as [HA1 HA2].
  apply Forall_app. split.
  - apply walk_rev in W1. rewrite rev_app_distr in W1. simpl in W1.
    assert (Forall C (c :: rev vs1)).
    { apply (closure_fwd C A HC _ _ W1) with (a := c); [| reflexivity | exact Cc].
      constructor; [inversion HA2; auto|]. apply Forall_rev; auto. }
    inversion H0; subst. apply Forall_rev in H4. rewrite rev_involutive in H4. auto.
  - apply (closure_fwd C A HC _ _ W2) with (a := c); [exact HA2 | reflexivity | exact Cc].
Qed.

Lemma walk_extend : forall vs ks a k b, walk eu ev vs ks -> last vs 0%N = a ->
  joins eu ev k a b ->
  exists vs', walk eu ev vs' (ks ++ [k]) /\ hd_error vs' = hd_error vs /\ last vs' 0%N = b.
Proof.
  intros vs ks a k b W Hl Hj.
  assert (Hne := walk_nonnil _ _ W).
  pose proof (app_removelast_last 0%N Hne) as E. rewrite Hl in E.
  exists (removelast vs ++ a :: [b]). split; [|split].
  - apply walk_app; [rewrite <- E; exact W | constructor; [exact Hj | constructor]].
  - rewrite E at 2. destruct (removelast vs); reflexivity.
  - rewrite last_app_cons. reflexivity.
Qed.

End Walks.

Lemma pigeon : forall (f : nat -> Z) (t : nat) (N : Z), (0 <= N)%Z ->
  (forall i, (i < t)%nat -> (1 <= f i <= N)%Z) ->
  (forall i j, (i < t)%nat -> (j < t)%nat -> f i = f j -> i = j) ->
  (Z.of_nat t <= N)%Z.
Proof.
  intros f t N HN Hr Hi.
  assert (ND : NoDup (map f (seq 0 t))).
  { apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros a b Ha Hb. apply in_seq in Ha, Hb. apply Hi; lia. }
  assert (Inc : incl (map f (seq 0 t)) (map Z.of_nat (seq 1 (Z.to_nat N)))).
  { intros z Hz. apply in_map_iff in Hz as (i & <- & Hi'). apply in_seq in Hi'.
    specialize (Hr i ltac:(lia)). apply in_map_iff. exists (Z.to_nat (f i)).
    split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length ND Inc) as Hl.
  rewrite !length_map, !length_seq in Hl. lia.
Qed.

Definition nodeN (x : int) : N := Z.to_N (φ x).

Lemma nodeN_Z : forall x, Z.of_N (nodeN x) = (φ x).
Proof. intros x. unfold nodeN. pose proof (to_Z_bounded x). lia. Qed.

Lemma nodeN_inj : forall x y, nodeN x = nodeN y -> x = y.
Proof.
  intros x y E. apply to_Z_inj. rewrite <- (nodeN_Z x), <- (nodeN_Z y), E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The BFS                                                             *)
(* ------------------------------------------------------------------ *)

Section Graph.
Variables eu ev ew : list N.
Variable n : Z.
Variables sa nbr wt : array int.
Variable alive : array bool.
Hypothesis Hn : (1 <= n <= 200000)%Z.
Hypothesis Hsound : forall x j : int, (1 <= (φ x) <= n)%Z ->
  ((φ (sa.[x])) <= (φ j) < (φ (sa.[x + 1])))%Z ->
  exists k, joins eu ev k (nodeN x) (nodeN (nbr.[j])) /\
    (φ (wt.[j])) = Z.of_N (Prelude.get ew k) /\ ((φ (wt.[j])) <= 1000000)%Z.
Hypothesis Halive : forall y : int, alive.[y] = true -> (1 <= (φ y) <= n)%Z.

Definition adj (x j : int) : Prop := ((φ (sa.[x])) <= (φ j) < (φ (sa.[x + 1])))%Z.

Definition witness (root x : int) (dx : Z) : Prop :=
  exists vs ks, walk eu ev vs ks /\ hd_error vs = Some (nodeN root) /\
    last vs 0%N = nodeN x /\ (Z.of_N (wsum ew ks) <= dx)%Z.

Record binv (s root : int) (b : bst) (h : int) : Prop := {
  bi_lv : (φ (PArray.length (b_vis b))) = (n + 1)%Z;
  bi_lc : (φ (PArray.length (b_comp b))) = (n + 1)%Z;
  bi_lp : (φ (PArray.length (b_par b))) = (n + 1)%Z;
  bi_ld : (φ (PArray.length (b_d b))) = (n + 1)%Z;
  bi_ht : ((φ h) <= (φ (b_tail b)) <= n)%Z;
  bi_t1 : (1 <= (φ (b_tail b)))%Z;
  bi_root : (b_comp b).[0] = root;
  bi_in : forall i, ((φ i) < (φ (b_tail b)))%Z ->
    (1 <= (φ ((b_comp b).[i])) <= n)%Z /\ alive.[(b_comp b).[i]] = true /\
    (b_vis b).[(b_comp b).[i]] = s;
  bi_nd : forall i j, ((φ i) < (φ (b_tail b)))%Z -> ((φ j) < (φ (b_tail b)))%Z ->
    (b_comp b).[i] = (b_comp b).[j] -> i = j;
  bi_vis : forall y, (b_vis b).[y] = s -> exists i, ((φ i) < (φ (b_tail b)))%Z /\ (b_comp b).[i] = y;
  bi_le : forall y, ((φ ((b_vis b).[y])) <= (φ s))%Z;
  bi_clo : forall i j, ((φ i) < (φ h))%Z -> adj ((b_comp b).[i]) j -> alive.[nbr.[j]] = true ->
    (b_vis b).[nbr.[j]] = s;
  bi_flag : b_flag b = true -> forall i j, ((φ i) < (φ h))%Z -> adj ((b_comp b).[i]) j ->
    alive.[nbr.[j]] = true ->
    ((φ ((b_d b).[nbr.[j]])) <= (φ ((b_d b).[(b_comp b).[i]])) + (φ (wt.[j])))%Z;
  bi_wit : forall i, ((φ i) < (φ (b_tail b)))%Z ->
    witness root ((b_comp b).[i]) (φ ((b_d b).[(b_comp b).[i]])) /\
    ((φ ((b_d b).[(b_comp b).[i]])) <= (φ i) * 1000000)%Z
}.

(* the partial scan of x = comp.[h] up to j *)
Definition spart (s : int) (b : bst) (x dx j : int) : Prop :=
  forall j', ((φ (sa.[x])) <= (φ j') < (φ j))%Z -> alive.[nbr.[j']] = true ->
    (b_vis b).[nbr.[j']] = s /\
    (b_flag b = true -> ((φ ((b_d b).[nbr.[j']])) <= (φ dx) + (φ (wt.[j'])))%Z).

Lemma tail_bound : forall s root b h, binv s root b h ->
  forall y, (1 <= (φ y) <= n)%Z -> (b_vis b).[y] <> s -> ((φ (b_tail b)) < n)%Z.
Proof.
  intros s root b h I y Hy Hv.
  set (t := b_tail b). set (c := b_comp b).
  pose proof (bi_t1 _ _ _ _ I) as T1. pose proof (bi_ht _ _ _ _ I) as T2.
  assert (Hc : forall i : nat, (i < Z.to_nat (φ t))%nat ->
            (φ (of_Z (Z.of_nat i))) = Z.of_nat i).
  { intros i Hi. apply of_Z_nat_phi. rewrite wB_val. lia. }
  set (f := fun i : nat => if (i <? Z.to_nat (φ t))%nat then (φ (c.[of_Z (Z.of_nat i)])) else (φ y)).
  assert (Z.of_nat (S (Z.to_nat (φ t))) <= n)%Z; [|lia].
  apply (pigeon f); [lia | |].
  - intros i Hi. unfold f. destruct (Nat.ltb_spec i (Z.to_nat (φ t))).
    + destruct (bi_in _ _ _ _ I (of_Z (Z.of_nat i)) ltac:(rewrite Hc; lia)) as [A _]. exact A.
    + exact Hy.
  - intros i j Hi Hj E. unfold f in E.
    destruct (Nat.ltb_spec i (Z.to_nat (φ t))), (Nat.ltb_spec j (Z.to_nat (φ t))).
    + apply to_Z_inj in E. apply (bi_nd _ _ _ _ I) in E; try (rewrite Hc; lia).
      apply (f_equal to_Z) in E. rewrite !Hc in E by lia. lia.
    + exfalso. apply to_Z_inj in E.
      destruct (bi_in _ _ _ _ I (of_Z (Z.of_nat i)) ltac:(rewrite Hc; lia)) as (_ & _ & V).
      apply Hv. rewrite <- E. exact V.
    + exfalso. apply to_Z_inj in E.
      destruct (bi_in _ _ _ _ I (of_Z (Z.of_nat j)) ltac:(rewrite Hc; lia)) as (_ & _ & V).
      apply Hv. rewrite E. exact V.
    + lia.
Qed.

Lemma phi_add_small : forall a b : int, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof. intros a b H. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded a); pose proof (to_Z_bounded b). lia. Qed.

Lemma phi_succ : forall a b : int, ((φ a) < (φ b))%Z -> (φ (a + 1)) = ((φ a) + 1)%Z.
Proof. intros a b H. pose proof (to_Z_bounded b). apply phi_add_small. change (φ 1) with 1%Z. lia. Qed.

Lemma scan_step_ok : forall s root b h j dx,
  binv s root b h -> ((φ h) < (φ (b_tail b)))%Z ->
  (b_d b).[(b_comp b).[h]] = dx ->
  spart s b ((b_comp b).[h]) dx j -> adj ((b_comp b).[h]) j ->
  let b' := scan_step alive s ((b_comp b).[h]) dx nbr.[j] wt.[j] b in
  binv s root b' h /\ spart s b' ((b_comp b).[h]) dx (j + 1) /\
  (b_d b').[(b_comp b').[h]] = dx /\ (b_comp b').[h] = (b_comp b).[h].
Proof.
  intros s root b h j dx I Hh Hdx Sp Ha b'.
  set (x := (b_comp b).[h]) in *.
  destruct (bi_in _ _ _ _ I h Hh) as (Hx & Ax & Vx).
  destruct (Hsound x j Hx Ha) as (k & Jk & Wk & Wb).
  destruct (bi_wit _ _ _ _ I h Hh) as [Wx Bx]. fold x in Wx, Bx. rewrite Hdx in Wx, Bx.
  pose proof (bi_ht _ _ _ _ I) as Ht.
  assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by (apply (phi_succ j (sa.[x+1])); unfold adj in Ha; lia).
  assert (Hdw : (φ (dx + wt.[j])) = ((φ dx) + (φ (wt.[j])))%Z) by (apply phi_add_small; rewrite wB_val; nia).
  unfold b', scan_step.
  destruct (alive.[nbr.[j]]) eqn:Ay.
  2:{ split; [exact I|]. split; [|split; [exact Hdx | reflexivity]].
      intros j' Hj' Aj'. destruct (Z.eq_dec (φ j') (φ j)).
      - apply to_Z_inj in e. subst j'. congruence.
      - apply Sp; auto. lia. }
  set (y := nbr.[j]) in *.
  destruct ((b_vis b).[y] =? s) eqn:Vy.
  - apply eqb_true in Vy. destruct b as [vis comp par d t fl]; simpl in *.
    split; [|split; [|split; [exact Hdx | reflexivity]]].
    + destruct I; constructor; simpl; auto.
      intros F. apply andb_prop in F as [F _]. auto.
    + intros j' Hj' Aj'. destruct (Z.eq_dec (φ j') (φ j)).
      * apply to_Z_inj in e. subst j'. fold y. split; auto. intros F.
        apply andb_prop in F as [_ F]. apply leb_true in F. rewrite Hdw in F. simpl. lia.
      * destruct (Sp j' ltac:(lia) Aj') as [S1 S2]. split; auto.
        intros F. apply andb_prop in F as [F _]. auto.
  - apply eqb_false in Vy.
    pose proof (Halive y Ay) as Hy.
    pose proof (tail_bound _ _ _ _ I y Hy Vy) as Ht'.
    clear b'. destruct b as [vis comp par d t fl]; simpl in *.
    destruct I as [Lv Lc Lp Ld HT T1 R IN ND VI LE CL FL WI]; simpl in *.
    assert (Hyl : (y <? PArray.length vis) = true) by (apply ltb_true; lia).
    assert (Hyd : (y <? PArray.length d) = true) by (apply ltb_true; lia).
    assert (Hyp : (y <? PArray.length par) = true) by (apply ltb_true; lia).
    assert (Htl : (t <? PArray.length comp) = true) by (apply ltb_true; lia).
    assert (Hcy : forall i, ((φ i) < (φ t))%Z -> comp.[i] <> y).
    { intros i Hi E. destruct (IN i Hi) as (_ & _ & V). rewrite E in V. auto. }
    assert (Hcomp : forall i, comp.[t <- y].[i] = if t =? i then y else comp.[i])
      by (intros; apply aget_set; auto).
    assert (Hvis : forall z, vis.[y <- s].[z] = if y =? z then s else vis.[z])
      by (intros; apply aget_set; auto).
    assert (Hd : forall z, d.[y <- dx + wt.[j]].[z] = if y =? z then dx + wt.[j] else d.[z])
      by (intros; apply aget_set; auto).
    assert (Hvy : forall z, vis.[z] = s -> y <> z) by (intros z Hz E; subst; auto).
    assert (Ht1 : (φ (t + 1)) = ((φ t) + 1)%Z) by (apply (phi_succ t (of_Z n)); rewrite of_Z_spec, Z.mod_small; rewrite ?wB_val; lia).
    assert (Hxy : x <> y) by (apply Hcy; lia).
    assert (Ex : comp.[t <- y].[h] = x).
    { rewrite Hcomp. destruct (t =? h) eqn:E; [apply eqb_true in E; subst; lia | reflexivity]. }
    split; [|split; [|split]].
    + constructor; simpl.
      * rewrite alength_set; auto.
      * rewrite alength_set; auto.
      * rewrite alength_set; auto.
      * rewrite alength_set; auto.
      * lia.
      * lia.
      * rewrite Hcomp. destruct (t =? 0) eqn:E; [apply eqb_true in E; subst; change (φ 0) with 0%Z in T1; lia | auto].
      * intros i Hi. rewrite Hcomp. destruct (t =? i) eqn:E.
        -- apply eqb_true in E. subst. rewrite Hvis, Uint63.eqb_refl. repeat split; auto; lia.
        -- apply eqb_false in E. assert ((φ i) < (φ t))%Z by (assert ((φ i) <> (φ t)) by (intro F; apply E; apply to_Z_inj; auto); lia).
           destruct (IN i H) as (A1 & A2 & A3). rewrite Hvis.
           destruct (y =? comp.[i]) eqn:E2; [apply eqb_true in E2; exfalso; apply (Hcy i H); auto|]. repeat split; auto; lia.
      * intros i i' Hi Hi' E. rewrite !Hcomp in E.
        assert (Lt : forall i0, ((φ i0) < (φ (t + 1)))%Z -> (t =? i0) = false -> ((φ i0) < (φ t))%Z).
        { intros i0 H1 H2. apply eqb_false in H2.
          assert ((φ i0) <> (φ t)) by (intro F; apply H2; apply to_Z_inj; auto). lia. }
        destruct (t =? i) eqn:E1; destruct (t =? i') eqn:E2.
        -- apply eqb_true in E1, E2. congruence.
        -- exfalso. apply (Hcy i' (Lt i' Hi' E2)). auto.
        -- exfalso. apply (Hcy i (Lt i Hi E1)). auto.
        -- apply ND; auto.
      * intros z Hz. rewrite Hvis in Hz. destruct (y =? z) eqn:E.
        -- apply eqb_true in E. subst. exists t. split; [lia|]. rewrite Hcomp, Uint63.eqb_refl. auto.
        -- destruct (VI z Hz) as (i & Hi & Ei). exists i. split; [lia|]. rewrite Hcomp.
           destruct (t =? i) eqn:E2; [apply eqb_true in E2; subst; lia | auto].
      * intros z. rewrite Hvis. destruct (y =? z); [lia | apply LE].
      * intros i j0 Hi Hadj Aj.
        destruct (t =? i) eqn:E; [apply eqb_true in E; subst; lia|].
        assert (Ci : comp.[t<-y].[i] = comp.[i]) by (rewrite Hcomp, E; reflexivity).
        rewrite Ci in Hadj. pose proof (CL i j0 Hi Hadj Aj) as C0.
        rewrite (Hvis (nbr.[j0])). destruct (y =? nbr.[j0]); [reflexivity | exact C0].
      * intros F i j0 Hi Hadj Aj.
        destruct (t =? i) eqn:E; [apply eqb_true in E; subst; lia|].
        assert (Ci : comp.[t<-y].[i] = comp.[i]) by (rewrite Hcomp, E; reflexivity).
        rewrite Ci in Hadj |- *.
        pose proof (CL i j0 Hi Hadj Aj) as C1.
        rewrite !Hd.
        destruct (y =? nbr.[j0]) eqn:E1; [apply eqb_true in E1; exfalso; apply (Hvy _ C1); auto|].
        destruct (y =? comp.[i]) eqn:E2; [apply eqb_true in E2; exfalso; apply (Hcy i ltac:(lia)); auto|].
        apply FL; auto.
      * intros i Hi. rewrite Hcomp. destruct (t =? i) eqn:E.
        -- apply eqb_true in E. subst i. rewrite Hd, Uint63.eqb_refl. rewrite Hdw. split.
           ++ destruct Wx as (vs & ks & W & H1 & H2 & H3).
              destruct (walk_extend eu ev vs ks (nodeN x) k (nodeN y) W H2 Jk) as (vs' & W' & H1' & H2').
              exists vs', (ks ++ [k]). split; [auto|]. split; [congruence|]. split; [auto|].
              rewrite wsum_app. simpl. rewrite Wk in *. lia.
           ++ lia.
        -- apply eqb_false in E. assert ((φ i) < (φ t))%Z by (assert ((φ i) <> (φ t)) by (intro F; apply E; apply to_Z_inj; auto); lia).
           rewrite Hd. destruct (y =? comp.[i]) eqn:E2; [apply eqb_true in E2; exfalso; apply (Hcy i H); auto|].
           apply WI; auto.
    + intros j' Hj' Aj'. simpl. rewrite Hvis, !Hd.
      destruct (Z.eq_dec (φ j') (φ j)).
      * apply to_Z_inj in e. subst j'. fold y. rewrite Uint63.eqb_refl. split; auto. intros _. lia.
      * destruct (Sp j' ltac:(lia) Aj') as [S1 S2]. simpl in S1, S2.
        destruct (y =? nbr.[j']) eqn:E1; [apply eqb_true in E1; exfalso; apply (Hvy _ S1); auto|].
        split; auto.
    + simpl. rewrite Ex, Hd. destruct (y =? x) eqn:E; [apply eqb_true in E; congruence | auto].
    + simpl. exact Ex.
Qed.

Lemma scan_loop_eq : forall nbr wt alive s x dx e j b H,
  scan_loop nbr wt alive s x dx e j b H =
  match bdec (j <? e) with
  | left Hj =>
      scan_loop nbr wt alive s x dx e (j + 1)
        (scan_step alive s x dx nbr.[j] wt.[j] b)
        (Acc_inv H (dec_step e j Hj))
  | right _ => b
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_loop_ok : forall s root h x dx z j b H,
  gap (sa.[x + 1]) j = z ->
  binv s root b h -> ((φ h) < (φ (b_tail b)))%Z ->
  (b_comp b).[h] = x -> (b_d b).[x] = dx ->
  spart s b x dx j -> ((φ (sa.[x])) <= (φ j))%Z ->
  let b' := scan_loop nbr wt alive s x dx (sa.[x + 1]) j b H in
  binv s root b' h /\
  (forall j', adj x j' -> alive.[nbr.[j']] = true ->
     (b_vis b').[nbr.[j']] = s /\
     (b_flag b' = true -> ((φ ((b_d b').[nbr.[j']])) <= (φ dx) + (φ (wt.[j'])))%Z)) /\
  (b_d b').[x] = dx /\ (b_comp b').[h] = x /\
  ((φ (b_tail b)) <= (φ (b_tail b')))%Z.
Proof.
  intros s root h x dx z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j b H Hz I Hh Ex Hdx Sp Hj b'. unfold b'. clear b'.
  rewrite scan_loop_eq.
  destruct (bdec (j <? sa.[x + 1])) as [Hl | Hl].
  - pose proof Hl as Hl'. apply ltb_true in Hl'.
    pose proof (scan_step_ok s root b h j dx I Hh) as SS.
    rewrite Ex in SS. specialize (SS Hdx Sp ltac:(unfold adj; lia)).
    destruct SS as (I' & Sp' & Hdx' & Ex').
    set (b1 := scan_step alive s x dx nbr.[j] wt.[j] b) in *.
    rewrite Ex' in Hdx'.
    pose proof (bi_ht _ _ _ _ I') as Ht1.
    assert (Tm : ((φ (b_tail b)) <= (φ (b_tail b1)))%Z).
    { unfold b1, scan_step. destruct (alive.[nbr.[j]]); [|simpl; lia].
      destruct ((b_vis b).[nbr.[j]] =? s); simpl; [lia|].
      destruct (Z.le_gt_cases (φ (b_tail b)) (φ (b_tail b + 1))) as [A|A]; [exact A|].
      exfalso. pose proof (bi_ht _ _ _ _ I) as B. rewrite add_spec in A.
      change (φ 1) with 1%Z in A. rewrite Z.mod_small in A; [lia|]. rewrite wB_val. lia. }
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by (apply (phi_succ j _ Hl')).
    destruct (IH (gap (sa.[x + 1]) (j + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hl)
                (j + 1) b1 (Acc_inv H (dec_step (sa.[x + 1]) j Hl)) eq_refl I'
                ltac:(lia) Ex' Hdx' Sp' ltac:(lia)) as (A1 & A2 & A3 & A4 & A5).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|lia].
  - apply ltb_false in Hl. split; [exact I|]. split; [|split; [exact Hdx|split; [exact Ex|lia]]].
    intros j' Ha Aj. apply Sp; auto. unfold adj in Ha. lia.
Qed.

Lemma phi_lt_succ_eq : forall i h : int, ((φ i) < (φ h) + 1)%Z -> ~ ((φ i) < (φ h))%Z -> i = h.
Proof. intros i h H1 H2. apply to_Z_inj. lia. Qed.

Lemma binv_next : forall s root b b' h x dx,
  binv s root b' h -> ((φ h) < (φ (b_tail b)))%Z -> ((φ (b_tail b)) <= (φ (b_tail b')))%Z ->
  (b_comp b').[h] = x -> (b_d b').[x] = dx ->
  (forall j', adj x j' -> alive.[nbr.[j']] = true ->
     (b_vis b').[nbr.[j']] = s /\
     (b_flag b' = true -> ((φ ((b_d b').[nbr.[j']])) <= (φ dx) + (φ (wt.[j'])))%Z)) ->
  binv s root b' (h + 1).
Proof.
  intros s root b b' h x dx I Hh Ht Ex Hdx A.
  assert (Hh1 : (φ (h + 1)) = ((φ h) + 1)%Z).
  { apply (phi_succ h (b_tail b)). exact Hh. }
  destruct I; constructor; auto.
  - lia.
  - intros i j Hi Ha Al. rewrite Hh1 in Hi. destruct (Z_lt_le_dec (φ i) (φ h)).
    + apply bi_clo0 with (i := i); auto.
    + assert (i = h) by (apply to_Z_inj; lia). subst i. rewrite Ex in Ha. apply (A j Ha Al).
  - intros F i j Hi Ha Al. rewrite Hh1 in Hi. destruct (Z_lt_le_dec (φ i) (φ h)).
    + apply bi_flag0 with (i := i); auto.
    + assert (i = h) by (apply to_Z_inj; lia). subst i. rewrite Ex in Ha |- *. rewrite Hdx.
      apply (A j Ha Al). exact F.
Qed.

Lemma bfs_loop_eq : forall sa nbr wt alive s L head b H,
  bfs_loop sa nbr wt alive s L head b H =
  match bdec (head <? b_tail b) with
  | left _ =>
      match bdec (head <? L) with
      | left Hh =>
          let x := (b_comp b).[head] in
          bfs_loop sa nbr wt alive s L (head + 1)
            (scan_loop nbr wt alive s x (b_d b).[x] sa.[x + 1] sa.[x] b
               (Zwf_well_founded 0 (gap sa.[x + 1] sa.[x])))
            (Acc_inv H (dec_step L head Hh))
      | right _ => b
      end
  | right _ => b
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bfs_loop_ok : forall s root L z h b H,
  (φ L) = (n + 1)%Z -> gap L h = z -> binv s root b h ->
  let b' := bfs_loop sa nbr wt alive s L h b H in
  binv s root b' (b_tail b').
Proof.
  intros s root L z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h b H HL Hz I b'. unfold b'. clear b'.
  rewrite bfs_loop_eq.
  pose proof (bi_ht _ _ _ _ I) as Ht.
  destruct (bdec (h <? b_tail b)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'.
    destruct (bdec (h <? L)) as [HL' | HL']; [|apply ltb_false in HL'; lia].
    cbv zeta.
    set (x := (b_comp b).[h]).
    destruct (scan_loop_ok s root h x ((b_d b).[x]) _ (sa.[x]) b
                (Zwf_well_founded 0 (gap sa.[x + 1] sa.[x])) eq_refl I Hl' eq_refl eq_refl
                ltac:(intros j' Hj'; lia) ltac:(lia)) as (A1 & A2 & A3 & A4 & A5).
    set (b1 := scan_loop nbr wt alive s x (b_d b).[x] sa.[x + 1] sa.[x] b
                (Zwf_well_founded 0 (gap sa.[x + 1] sa.[x]))) in *.
    pose proof (binv_next s root b b1 h x _ A1 Hl' A5 A4 A3 A2) as I1.
    apply (IH (gap L (h + 1))); auto.
    rewrite <- Hz. apply dec_step. exact HL'.
  - apply ltb_false in Hl.
    assert (h = b_tail b) by (apply to_Z_inj; lia). subst h. exact I.
Qed.

Lemma bfs_ok : forall s root vis comp par d,
  (φ (PArray.length vis)) = (n + 1)%Z -> (φ (PArray.length comp)) = (n + 1)%Z ->
  (φ (PArray.length par)) = (n + 1)%Z -> (φ (PArray.length d)) = (n + 1)%Z ->
  alive.[root] = true -> (forall y, ((φ (vis.[y])) < (φ s))%Z) ->
  let b := bfs sa nbr wt alive s root vis comp par d in
  binv s root b (b_tail b).
Proof.
  intros s root vis comp par d Lv Lc Lp Ld Ar Vs b. unfold b, bfs. clear b.
  pose proof (Halive root Ar) as Hr.
  assert (Hrv : (root <? PArray.length vis) = true) by (apply ltb_true; lia).
  assert (Hrd : (root <? PArray.length d) = true) by (apply ltb_true; lia).
  assert (H0c : (0 <? PArray.length comp) = true) by (apply ltb_true; change (φ 0) with 0%Z; lia).
  apply (bfs_loop_ok s root (PArray.length comp) (gap (PArray.length comp) 0) 0); [exact Lc | reflexivity |].
  unfold bfs_init. constructor; simpl.
  - rewrite alength_set; auto.
  - rewrite alength_set; auto.
  - rewrite alength_set; auto.
  - rewrite alength_set; auto.
  - change (φ 0) with 0%Z. change (φ 1) with 1%Z. lia.
  - change (φ 1) with 1%Z. lia.
  - apply aget_set_same; auto.
  - intros i Hi. change (φ 1) with 1%Z in Hi.
    assert (i = 0) by (apply to_Z_inj; pose proof (to_Z_bounded i); change (φ 0) with 0%Z; lia).
    subst i. rewrite aget_set_same by auto. rewrite aget_set_same by auto. auto.
  - intros i j Hi Hj _. change (φ 1) with 1%Z in Hi, Hj.
    apply to_Z_inj. pose proof (to_Z_bounded i). pose proof (to_Z_bounded j). lia.
  - intros y Hy. exists 0. split; [change (φ 0) with 0%Z; change (φ 1) with 1%Z; lia|].
    rewrite aget_set_same by auto. rewrite aget_set in Hy by auto.
    destruct (root =? y) eqn:E; [apply eqb_true in E; auto|].
    specialize (Vs y). rewrite Hy in Vs. lia.
  - intros y. rewrite aget_set by auto. destruct (root =? y); [lia|]. specialize (Vs y). lia.
  - intros i j Hi. change (φ 0) with 0%Z in Hi. pose proof (to_Z_bounded i). lia.
  - intros _ i j Hi. change (φ 0) with 0%Z in Hi. pose proof (to_Z_bounded i). lia.
  - intros i Hi. change (φ 1) with 1%Z in Hi.
    assert (i = 0) by (apply to_Z_inj; pose proof (to_Z_bounded i); change (φ 0) with 0%Z; lia).
    subst i. rewrite aget_set_same by auto. rewrite aget_set_same by auto. change (φ 0) with 0%Z.
    split; [|lia]. exists [nodeN root], []. split; [constructor|]. split; [reflexivity|].
    split; [reflexivity|]. simpl. lia.
Qed.

Definition Bd : Z := 200000000000%Z.

Definition RI (root : int) (comp : array int) (t : int) (d : array int) : Prop :=
  (φ (PArray.length d)) = (n + 1)%Z /\
  forall i, ((φ i) < (φ t))%Z ->
    witness root (comp.[i]) (φ (d.[comp.[i]])) /\ ((φ (d.[comp.[i]])) <= Bd)%Z.

Section Relax.
Variables (root : int) (comp : array int) (t : int).
Hypothesis Hin : forall i, ((φ i) < (φ t))%Z -> (1 <= (φ (comp.[i])) <= n)%Z.
Hypothesis Hclo : forall i j, ((φ i) < (φ t))%Z -> adj (comp.[i]) j -> alive.[nbr.[j]] = true ->
  exists i', ((φ i') < (φ t))%Z /\ comp.[i'] = nbr.[j].

Lemma rscan_ok : forall i dx z j d ch H,
  ((φ i) < (φ t))%Z -> witness root (comp.[i]) (φ dx) -> ((φ dx) <= Bd)%Z ->
  gap (sa.[comp.[i] + 1]) j = z -> ((φ (sa.[comp.[i]])) <= (φ j))%Z -> RI root comp t d ->
  let r := rscan nbr wt alive dx (sa.[comp.[i] + 1]) j d ch H in
  RI root comp t (fst r) /\
  (snd r = false -> ch = false /\ fst r = d /\
     forall j', ((φ j) <= (φ j') < (φ (sa.[comp.[i] + 1])))%Z -> alive.[nbr.[j']] = true ->
       ((φ (d.[nbr.[j']])) <= (φ dx) + (φ (wt.[j'])))%Z).
Proof.
  intros i dx z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j d ch H Hi Wx Bx Hz Hj [Ld RId] r. unfold r. clear r.
  set (x := comp.[i]) in *.
  rewrite rscan_eq. destruct (bdec (j <? sa.[x + 1])) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by (apply (phi_succ j _ Hl')).
    assert (Ha : adj x j) by (unfold adj; lia).
    destruct (Hsound x j (Hin i Hi) Ha) as (k & Jk & Wk & Wb).
    assert (Hnv : (φ (dx + wt.[j])) = ((φ dx) + (φ (wt.[j])))%Z) by (apply phi_add_small; unfold Bd in Bx; rewrite wB_val; lia).
    cbv zeta.
    destruct (alive.[nbr.[j]] && (nbr.[j] <? PArray.length d) && (dx + wt.[j] <? d.[nbr.[j]])) eqn:C.
    + apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
      apply ltb_true in C2, C3.
      destruct (Hclo i j Hi Ha C1) as (i' & Hi' & Ei').
      assert (RI root comp t d.[nbr.[j] <- dx + wt.[j]]) as RI'.
      { split; [rewrite alength_set; auto|].
        intros i0 Hi0. rewrite aget_set by (apply ltb_true; auto).
        destruct (nbr.[j] =? comp.[i0]) eqn:E.
        - apply eqb_true in E. rewrite <- E. split.
          + destruct Wx as (vs & ks & W & H1 & H2 & H3).
            destruct (walk_extend eu ev vs ks (nodeN x) k (nodeN (nbr.[j])) W H2 Jk) as (vs' & W' & H1' & H2').
            exists vs', (ks ++ [k]). split; [auto|]. split; [congruence|]. split; [auto|].
            rewrite wsum_app. simpl. lia.
          + destruct (RId i' Hi') as [_ B]. rewrite Ei' in B. lia.
        - apply RId; auto. }
      edestruct (IH (gap (sa.[x + 1]) (j + 1))) as [A1 A2];
        [rewrite <- Hz; apply dec_step; exact Hl | exact Hi | exact Wx | exact Bx | reflexivity | lia | exact RI' |].
      split; [exact A1|]. intros F. destruct (A2 F) as [F1 _]. discriminate.
    + edestruct (IH (gap (sa.[x + 1]) (j + 1))) as [A1 A2];
        [rewrite <- Hz; apply dec_step; exact Hl | exact Hi | exact Wx | exact Bx | reflexivity | lia | split; [exact Ld | exact RId] |].
      split; [exact A1|]. intros F. destruct (A2 F) as (F1 & F2 & F3).
      split; [auto|]. split; [auto|].
      intros j' Hj' Aj'. destruct (Z.eq_dec (φ j') (φ j)).
      * apply to_Z_inj in e. subst j'.
        destruct (Hclo i j Hi Ha Aj') as (i' & Hi' & Ei').
        pose proof (Hin i' Hi') as Hy. rewrite Ei' in Hy.
        rewrite Aj' in C. simpl in C.
        assert (C' : (nbr.[j] <? PArray.length d) = true) by (apply ltb_true; lia).
        rewrite C' in C. simpl in C. apply ltb_false in C. lia.
      * apply F3; auto. lia.
  - apply ltb_false in Hl. split; [split; auto|].
    intros F. split; [auto|]. split; [auto|]. intros j' Hj'. lia.
Qed.

Lemma rpass_ok : forall z i d ch H,
  gap t i = z -> RI root comp t d ->
  let r := rpass sa nbr wt alive comp t i d ch H in
  RI root comp t (fst r) /\
  (snd r = false -> ch = false /\ fst r = d /\
     forall i' j', ((φ i) <= (φ i') < (φ t))%Z -> adj (comp.[i']) j' -> alive.[nbr.[j']] = true ->
       ((φ (d.[nbr.[j']])) <= (φ (d.[comp.[i']])) + (φ (wt.[j'])))%Z).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i d ch H Hz RId r. unfold r. clear r.
  rewrite rpass_eq. destruct (bdec (i <? t)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'. cbv zeta.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply (phi_succ i _ Hl')).
    destruct RId as [Ld RId'].
    destruct (RId' i Hl') as [Wx Bx].
    destruct (rscan_ok i (d.[comp.[i]]) _ (sa.[comp.[i]]) d ch
                (Zwf_well_founded 0 (gap sa.[comp.[i] + 1] sa.[comp.[i]]))
                Hl' Wx Bx eq_refl ltac:(lia) (conj Ld RId')) as [A1 A2].
    set (r0 := rscan nbr wt alive d.[comp.[i]] sa.[comp.[i] + 1] sa.[comp.[i]] d ch
                (Zwf_well_founded 0 (gap sa.[comp.[i] + 1] sa.[comp.[i]]))) in *.
    edestruct (IH (gap t (i + 1))) as [B1 B2];
      [rewrite <- Hz; apply dec_step; exact Hl | reflexivity | exact A1 |].
    split; [exact B1|]. intros F. destruct (B2 F) as (F1 & F2 & F3).
    destruct (A2 F1) as (G1 & G2 & G3).
    split; [auto|]. split; [congruence|].
    intros i' j' Hi' Ha Al. destruct (Z.eq_dec (φ i') (φ i)).
    + apply to_Z_inj in e. subst i'. apply G3; auto; unfold adj in Ha; lia.
    + rewrite G2 in F3. apply F3; auto. lia.
  - apply ltb_false in Hl. split; [auto|]. intros F. split; [auto|]. split; [auto|].
    intros. lia.
Qed.

Lemma rloop_ok : forall z d H, dsum d = z -> RI root comp t d ->
  let d' := rloop sa nbr wt alive comp t d H in
  RI root comp t d' /\
  forall i' j', ((φ i') < (φ t))%Z -> adj (comp.[i']) j' -> alive.[nbr.[j']] = true ->
    ((φ (d'.[nbr.[j']])) <= (φ (d'.[comp.[i']])) + (φ (wt.[j'])))%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d H Hz RId d'. unfold d'. clear d'.
  destruct H as [H]. simpl. cbv zeta.
  destruct (rpass_ok _ 0 d false (Zwf_well_founded 0 (gap t 0)) eq_refl RId) as [A1 A2].
  destruct (bdec (snd (rpass sa nbr wt alive comp t 0 d false (Zwf_well_founded 0 (gap t 0))))) as [Hc | Hc].
  - apply (IH (dsum (fst (rpass sa nbr wt alive comp t 0 d false (Zwf_well_founded 0 (gap t 0)))))); auto.
    rewrite <- Hz. apply rloop_step. exact Hc.
  - destruct (A2 Hc) as (_ & E & F). split; [exact A1|]. rewrite E.
    intros i' j' Hi'. apply F. pose proof (to_Z_bounded i'). change (φ 0) with 0%Z. lia.
Qed.

End Relax.

Lemma relax_ok : forall s root b,
  binv s root b (b_tail b) ->
  let d := relax sa nbr wt alive (b_comp b) (b_tail b) b in
  RI root (b_comp b) (b_tail b) d /\
  forall i' j', ((φ i') < (φ (b_tail b)))%Z -> adj ((b_comp b).[i']) j' -> alive.[nbr.[j']] = true ->
    ((φ (d.[nbr.[j']])) <= (φ (d.[(b_comp b).[i']])) + (φ (wt.[j'])))%Z.
Proof.
  intros s root b I d. unfold d, relax. clear d.
  assert (RI0 : RI root (b_comp b) (b_tail b) (b_d b)).
  { split; [apply (bi_ld _ _ _ _ I)|]. intros i Hi. destruct (bi_wit _ _ _ _ I i Hi) as [W B].
    split; [exact W|]. pose proof (bi_ht _ _ _ _ I). unfold Bd. nia. }
  destruct (b_flag b) eqn:F.
  - split; [exact RI0|]. intros. apply (bi_flag _ _ _ _ I F); auto.
  - apply (rloop_ok root (b_comp b) (b_tail b)) with (z := dsum (b_d b)); auto.
    + intros i Hi. apply (bi_in _ _ _ _ I i Hi).
    + intros i j Hi Ha Al. pose proof (bi_clo _ _ _ _ I i j Hi Ha Al) as V.
      apply (bi_vis _ _ _ _ I _ V).
Qed.

End Graph.

(* ------------------------------------------------------------------ *)
(* The Li Chao tree                                                    *)
(* ------------------------------------------------------------------ *)

Lemma INF_val : (φ INF) = 4611686018427387904%Z.
Proof. reflexivity. Qed.

Definition lv (m b x : int) : Z := ((φ m) * (φ x) + (φ b))%Z.

Lemma lv_phi : forall m b x : int, ((φ m) <= 1000000)%Z -> ((φ x) <= 1000001)%Z -> ((φ b) <= Bd)%Z ->
  (φ (m * x + b)) = lv m b x /\ (lv m b x < (φ INF))%Z.
Proof.
  intros m b x Hm Hx Hb. unfold lv, Bd in *. rewrite INF_val.
  pose proof (to_Z_bounded m); pose proof (to_Z_bounded x); pose proof (to_Z_bounded b).
  assert ((φ m) * (φ x) <= 1000000 * 1000001)%Z by nia.
  split; [|lia].
  rewrite add_spec, mul_spec. rewrite (Z.mod_small ((φ m) * (φ x))) by (rewrite wB_val; lia).
  apply Z.mod_small. rewrite wB_val. lia.
Qed.

Lemma conv1 : forall A B lo x mid : Z, (lo <= x <= mid)%Z ->
  (0 <= A * lo + B)%Z -> (0 <= A * mid + B)%Z -> (0 <= A * x + B)%Z.
Proof. intros. destruct (Z_le_gt_dec 0 A); nia. Qed.

Lemma conv2 : forall A B lo x mid : Z, (lo <= mid <= x)%Z ->
  (A * lo + B < 0)%Z -> (0 <= A * mid + B)%Z -> (0 <= A * x + B)%Z.
Proof. intros. destruct (Z_le_gt_dec A 0); nia. Qed.

Lemma lv_conv1 : forall om ob wm wb lo mid x : int,
  (lv wm wb lo <= lv om ob lo)%Z -> (lv wm wb mid <= lv om ob mid)%Z ->
  ((φ lo) <= (φ x) <= (φ mid))%Z -> (lv wm wb x <= lv om ob x)%Z.
Proof.
  intros om ob wm wb lo mid x H1 H2 H3. unfold lv in *.
  pose proof (conv1 ((φ om) - (φ wm)) ((φ ob) - (φ wb)) (φ lo) (φ x) (φ mid) H3 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma lv_conv2 : forall om ob wm wb lo mid x : int,
  (lv om ob lo < lv wm wb lo)%Z -> (lv wm wb mid <= lv om ob mid)%Z ->
  ((φ lo) <= (φ mid) <= (φ x))%Z -> (lv wm wb x <= lv om ob x)%Z.
Proof.
  intros om ob wm wb lo mid x H1 H2 H3. unfold lv in *.
  pose proof (conv2 ((φ om) - (φ wm)) ((φ ob) - (φ wb)) (φ lo) (φ x) (φ mid) H3 ltac:(lia) ltac:(lia)). lia.
Qed.

Section LiChao.
Variables X s : int.
Hypothesis HX : (1 <= (φ X) <= 1000001)%Z.

Definition inK (lo hi k : int) : Prop :=
  ((φ lo) < (φ k) <= (φ hi))%Z \/ ((φ X) + (φ lo) <= (φ k) <= (φ X) + (φ hi))%Z.

Definition agree (P : int -> Prop) (T1 T2 : lct) : Prop :=
  forall k, P k -> (l_st T1).[k] = (l_st T2).[k] /\ (l_m T1).[k] = (l_m T2).[k] /\
                   (l_b T1).[k] = (l_b T2).[k].

Definition LW (T : lct) : Prop :=
  (φ (PArray.length (l_st T))) = ((φ X) + (φ X))%Z /\ (φ (PArray.length (l_m T))) = ((φ X) + (φ X))%Z /\
  (φ (PArray.length (l_b T))) = ((φ X) + (φ X))%Z.

Definition VB (T : lct) : Prop :=
  forall k, (l_st T).[k] = s -> ((φ ((l_m T).[k])) <= 1000000)%Z /\ ((φ ((l_b T).[k])) <= Bd)%Z.

Definition dom (lo hi : int) : Prop := ((φ lo) <= (φ hi) < (φ X))%Z.

Lemma mid_phi : forall lo hi : int, ((φ lo) <= (φ hi))%Z ->
  (φ (lo + (hi - lo) / 2)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z.
Proof. intros lo hi H. sia. Qed.

Lemma key_phi : forall lo hi, dom lo hi ->
  (φ (lkey X lo hi)) = if ((φ lo) =? (φ hi))%Z then ((φ X) + (φ lo))%Z else ((φ lo) + ((φ hi) - (φ lo)) / 2 + 1)%Z.
Proof.
  intros lo hi D. unfold dom in D. unfold lkey.
  destruct (lo =? hi) eqn:E.
  - apply eqb_true in E. subst. rewrite Z.eqb_refl. apply phi_add_small. rewrite wB_val. lia.
  - apply eqb_false in E. assert ((φ lo) <> (φ hi)) by (intro F; apply E; apply to_Z_inj; auto).
    replace ((φ lo) =? (φ hi))%Z with false by (symmetry; apply Z.eqb_neq; auto).
    rewrite phi_add_small; rewrite mid_phi by lia; change (φ 1) with 1%Z; [lia|].
    rewrite wB_val. pose proof (Z.div_le_upper_bound ((φ hi) - (φ lo)) 2 ((φ hi) - (φ lo))). lia.
Qed.

Lemma key_in : forall lo hi, dom lo hi -> inK lo hi (lkey X lo hi) /\ ((φ (lkey X lo hi)) < (φ X) + (φ X))%Z.
Proof.
  intros lo hi D. unfold inK. rewrite key_phi by auto. unfold dom in *.
  destruct ((φ lo) =? (φ hi))%Z eqn:E.
  - apply Z.eqb_eq in E. split; [right|]; lia.
  - apply Z.eqb_neq in E. pose proof (Z.div_pos ((φ hi) - (φ lo)) 2). pose proof (Z.div_le_upper_bound ((φ hi) - (φ lo)) 2 ((φ hi) - (φ lo))).
    assert (((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z by (apply Z.div_lt; lia).
    split; [left|]; lia.
Qed.

Lemma lc_query_eq : forall lo hi x T H,
  lc_query X s lo hi x T H =
  let k := lkey X lo hi in
  let v := if (l_st T).[k] =? s then (l_m T).[k] * x + (l_b T).[k] else INF in
  match bdec (lo <? hi) with
  | left Hlh =>
      let mid := lo + (hi - lo) / 2 in
      let r := if x <=? mid then lc_query X s lo mid x T (Acc_inv H (lc_left lo hi Hlh))
               else lc_query X s (mid + 1) hi x T (Acc_inv H (lc_right lo hi Hlh)) in
      if r <? v then r else v
  | right _ => v
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma lc_insert_eq : forall lo hi m b T H,
  lc_insert X s lo hi m b T H =
  let k := lkey X lo hi in
  if (l_st T).[k] =? s then
    let cm := (l_m T).[k] in
    let cb := (l_b T).[k] in
    let mid := lo + (hi - lo) / 2 in
    let nb := m * mid + b <? cm * mid + cb in
    let wm := if nb then m else cm in
    let wb := if nb then b else cb in
    let om := if nb then cm else m in
    let ob := if nb then cb else b in
    let T1 := if nb then mkL (l_st T) (l_m T).[k <- m] (l_b T).[k <- b] else T in
    match bdec (lo <? hi) with
    | left Hlh =>
        if om * lo + ob <? wm * lo + wb then
          lc_insert X s lo mid om ob T1 (Acc_inv H (lc_left lo hi Hlh))
        else
          lc_insert X s (mid + 1) hi om ob T1 (Acc_inv H (lc_right lo hi Hlh))
    | right _ => T1
    end
  else mkL (l_st T).[k <- s] (l_m T).[k <- m] (l_b T).[k <- b].
Proof. intros. destruct H. reflexivity. Qed.

(* the children's ranges *)
Lemma child_facts : forall lo hi, dom lo hi -> ((φ lo) < (φ hi))%Z ->
  let mid := lo + (hi - lo) / 2 in
  dom lo mid /\ dom (mid + 1) hi /\
  (φ mid) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z /\ (φ (mid + 1)) = ((φ mid) + 1)%Z /\
  ((φ lo) <= (φ mid) < (φ hi))%Z /\ (φ (lkey X lo hi)) = ((φ mid) + 1)%Z.
Proof.
  intros lo hi D Hl mid. unfold dom in *.
  assert (Hm : (φ mid) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z) by (apply mid_phi; lia).
  pose proof (Z.div_pos ((φ hi) - (φ lo)) 2).
  assert (((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z by (apply Z.div_lt; lia).
  assert (Hm1 : (φ (mid + 1)) = ((φ mid) + 1)%Z) by (apply phi_add_small; rewrite wB_val; change (φ 1) with 1%Z; lia).
  rewrite key_phi by (unfold dom; lia).
  replace ((φ lo) =? (φ hi))%Z with false by (symmetry; apply Z.eqb_neq; lia).
  repeat split; lia.
Qed.

Lemma query_frame : forall z lo hi x T1 T2 H1 H2,
  gap hi lo = z -> dom lo hi -> agree (inK lo hi) T1 T2 ->
  lc_query X s lo hi x T1 H1 = lc_query X s lo hi x T2 H2.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi x T1 T2 H1 H2 Hz D A.
  rewrite (lc_query_eq lo hi x T1), (lc_query_eq lo hi x T2). cbv zeta.
  destruct (key_in lo hi D) as [Kin _].
  destruct (A _ Kin) as (E1 & E2 & E3). rewrite E1, E2, E3.
  destruct (bdec (lo <? hi)) as [Hl | Hl]; [|reflexivity].
  apply ltb_true in Hl as Hl'.
  destruct (child_facts lo hi D Hl') as (D1 & D2 & M1 & M2 & M3 & _).
  destruct (x <=? lo + (hi - lo) / 2).
  - erewrite (IH (gap (lo + (hi - lo) / 2) lo)); [reflexivity | | reflexivity | exact D1 |].
    + rewrite <- Hz. apply lc_left. exact Hl.
    + intros k Hk. apply A. unfold inK in *. lia.
  - erewrite (IH (gap hi (lo + (hi - lo) / 2 + 1))); [reflexivity | | reflexivity | exact D2 |].
    + rewrite <- Hz. apply lc_right. exact Hl.
    + intros k Hk. apply A. unfold inK in *. lia.
Qed.

Lemma agree_refl : forall P T, agree P T T.
Proof. intros P T k _. auto. Qed.

Lemma agree_trans : forall P T1 T2 T3, agree P T1 T2 -> agree P T2 T3 -> agree P T1 T3.
Proof. intros P T1 T2 T3 A B k Hk. destruct (A k Hk) as (? & ? & ?), (B k Hk) as (? & ? & ?). split; [congruence|split; congruence]. Qed.

Lemma agree_weaken : forall (P Q : int -> Prop) T1 T2, (forall k, Q k -> P k) -> agree P T1 T2 -> agree Q T1 T2.
Proof. intros P Q T1 T2 H A k Hk. apply A. auto. Qed.

Lemma agree_sym : forall P T1 T2, agree P T1 T2 -> agree P T2 T1.
Proof. intros P T1 T2 A k Hk. destruct (A k Hk) as (? & ? & ?). auto. Qed.

(* insertion keeps the lengths and the bounds, and touches only its range *)
Lemma insert_frame : forall z lo hi m b T H,
  gap hi lo = z -> dom lo hi -> LW T -> VB T ->
  ((φ m) <= 1000000)%Z -> ((φ b) <= Bd)%Z ->
  let T' := lc_insert X s lo hi m b T H in
  LW T' /\ VB T' /\ agree (fun k => ~ inK lo hi k) T' T.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi m b T H Hz D L V Hm Hb T'. unfold T'. clear T'.
  rewrite lc_insert_eq. cbv zeta.
  destruct (key_in lo hi D) as [Kin Kb].
  set (k := lkey X lo hi) in *.
  destruct L as (L1 & L2 & L3).
  assert (Ks : (k <? PArray.length (l_st T)) = true) by (apply ltb_true; lia).
  assert (Km : (k <? PArray.length (l_m T)) = true) by (apply ltb_true; lia).
  assert (Kb' : (k <? PArray.length (l_b T)) = true) by (apply ltb_true; lia).
  destruct ((l_st T).[k] =? s) eqn:Sk.
  - apply eqb_true in Sk. destruct (V k Sk) as [Vm Vb].
    set (nb := m * (lo + (hi - lo) / 2) + b <? (l_m T).[k] * (lo + (hi - lo) / 2) + (l_b T).[k]).
    set (T1 := if nb then mkL (l_st T) (l_m T).[k <- m] (l_b T).[k <- b] else T).
    assert (P1 : LW T1 /\ VB T1 /\ agree (fun k' => k' <> k) T1 T).
    { unfold T1. destruct nb.
      - split; [unfold LW; simpl; rewrite !alength_set; auto|]. split.
        + intros k' Hk'. simpl in *. rewrite !aget_set by auto.
          destruct (k =? k') eqn:E; [lia| apply V; auto].
        + intros k' Hk'. simpl. rewrite !aget_set by auto.
          destruct (k =? k') eqn:E; [apply eqb_true in E; congruence | auto].
      - split; [unfold LW; auto|]. split; [auto|apply agree_refl]. }
    destruct P1 as (LW1 & VB1 & A1).
    assert (Bo : ((φ (if nb then (l_m T).[k] else m)) <= 1000000)%Z /\
                 ((φ (if nb then (l_b T).[k] else b)) <= Bd)%Z) by (destruct nb; auto).
    destruct (bdec (lo <? hi)) as [Hl | Hl].
    + apply ltb_true in Hl as Hl'.
      destruct (child_facts lo hi D Hl') as (D1 & D2 & M1 & M2 & M3 & M4).
      destruct ((if nb then (l_m T).[k] else m) * lo + (if nb then (l_b T).[k] else b) <?
                (if nb then m else (l_m T).[k]) * lo + (if nb then b else (l_b T).[k])).
      * destruct (IH (gap (lo + (hi - lo) / 2) lo) ltac:(rewrite <- Hz; apply lc_left; exact Hl)
          lo (lo + (hi - lo) / 2) _ _ T1 (Acc_inv H (lc_left lo hi Hl)) eq_refl D1 LW1 VB1
          (proj1 Bo) (proj2 Bo)) as (B1 & B2 & B3).
        split; [exact B1|]. split; [exact B2|].
        apply (agree_trans _ _ T1).
        -- eapply agree_weaken; [|exact B3]. intros k' Hk' F. apply Hk'. unfold inK in *. lia.
        -- eapply agree_weaken; [|exact A1]. intros k' Hk' E. subst k'. apply Hk'. exact Kin.
      * destruct (IH (gap hi (lo + (hi - lo) / 2 + 1)) ltac:(rewrite <- Hz; apply lc_right; exact Hl)
          (lo + (hi - lo) / 2 + 1) hi _ _ T1 (Acc_inv H (lc_right lo hi Hl)) eq_refl D2 LW1 VB1
          (proj1 Bo) (proj2 Bo)) as (B1 & B2 & B3).
        split; [exact B1|]. split; [exact B2|].
        apply (agree_trans _ _ T1).
        -- eapply agree_weaken; [|exact B3]. intros k' Hk' F. apply Hk'. unfold inK in *. lia.
        -- eapply agree_weaken; [|exact A1]. intros k' Hk' E. subst k'. apply Hk'. exact Kin.
    + split; [exact LW1|]. split; [exact VB1|]. eapply agree_weaken; [|exact A1].
      intros k' Hk' E. subst k'. auto.
  - split; [unfold LW; simpl; rewrite !alength_set; auto|]. split.
    + intros k' Hk'. simpl in *. rewrite aget_set in Hk' by auto. rewrite !aget_set by auto.
      destruct (k =? k') eqn:E; [lia| apply V; auto].
    + intros k' Hk'. simpl. rewrite !aget_set by auto.
      destruct (k =? k') eqn:E; [apply eqb_true in E; subst; contradiction | auto].
Qed.

Definition qval (T : lct) (k x : int) : Z :=
  if (l_st T).[k] =? s then lv ((l_m T).[k]) ((l_b T).[k]) x else (φ INF).

Lemma v_phi : forall T k x, VB T -> ((φ x) <= 1000001)%Z ->
  (φ (if (l_st T).[k] =? s then (l_m T).[k] * x + (l_b T).[k] else INF)) = qval T k x /\
  (qval T k x <= (φ INF))%Z.
Proof.
  intros T k x V Hx. unfold qval. destruct ((l_st T).[k] =? s) eqn:E; [|lia].
  apply eqb_true in E. destruct (V k E). destruct (lv_phi ((l_m T).[k]) ((l_b T).[k]) x); auto. lia.
Qed.

Lemma min_phi : forall r v : int, (φ (if r <? v then r else v)) = Z.min (φ r) (φ v).
Proof.
  intros r v. destruct (r <? v) eqn:E; [apply ltb_true in E | apply ltb_false in E]; lia.
Qed.

Lemma query_bound : forall z lo hi x T H, gap hi lo = z -> dom lo hi -> VB T ->
  ((φ x) <= 1000001)%Z -> ((φ (lc_query X s lo hi x T H)) <= (φ INF))%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi x T H Hz D V Hx. rewrite lc_query_eq. cbv zeta.
  destruct (v_phi T (lkey X lo hi) x V Hx) as [E1 E2].
  destruct (bdec (lo <? hi)) as [Hl | Hl]; [|lia].
  rewrite min_phi. rewrite E1. lia.
Qed.

Lemma query_empty : forall z lo hi x T H, gap hi lo = z -> dom lo hi ->
  (forall k, inK lo hi k -> (l_st T).[k] <> s) ->
  (φ (lc_query X s lo hi x T H)) = (φ INF).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi x T H Hz D Hk. rewrite lc_query_eq. cbv zeta.
  destruct (key_in lo hi D) as [Kin _].
  destruct ((l_st T).[lkey X lo hi] =? s) eqn:E; [apply eqb_true in E; exfalso; apply (Hk _ Kin E)|].
  destruct (bdec (lo <? hi)) as [Hl | Hl]; [|reflexivity].
  apply ltb_true in Hl as Hl'.
  destruct (child_facts lo hi D Hl') as (D1 & D2 & M1 & M2 & M3 & M4).
  rewrite min_phi.
  destruct (x <=? lo + (hi - lo) / 2).
  - rewrite (IH (gap (lo + (hi - lo) / 2) lo)); [lia | rewrite <- Hz; apply lc_left; exact Hl | reflexivity | exact D1 |].
    intros k Hk'. apply Hk. unfold inK in *. lia.
  - rewrite (IH (gap hi (lo + (hi - lo) / 2 + 1))); [lia | rewrite <- Hz; apply lc_right; exact Hl | reflexivity | exact D2 |].
    intros k Hk'. apply Hk. unfold inK in *. lia.
Qed.

Lemma min_swap : forall q w o c n : Z, (w = n /\ o = c) \/ (w = c /\ o = n) ->
  Z.min (Z.min q o) w = Z.min (Z.min q c) n.
Proof. intros. lia. Qed.

Lemma min_drop : forall q w o c n : Z, (w = n /\ o = c) \/ (w = c /\ o = n) -> (w <= o)%Z ->
  Z.min q w = Z.min (Z.min q c) n.
Proof. intros. lia. Qed.

Lemma min_leaf : forall w o c n : Z, (w = n /\ o = c) \/ (w = c /\ o = n) -> (w <= o)%Z ->
  w = Z.min c n.
Proof. intros. lia. Qed.

Lemma query_node : forall lo hi x T H, dom lo hi -> VB T -> ((φ x) <= 1000001)%Z ->
  let k := lkey X lo hi in
  let mid := lo + (hi - lo) / 2 in
  ((φ lo) = (φ hi) /\ (φ (lc_query X s lo hi x T H)) = qval T k x) \/
  ((φ lo) < (φ hi) /\
   (((φ x) <= (φ mid))%Z -> exists H', (φ (lc_query X s lo hi x T H)) =
       Z.min (φ (lc_query X s lo mid x T H')) (qval T k x)) /\
   (((φ mid) < (φ x))%Z -> exists H', (φ (lc_query X s lo hi x T H)) =
       Z.min (φ (lc_query X s (mid + 1) hi x T H')) (qval T k x))).
Proof.
  intros lo hi x T H D V Hx k mid.
  rewrite lc_query_eq. cbv zeta. fold k mid.
  destruct (v_phi T k x V Hx) as [E1 _].
  destruct (bdec (lo <? hi)) as [Hl | Hl].
  - right. apply ltb_true in Hl as Hl'. split; [exact Hl'|]. rewrite min_phi, E1.
    split; intros Hm.
    + replace (x <=? mid) with true by (symmetry; apply leb_true; lia). eexists; reflexivity.
    + replace (x <=? mid) with false by (symmetry; apply leb_false; lia). eexists; reflexivity.
  - left. apply ltb_false in Hl. unfold dom in D. split; [lia | exact E1].
Qed.

Lemma insert_node : forall lo hi m b T H, dom lo hi -> LW T -> VB T ->
  ((φ m) <= 1000000)%Z -> ((φ b) <= Bd)%Z ->
  let k := lkey X lo hi in
  let mid := lo + (hi - lo) / 2 in
  let T' := lc_insert X s lo hi m b T H in
  ((l_st T).[k] <> s /\ (l_st T').[k] = s /\ (l_m T').[k] = m /\ (l_b T').[k] = b /\
     agree (fun k0 => k0 <> k) T' T) \/
  ((l_st T).[k] = s /\ exists wm wb om ob T1,
     ((lv wm wb = lv m b /\ lv om ob = lv ((l_m T).[k]) ((l_b T).[k])) \/
      (lv wm wb = lv ((l_m T).[k]) ((l_b T).[k]) /\ lv om ob = lv m b)) /\
     (lv wm wb mid <= lv om ob mid)%Z /\
     ((φ om) <= 1000000)%Z /\ ((φ ob) <= Bd)%Z /\
     (l_st T1).[k] = s /\ (l_m T1).[k] = wm /\ (l_b T1).[k] = wb /\
     agree (fun k0 => k0 <> k) T1 T /\ LW T1 /\ VB T1 /\
     (((φ lo) = (φ hi) /\ T' = T1) \/
      ((φ lo) < (φ hi) /\ (lv om ob lo < lv wm wb lo)%Z /\
         exists H', T' = lc_insert X s lo mid om ob T1 H') \/
      ((φ lo) < (φ hi) /\ (lv wm wb lo <= lv om ob lo)%Z /\
         exists H', T' = lc_insert X s (mid + 1) hi om ob T1 H'))).
Proof.
  intros lo hi m b T H D L V Hm Hb k mid T'. unfold T'. clear T'.
  destruct (key_in lo hi D) as [Kin Kb]. fold k in Kin, Kb.
  pose proof L as L0. destruct L0 as (L1 & L2 & L3).
  assert (Ks : (k <? PArray.length (l_st T)) = true) by (apply ltb_true; lia).
  assert (Km : (k <? PArray.length (l_m T)) = true) by (apply ltb_true; lia).
  assert (Kb' : (k <? PArray.length (l_b T)) = true) by (apply ltb_true; lia).
  assert (Hx1 : ((φ mid) <= 1000001)%Z /\ ((φ lo) <= (φ mid) <= (φ hi))%Z).
  { unfold mid. unfold dom in D. rewrite mid_phi by lia.
    pose proof (Z.div_pos ((φ hi) - (φ lo)) 2). pose proof (Z.div_le_upper_bound ((φ hi) - (φ lo)) 2 ((φ hi) - (φ lo))). lia. }
  assert (Hlo1 : ((φ lo) <= 1000001)%Z) by (unfold dom in D; lia).
  rewrite lc_insert_eq. cbv zeta. fold k mid.
  destruct ((l_st T).[k] =? s) eqn:Sk.
  - apply eqb_true in Sk. right. split; [exact Sk|].
    destruct (V k Sk) as [Vm Vb].
    set (cm := (l_m T).[k]) in *. set (cb := (l_b T).[k]) in *.
    assert (Enb : (m * mid + b <? cm * mid + cb) = (lv m b mid <? lv cm cb mid)%Z).
    { destruct (lv_phi m b mid Hm (proj1 Hx1) Hb) as [E1 _]. destruct (lv_phi cm cb mid Vm (proj1 Hx1) Vb) as [E2 _].
      apply eq_iff_eq_true. rewrite ltb_true, Z.ltb_lt. lia. }
    rewrite Enb.
    assert (Gen : forall (nb : bool), (nb = true -> lv m b mid < lv cm cb mid)%Z ->
      (nb = false -> lv cm cb mid <= lv m b mid)%Z ->
      exists wm wb om ob T1,
     ((lv wm wb = lv m b /\ lv om ob = lv cm cb) \/ (lv wm wb = lv cm cb /\ lv om ob = lv m b)) /\
     (lv wm wb mid <= lv om ob mid)%Z /\
     ((φ om) <= 1000000)%Z /\ ((φ ob) <= Bd)%Z /\
     (l_st T1).[k] = s /\ (l_m T1).[k] = wm /\ (l_b T1).[k] = wb /\
     agree (fun k0 => k0 <> k) T1 T /\ LW T1 /\ VB T1 /\
     (((φ lo) = (φ hi) /\
         match bdec (lo <? hi) with
         | left Hlh =>
             if (if nb then cm else m) * lo + (if nb then cb else b) <? (if nb then m else cm) * lo + (if nb then b else cb)
             then lc_insert X s lo mid (if nb then cm else m) (if nb then cb else b)
                    (if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T)
                    (Acc_inv H (lc_left lo hi Hlh))
             else lc_insert X s (mid + 1) hi (if nb then cm else m) (if nb then cb else b)
                    (if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T)
                    (Acc_inv H (lc_right lo hi Hlh))
         | right _ => if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T
         end = T1) \/
      ((φ lo) < (φ hi) /\ (lv om ob lo < lv wm wb lo)%Z /\
         exists H', match bdec (lo <? hi) with
         | left Hlh =>
             if (if nb then cm else m) * lo + (if nb then cb else b) <? (if nb then m else cm) * lo + (if nb then b else cb)
             then lc_insert X s lo mid (if nb then cm else m) (if nb then cb else b)
                    (if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T)
                    (Acc_inv H (lc_left lo hi Hlh))
             else lc_insert X s (mid + 1) hi (if nb then cm else m) (if nb then cb else b)
                    (if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T)
                    (Acc_inv H (lc_right lo hi Hlh))
         | right _ => if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T
         end = lc_insert X s lo mid om ob T1 H') \/
      ((φ lo) < (φ hi) /\ (lv wm wb lo <= lv om ob lo)%Z /\
         exists H', match bdec (lo <? hi) with
         | left Hlh =>
             if (if nb then cm else m) * lo + (if nb then cb else b) <? (if nb then m else cm) * lo + (if nb then b else cb)
             then lc_insert X s lo mid (if nb then cm else m) (if nb then cb else b)
                    (if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T)
                    (Acc_inv H (lc_left lo hi Hlh))
             else lc_insert X s (mid + 1) hi (if nb then cm else m) (if nb then cb else b)
                    (if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T)
                    (Acc_inv H (lc_right lo hi Hlh))
         | right _ => if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T
         end = lc_insert X s (mid + 1) hi om ob T1 H'))).
    { intros nb N1 N2.
      set (T1 := if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T).
      exists (if nb then m else cm), (if nb then b else cb), (if nb then cm else m), (if nb then cb else b), T1.
      split; [destruct nb; [left|right]; auto|].
      split; [destruct nb; [specialize (N1 eq_refl) | specialize (N2 eq_refl)]; lia|].
      split; [destruct nb; auto|]. split; [destruct nb; auto|].
      split; [unfold T1; destruct nb; simpl; auto|].
      split; [unfold T1; destruct nb; simpl; [rewrite aget_set_same by auto|]; auto|].
      split; [unfold T1; destruct nb; simpl; [rewrite aget_set_same by auto|]; auto|].
      split; [unfold T1; destruct nb; [|apply agree_refl]; intros k0 Hk0; simpl; rewrite !aget_set_other by auto; auto|].
      split; [unfold T1; destruct nb; [unfold LW; simpl; rewrite !alength_set; auto | exact L]|].
      split; [unfold T1; destruct nb; [|exact V]; intros k0 Hk0; simpl in *; rewrite !aget_set by auto;
              destruct (k =? k0); [auto | apply V; auto]|].
      fold T1.
      set (om := if nb then cm else m). set (ob := if nb then cb else b).
      set (wm := if nb then m else cm). set (wb := if nb then b else cb).
      destruct (lv_phi om ob lo ltac:(unfold om; destruct nb; auto) Hlo1 ltac:(unfold ob; destruct nb; auto)) as [E1 _].
      destruct (lv_phi wm wb lo ltac:(unfold wm; destruct nb; auto) Hlo1 ltac:(unfold wb; destruct nb; auto)) as [E2 _].
      destruct (bdec (lo <? hi)) as [Hl | Hl].
      - apply ltb_true in Hl as Hl'. right.
        destruct (om * lo + ob <? wm * lo + wb) eqn:C.
        + left. apply ltb_true in C. split; [exact Hl'|]. split; [rewrite <- E1, <- E2; exact C|]. eexists; reflexivity.
        + right. apply ltb_false in C. split; [exact Hl'|]. split; [rewrite <- E1, <- E2; exact C|]. eexists; reflexivity.
      - left. apply ltb_false in Hl. unfold dom in D. split; [lia | reflexivity]. }
    apply Gen.
    + intros E. apply Z.ltb_lt. exact E.
    + intros E. apply Z.ltb_ge. exact E.
  - apply eqb_false in Sk. left. simpl. split; [exact Sk|].
    rewrite !aget_set_same by auto. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros k0 Hk0. simpl. rewrite !aget_set_other by auto. auto.
Qed.
Lemma QF : forall lo hi x T Ha Hb, dom lo hi ->
  (φ (lc_query X s lo hi x T Ha)) = (φ (lc_query X s lo hi x T Hb)).
Proof. intros. f_equal. apply (query_frame _ lo hi x T T Ha Hb eq_refl); auto. apply agree_refl. Qed.

Lemma insert_main : forall z lo hi m b T H x H1 H2,
  gap hi lo = z -> dom lo hi -> LW T -> VB T ->
  ((φ m) <= 1000000)%Z -> ((φ b) <= Bd)%Z -> ((φ lo) <= (φ x) <= (φ hi))%Z ->
  (φ (lc_query X s lo hi x (lc_insert X s lo hi m b T H) H1)) =
  Z.min (φ (lc_query X s lo hi x T H2)) (lv m b x).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi m b T H x H1 H2 Hz D L V Hm Hb Hx.
  assert (Hx1 : ((φ x) <= 1000001)%Z) by (unfold dom in D; lia).
  destruct (insert_frame _ lo hi m b T H eq_refl D L V Hm Hb) as (L' & V' & A').
  destruct (lv_phi m b x Hm Hx1 Hb) as [_ LvI].
  destruct (key_in lo hi D) as [Kin Kb].
  pose proof (insert_node lo hi m b T H D L V Hm Hb) as N.
  pose proof (query_node lo hi x T H2 D V Hx1) as QT.
  set (T' := lc_insert X s lo hi m b T H) in *.
  pose proof (query_node lo hi x T' H1 D V' Hx1) as QT'.
  cbv zeta in N, QT, QT'.
  set (k := lkey X lo hi) in *. set (mid := lo + (hi - lo) / 2) in *.
  assert (Hmid : ((φ lo) <= (φ mid) <= (φ hi))%Z /\ ((φ lo) < (φ hi) -> (φ mid) < (φ hi))%Z).
  { unfold mid. unfold dom in D. rewrite mid_phi by lia.
    pose proof (Z.div_pos ((φ hi) - (φ lo)) 2). pose proof (Z.div_le_upper_bound ((φ hi) - (φ lo)) 2 ((φ hi) - (φ lo))).
    split; [lia|]. intros. assert (((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z by (apply Z.div_lt; lia). lia. }
  assert (Child : ((φ lo) < (φ hi))%Z -> dom lo mid /\ dom (mid + 1) hi /\ (φ (mid + 1)) = ((φ mid) + 1)%Z /\
            (forall k0, inK lo mid k0 -> k0 <> k) /\ (forall k0, inK (mid + 1) hi k0 -> k0 <> k) /\
            (lo <? hi) = true).
  { intros Hl. destruct (child_facts lo hi D Hl) as (D1 & D2 & M1 & M2 & M3 & M4). fold mid k in D1, D2, M1, M2, M3, M4.
    unfold dom in D. split; [auto|]. split; [auto|]. split; [auto|].
    split; [|split]; [intros k0 Hk0 E; subst k0; unfold inK in Hk0; lia ..| apply ltb_true; auto]. }
  destruct N as [(N1 & N2 & N3 & N4 & N5) | (N1 & wm & wb & om & ob & T1 & P & WO & Bo1 & Bo2 & F1 & F2 & F3 & T1A & LW1 & VB1 & Cs)].
  - (* the key was unused *)
    assert (QT'k : qval T' k x = lv m b x) by (unfold qval; rewrite N2, N3, N4, Uint63.eqb_refl; reflexivity).
    assert (QTk : qval T k x = (φ INF)) by (unfold qval; destruct ((l_st T).[k] =? s) eqn:E; [apply eqb_true in E; contradiction | reflexivity]).
    destruct QT' as [[A1 A2] | (A1 & A2 & A3)]; destruct QT as [[B1 B2] | (B1 & B2 & B3)]; try lia.
    destruct (Child A1) as (D1 & D2 & M2 & CL & CR & Hl).
      destruct (Z_le_gt_dec (φ x) (φ mid)) as [Xm | Xm]; [|apply Z.gt_lt in Xm].
      + destruct (A2 Xm) as [Ha EA]. destruct (B2 Xm) as [Hb' EB]. rewrite EA, EB, QT'k, QTk.
        rewrite (query_frame _ lo mid x T' T Ha Hb' eq_refl D1).
        2:{ eapply agree_weaken; [|exact N5]. intros k0 Hk0. apply CL. exact Hk0. }
        pose proof (query_bound _ lo mid x T Hb' eq_refl D1 V Hx1). lia.
      + destruct (A3 Xm) as [Ha EA]. destruct (B3 Xm) as [Hb' EB]. rewrite EA, EB, QT'k, QTk.
        rewrite (query_frame _ (mid + 1) hi x T' T Ha Hb' eq_refl D2).
        2:{ eapply agree_weaken; [|exact N5]. intros k0 Hk0. apply CR. exact Hk0. }
        pose proof (query_bound _ (mid + 1) hi x T Hb' eq_refl D2 V Hx1). lia.
  - (* the key held (cm, cb) *)
    assert (QTk : qval T k x = lv ((l_m T).[k]) ((l_b T).[k]) x) by (unfold qval; rewrite N1, Uint63.eqb_refl; reflexivity).
    assert (Pw : (lv wm wb x = lv m b x /\ lv om ob x = lv ((l_m T).[k]) ((l_b T).[k]) x) \/
                 (lv wm wb x = lv ((l_m T).[k]) ((l_b T).[k]) x /\ lv om ob x = lv m b x)).
    { destruct P as [[P1 P2]|[P1 P2]]; [left|right]; rewrite P1, P2; auto. }
    assert (QT1k : forall T2, agree (fun k0 => k0 = k) T2 T1 -> qval T2 k x = lv wm wb x).
    { intros T2 A. destruct (A k eq_refl) as (E1 & E2 & E3). unfold qval. rewrite E1, E2, E3, F1, F2, F3, Uint63.eqb_refl. reflexivity. }
    destruct Cs as [(C1 & C2) | [(C1 & C2 & H' & C3) | (C1 & C2 & H' & C3)]].
    + (* a leaf *)
      assert (Ex : x = mid) by (apply to_Z_inj; lia). subst x.
      destruct QT' as [[A1 A2] | (A1 & _)]; [|lia]. destruct QT as [[B1 B2] | (B1 & _)]; [|lia].
      rewrite A2, B2, QTk, (QT1k T'); [|rewrite C2; apply agree_refl].
      apply (min_leaf _ _ _ _ Pw WO).
    + (* the loser went left *)
      destruct (Child C1) as (D1 & D2 & M2 & CL & CR & Hl).
      destruct (insert_frame _ lo mid om ob T1 H' eq_refl D1 LW1 VB1 Bo1 Bo2) as (Li & Vi & Ai).
      rewrite <- C3 in Li, Vi, Ai.
      assert (QT'k : qval T' k x = lv wm wb x).
      { apply QT1k. eapply agree_weaken; [|exact Ai]. intros k0 E F. subst k0. apply (CL k F). reflexivity. }
      destruct QT' as [[A1 _] | (_ & A2 & A3)]; [lia|]. destruct QT as [[B1 _] | (_ & B2 & B3)]; [lia|].
      destruct (Z_le_gt_dec (φ x) (φ mid)) as [Xm | Xm]; [|apply Z.gt_lt in Xm].
      * destruct (A2 Xm) as [Ha EA]. destruct (B2 Xm) as [Hb' EB]. rewrite EA, EB, QT'k, QTk.
        rewrite C3 in EA |- *.
        rewrite (IH (gap mid lo) ltac:(rewrite <- Hz; apply lc_left; exact Hl) lo mid om ob T1 H' x Ha Hb'
                   eq_refl D1 LW1 VB1 Bo1 Bo2 ltac:(clear - Xm Hx; lia)).
        rewrite (query_frame _ lo mid x T1 T Hb' Hb' eq_refl D1).
        2:{ eapply agree_weaken; [|exact T1A]. intros k0 Hk0. apply CL. exact Hk0. }
        apply (min_swap _ _ _ _ _ Pw).
      * destruct (A3 Xm) as [Ha EA]. destruct (B3 Xm) as [Hb' EB]. rewrite EA, EB, QT'k, QTk.
        rewrite (query_frame _ (mid + 1) hi x T' T Ha Hb' eq_refl D2).
        2:{ apply (agree_trans _ _ T1).
            - eapply agree_weaken; [|exact Ai]. intros k0 Hk0 F. unfold dom in D. unfold inK in Hk0, F. lia.
            - eapply agree_weaken; [|exact T1A]. intros k0 Hk0. apply CR. exact Hk0. }
        assert (Hc : (lv wm wb x <= lv om ob x)%Z) by (apply (lv_conv2 om ob wm wb lo mid x C2 WO); lia).
        apply (min_drop _ _ _ _ _ Pw Hc).
    + (* the loser went right *)
      destruct (Child C1) as (D1 & D2 & M2 & CL & CR & Hl).
      destruct (insert_frame _ (mid + 1) hi om ob T1 H' eq_refl D2 LW1 VB1 Bo1 Bo2) as (Li & Vi & Ai).
      rewrite <- C3 in Li, Vi, Ai.
      assert (QT'k : qval T' k x = lv wm wb x).
      { apply QT1k. eapply agree_weaken; [|exact Ai]. intros k0 E F. subst k0. apply (CR k F). reflexivity. }
      destruct QT' as [[A1 _] | (_ & A2 & A3)]; [lia|]. destruct QT as [[B1 _] | (_ & B2 & B3)]; [lia|].
      destruct (Z_le_gt_dec (φ x) (φ mid)) as [Xm | Xm]; [|apply Z.gt_lt in Xm].
      * destruct (A2 Xm) as [Ha EA]. destruct (B2 Xm) as [Hb' EB]. rewrite EA, EB, QT'k, QTk.
        rewrite (query_frame _ lo mid x T' T Ha Hb' eq_refl D1).
        2:{ apply (agree_trans _ _ T1).
            - eapply agree_weaken; [|exact Ai]. intros k0 Hk0 F. unfold dom in D. unfold inK in Hk0, F. lia.
            - eapply agree_weaken; [|exact T1A]. intros k0 Hk0. apply CL. exact Hk0. }
        assert (Hc : (lv wm wb x <= lv om ob x)%Z) by (apply (lv_conv1 om ob wm wb lo mid x C2 WO); lia).
        apply (min_drop _ _ _ _ _ Pw Hc).
      * destruct (A3 Xm) as [Ha EA]. destruct (B3 Xm) as [Hb' EB]. rewrite EA, EB, QT'k, QTk.
        rewrite C3 in EA |- *.
        rewrite (IH (gap hi (mid + 1)) ltac:(rewrite <- Hz; apply lc_right; exact Hl) (mid + 1) hi om ob T1 H' x Ha Hb'
                   eq_refl D2 LW1 VB1 Bo1 Bo2 ltac:(clear - M2 Xm Hx; lia)).
        rewrite (query_frame _ (mid + 1) hi x T1 T Hb' Hb' eq_refl D2).
        2:{ eapply agree_weaken; [|exact T1A]. intros k0 Hk0. apply CR. exact Hk0. }
        apply (min_swap _ _ _ _ _ Pw).
Qed.

End LiChao.

(* ------------------------------------------------------------------ *)
(* The round of the Li Chao tree                                       *)
(* ------------------------------------------------------------------ *)

Section Round.
Variables (xp comp d : array int) (X s t : int).
Hypothesis HX : (1 <= (φ X) <= 1000001)%Z.
Hypothesis Hlines : forall i, ((φ i) < (φ t))%Z ->
  ((φ (xp.[comp.[i] - 1])) <= 1000000)%Z /\ ((φ (d.[comp.[i]])) <= Bd)%Z.

Definition Qr (T : lct) (x : int) : int :=
  lc_query X s 0 (X - 1) x T (Zwf_well_founded 0 (gap (X - 1) 0)).

Definition line (i x : int) : Z := lv (xp.[comp.[i] - 1]) (d.[comp.[i]]) x.

Definition QInv (T : lct) (i0 : int) : Prop :=
  LW X T /\ VB s T /\
  forall x, ((φ x) < (φ X))%Z ->
    (forall i, ((φ i) < (φ i0))%Z -> ((φ (Qr T x)) <= line i x)%Z) /\
    ((φ (Qr T x)) = (φ INF) \/ exists i, ((φ i) < (φ i0))%Z /\ (φ (Qr T x)) = line i x).

Lemma dom_root : dom X 0 (X - 1).
Proof. unfold dom. change (φ 0) with 0%Z. assert ((φ (X - 1)) = (φ X) - 1)%Z by sia. lia. Qed.

Lemma ins_loop_eq : forall T i H,
  ins_loop xp comp d X s t i T H =
  match bdec (i <? t) with
  | left Hi =>
      let v := comp.[i] in
      ins_loop xp comp d X s t (i + 1)
        (lc_insert X s 0 (X - 1) xp.[v - 1] d.[v] T (Zwf_well_founded 0 (gap (X - 1) 0)))
        (Acc_inv H (dec_step t i Hi))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ins_loop_ok : forall z i T H, gap t i = z -> ((φ i) <= (φ t))%Z -> QInv T i ->
  QInv (ins_loop xp comp d X s t i T H) t.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T H Hz Hit [L [V Q]]. rewrite ins_loop_eq.
  destruct (bdec (i <? t)) as [Hi | Hi].
  - apply ltb_true in Hi as Hi'. cbv zeta.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply (phi_succ i t Hi')).
    destruct (Hlines i Hi') as [Bm Bb].
    destruct (insert_frame X s HX _ 0 (X - 1) _ _ T (Zwf_well_founded 0 (gap (X - 1) 0)) eq_refl dom_root L V Bm Bb)
      as (L' & V' & _).
    apply (IH (gap t (i + 1))); [rewrite <- Hz; apply dec_step; exact Hi | reflexivity | lia |].
    split; [exact L'|]. split; [exact V'|].
    intros x Hx.
    assert (E : (φ (Qr (lc_insert X s 0 (X - 1) xp.[comp.[i] - 1] d.[comp.[i]] T
                        (Zwf_well_founded 0 (gap (X - 1) 0))) x)) =
                Z.min (φ (Qr T x)) (line i x)).
    { unfold Qr, line. apply (insert_main X s HX (gap (X - 1) 0) 0 (X - 1)); auto; [apply dom_root|].
      change (φ 0) with 0%Z. assert ((φ (X - 1)) = (φ X) - 1)%Z by sia. pose proof (to_Z_bounded x). lia. }
    rewrite E. destruct (Q x Hx) as [Q1 Q2]. split.
    + intros i' Hi''. rewrite Hi1 in Hi''. destruct (Z.eq_dec (φ i') (φ i)).
      * apply to_Z_inj in e. subst. lia.
      * pose proof (Q1 i' ltac:(lia)). lia.
    + destruct (Z.min_spec (φ (Qr T x)) (line i x)) as [[_ M] | [_ M]]; rewrite M.
      * destruct Q2 as [Q2 | (i' & Hi'' & Q2)]; [left; auto | right; exists i'; split; [lia | auto]].
      * right. exists i. split; [lia | reflexivity].
  - apply ltb_false in Hi. assert (i = t) by (apply to_Z_inj; lia). subst. split; auto.
Qed.

Lemma qinv_init : forall T, LW X T -> (forall k, ((φ ((l_st T).[k])) < (φ s))%Z) -> QInv T 0.
Proof.
  intros T L St. split; [exact L|]. split.
  - intros k E. specialize (St k). rewrite E in St. lia.
  - intros x Hx. split.
    + intros i Hi. change (φ 0) with 0%Z in Hi. pose proof (to_Z_bounded i). lia.
    + left. unfold Qr. apply (query_empty X s HX (gap (X - 1) 0) 0 (X - 1)); [reflexivity | apply dom_root |].
      intros k _ E. specialize (St k). rewrite E in St. lia.
Qed.

Section Queries.
Variable T : lct.
Hypothesis HV : VB s T.
Hypothesis Hq : forall i, ((φ i) < (φ t))%Z -> ((φ (xp.[comp.[i] - 1])) <= 1000001)%Z.

Definition qv (u : int) : Z := ((φ (d.[u])) + (φ (Qr T (xp.[u - 1]))))%Z.

Lemma qry_loop_eq : forall i best H,
  qry_loop xp comp d X s t i T best H =
  match bdec (i <? t) with
  | left Hi =>
      let u := comp.[i] in
      let q := d.[u] + lc_query X s 0 (X - 1) xp.[u - 1] T (Zwf_well_founded 0 (gap (X - 1) 0)) in
      qry_loop xp comp d X s t (i + 1) T
        (if q <? best.[u] then best.[u <- q] else best)
        (Acc_inv H (dec_step t i Hi))
  | right _ => best
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma qry_loop_ok : forall z i best H, gap t i = z -> ((φ i) <= (φ t))%Z ->
  (forall j, ((φ j) < (φ t))%Z -> ((φ (comp.[j])) < (φ (PArray.length best)))%Z) ->
  let best' := qry_loop xp comp d X s t i T best H in
  PArray.length best' = PArray.length best /\
  forall u, ((φ (best'.[u])) <= (φ (best.[u])))%Z /\
    ((exists j, ((φ i) <= (φ j) < (φ t))%Z /\ comp.[j] = u) -> ((φ (best'.[u])) <= qv u)%Z) /\
    (best'.[u] = best.[u] \/ ((exists j, ((φ i) <= (φ j) < (φ t))%Z /\ comp.[j] = u) /\ (φ (best'.[u])) = qv u)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i best H Hz Hit Hcb best'. unfold best'. clear best'. rewrite qry_loop_eq.
  destruct (bdec (i <? t)) as [Hi | Hi].
  - apply ltb_true in Hi as Hi'. cbv zeta.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply (phi_succ i t Hi')).
    set (u := comp.[i]).
    destruct (Hlines i Hi') as [_ Bb].
    pose proof (query_bound X s _ 0 (X - 1) (xp.[u - 1]) T (Zwf_well_founded 0 (gap (X - 1) 0)) eq_refl
                  dom_root HV (Hq i Hi')) as QB.
    assert (Eq : (φ (d.[u] + lc_query X s 0 (X - 1) xp.[u - 1] T (Zwf_well_founded 0 (gap (X - 1) 0)))) = qv u).
    { unfold qv, Qr. apply phi_add_small. rewrite wB_val. rewrite INF_val in QB. unfold Bd in Bb. fold u in Bb. lia. }
    set (q := d.[u] + lc_query X s 0 (X - 1) xp.[u - 1] T (Zwf_well_founded 0 (gap (X - 1) 0))) in *.
    set (b1 := if q <? best.[u] then best.[u <- q] else best).
    assert (B1 : PArray.length b1 = PArray.length best /\
      forall w, ((φ (b1.[w])) <= (φ (best.[w])))%Z /\ (w = u -> ((φ (b1.[w])) <= qv u)%Z) /\
        (b1.[w] = best.[w] \/ (w = u /\ (φ (b1.[w])) = qv u))).
    { unfold b1. destruct (q <? best.[u]) eqn:C.
      - apply ltb_true in C.
        assert (Hu : (u <? PArray.length best) = true) by (apply ltb_true; apply Hcb; exact Hi').
        split; [apply alength_set|]. intros w. rewrite aget_set by exact Hu.
        destruct (u =? w) eqn:E.
        + apply eqb_true in E. subst w. split; [lia|]. split; [intros; lia|]. right. auto.
        + apply eqb_false in E. split; [lia|]. split; [intros F; congruence|]. left; auto.
      - apply ltb_false in C. split; [reflexivity|]. intros w. split; [lia|].
        split; [intros ->; lia|]. left; auto. }
    destruct B1 as [BL BW].
    destruct (IH (gap t (i + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hi) (i + 1) b1
                (Acc_inv H (dec_step t i Hi)) eq_refl ltac:(lia) ltac:(rewrite BL; exact Hcb)) as [L2 W2].
    split; [congruence|]. intros w. destruct (W2 w) as (W1 & W3 & W4). destruct (BW w) as (V1 & V2 & V3).
    split; [lia|]. split.
    + intros (j & Hj & Ej). destruct (Z.eq_dec (φ j) (φ i)).
      * apply to_Z_inj in e. subst j. fold u in Ej. subst w. pose proof (V2 eq_refl). lia.
      * apply W3. exists j. split; [lia | auto].
    + destruct W4 as [W4 | ((j & Hj & Ej) & W4)].
      * rewrite W4. destruct V3 as [V3 | (V3 & V4)].
        -- left. exact V3.
        -- subst w. right. split; [exists i; split; [lia | reflexivity] | exact V4].
      * right. split; [exists j; split; [lia | auto] | auto].
  - apply ltb_false in Hi. split; [reflexivity|]. intros w. split; [lia|]. split.
    + intros (j & Hj & _). lia.
    + left; auto.
Qed.

End Queries.
End Round.

(* ------------------------------------------------------------------ *)
(* The CSR layout                                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint cnt (f : nat -> Z) (x : Z) (h : nat) : nat :=
  match h with
  | O => O
  | S h' => (cnt f x h' + if (f h' =? x)%Z then 1 else 0)%nat
  end.

Fixpoint psum (g : nat -> nat) (y : nat) : nat :=
  match y with
  | O => O
  | S y' => (psum g y' + g y')%nat
  end.

Lemma cnt_mono : forall f x h1 h2, (h1 <= h2)%nat -> (cnt f x h1 <= cnt f x h2)%nat.
Proof.
  intros f x h1 h2 H. induction H; [lia|]. simpl. lia.
Qed.

Lemma cnt_le : forall f x h, (cnt f x h <= h)%nat.
Proof. intros f x h. induction h; simpl; [lia|]. destruct (f h =? x)%Z; lia. Qed.

Lemma cnt_lt : forall f h1 h2, (h1 < h2)%nat -> (cnt f (f h1) h1 < cnt f (f h1) h2)%nat.
Proof.
  intros f h1 h2 H. pose proof (cnt_mono f (f h1) (S h1) h2 H). simpl in H0.
  rewrite Z.eqb_refl in H0. lia.
Qed.

Lemma cnt_surj : forall f x H j, (j < cnt f x H)%nat ->
  exists h, (h < H)%nat /\ f h = x /\ cnt f x h = j.
Proof.
  intros f x H. induction H as [| H IH]; intros j Hj; simpl in Hj; [lia|].
  destruct (f H =? x)%Z eqn:E.
  - destruct (Nat.eq_dec j (cnt f x H)).
    + exists H. split; [lia|]. split; [apply Z.eqb_eq; auto | auto].
    + destruct (IH j ltac:(lia)) as (h & A & B & C). exists h. split; [lia | auto].
  - destruct (IH j ltac:(lia)) as (h & A & B & C). exists h. split; [lia | auto].
Qed.

Lemma psum_mono : forall g y1 y2, (y1 <= y2)%nat -> (psum g y1 <= psum g y2)%nat.
Proof. intros g y1 y2 H. induction H; [lia|]. simpl. lia. Qed.

(* the counts over the nodes 0..N-1 add up to the number of half-edges *)
Lemma psum_cnt : forall f N H, (forall h, (h < H)%nat -> (0 <= f h < Z.of_nat N)%Z) ->
  psum (fun y => cnt f (Z.of_nat y) H) N = H.
Proof.
  intros f N H. induction H as [| H IH]; intros Hr.
  - simpl. induction N; simpl; [reflexivity|]. rewrite IHN; [reflexivity|]. intros; lia.
  - assert (Split : forall N', psum (fun y => cnt f (Z.of_nat y) (S H)) N' =
       (psum (fun y => cnt f (Z.of_nat y) H) N' + if (f H <? Z.of_nat N')%Z then 1 else 0)%nat).
    { intros N'. induction N' as [| N' IHN']; cbn [psum].
      - change (Z.of_nat 0) with 0%Z.
        destruct (f H <? 0)%Z eqn:E; [apply Z.ltb_lt in E; specialize (Hr H ltac:(lia)); lia | reflexivity].
      - rewrite IHN'. cbn [cnt]. rewrite Nat2Z.inj_succ.
        destruct (f H =? Z.of_nat N')%Z eqn:E1;
        destruct (f H <? Z.of_nat N')%Z eqn:E2; destruct (f H <? Z.succ (Z.of_nat N'))%Z eqn:E3;
        rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in *; lia. }
    rewrite Split, IH by (intros; apply Hr; lia).
    specialize (Hr H ltac:(lia)).
    destruct (f H <? Z.of_nat N)%Z eqn:E; [lia | apply Z.ltb_ge in E; lia].
Qed.

Lemma psum_cnt_le : forall f H y, (psum (fun z => cnt f (Z.of_nat z) H) y + cnt f (Z.of_nat y) H =
  psum (fun z => cnt f (Z.of_nat z) H) (S y))%nat.
Proof. intros. simpl. lia. Qed.

Definition ofn (h : nat) : int := of_Z (Z.of_nat h).

Lemma ofn_phi : forall h, (Z.of_nat h <= 4194304)%Z -> (φ (ofn h)) = Z.of_nat h.
Proof. intros h H. unfold ofn. apply of_Z_nat_phi. rewrite wB_val. lia. Qed.

Lemma phi_nat : forall i : int, ofn (Z.to_nat (φ i)) = i.
Proof. intros i. unfold ofn. rewrite Z2Nat.id by (pose proof (to_Z_bounded i); lia). apply of_to_Z. Qed.

Section CSR.
Variables xu xv xw : array int.
Variables n m : Z.
Hypothesis Hn : (1 <= n <= 200000)%Z.
Hypothesis Hm : (0 <= m <= n)%Z.
Hypothesis Lu : (φ (PArray.length xu)) = m.
Hypothesis Lv : (φ (PArray.length xv)) = m.
Hypothesis Ru : forall k, ((φ k) < m)%Z -> (1 <= (φ (xu.[k])) <= n)%Z.
Hypothesis Rv : forall k, ((φ k) < m)%Z -> (1 <= (φ (xv.[k])) <= n)%Z.

Definition HH : nat := Z.to_nat (2 * m).
Definition fh (h : nat) : Z := (φ (hsrc xu xv (ofn h))).
Definition gh (h : nat) : int := hdst xu xv (ofn h).
Definition wh (h : nat) : int := xw.[ofn h / 2].
Definition Sx (y : nat) : nat := psum (fun z => cnt fh (Z.of_nat z) HH) y.
Definition idx (h : nat) : nat := (Sx (Z.to_nat (fh h)) + cnt fh (fh h) h)%nat.

Lemma half_bound : forall h : nat, (h < HH)%nat -> ((φ (ofn h / 2)) < m)%Z.
Proof. intros h H. unfold HH in H. rewrite div_spec, ofn_phi by lia. change (φ 2) with 2%Z.
  apply Z.div_lt_upper_bound; lia. Qed.

Lemma fh_range : forall h, (h < HH)%nat -> (1 <= fh h <= n)%Z.
Proof.
  intros h H. unfold fh, hsrc. pose proof (half_bound h H).
  destruct (ofn h mod 2 =? 0); auto.
Qed.

Lemma Sx_total : Sx (Z.to_nat n + 1) = HH.
Proof.
  unfold Sx. apply psum_cnt. intros h H. pose proof (fh_range h H). lia.
Qed.

Lemma idx_bound : forall h, (h < HH)%nat ->
  (Sx (Z.to_nat (fh h)) <= idx h < Sx (Z.to_nat (fh h) + 1))%nat.
Proof.
  intros h H. unfold idx. pose proof (cnt_lt fh h HH H).
  replace (Z.to_nat (fh h) + 1)%nat with (S (Z.to_nat (fh h))) by lia.
  assert (E : Sx (S (Z.to_nat (fh h))) = (Sx (Z.to_nat (fh h)) + cnt fh (fh h) HH)%nat).
  { unfold Sx. cbn [psum]. rewrite Z2Nat.id by (pose proof (fh_range h H); lia). reflexivity. }
  lia.
Qed.

Lemma idx_lt : forall h, (h < HH)%nat -> (idx h < HH)%nat.
Proof.
  intros h H. pose proof (idx_bound h H). pose proof (fh_range h H).
  pose proof (psum_mono (fun z => cnt fh (Z.of_nat z) HH) (Z.to_nat (fh h) + 1) (Z.to_nat n + 1) ltac:(lia)).
  fold (Sx (Z.to_nat (fh h) + 1)) (Sx (Z.to_nat n + 1)) in H2. rewrite Sx_total in H2. lia.
Qed.

Lemma idx_inj : forall h1 h2, (h1 < h2)%nat -> (h2 < HH)%nat -> idx h1 <> idx h2.
Proof.
  intros h1 h2 H12 H2 E.
  destruct (Z.eq_dec (fh h1) (fh h2)) as [F | F].
  - unfold idx in E. rewrite F in E. pose proof (cnt_lt fh h1 h2 H12). rewrite F in H. lia.
  - pose proof (idx_bound h1 ltac:(lia)). pose proof (idx_bound h2 H2).
    pose proof (fh_range h1 ltac:(lia)). pose proof (fh_range h2 H2).
    destruct (Z_lt_le_dec (fh h1) (fh h2)).
    + pose proof (psum_mono (fun z => cnt fh (Z.of_nat z) HH) (Z.to_nat (fh h1) + 1) (Z.to_nat (fh h2)) ltac:(lia)) as PM.
      fold (Sx (Z.to_nat (fh h1) + 1)) (Sx (Z.to_nat (fh h2))) in PM. lia.
    + pose proof (psum_mono (fun z => cnt fh (Z.of_nat z) HH) (Z.to_nat (fh h2) + 1) (Z.to_nat (fh h1)) ltac:(lia)) as PM.
      fold (Sx (Z.to_nat (fh h2) + 1)) (Sx (Z.to_nat (fh h1))) in PM. lia.
Qed.

Lemma deg_loop_eq : forall hh h deg H,
  deg_loop xu xv hh h deg H =
  match bdec (h <? hh) with
  | left Hh =>
      let x := hsrc xu xv h in
      deg_loop xu xv hh (h + 1) deg.[x <- deg.[x] + 1] (Acc_inv H (dec_step hh h Hh))
  | right _ => deg
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma deg_loop_ok : forall hh z h deg H, (φ hh) = (2 * m)%Z -> gap hh h = z -> ((φ h) <= (φ hh))%Z ->
  (φ (PArray.length deg)) = (n + 1)%Z ->
  (forall x : int, ((φ x) <= n)%Z -> (φ (deg.[x])) = Z.of_nat (cnt fh (φ x) (Z.to_nat (φ h)))) ->
  let deg' := deg_loop xu xv hh h deg H in
  (φ (PArray.length deg')) = (n + 1)%Z /\
  forall x : int, ((φ x) <= n)%Z -> (φ (deg'.[x])) = Z.of_nat (cnt fh (φ x) HH).
Proof.
  intros hh z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h deg H Hhh Hz Hh Ld Inv deg'. unfold deg'. clear deg'. rewrite deg_loop_eq.
  destruct (bdec (h <? hh)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'. cbv zeta.
    assert (Hh1 : (φ (h + 1)) = ((φ h) + 1)%Z) by (apply (phi_succ h hh Hl')).
    assert (Hhn : (Z.to_nat (φ h) < HH)%nat) by (unfold HH; lia).
    pose proof (fh_range _ Hhn) as Fr. unfold fh in Fr. rewrite phi_nat in Fr.
    set (x0 := hsrc xu xv h) in *.
    assert (Hx0 : (x0 <? PArray.length deg) = true) by (apply ltb_true; lia).
    apply (IH (gap hh (h + 1))); [rewrite <- Hz; apply dec_step; exact Hl | exact Hhh | reflexivity | lia | rewrite alength_set; auto |].
    intros x Hx. rewrite aget_set by exact Hx0. rewrite Hh1, Z2Nat.inj_add by lia.
    replace (Z.to_nat 1) with 1%nat by reflexivity. rewrite Nat.add_1_r. cbn [cnt].
    assert (Fx : fh (Z.to_nat (φ h)) = (φ x0)) by (unfold fh; rewrite phi_nat; reflexivity). rewrite Fx.
    destruct (x0 =? x) eqn:E.
    + apply eqb_true in E. subst x. rewrite Z.eqb_refl. rewrite phi_add_small.
      * rewrite Inv by lia. change (φ 1) with 1%Z. lia.
      * rewrite Inv by lia. change (φ 1) with 1%Z. rewrite wB_val.
        pose proof (cnt_mono fh (φ x0) (Z.to_nat (φ h)) HH ltac:(lia)).
        pose proof (cnt_le fh (φ x0) HH).
        unfold HH in *. lia.
    + apply eqb_false in E. replace ((φ x0) =? (φ x))%Z with false by (symmetry; apply Z.eqb_neq; intro F; apply E; apply to_Z_inj; auto).
      rewrite Inv by lia. lia.
  - apply ltb_false in Hl. assert (h = hh) by (apply to_Z_inj; lia). subst h.
    split; auto. intros x Hx. rewrite Inv by lia. unfold HH. rewrite Hhh. reflexivity.
Qed.

Lemma Sx_succ : forall y, Sx (S y) = (Sx y + cnt fh (Z.of_nat y) HH)%nat.
Proof. intros. unfold Sx. cbn [psum]. reflexivity. Qed.

Lemma Sx_le_HH : forall y, (y <= Z.to_nat n + 1)%nat -> (Sx y <= HH)%nat.
Proof.
  intros y Hy. rewrite <- Sx_total. unfold Sx. apply psum_mono. exact Hy.
Qed.

Lemma HH_small : (Z.of_nat HH <= 400000)%Z.
Proof. unfold HH. lia. Qed.

Lemma start_loop_eq : forall deg n1 x sa pos H,
  start_loop deg n1 x sa pos H =
  match bdec (x <? n1) with
  | left Hx =>
      let s := sa.[x] in
      start_loop deg n1 (x + 1) sa.[x + 1 <- s + deg.[x]] pos.[x <- s]
        (Acc_inv H (dec_step n1 x Hx))
  | right _ => (sa, pos)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma start_loop_ok : forall deg n1 z x sa pos H,
  (φ n1) = (n + 1)%Z -> gap n1 x = z -> ((φ x) <= (φ n1))%Z ->
  (φ (PArray.length sa)) = (n + 2)%Z -> (φ (PArray.length pos)) = (n + 1)%Z ->
  (forall y : int, ((φ y) <= n)%Z -> (φ (deg.[y])) = Z.of_nat (cnt fh (φ y) HH)) ->
  (forall y : int, ((φ y) <= (φ x))%Z -> (φ (sa.[y])) = Z.of_nat (Sx (Z.to_nat (φ y)))) ->
  (forall y : int, ((φ y) < (φ x))%Z -> (φ (pos.[y])) = Z.of_nat (Sx (Z.to_nat (φ y)))) ->
  let r := start_loop deg n1 x sa pos H in
  (φ (PArray.length (fst r))) = (n + 2)%Z /\ (φ (PArray.length (snd r))) = (n + 1)%Z /\
  (forall y : int, ((φ y) <= n + 1)%Z -> (φ ((fst r).[y])) = Z.of_nat (Sx (Z.to_nat (φ y)))) /\
  (forall y : int, ((φ y) <= n)%Z -> (φ ((snd r).[y])) = Z.of_nat (Sx (Z.to_nat (φ y)))).
Proof.
  intros deg n1 z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x sa pos H Hn1 Hz Hx Ls Lp Hd Is Ip r. unfold r. clear r. rewrite start_loop_eq.
  destruct (bdec (x <? n1)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'. cbv zeta.
    assert (Hx1 : (φ (x + 1)) = ((φ x) + 1)%Z) by (apply (phi_succ x n1 Hl')).
    assert (B1 : (x + 1 <? PArray.length sa) = true) by (apply ltb_true; lia).
    assert (B2 : (x <? PArray.length pos) = true) by (apply ltb_true; lia).
    assert (Ev : (φ (sa.[x] + deg.[x])) = Z.of_nat (Sx (Z.to_nat (φ (x + 1))))).
    { rewrite Hx1, Z2Nat.inj_add by (pose proof (to_Z_bounded x); lia).
      replace (Z.to_nat 1) with 1%nat by reflexivity. rewrite Nat.add_1_r, Sx_succ.
      rewrite Z2Nat.id by (pose proof (to_Z_bounded x); lia).
      pose proof (Sx_le_HH (S (Z.to_nat (φ x))) ltac:(lia)) as SB. rewrite Sx_succ in SB.
      rewrite Z2Nat.id in SB by (pose proof (to_Z_bounded x); lia).
      pose proof HH_small.
      rewrite phi_add_small; rewrite Is by lia; rewrite Hd by lia; [lia|]. rewrite wB_val. lia. }
    apply (IH (gap n1 (x + 1))); [rewrite <- Hz; apply dec_step; exact Hl | exact Hn1 | reflexivity | lia
          | rewrite alength_set; auto | rewrite alength_set; auto | exact Hd | |].
    + intros y Hy. rewrite aget_set by exact B1. destruct (x + 1 =? y) eqn:E.
      * apply eqb_true in E. subst y. exact Ev.
      * apply eqb_false in E. apply Is. assert ((φ y) <> (φ (x + 1))) by (intro F; apply E; apply to_Z_inj; auto). lia.
    + intros y Hy. rewrite aget_set by exact B2. destruct (x =? y) eqn:E.
      * apply eqb_true in E. subst y. apply Is. lia.
      * apply eqb_false in E. apply Ip. assert ((φ y) <> (φ x)) by (intro F; apply E; apply to_Z_inj; auto). lia.
  - apply ltb_false in Hl. simpl. split; [auto|]. split; [auto|].
    split; intros y Hy; [apply Is | apply Ip]; lia.
Qed.

Lemma fill_loop_eq : forall xw hh h pos nbr wt H,
  fill_loop xu xv xw hh h pos nbr wt H =
  match bdec (h <? hh) with
  | left Hh =>
      let x := hsrc xu xv h in
      let i := pos.[x] in
      fill_loop xu xv xw hh (h + 1) pos.[x <- i + 1]
        nbr.[i <- hdst xu xv h] wt.[i <- xw.[h / 2]]
        (Acc_inv H (dec_step hh h Hh))
  | right _ => (nbr, wt)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_loop_ok : forall hh z h pos nbr wt H,
  (φ hh) = (2 * m)%Z -> gap hh h = z -> ((φ h) <= (φ hh))%Z ->
  (φ (PArray.length pos)) = (n + 1)%Z -> (φ (PArray.length nbr)) = (2 * m)%Z -> (φ (PArray.length wt)) = (2 * m)%Z ->
  (forall x : int, ((φ x) <= n)%Z ->
     (φ (pos.[x])) = Z.of_nat (Sx (Z.to_nat (φ x)) + cnt fh (φ x) (Z.to_nat (φ h)))) ->
  (forall h', (h' < Z.to_nat (φ h))%nat -> nbr.[ofn (idx h')] = gh h' /\ wt.[ofn (idx h')] = wh h') ->
  let r := fill_loop xu xv xw hh h pos nbr wt H in
  (φ (PArray.length (fst r))) = (2 * m)%Z /\ (φ (PArray.length (snd r))) = (2 * m)%Z /\
  forall h', (h' < HH)%nat -> (fst r).[ofn (idx h')] = gh h' /\ (snd r).[ofn (idx h')] = wh h'.
Proof.
  intros hh z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h pos nbr wt H Hhh Hz Hh Lp Ln Lw Ip In r. unfold r. clear r. rewrite fill_loop_eq.
  destruct (bdec (h <? hh)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'. cbv zeta.
    assert (Hh1 : (φ (h + 1)) = ((φ h) + 1)%Z) by (apply (phi_succ h hh Hl')).
    set (hn := Z.to_nat (φ h)).
    assert (Hhn : (hn < HH)%nat) by (unfold hn, HH; lia).
    pose proof (fh_range _ Hhn) as Fr.
    assert (Fx : fh hn = (φ (hsrc xu xv h))) by (unfold fh, hn; rewrite phi_nat; reflexivity).
    set (x0 := hsrc xu xv h) in *.
    pose proof (idx_lt hn Hhn) as IL. pose proof HH_small.
    assert (Ei : pos.[x0] = ofn (idx hn)).
    { apply to_Z_inj. rewrite ofn_phi by lia. rewrite Ip by lia. unfold idx. rewrite Fx. reflexivity. }
    rewrite Ei.
    assert (Bi : (ofn (idx hn) <? PArray.length nbr) = true) by (apply ltb_true; rewrite ofn_phi by lia; unfold HH in IL; lia).
    assert (Bw : (ofn (idx hn) <? PArray.length wt) = true) by (apply ltb_true; rewrite ofn_phi by lia; unfold HH in IL; lia).
    assert (Bp : (x0 <? PArray.length pos) = true) by (apply ltb_true; lia).
    apply (IH (gap hh (h + 1))); [rewrite <- Hz; apply dec_step; exact Hl | exact Hhh | reflexivity | lia
          | rewrite alength_set; auto | rewrite alength_set; auto | rewrite alength_set; auto | |].
    + intros x Hx. rewrite aget_set by exact Bp.
      rewrite Hh1, Z2Nat.inj_add by (pose proof (to_Z_bounded h); lia).
      replace (Z.to_nat 1) with 1%nat by reflexivity. rewrite Nat.add_1_r. cbn [cnt]. fold hn. rewrite Fx.
      destruct (x0 =? x) eqn:E.
      * apply eqb_true in E. subst x. rewrite Z.eqb_refl. rewrite phi_add_small; rewrite ofn_phi by lia.
        -- unfold idx. rewrite Fx. change (φ 1) with 1%Z. lia.
        -- change (φ 1) with 1%Z. rewrite wB_val. lia.
      * apply eqb_false in E. replace ((φ x0) =? (φ x))%Z with false by (symmetry; apply Z.eqb_neq; intro F; apply E; apply to_Z_inj; auto).
        rewrite Ip by lia. unfold hn. lia.
    + intros h' Hh'. rewrite Hh1, Z2Nat.inj_add in Hh' by (pose proof (to_Z_bounded h); lia).
      replace (Z.to_nat 1) with 1%nat in Hh' by reflexivity. fold hn in Hh'.
      rewrite !aget_set by auto.
      destruct (Nat.eq_dec h' hn).
      * subst h'. rewrite !Uint63.eqb_refl. unfold gh, wh, hn. rewrite phi_nat. split; reflexivity.
      * assert (Ne : ofn (idx hn) <> ofn (idx h')).
        { intro F. apply (f_equal to_Z) in F. rewrite !ofn_phi in F by (pose proof (idx_lt h' ltac:(lia)); lia).
          apply (idx_inj h' hn ltac:(lia) Hhn). lia. }
        apply eqb_false in Ne. rewrite !Ne. apply In. lia.
  - apply ltb_false in Hl. assert (h = hh) by (apply to_Z_inj; lia). subst h.
    simpl. split; [auto|]. split; [auto|]. intros h' Hh'. apply In. unfold HH in Hh'. lia.
Qed.

End CSR.

(* ------------------------------------------------------------------ *)
(* Stamps and monotonicity                                             *)
(* ------------------------------------------------------------------ *)

Definition stle (s : int) (T : lct) : Prop := forall k, ((φ ((l_st T).[k])) <= (φ s))%Z.

Lemma insert_stamp : forall X s z lo hi m b T H, gap hi lo = z -> stle s T ->
  stle s (lc_insert X s lo hi m b T H).
Proof.
  intros X s z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi m b T H Hz St. rewrite lc_insert_eq. cbv zeta.
  set (k := lkey X lo hi).
  destruct ((l_st T).[k] =? s) eqn:Sk.
  - set (nb := m * (lo + (hi - lo) / 2) + b <? (l_m T).[k] * (lo + (hi - lo) / 2) + (l_b T).[k]).
    assert (S1 : stle s (if nb then {| l_st := l_st T; l_m := (l_m T).[k <- m]; l_b := (l_b T).[k <- b] |} else T))
      by (destruct nb; exact St).
    destruct (bdec (lo <? hi)) as [Hl | Hl]; [|exact S1].
    destruct ((if nb then (l_m T).[k] else m) * lo + (if nb then (l_b T).[k] else b) <?
              (if nb then m else (l_m T).[k]) * lo + (if nb then b else (l_b T).[k])).
    + apply (IH (gap (lo + (hi - lo) / 2) lo)); [rewrite <- Hz; apply lc_left; exact Hl | reflexivity | exact S1].
    + apply (IH (gap hi (lo + (hi - lo) / 2 + 1))); [rewrite <- Hz; apply lc_right; exact Hl | reflexivity | exact S1].
  - intros k0. simpl. rewrite aget_set_le.
    destruct ((k =? k0) && (k <? PArray.length (l_st T))); [lia | apply St].
Qed.

Lemma ins_loop_stamp : forall xp comp d X s t z i T H, gap t i = z -> stle s T ->
  stle s (ins_loop xp comp d X s t i T H).
Proof.
  intros xp comp d X s t z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T H Hz St. rewrite ins_loop_eq. destruct (bdec (i <? t)) as [Hi | Hi]; [|exact St].
  cbv zeta. apply (IH (gap t (i + 1))); [rewrite <- Hz; apply dec_step; exact Hi | reflexivity |].
  apply (insert_stamp X s (gap (X - 1) 0) 0 (X - 1)); [reflexivity | exact St].
Qed.

Lemma rloop_le : forall sa nbr wt alive comp t z d H, dsum d = z ->
  dle (rloop sa nbr wt alive comp t d H) d.
Proof.
  intros sa nbr wt alive comp t z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d H Hz. destruct H as [H]. simpl. cbv zeta.
  destruct (rpass_dec sa nbr wt alive comp t _ 0 d false (Zwf_well_founded 0 (gap t 0)) eq_refl) as [A _].
  destruct (bdec (snd (rpass sa nbr wt alive comp t 0 d false (Zwf_well_founded 0 (gap t 0))))) as [Hc | Hc].
  - eapply dle_trans; [|exact A]. apply (IH (dsum (fst (rpass sa nbr wt alive comp t 0 d false (Zwf_well_founded 0 (gap t 0)))))); [|reflexivity].
    rewrite <- Hz. apply rloop_step. exact Hc.
  - exact A.
Qed.

Lemma relax_le : forall sa nbr wt alive comp t b, dle (relax sa nbr wt alive comp t b) (b_d b).
Proof.
  intros. unfold relax. destruct (b_flag b); [apply dle_refl|]. apply (rloop_le _ _ _ _ _ _ _ _ _ eq_refl).
Qed.

(* ------------------------------------------------------------------ *)
(* The input                                                           *)
(* ------------------------------------------------------------------ *)

Lemma repr_len : forall (x : array uint) (l : list N), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros x l [H _]. symmetry. exact H. Qed.

Lemma repr_get : forall (x : array uint) (l : list N), repr x l ->
  forall k : int, ((φ k) < Z.of_nat (List.length l))%Z -> (φ (x.[k])) = Z.of_N (Prelude.get l (Z.to_N (φ k))).
Proof.
  intros x l [Hl Hc] k Hk.
  destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded k); lia). rewrite of_to_Z in Hr.
  unfold Prelude.get. rewrite Z_N_nat. rewrite (nth_error_nth l _ _ Hv). rewrite <- Hr.
  pose proof (to_Z_bounded (x.[k])). lia.
Qed.

Section Abstract.
Variables eu ev ew : list N.

Lemma lb_abstract : forall (C A : N -> Prop) (D B : N -> Z) (Pz : N -> Z) (c : N),
  (forall k a b, joins eu ev k a b -> C a -> A b -> C b) ->
  (forall k a b, joins eu ev k a b -> C a -> C b -> (D b <= D a + Z.of_N (Prelude.get ew k))%Z) ->
  C c -> (D c <= 0)%Z ->
  (forall u v, C u -> C v -> (B u <= D u + D v + Pz u * Pz v)%Z) ->
  forall vs ks u, walk eu ev vs ks -> hd_error vs = Some u -> Forall A vs -> In c vs ->
  (B u <= Z.of_N (wsum ew ks) + Pz u * Pz (last vs 0%N))%Z.
Proof.
  intros C A D B Pz c HC HD Cc Dc HB vs ks u W Hu HA Hin.
  pose proof (closure eu ev C A HC vs ks W HA c Hin Cc) as FC.
  destruct (walk_split eu ev vs ks c W Hin) as (vs1 & vs2 & ks1 & ks2 & E1 & E2 & W1 & W2).
  subst vs ks. apply Forall_app in FC as [FC1 FC2].
  assert (Cu : C u).
  { destruct vs1 as [| a vs1]; simpl in Hu; inversion Hu; subst; [exact Cc | inversion FC1; auto]. }
  assert (Lv : last (vs1 ++ c :: vs2) 0%N = last (c :: vs2) 0%N) by apply last_app_cons.
  assert (Cv : C (last (c :: vs2) 0%N)).
  { rewrite Forall_forall in FC2. apply FC2. clear. revert c. induction vs2 as [| b vs2 IH]; intros c; [left; reflexivity|].
    change (last (c :: b :: vs2) 0%N) with (last (b :: vs2) 0%N). right. apply IH. }
  pose proof (potential eu ev ew C D HD _ _ W2 FC2 c 0%N eq_refl) as P2.
  apply walk_rev in W1. rewrite rev_app_distr in W1. simpl in W1.
  assert (FR : Forall C (c :: rev vs1)) by (constructor; [exact Cc | apply Forall_rev; exact FC1]).
  pose proof (potential eu ev ew C D HD _ _ W1 FR c 0%N eq_refl) as P1.
  assert (L1 : last (c :: rev vs1) 0%N = u).
  { destruct vs1 as [| a vs1]; simpl in Hu; inversion Hu; subst; [reflexivity|].
    simpl rev. rewrite app_comm_cons, last_app_single. reflexivity. }
  rewrite L1, wsum_rev in P1. rewrite Lv. rewrite wsum_app.
  pose proof (HB u _ Cu Cv). lia.
Qed.

Lemma wit_abstract : forall root u v du dv,
  (exists vs ks, walk eu ev vs ks /\ hd_error vs = Some root /\ last vs 0%N = u /\ (Z.of_N (wsum ew ks) <= du)%Z) ->
  (exists vs ks, walk eu ev vs ks /\ hd_error vs = Some root /\ last vs 0%N = v /\ (Z.of_N (wsum ew ks) <= dv)%Z) ->
  exists vs ks, walk eu ev vs ks /\ hd_error vs = Some u /\ last vs 0%N = v /\
    (Z.of_N (wsum ew ks) <= du + dv)%Z.
Proof.
  intros root u v du dv (vs1 & ks1 & W1 & H1 & L1 & S1) (vs2 & ks2 & W2 & H2 & L2 & S2).
  destruct vs1 as [| r1 vs1]; [inversion W1|]. destruct vs2 as [| r2 vs2]; [inversion W2|].
  simpl in H1, H2. inversion H1; inversion H2; subst r1 r2.
  apply walk_rev in W1.
  assert (E : rev (root :: vs1) = rev vs1 ++ [root]) by reflexivity. rewrite E in W1.
  exists (rev vs1 ++ root :: vs2), (rev ks1 ++ ks2). split; [apply walk_app; auto|].
  split.
  - assert (Hl : hd_error (rev (root :: vs1)) = Some (last (root :: vs1) 0%N)).
    { clear. revert root. induction vs1 as [| a vs1 IH]; intros root; [reflexivity|].
      change (last (root :: a :: vs1) 0%N) with (last (a :: vs1) 0%N). rewrite <- IH.
      simpl. destruct (rev vs1); reflexivity. }
    rewrite E, L1 in Hl. rewrite <- Hl. destruct (rev vs1); reflexivity.
  - split; [rewrite last_app_cons; exact L2|]. rewrite wsum_app, wsum_rev. lia.
Qed.

End Abstract.

Definition ni (a : N) : int := of_Z (Z.of_N a).

Lemma ni_phi : forall a, (Z.of_N a < wB)%Z -> (φ (ni a)) = Z.of_N a.
Proof. intros a H. unfold ni. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma ni_nodeN : forall x, ni (nodeN x) = x.
Proof. intros x. unfold ni. rewrite nodeN_Z. apply of_to_Z. Qed.

Lemma nodeN_ni : forall a, (Z.of_N a < wB)%Z -> nodeN (ni a) = a.
Proof. intros a H. unfold nodeN. rewrite ni_phi by auto. lia. Qed.

Lemma Forall_get : forall (P : N -> Prop) l k, Forall P l -> (k < len l)%N -> P (Prelude.get l k).
Proof.
  intros P l k H Hk. unfold Prelude.get, len in *. rewrite Forall_forall in H. apply H.
  apply nth_In. lia.
Qed.

Section Main.
Variables (p eu ev ew : list N) (xp xu xv xw : array int).
Hypothesis HV : valid_input p eu ev ew.
Hypotheses (Rp : repr (xp : array uint) p) (Ru : repr (xu : array uint) eu)
           (Rv : repr (xv : array uint) ev) (Rw : repr (xw : array uint) ew).

Definition nZ : Z := Z.of_nat (List.length p).
Definition mZ : Z := Z.of_nat (List.length eu).

Lemma n_bounds : (1 <= nZ <= 200000)%Z.
Proof. destruct HV. unfold nZ, len in *. lia. Qed.

Lemma m_eq : mZ = (nZ - 1)%Z.
Proof. destruct HV. unfold nZ, mZ, len in *. lia. Qed.

Lemma len_xp : (φ (PArray.length xp)) = nZ.
Proof. exact (repr_len xp p Rp). Qed.
Lemma len_xu : (φ (PArray.length xu)) = mZ.
Proof. exact (repr_len xu eu Ru). Qed.
Lemma len_xv : (φ (PArray.length xv)) = mZ.
Proof. transitivity (Z.of_nat (List.length ev)); [exact (repr_len xv ev Rv) | destruct HV; unfold mZ, len in *; lia]. Qed.
Lemma len_xw : (φ (PArray.length xw)) = mZ.
Proof. transitivity (Z.of_nat (List.length ew)); [exact (repr_len xw ew Rw) | destruct HV; unfold mZ, len in *; lia]. Qed.

Lemma get_xu : forall k, ((φ k) < mZ)%Z -> (φ (xu.[k])) = Z.of_N (Prelude.get eu (Z.to_N (φ k))).
Proof. intros k Hk. exact (repr_get xu eu Ru k Hk). Qed.
Lemma get_xv : forall k, ((φ k) < mZ)%Z -> (φ (xv.[k])) = Z.of_N (Prelude.get ev (Z.to_N (φ k))).
Proof. intros k Hk. exact (repr_get xv ev Rv k ltac:(destruct HV; unfold mZ, len in *; lia)). Qed.
Lemma get_xw : forall k, ((φ k) < mZ)%Z -> (φ (xw.[k])) = Z.of_N (Prelude.get ew (Z.to_N (φ k))).
Proof. intros k Hk. exact (repr_get xw ew Rw k ltac:(destruct HV; unfold mZ, len in *; lia)). Qed.
Lemma get_xp : forall k, ((φ k) < nZ)%Z -> (φ (xp.[k])) = Z.of_N (Prelude.get p (Z.to_N (φ k))).
Proof. intros k Hk. exact (repr_get xp p Rp k Hk). Qed.

Lemma xu_range : forall k, ((φ k) < mZ)%Z -> (1 <= (φ (xu.[k])) <= nZ)%Z.
Proof.
  intros k Hk. rewrite get_xu by auto. destruct HV.
  pose proof (Forall_get _ eu (Z.to_N (φ k)) vi_i ltac:(unfold len, mZ in *; lia)). simpl in H.
  unfold nZ, len in *. lia.
Qed.
Lemma xv_range : forall k, ((φ k) < mZ)%Z -> (1 <= (φ (xv.[k])) <= nZ)%Z.
Proof.
  intros k Hk. rewrite get_xv by auto. destruct HV.
  pose proof (Forall_get _ ev (Z.to_N (φ k)) vi_j ltac:(unfold len, mZ in *; lia)). simpl in H.
  unfold nZ, len in *. lia.
Qed.
Lemma xw_range : forall k, ((φ k) < mZ)%Z -> (1 <= (φ (xw.[k])) <= 1000000)%Z.
Proof.
  intros k Hk. rewrite get_xw by auto. destruct HV.
  pose proof (Forall_get _ ew (Z.to_N (φ k)) vi_w ltac:(unfold len, mZ in *; lia)). simpl in H. lia.
Qed.
Lemma xp_range : forall k, ((φ k) < nZ)%Z -> (1 <= (φ (xp.[k])) <= 1000000)%Z.
Proof.
  intros k Hk. rewrite get_xp by auto. destruct HV.
  pose proof (Forall_get _ p (Z.to_N (φ k)) vi_p ltac:(unfold len, nZ in *; lia)). simpl in H. lia.
Qed.

Lemma mbound : (0 <= mZ <= nZ)%Z.
Proof. pose proof m_eq. pose proof n_bounds. unfold mZ in *. lia. Qed.

Definition P (a : N) : Z := Z.of_N (penalty p a).

Lemma pen : forall v : int, (1 <= (φ v) <= nZ)%Z -> (φ (xp.[v - 1])) = P (nodeN v).
Proof.
  intros v Hv. assert (E : (φ (v - 1)) = ((φ v) - 1)%Z) by sia.
  rewrite get_xp by lia. unfold P, penalty, nodeN. f_equal. f_equal. lia.
Qed.

Lemma half_edge : forall h, (h < HH mZ)%nat ->
  exists kN, joins eu ev kN (nodeN (hsrc xu xv (ofn h))) (nodeN (gh xu xv h)) /\
    (φ (wh xw h)) = Z.of_N (Prelude.get ew kN) /\ ((φ (wh xw h)) <= 1000000)%Z.
Proof.
  intros h Hh. pose proof (half_bound xu xv nZ mZ n_bounds mbound h Hh) as Hk. set (k := ofn h / 2) in *.
  exists (Z.to_N (φ k)). unfold gh, wh, hsrc, hdst. fold k.
  rewrite get_xw by auto. split; [|split; [reflexivity | rewrite <- get_xw by auto; apply xw_range; auto]].
  split; [unfold len, mZ in *; lia|].
  destruct (ofn h mod 2 =? 0); unfold nodeN; rewrite ?get_xu, ?get_xv by auto; [left|right]; split; lia.
Qed.

Lemma edge_half : forall kN a b, joins eu ev kN a b ->
  exists h, (h < HH mZ)%nat /\ fh xu xv h = Z.of_N a /\ gh xu xv h = ni b /\
    (φ (wh xw h)) = Z.of_N (Prelude.get ew kN).
Proof.
  intros kN a b [Hk Hab]. unfold len in Hk. fold mZ in Hk.
  assert (Hm : (Z.of_N kN < mZ)%Z) by (unfold mZ; lia).
  set (k := of_Z (Z.of_N kN)).
  assert (Ek : (φ k) = Z.of_N kN) by (unfold k; rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; pose proof n_bounds; pose proof m_eq; lia).
  assert (Hwk : (φ (xw.[k])) = Z.of_N (Prelude.get ew kN)) by (rewrite get_xw by lia; rewrite Ek; f_equal; f_equal; lia).
  pose proof n_bounds as NB. pose proof mbound as MB.
  destruct Hab as [[E1 E2] | [E1 E2]].
  - exists (2 * N.to_nat kN)%nat.
    assert (Eo : ofn (2 * N.to_nat kN) = 2 * k) by (apply to_Z_inj; rewrite ofn_phi by lia; rewrite mul_spec, Ek; change (φ 2) with 2%Z; rewrite Z.mod_small; rewrite ?wB_val; lia).
    assert (Hm2 : (2 * k) mod 2 =? 0 = true) by (apply eqb_true; apply to_Z_inj; rewrite mod_spec, mul_spec, Ek; change (φ 2) with 2%Z; rewrite (Z.mod_small (2 * _)) by (rewrite wB_val; lia); rewrite Z.mul_comm, Z_mod_mult; reflexivity).
    assert (Hd2 : (2 * k) / 2 = k) by (apply to_Z_inj; rewrite div_spec, mul_spec, Ek; change (φ 2) with 2%Z; rewrite (Z.mod_small (2 * _)) by (rewrite wB_val; lia); rewrite Z.mul_comm, Z_div_mult; lia).
    split; [unfold HH; lia|]. unfold fh, gh, wh, hsrc, hdst. rewrite Eo, Hm2, Hd2. split; [|split].
    + rewrite get_xu by lia. rewrite Ek, N2Z.id. congruence.
    + pose proof (xv_range k ltac:(lia)) as XV. rewrite get_xv in XV by lia. rewrite Ek, N2Z.id, E2 in XV.
      apply to_Z_inj. rewrite ni_phi by (rewrite wB_val; lia).
      rewrite get_xv by lia. rewrite Ek, N2Z.id. congruence.
    + exact Hwk.
  - exists (2 * N.to_nat kN + 1)%nat.
    assert (Eo : ofn (2 * N.to_nat kN + 1) = 2 * k + 1) by (apply to_Z_inj; rewrite ofn_phi by lia; rewrite add_spec, mul_spec, Ek; change (φ 2) with 2%Z; change (φ 1) with 1%Z; rewrite (Z.mod_small (2 * _)) by (rewrite wB_val; lia); rewrite Z.mod_small; rewrite ?wB_val; lia).
    assert (Hm2 : (2 * k + 1) mod 2 =? 0 = false).
    { apply eqb_false. intro F. apply (f_equal to_Z) in F. rewrite mod_spec in F. rewrite <- Eo, ofn_phi in F by lia.
      change (φ 2) with 2%Z in F. change (φ 0) with 0%Z in F.
      replace (Z.of_nat (2 * N.to_nat kN + 1)) with (1 + Z.of_N kN * 2)%Z in F by lia.
      rewrite Z_mod_plus_full in F. discriminate. }
    assert (Hd2 : (2 * k + 1) / 2 = k).
    { apply to_Z_inj. rewrite div_spec. rewrite <- Eo, ofn_phi by lia. change (φ 2) with 2%Z. rewrite Ek.
      replace (Z.of_nat (2 * N.to_nat kN + 1)) with (1 + Z.of_N kN * 2)%Z by lia.
      rewrite Z_div_plus_full by lia. reflexivity. }
    split; [unfold HH; lia|]. unfold fh, gh, wh, hsrc, hdst. rewrite Eo, Hm2, Hd2. split; [|split].
    + rewrite get_xv by lia. rewrite Ek, N2Z.id. congruence.
    + pose proof (xu_range k ltac:(lia)) as XU. rewrite get_xu in XU by lia. rewrite Ek, N2Z.id, E1 in XU.
      apply to_Z_inj. rewrite ni_phi by (rewrite wB_val; lia).
      rewrite get_xu by lia. rewrite Ek, N2Z.id. congruence.
    + exact Hwk.
Qed.

Definition n1 : int := PArray.length xp + 1.
Definition hh : int := PArray.length xu + PArray.length xu.
Definition degA : array int := deg_loop xu xv hh 0 (PArray.make n1 0) (Zwf_well_founded 0 (gap hh 0)).
Definition spA : array int * array int :=
  start_loop degA n1 0 (PArray.make (n1 + 1) 0) (PArray.make n1 0) (Zwf_well_founded 0 (gap n1 0)).
Definition nwA : array int * array int :=
  fill_loop xu xv xw hh 0 (snd spA) (PArray.make hh 0) (PArray.make hh 0) (Zwf_well_founded 0 (gap hh 0)).
Definition saA : array int := fst spA.
Definition nbrA : array int := fst nwA.
Definition wtA : array int := snd nwA.

Lemma n1_phi : (φ n1) = (nZ + 1)%Z.
Proof. unfold n1. pose proof n_bounds. pose proof len_xp. rewrite phi_add_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia. Qed.

Lemma hh_phi : (φ hh) = (2 * mZ)%Z.
Proof. unfold hh. pose proof mbound. pose proof n_bounds. pose proof len_xu. rewrite phi_add_small; rewrite ?wB_val; lia. Qed.

Lemma deg_facts : (φ (PArray.length degA)) = (nZ + 1)%Z /\
  forall x : int, ((φ x) <= nZ)%Z -> (φ (degA.[x])) = Z.of_nat (cnt (fh xu xv) (φ x) (HH mZ)).
Proof.
  pose proof n_bounds. pose proof n1_phi. pose proof hh_phi. pose proof mbound.
  apply (deg_loop_ok xu xv nZ mZ n_bounds mbound len_xv xu_range xv_range hh _ 0 _ _ hh_phi eq_refl).
  - change (φ 0) with 0%Z. lia.
  - rewrite alength_make_small; lia.
  - intros x _. rewrite aget_make. reflexivity.
Qed.

Lemma sa_facts : (φ (PArray.length saA)) = (nZ + 2)%Z /\ (φ (PArray.length (snd spA))) = (nZ + 1)%Z /\
  (forall y : int, ((φ y) <= nZ + 1)%Z -> (φ (saA.[y])) = Z.of_nat (Sx xu xv mZ (Z.to_nat (φ y)))) /\
  (forall y : int, ((φ y) <= nZ)%Z -> (φ ((snd spA).[y])) = Z.of_nat (Sx xu xv mZ (Z.to_nat (φ y)))).
Proof.
  pose proof n_bounds. pose proof n1_phi. pose proof mbound. destruct deg_facts as [D1 D2].
  assert (E2 : (φ (n1 + 1)) = (nZ + 2)%Z) by (rewrite phi_add_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia).
  apply (start_loop_ok xu xv nZ mZ n_bounds mbound len_xv xu_range xv_range degA n1 _ 0 _ _ _ n1_phi eq_refl).
  - change (φ 0) with 0%Z. lia.
  - rewrite alength_make_small; lia.
  - rewrite alength_make_small; lia.
  - exact D2.
  - intros y Hy. rewrite aget_make. change (φ 0) with 0%Z in Hy. pose proof (to_Z_bounded y).
    replace (Z.to_nat (φ y)) with O by lia. reflexivity.
  - intros y Hy. change (φ 0) with 0%Z in Hy. pose proof (to_Z_bounded y). lia.
Qed.

Lemma nw_facts : (φ (PArray.length nbrA)) = (2 * mZ)%Z /\ (φ (PArray.length wtA)) = (2 * mZ)%Z /\
  forall h, (h < HH mZ)%nat -> nbrA.[ofn (idx xu xv mZ h)] = gh xu xv h /\ wtA.[ofn (idx xu xv mZ h)] = wh xw h.
Proof.
  pose proof n_bounds. pose proof hh_phi. pose proof mbound. destruct sa_facts as (S1 & S2 & S3 & S4).
  apply (fill_loop_ok xu xv xw nZ mZ n_bounds mbound len_xv xu_range xv_range hh _ 0 _ _ _ _ hh_phi eq_refl).
  - change (φ 0) with 0%Z. lia.
  - exact S2.
  - rewrite alength_make_small; lia.
  - rewrite alength_make_small; lia.
  - intros x Hx. rewrite S4 by lia. change (Z.to_nat (φ 0)) with O. simpl. lia.
  - intros h' Hh'. change (Z.to_nat (φ 0)) with O in Hh'. lia.
Qed.

Lemma csr_sound : forall x j : int, (1 <= (φ x) <= nZ)%Z ->
  ((φ (saA.[x])) <= (φ j) < (φ (saA.[x + 1])))%Z ->
  exists k, joins eu ev k (nodeN x) (nodeN (nbrA.[j])) /\
    (φ (wtA.[j])) = Z.of_N (Prelude.get ew k) /\ ((φ (wtA.[j])) <= 1000000)%Z.
Proof.
  intros x j Hx Hj.
  assert (Ex1 : (φ (x + 1)) = ((φ x) + 1)%Z).
  { pose proof n_bounds as NB0. clear - Hx NB0. rewrite phi_add_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia. }
  pose proof n_bounds. pose proof mbound.
  destruct sa_facts as (S1 & S2 & S3 & S4). destruct nw_facts as (N1 & N2 & N3).
  assert (T0 : ((φ x) <= nZ + 1)%Z) by (clear - Hx; lia).
  assert (T1 : ((φ (x + 1)) <= nZ + 1)%Z) by (clear - Hx Ex1; lia).
  pose proof (S3 x T0) as E0. pose proof (S3 (x + 1) T1) as E1'.
  clear S1 S2 S3 S4.
  rewrite E0, E1' in Hj. rewrite Ex1 in Hj.
  assert (Hs1 : Sx xu xv mZ (Z.to_nat ((φ x) + 1)) =
                (Sx xu xv mZ (Z.to_nat (φ x)) + cnt (fh xu xv) (φ x) (HH mZ))%nat).
  { replace (Z.to_nat ((φ x) + 1)) with (S (Z.to_nat (φ x))) by (clear - Hx; lia). rewrite Sx_succ.
    rewrite Z2Nat.id by (clear - Hx; lia). reflexivity. }
  rewrite Hs1 in Hj.
  destruct (cnt_surj (fh xu xv) (φ x) (HH mZ) (Z.to_nat (φ j) - Sx xu xv mZ (Z.to_nat (φ x))) ltac:(clear - Hj; lia))
    as (h & Hh & Fh & Ch).
  assert (Ej : ofn (idx xu xv mZ h) = j).
  { apply to_Z_inj. pose proof (idx_lt xu xv nZ mZ n_bounds mbound xu_range xv_range h Hh) as IL.
    assert (HS : (Z.of_nat (HH mZ) <= 400000)%Z) by (unfold HH; pose proof mbound as Q1; pose proof n_bounds as Q2; clear - Q1 Q2; lia). rewrite ofn_phi by (clear - IL HS; lia).
    unfold idx. rewrite Fh, Ch. clear - Hj. lia. }
  destruct (N3 h Hh) as [E1 E2]. rewrite Ej in E1, E2. rewrite E1, E2.
  destruct (half_edge h Hh) as (kN & J & W & Wb). exists kN. split; [|auto].
  replace (nodeN x) with (nodeN (hsrc xu xv (ofn h))); [exact J|].
  unfold nodeN. f_equal. exact Fh.
Qed.

Lemma csr_complete : forall kN a b, joins eu ev kN a b ->
  exists j, ((φ (saA.[ni a])) <= (φ j) < (φ (saA.[ni a + 1])))%Z /\ nbrA.[j] = ni b /\
    (φ (wtA.[j])) = Z.of_N (Prelude.get ew kN).
Proof.
  intros kN a b J. pose proof n_bounds as NB. pose proof mbound as MB.
  destruct (edge_half kN a b J) as (h & Hh & Fh & Gh & Wh).
  pose proof (fh_range xu xv nZ mZ n_bounds mbound xu_range xv_range h Hh) as Fr.
  pose proof (idx_bound xu xv nZ mZ n_bounds mbound xu_range xv_range h Hh) as IB.
  pose proof (idx_lt xu xv nZ mZ n_bounds mbound xu_range xv_range h Hh) as IL.
  assert (HS : (Z.of_nat (HH mZ) <= 400000)%Z) by (unfold HH; pose proof mbound as Q1; pose proof n_bounds as Q2; clear - Q1 Q2; lia).
  destruct nw_facts as (N1 & N2 & N3).
  exists (ofn (idx xu xv mZ h)). destruct (N3 h Hh) as [E1 E2].
  clear N1 N2 N3.
  assert (Ea : (φ (ni a)) = Z.of_N a) by (apply ni_phi; rewrite wB_val; clear - Fr Fh NB; lia).
  assert (Ea1 : (φ (ni a + 1)) = (Z.of_N a + 1)%Z).
  { rewrite phi_add_small; rewrite ?Ea; change (φ 1) with 1%Z; [reflexivity|]. rewrite wB_val. clear - Fr Fh NB. lia. }
  split; [|split; [rewrite E1; exact Gh | rewrite E2; exact Wh]].
  destruct sa_facts as (S1 & S2 & S3 & S4).
  rewrite (S3 (ni a) ltac:(clear - Ea Fr Fh; lia)), (S3 (ni a + 1) ltac:(clear - Ea1 Fr Fh; lia)).
  clear S1 S2 S3 S4.
  rewrite ofn_phi by (clear - IL HS; lia). rewrite Ea, Ea1. rewrite Fh in IB.
  replace (Z.to_nat (Z.of_N a + 1)) with (Z.to_nat (Z.of_N a) + 1)%nat by (clear; lia). clear - IB. lia.
Qed.

Lemma max_loop_eq : forall a n i acc H,
  max_loop a n i acc H =
  match bdec (i <? n) with
  | left Hi => max_loop a n (i + 1) (if acc <? a.[i] then a.[i] else acc) (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma max_loop_ok : forall z i acc H, gap (PArray.length xp) i = z -> ((φ i) <= nZ)%Z ->
  ((φ acc) <= 1000000)%Z ->
  let r := max_loop xp (PArray.length xp) i acc H in
  ((φ acc) <= (φ r) <= 1000000)%Z /\ forall k, ((φ i) <= (φ k) < nZ)%Z -> ((φ (xp.[k])) <= (φ r))%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Hi Ha r. unfold r. clear r. rewrite max_loop_eq.
  pose proof len_xp as LX.
  destruct (bdec (i <? PArray.length xp)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply (phi_succ i _ Hl')).
    pose proof (xp_range i ltac:(clear - Hl' LX; lia)) as XR.
    destruct (acc <? xp.[i]) eqn:E; [apply ltb_true in E | apply ltb_false in E].
    + destruct (IH (gap (PArray.length xp) (i + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hl)
                (i + 1) (xp.[i]) (Acc_inv H (dec_step _ i Hl)) eq_refl ltac:(clear - Hi1 Hl' LX; lia) ltac:(clear - XR; lia))
        as [B1 B2].
      split; [clear - E B1; lia|]. intros k Hk. destruct (Z.eq_dec (φ k) (φ i)) as [Ek | Nk].
      * apply to_Z_inj in Ek. subst k. clear - B1. lia.
      * apply B2. clear - Hk Nk Hi1. lia.
    + destruct (IH (gap (PArray.length xp) (i + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hl)
                (i + 1) acc (Acc_inv H (dec_step _ i Hl)) eq_refl ltac:(clear - Hi1 Hl' LX; lia) ltac:(clear - Ha; lia))
        as [B1 B2].
      split; [clear - B1; lia|]. intros k Hk. destruct (Z.eq_dec (φ k) (φ i)) as [Ek | Nk].
      * apply to_Z_inj in Ek. subst k. clear - B1 E. lia.
      * apply B2. clear - Hk Nk Hi1. lia.
  - apply ltb_false in Hl. split; [clear - Ha; lia|]. intros k Hk. clear - Hk Hl LX. lia.
Qed.

Definition Xv : int := max_loop xp (PArray.length xp) 0 0 (Zwf_well_founded 0 (gap (PArray.length xp) 0)) + 1.

Lemma Xv_facts : (1 <= (φ Xv) <= 1000001)%Z /\
  forall v : int, (1 <= (φ v) <= nZ)%Z -> ((φ (xp.[v - 1])) < (φ Xv))%Z.
Proof.
  pose proof n_bounds as NB.
  destruct (max_loop_ok _ 0 0 (Zwf_well_founded 0 (gap (PArray.length xp) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; clear - NB; lia) ltac:(change (φ 0) with 0%Z; lia)) as [A B].
  unfold Xv. set (mx := max_loop xp (PArray.length xp) 0 0 (Zwf_well_founded 0 (gap (PArray.length xp) 0))) in *.
  assert (E : (φ (mx + 1)) = ((φ mx) + 1)%Z) by (apply phi_add_small; rewrite wB_val; change (φ 1) with 1%Z; clear - A; lia).
  rewrite E. split; [change (φ 0) with 0%Z in A; clear - A; lia|].
  intros v Hv. assert (Ev : (φ (v - 1)) = ((φ v) - 1)%Z) by (clear - Hv; sia).
  pose proof (B (v - 1) ltac:(change (φ 0) with 0%Z; clear - Hv Ev; lia)). clear - H. lia.
Qed.

Lemma true_loop_eq : forall n1 i a H,
  true_loop n1 i a H =
  match bdec (i <? n1) with
  | left Hi => true_loop n1 (i + 1) a.[i <- true] (Acc_inv H (dec_step n1 i Hi))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma true_loop_ok : forall z i a H, gap n1 i = z -> (1 <= (φ i) <= (φ n1))%Z ->
  (φ (PArray.length a)) = (φ n1) ->
  (forall y, a.[y] = true <-> (1 <= (φ y) < (φ i))%Z) ->
  let a' := true_loop n1 i a H in
  (φ (PArray.length a')) = (φ n1) /\ (forall y, a'.[y] = true <-> (1 <= (φ y) < (φ n1))%Z) .
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i a H Hz Hi La Ha a'. unfold a'. clear a'. rewrite true_loop_eq.
  destruct (bdec (i <? n1)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply (phi_succ i _ Hl')).
    assert (Bi : (i <? PArray.length a) = true) by (apply ltb_true; clear - La Hl'; lia).
    apply (IH (gap n1 (i + 1))); [rewrite <- Hz; apply dec_step; exact Hl | reflexivity | clear - Hi Hi1 Hl'; lia
          | rewrite blength_set; exact La |].
    intros y. rewrite bget_set by exact Bi. destruct (i =? y) eqn:E.
    + apply eqb_true in E. subst. split; [intros _; clear - Hi Hi1; lia | reflexivity].
    + apply eqb_false in E. rewrite Ha. assert ((φ i) <> (φ y)) by (intro F; apply E; apply to_Z_inj; auto).
      clear - H0 Hi1. lia.
  - apply ltb_false in Hl. split; [exact La|]. intros y. rewrite Ha. clear - Hl Hi. lia.
Qed.

Definition A1 (alive : array bool) (a : N) : Prop := alive.[ni a] = true.

Lemma walk_range : forall vs ks, walk eu ev vs ks -> forall u, hd_error vs = Some u ->
  (1 <= Z.of_N u <= nZ)%Z -> Forall (fun a => (1 <= Z.of_N a <= nZ)%Z) vs.
Proof.
  intros vs ks W. induction W as [a | a b k vs ks Jk W IH]; intros u Hu Hr; simpl in Hu; inversion Hu; subst.
  - constructor; auto.
  - constructor; auto. apply (IH b eq_refl). destruct HV.
    destruct Jk as [Hk [[E1 E2] | [E1 E2]]].
    + pose proof (Forall_get _ ev k vi_j ltac:(rewrite vi_ev; exact Hk)). simpl in H. unfold nZ, len in *. lia.
    + pose proof (Forall_get _ eu k vi_i Hk). simpl in H. unfold nZ, len in *. lia.
Qed.

Lemma ni_range : forall a, (1 <= Z.of_N a <= nZ)%Z -> (φ (ni a)) = Z.of_N a /\ nodeN (ni a) = a.
Proof.
  intros a H. pose proof n_bounds. assert (Z.of_N a < wB)%Z by (rewrite wB_val; lia).
  split; [apply ni_phi | apply nodeN_ni]; auto.
Qed.

Lemma joins_range : forall k a b, joins eu ev k a b ->
  (1 <= Z.of_N a <= nZ)%Z /\ (1 <= Z.of_N b <= nZ)%Z.
Proof.
  intros k a b [Hk Hab]. destruct HV.
  pose proof (Forall_get _ ev k vi_j ltac:(rewrite vi_ev; exact Hk)).
  pose proof (Forall_get _ eu k vi_i Hk). simpl in *. unfold nZ, len in *.
  destruct Hab as [[E1 E2] | [E1 E2]]; subst; lia.
Qed.

Record MI (r rnd : int) (alive : array bool) (S : mst) : Prop := {
  mi_la : (φ (PArray.length alive)) = (nZ + 1)%Z;
  mi_al : forall y, alive.[y] = true -> (1 <= (φ y) <= nZ)%Z;
  mi_r : (1 <= (φ r) <= nZ + 1)%Z;
  mi_dead : forall y, ((φ y) < (φ r))%Z -> alive.[y] = false;
  mi_rnd : (1 <= (φ rnd))%Z /\ ((φ rnd) + bcount alive (Z.to_nat (nZ + 1)) = nZ + 1)%Z;
  mi_lv : (φ (PArray.length (m_vis S))) = (nZ + 1)%Z;
  mi_lc : (φ (PArray.length (m_comp S))) = (nZ + 1)%Z;
  mi_lp : (φ (PArray.length (m_par S))) = (nZ + 1)%Z;
  mi_ld : (φ (PArray.length (m_d S))) = (nZ + 1)%Z;
  mi_lb : (φ (PArray.length (m_best S))) = (nZ + 1)%Z;
  mi_vis : forall y, ((φ ((m_vis S).[y])) < 2 * (φ rnd))%Z;
  mi_lw : LW Xv (m_T S);
  mi_st : forall k, ((φ ((l_st (m_T S)).[k])) < (φ rnd))%Z;
  mi_low : forall u, (1 <= Z.of_N u <= nZ)%Z -> forall vs ks, walk eu ev vs ks -> hd_error vs = Some u ->
    ((φ ((m_best S).[ni u])) <= Z.of_N (wsum ew ks) + P u * P (last vs 0%N))%Z \/ Forall (A1 alive) vs;
  mi_wit : forall u, (1 <= Z.of_N u <= nZ)%Z ->
    ((φ INF) <= (φ ((m_best S).[ni u])))%Z \/
    exists vs ks, walk eu ev vs ks /\ hd_error vs = Some u /\
      (Z.of_N (wsum ew ks) + P u * P (last vs 0%N) <= (φ ((m_best S).[ni u])))%Z
}.

Lemma process_ok : forall r rnd alive S, MI r rnd alive S -> ((φ r) <= nZ)%Z -> alive.[r] = true ->
  MI r (rnd + 1) alive.[fst (process saA nbrA wtA xp Xv alive r rnd S) <- false]
     (snd (process saA nbrA wtA xp Xv alive r rnd S)).
Proof.
  intros r rnd alive S M Hr Ar.
  destruct M as [La Al Rr Dd [R1 R2] Lv Lc Lp Ld Lb Vs LWT St Low Wit].
  pose proof n_bounds as NB.
  pose proof (bcount_nonneg alive (Z.to_nat (nZ + 1))) as BC.
  assert (Hs1 : (φ (2 * rnd)) = (2 * (φ rnd))%Z) by (clear - R1 R2 BC NB; rewrite mul_spec; change (φ 2) with 2%Z; rewrite Z.mod_small; rewrite ?wB_val; lia).
  assert (Hs2 : (φ (2 * rnd + 1)) = (2 * (φ rnd) + 1)%Z) by (clear - Hs1 R1 R2 BC NB; rewrite phi_add_small; rewrite Hs1; change (φ 1) with 1%Z; rewrite ?wB_val; lia).
  assert (Hr1 : (φ (rnd + 1)) = ((φ rnd) + 1)%Z) by (clear - R1 R2 BC NB; rewrite phi_add_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia).
  assert (Hrl : (r <? PArray.length alive) = true) by (apply ltb_true; clear - La Hr; lia).
  unfold process. cbv zeta. cbn [fst snd m_vis m_comp m_par m_d m_sz m_big m_T m_best].
  set (b1 := bfs saA nbrA wtA alive (2 * rnd) r (m_vis S) (m_comp S) (m_par S) (m_d S)).
  pose proof (bfs_ok eu ev ew nZ saA nbrA wtA alive n_bounds csr_sound Al (2 * rnd) r _ _ _ _ Lv Lc Lp Ld Ar
                ltac:(intros y; rewrite Hs1; apply Vs)) as I1. fold b1 in I1.
  set (c := pick alive (fst (centroid (b_comp b1) (b_par b1) (m_sz S) (m_big S) (b_tail b1))) r).
  destruct (pick_ok alive (fst (centroid (b_comp b1) (b_par b1) (m_sz S) (m_big S) (b_tail b1))) r Hrl Ar) as [Pc1 Pc2].
  fold c in Pc1, Pc2.
  set (b2 := bfs saA nbrA wtA alive (2 * rnd + 1) c (b_vis b1) (b_comp b1) (b_par b1) (b_d b1)).
  pose proof (bfs_ok eu ev ew nZ saA nbrA wtA alive n_bounds csr_sound Al (2 * rnd + 1) c _ _ _ _
                (bi_lv _ _ _ _ _ _ _ _ _ _ _ _ I1) (bi_lc _ _ _ _ _ _ _ _ _ _ _ _ I1)
                (bi_lp _ _ _ _ _ _ _ _ _ _ _ _ I1) (bi_ld _ _ _ _ _ _ _ _ _ _ _ _ I1) Pc2
                ltac:(intros y; pose proof (bi_le _ _ _ _ _ _ _ _ _ _ _ _ I1 y); rewrite Hs2; rewrite Hs1 in *; lia)) as I2.
  fold b2 in I2.
  set (t := b_tail b2) in *. set (comp2 := b_comp b2) in *.
  set (d' := relax saA nbrA wtA alive comp2 t b2).
  destruct (relax_ok eu ev ew nZ saA nbrA wtA alive n_bounds csr_sound _ c b2 I2) as [[Ld' RI2] Cons].
  fold comp2 t d' in Ld', RI2, Cons.
  pose proof (relax_le saA nbrA wtA alive comp2 t b2) as DLE. fold d' in DLE.
  pose proof (bi_in _ _ _ _ _ _ _ _ _ _ _ _ I2) as IN2. fold t comp2 in IN2.
  pose proof (bi_ht _ _ _ _ _ _ _ _ _ _ _ _ I2) as HT2. fold t in HT2.
  destruct Xv_facts as [HX HXp].
  assert (Hlines : forall i, ((φ i) < (φ t))%Z ->
     ((φ (xp.[comp2.[i] - 1])) <= 1000000)%Z /\ ((φ (d'.[comp2.[i]])) <= Bd)%Z).
  { intros i Hi. destruct (IN2 i Hi) as [Ri _]. split; [|apply (RI2 i Hi)].
    assert (E : (φ (comp2.[i] - 1)) = ((φ (comp2.[i])) - 1)%Z) by (clear - Ri; sia).
    pose proof (xp_range (comp2.[i] - 1) ltac:(clear - Ri E; lia)). clear - H. lia. }
  pose proof (qinv_init xp comp2 d' Xv rnd HX (m_T S) LWT St) as Q0.
  set (T := ins_loop xp comp2 d' Xv rnd t 0 (m_T S) (Zwf_well_founded 0 (gap t 0))).
  pose proof (ins_loop_ok xp comp2 d' Xv rnd t HX Hlines _ 0 (m_T S) (Zwf_well_founded 0 (gap t 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; clear - HT2; lia) Q0) as Q. fold T in Q.
  destruct Q as (LWT' & VBT & QT).
  assert (Hq : forall i, ((φ i) < (φ t))%Z -> ((φ (xp.[comp2.[i] - 1])) <= 1000001)%Z)
    by (intros i Hi; pose proof (Hlines i Hi); clear - H; lia).
  assert (Hcb : forall j, ((φ j) < (φ t))%Z -> ((φ (comp2.[j])) < (φ (PArray.length (m_best S))))%Z)
    by (intros j Hj; destruct (IN2 j Hj) as [Rj _]; clear - Rj Lb; lia).
  set (best' := qry_loop xp comp2 d' Xv rnd t 0 T (m_best S) (Zwf_well_founded 0 (gap t 0))).
  destruct (qry_loop_ok xp comp2 d' Xv rnd t HX Hlines T VBT Hq _ 0 (m_best S) (Zwf_well_founded 0 (gap t 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; clear - HT2; lia) Hcb) as [LB' BB].
  fold best' in LB', BB.
  assert (Hcl : (c <? PArray.length alive) = true) by exact Pc1.
  assert (Hc : (1 <= (φ c) <= nZ)%Z) by (apply Al; exact Pc2).
  assert (Alv : forall y, alive.[c <- false].[y] = if c =? y then false else alive.[y])
    by (intros y; apply bget_set; exact Hcl).
  (* the members of the component *)
  set (Cset := fun a : N => (1 <= Z.of_N a <= nZ)%Z /\ exists i, ((φ i) < (φ t))%Z /\ comp2.[i] = ni a).
  assert (Croot : comp2.[0] = c) by apply (bi_root _ _ _ _ _ _ _ _ _ _ _ _ I2).
  assert (Ht0 : (0 < (φ t))%Z) by (pose proof (bi_t1 _ _ _ _ _ _ _ _ _ _ _ _ I2); fold t in H; clear - H; lia).
  assert (CsetN : forall a, Cset a -> alive.[ni a] = true).
  { intros a (_ & i & Hi & Ei). destruct (IN2 i Hi) as (_ & A2' & _). rewrite Ei in A2'. exact A2'. }
  constructor; cbn [m_vis m_comp m_par m_d m_sz m_big m_T m_best].
  - rewrite blength_set. exact La.
  - intros y Hy. rewrite Alv in Hy. destruct (c =? y); [discriminate | apply Al; exact Hy].
  - exact Rr.
  - intros y Hy. rewrite Alv. destruct (c =? y); [reflexivity | apply Dd; exact Hy].
  - split; [clear - Hr1 R1; lia|].
    rewrite bcount_kill by (auto; clear - La NB; lia).
    replace ((φ c) <? Z.of_nat (Z.to_nat (nZ + 1)))%Z with true by (symmetry; apply Z.ltb_lt; clear - Hc NB; lia).
    clear - Hr1 R2. lia.
  - exact (bi_lv _ _ _ _ _ _ _ _ _ _ _ _ I2).
  - exact (bi_lc _ _ _ _ _ _ _ _ _ _ _ _ I2).
  - exact (bi_lp _ _ _ _ _ _ _ _ _ _ _ _ I2).
  - exact Ld'.
  - rewrite LB'. exact Lb.
  - intros y. pose proof (bi_le _ _ _ _ _ _ _ _ _ _ _ _ I2 y). rewrite Hs2 in H. rewrite Hr1. clear - H. lia.
  - exact LWT'.
  - intros k. pose proof (ins_loop_stamp xp comp2 d' Xv rnd t _ 0 (m_T S) (Zwf_well_founded 0 (gap t 0)) eq_refl
                            ltac:(intros k0; pose proof (St k0); clear - H; lia) k) as SK.
    fold T in SK. rewrite Hr1. clear - SK. lia.
  - intros u Hu vs ks W Hd.
    pose proof (walk_range vs ks W u Hd Hu) as WR.
    destruct (Low u Hu vs ks W Hd) as [B | FA].
    + left. destruct (BB (ni u)) as [B1 _]. clear - B B1. lia.
    + destruct (in_dec N.eq_dec (nodeN c) vs) as [Hin | Hnin].
      * left.
        apply (lb_abstract eu ev ew Cset (A1 alive) (fun a => (φ (d'.[ni a]))) (fun a => (φ (best'.[ni a]))) P (nodeN c));
          [ | | | | | exact W | exact Hd | exact FA | exact Hin ].
        -- intros k a b J Ca Ab. destruct (joins_range k a b J) as [Ra Rb]. split; [exact Rb|].
           destruct Ca as (_ & i & Hi & Ei). destruct (csr_complete k a b J) as (j & Hj & Nj & Wj).
           assert (Hadj : adj saA (comp2.[i]) j) by (unfold adj; rewrite Ei; exact Hj).
           assert (Aj : alive.[nbrA.[j]] = true) by (rewrite Nj; exact Ab).
           pose proof (bi_clo _ _ _ _ _ _ _ _ _ _ _ _ I2 i j Hi Hadj Aj) as V.
           destruct (bi_vis _ _ _ _ _ _ _ _ _ _ _ _ I2 _ V) as (i' & Hi' & Ei').
           exists i'. split; [exact Hi'|]. fold comp2 in Ei'. rewrite Ei', Nj. reflexivity.
        -- intros k a b J Ca Cb. cbv beta. destruct Ca as (Ra & i & Hi & Ei). destruct Cb as (Rb & i' & Hi' & Ei').
           destruct (csr_complete k a b J) as (j & Hj & Nj & Wj).
           assert (Hadj : adj saA (comp2.[i]) j) by (unfold adj; rewrite Ei; exact Hj).
           assert (Aj : alive.[nbrA.[j]] = true).
           { rewrite Nj, <- Ei'. destruct (IN2 i' Hi') as (_ & X & _). exact X. }
           pose proof (Cons i j Hi Hadj Aj) as Cn. rewrite Nj, Ei, Wj in Cn. exact Cn.
        -- split; [rewrite nodeN_Z; exact Hc|]. exists 0. split; [exact Ht0|]. rewrite ni_nodeN. exact Croot.
        -- cbv beta. rewrite ni_nodeN. destruct DLE as [DL1 DL2].
           pose proof (bi_ld _ _ _ _ _ _ _ _ _ _ _ _ I2) as Ld2.
           assert (Hc0 : ((φ 0) < (φ t))%Z) by exact Ht0.
           destruct (bi_wit _ _ _ _ _ _ _ _ _ _ _ _ I2 0 Hc0) as [_ W0]. fold comp2 in W0. rewrite Croot in W0.
           pose proof (DL2 c ltac:(clear - Ld2 Hc; lia)). change (φ 0) with 0%Z in W0. clear - H W0. lia.
        -- intros a v Ca Cv. cbv beta. destruct Ca as (Ra & i & Hi & Ei). destruct Cv as (Rv' & iv & Hiv & Eiv).
           destruct (BB (ni a)) as (_ & B2 & _).
           assert (Hi0 : ((φ 0) <= (φ i) < (φ t))%Z) by (change (φ 0) with 0%Z; pose proof (to_Z_bounded i); clear - Hi H; lia).
           specialize (B2 (ex_intro _ i (conj Hi0 Ei))).
           unfold qv in B2.
           destruct (ni_range a Ra) as [Pa Na]. destruct (ni_range v Rv') as [Pv Nv].
           assert (Ex : (φ (xp.[ni a - 1])) = P a) by (rewrite pen by (rewrite Pa; exact Ra); rewrite Na; reflexivity).
           assert (Exv : (φ (xp.[ni v - 1])) = P v) by (rewrite pen by (rewrite Pv; exact Rv'); rewrite Nv; reflexivity).
           assert (Hx : ((φ (xp.[ni a - 1])) < (φ Xv))%Z) by (apply HXp; rewrite Pa; exact Ra).
           destruct (QT _ Hx) as [Q1 _]. pose proof (Q1 iv Hiv) as Qi. unfold line, lv in Qi. rewrite Eiv in Qi.
           rewrite Ex, Exv in Qi. clear - B2 Qi. nia.
      * right. rewrite Forall_forall in FA, WR |- *. intros a Ha. unfold A1. rewrite Alv.
        destruct (c =? ni a) eqn:E; [|apply FA; exact Ha]. exfalso. apply eqb_true in E. apply Hnin.
        destruct (ni_range a (WR a Ha)) as [_ Na]. rewrite E, Na. exact Ha.
  - intros u Hu. destruct (ni_range u Hu) as [Pu Nu].
    destruct (BB (ni u)) as (B1 & _ & B3). destruct B3 as [E | ((jj & Hjj & Ejj) & E)].
    + rewrite E. apply Wit. exact Hu.
    + unfold qv in E.
      assert (Hx : ((φ (xp.[ni u - 1])) < (φ Xv))%Z) by (apply HXp; rewrite Pu; exact Hu).
      assert (Ex : (φ (xp.[ni u - 1])) = P u) by (rewrite pen by (rewrite Pu; exact Hu); rewrite Nu; reflexivity).
      destruct (QT _ Hx) as [_ [QI | (i & Hi & QL)]].
      * left. rewrite E, QI. pose proof (to_Z_bounded (d'.[ni u])). clear - H. lia.
      * right. unfold line, lv in QL.
        destruct (IN2 i Hi) as (Rvv & _ & _).
        assert (Hjj' : ((φ jj) < (φ t))%Z) by (clear - Hjj; lia).
        destruct (RI2 jj Hjj') as [Wu _]. destruct (RI2 i Hi) as [Wv _].
        rewrite Ejj in Wu.
        destruct Wu as (vs1 & ks1 & W1 & H1 & L1 & S1). destruct Wv as (vs2 & ks2 & W2 & H2 & L2 & S2).
        rewrite Nu in L1.
        destruct (wit_abstract eu ev ew (nodeN c) u (nodeN (comp2.[i])) _ _
                   (ex_intro _ vs1 (ex_intro _ ks1 (conj W1 (conj H1 (conj L1 S1)))))
                   (ex_intro _ vs2 (ex_intro _ ks2 (conj W2 (conj H2 (conj L2 S2))))))
          as (vs & ks & W & Hd & Lst & Sw).
        exists vs, ks. split; [exact W|]. split; [exact Hd|]. rewrite Lst.
        assert (Ev : (φ (xp.[comp2.[i] - 1])) = P (nodeN (comp2.[i]))) by (apply pen; exact Rvv).
        rewrite E, QL, Ev, Ex. clear - Sw. nia.
Qed.

Lemma main_loop_eq : forall sa nbr wt xp' X r rnd alive S H,
  main_loop sa nbr wt xp' X r rnd alive S H =
  match bdec (r <? PArray.length alive) with
  | left Hr =>
      match bdec alive.[r] with
      | left Ha =>
          let cS := process sa nbr wt xp' X alive r rnd S in
          main_loop sa nbr wt xp' X r (rnd + 1) alive.[fst cS <- false] (snd cS)
            (Acc_inv H (kill_dec alive r (fst cS) Hr
               (proj1 (process_pick sa nbr wt xp' X alive r rnd S Hr Ha))
               (proj2 (process_pick sa nbr wt xp' X alive r rnd S Hr Ha))))
      | right _ =>
          main_loop sa nbr wt xp' X (r + 1) rnd alive S (Acc_inv H (next_dec alive r Hr))
      end
  | right _ => m_best S
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition FinalP (best : array int) : Prop :=
  (φ (PArray.length best)) = (nZ + 1)%Z /\
  (forall u, (1 <= Z.of_N u <= nZ)%Z -> forall vs ks, walk eu ev vs ks -> hd_error vs = Some u ->
     ((φ (best.[ni u])) <= Z.of_N (wsum ew ks) + P u * P (last vs 0%N))%Z) /\
  (forall u, (1 <= Z.of_N u <= nZ)%Z ->
    ((φ INF) <= (φ (best.[ni u])))%Z \/
    exists vs ks, walk eu ev vs ks /\ hd_error vs = Some u /\
      (Z.of_N (wsum ew ks) + P u * P (last vs 0%N) <= (φ (best.[ni u])))%Z).

Lemma main_loop_ok : forall z r rnd alive S H, mmeasure alive r = z -> MI r rnd alive S ->
  FinalP (main_loop saA nbrA wtA xp Xv r rnd alive S H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros r rnd alive S H Hz M. rewrite main_loop_eq.
  pose proof (mi_la _ _ _ _ M) as La. pose proof (mi_r _ _ _ _ M) as Rr.
  destruct (bdec (r <? PArray.length alive)) as [Hr | Hr].
  - apply ltb_true in Hr as Hr'.
    destruct (bdec alive.[r]) as [Ha | Ha].
    + cbv zeta. eapply IH; [ | reflexivity | apply process_ok; auto; clear - Hr' La; lia ].
      rewrite <- Hz. apply kill_dec; auto.
      * apply (proj1 (process_pick _ _ _ _ _ _ _ _ _ Hr Ha)).
      * apply (proj2 (process_pick _ _ _ _ _ _ _ _ _ Hr Ha)).
    + eapply IH; [ rewrite <- Hz; apply next_dec; exact Hr | reflexivity | ].
      assert (Hr1 : (φ (r + 1)) = ((φ r) + 1)%Z) by (apply (phi_succ r _ Hr')).
      destruct M; constructor; auto.
      * clear - Hr1 Hr' La mi_r0. lia.
      * intros y Hy. destruct (Z.eq_dec (φ y) (φ r)).
        -- apply to_Z_inj in e. subst y. exact Ha.
        -- apply mi_dead0. clear - Hy Hr1 n. lia.
  - apply ltb_false in Hr. destruct M as [La' Al Rr' Dd _ _ _ _ _ Lb _ _ _ Low Wit].
    split; [exact Lb|]. split; [|exact Wit].
    intros u Hu vs ks W Hd. destruct (Low u Hu vs ks W Hd) as [B | FA]; [exact B|].
    exfalso. destruct vs as [| a vs]; [discriminate|]. simpl in Hd. inversion Hd; subst a.
    inversion FA; subst. unfold A1 in H2. destruct (ni_range u Hu) as [Pu _].
    rewrite (Dd (ni u) ltac:(clear - Pu Hu Hr La; lia)) in H2. discriminate.
Qed.

Definition aliveA : array bool := true_loop n1 1 (PArray.make n1 false) (Zwf_well_founded 0 (gap n1 1)).
Definition S0 : mst :=
  mkM (PArray.make n1 0) (PArray.make n1 0) (PArray.make n1 0)
      (PArray.make n1 0) (PArray.make n1 0) (PArray.make n1 0)
      (mkL (PArray.make (Xv + Xv) 0) (PArray.make (Xv + Xv) 0) (PArray.make (Xv + Xv) 0))
      (PArray.make n1 INF).

Lemma aliveA_facts : (φ (PArray.length aliveA)) = (nZ + 1)%Z /\
  forall y, aliveA.[y] = true <-> (1 <= (φ y) <= nZ)%Z.
Proof.
  pose proof n1_phi as N1. pose proof n_bounds as NB.
  destruct (true_loop_ok _ 1 (PArray.make n1 false) (Zwf_well_founded 0 (gap n1 1)) eq_refl
              ltac:(change (φ 1) with 1%Z; clear - N1 NB; lia)
              ltac:(rewrite blength_make_small; [reflexivity | clear - N1 NB; lia])
              ltac:(intros y; rewrite bget_make; change (φ 1) with 1%Z; split; [discriminate | intros; lia]))
    as [A B].
  fold aliveA in A, B. split; [rewrite A; exact N1|]. intros y. rewrite B. clear - N1. lia.
Qed.

Lemma bcount_aliveA : forall k, (Z.of_nat k <= nZ + 1)%Z -> bcount aliveA k = Z.max 0 (Z.of_nat k - 1).
Proof.
  destruct aliveA_facts as [A B]. pose proof n_bounds as NB.
  induction k; intros Hk; [reflexivity|]. cbn [bcount]. rewrite IHk by (clear - Hk; lia).
  assert (E : (φ (of_Z (Z.of_nat k))) = Z.of_nat k) by (apply of_Z_nat_phi; rewrite wB_val; clear - Hk NB; lia).
  destruct (aliveA.[of_Z (Z.of_nat k)]) eqn:F.
  - apply B in F. rewrite E in F. clear - F. lia.
  - destruct (Z.eq_dec (Z.of_nat k) 0) as [Z0 | Z0]; [clear - Z0; lia|].
    exfalso. assert (G : (1 <= (φ (of_Z (Z.of_nat k))) <= nZ)%Z) by (rewrite E; clear - Z0 Hk; lia).
    apply B in G. congruence.
Qed.

Lemma init_MI : MI 1 1 aliveA S0.
Proof.
  pose proof n1_phi as N1. pose proof n_bounds as NB. destruct aliveA_facts as [A B].
  destruct Xv_facts as [HX _].
  assert (L1 : forall (b : int), (φ (PArray.length (PArray.make n1 b))) = (nZ + 1)%Z)
    by (intros b; rewrite alength_make_small; [exact N1 | clear - N1 NB; lia]).
  assert (EX : (φ (Xv + Xv)) = ((φ Xv) + (φ Xv))%Z) by (apply phi_add_small; rewrite wB_val; clear - HX; lia).
  assert (L2 : (φ (PArray.length (PArray.make (Xv + Xv) 0))) = ((φ Xv) + (φ Xv))%Z)
    by (rewrite alength_make_small; [exact EX | clear - EX HX; lia]).
  constructor; unfold S0; cbn [m_vis m_comp m_par m_d m_sz m_big m_T m_best l_st l_m l_b].
  - exact A.
  - intros y Hy. apply B. exact Hy.
  - change (φ 1) with 1%Z. clear - NB. lia.
  - intros y Hy. change (φ 1) with 1%Z in Hy. destruct (aliveA.[y]) eqn:F; [|reflexivity].
    apply B in F. clear - F Hy. lia.
  - change (φ 1) with 1%Z. rewrite bcount_aliveA by (clear - NB; lia). split; [lia|]. clear - NB. lia.
  - apply L1.
  - apply L1.
  - apply L1.
  - apply L1.
  - apply L1.
  - intros y. rewrite aget_make. change (φ 1) with 1%Z. change (φ 0) with 0%Z. lia.
  - split; [exact L2 | split; exact L2].
  - intros k. rewrite aget_make. change (φ 1) with 1%Z. change (φ 0) with 0%Z. lia.
  - intros u Hu vs ks W Hd. right. pose proof (walk_range vs ks W u Hd Hu) as WR.
    rewrite Forall_forall in WR |- *. intros a Ha. unfold A1. apply B.
    destruct (ni_range a (WR a Ha)) as [E _]. rewrite E. apply WR. exact Ha.
  - intros u Hu. left. rewrite aget_make. lia.
Qed.

Lemma best_bound : forall best, FinalP best -> forall u, (1 <= Z.of_N u <= nZ)%Z ->
  ((φ (best.[ni u])) <= 1000000000000)%Z.
Proof.
  intros best [_ [Low _]] u Hu.
  pose proof (Low u Hu [u] [] (walk_one eu ev u) eq_refl) as B. simpl in B.
  assert (Hp : (1 <= P u <= 1000000)%Z).
  { unfold P, penalty. destruct HV. pose proof (Forall_get _ p (u - 1) vi_p ltac:(unfold len, nZ in *; lia)).
    simpl in H. lia. }
  clear - B Hp. nia.
Qed.

Lemma sum_loop_eq : forall best n1' i acc H,
  sum_loop best n1' i acc H =
  match bdec (i <? n1') with
  | left Hi => sum_loop best n1' (i + 1) (acc + best.[i]) (Acc_inv H (dec_step n1' i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sum_loop_ok : forall best, FinalP best -> forall z i acc H, gap n1 i = z ->
  (1 <= (φ i) <= nZ + 1)%Z ->
  (φ acc) = Z.of_N (sum_nodes (fun u => Z.to_N (φ (best.[ni u]))) (Z.to_nat ((φ i) - 1))) ->
  (φ (sum_loop best n1 i acc H)) = Z.of_N (sum_nodes (fun u => Z.to_N (φ (best.[ni u]))) (List.length p)).
Proof.
  intros best F z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Hi Ha. rewrite sum_loop_eq. pose proof n1_phi as N1. pose proof n_bounds as NB.
  set (f := fun u => Z.to_N (φ (best.[ni u]))).
  assert (SB : forall k, (Z.of_nat k <= nZ)%Z -> (Z.of_N (sum_nodes f k) <= Z.of_nat k * 1000000000000)%Z).
  { induction k; intros Hk; [simpl; lia|]. cbn [sum_nodes]. rewrite N2Z.inj_add.
    pose proof (IHk ltac:(lia)).
    pose proof (best_bound best F (N.of_nat (S k)) ltac:(clear - Hk; lia)). unfold f in *.
    rewrite Z2N.id by (apply to_Z_bounded). lia. }
  destruct (bdec (i <? n1)) as [Hl | Hl].
  - apply ltb_true in Hl as Hl'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply (phi_succ i _ Hl')).
    apply (IH (gap n1 (i + 1))); [rewrite <- Hz; apply dec_step; exact Hl | reflexivity | clear - Hi1 Hl' N1; lia |].
    rewrite Hi1. replace ((φ i) + 1 - 1)%Z with (Z.of_nat (S (Z.to_nat ((φ i) - 1)))) by (clear - Hi; lia).
    rewrite Nat2Z.id. cbn [sum_nodes]. fold f.
    assert (Ei : ni (N.of_nat (S (Z.to_nat ((φ i) - 1)))) = i).
    { apply to_Z_inj. rewrite ni_phi by (rewrite wB_val; clear - Hi NB; lia). clear - Hi. lia. }
    assert (Bi : ((φ (best.[i])) <= 1000000000000)%Z).
    { rewrite <- Ei. apply (best_bound best F). clear - Hi Hl' N1. lia. }
    pose proof (SB (Z.to_nat ((φ i) - 1)) ltac:(clear - Hi; lia)).
    rewrite phi_add_small.
    + rewrite Ha. rewrite N2Z.inj_add. unfold f in *. rewrite Ei. rewrite Z2N.id by (apply to_Z_bounded). reflexivity.
    + rewrite wB_val. rewrite Ha. unfold f in *. clear - H0 Bi Hi NB. nia.
  - apply ltb_false in Hl. rewrite Ha. f_equal. f_equal. unfold nZ in *. clear - Hl Hi N1. lia.
Qed.

Lemma last_any : forall (vs : list N) d1 d2, vs <> [] -> last vs d1 = last vs d2.
Proof. intros vs d1 d2 H. destruct vs as [| a vs]; [congruence|]. apply last_cons_any. Qed.

Lemma impl_correct : exists s : N, repr (yatp_impl xp xu xv xw : uint) s /\ yatp_spec p eu ev ew s.
Proof.
  pose proof n_bounds as NB. pose proof n1_phi as N1.
  change (yatp_impl xp xu xv xw) with
    (sum_loop (main_loop saA nbrA wtA xp Xv 1 1 aliveA S0 (Zwf_well_founded 0 (mmeasure aliveA 1)))
       n1 1 0 (Zwf_well_founded 0 (gap n1 1))).
  pose proof (main_loop_ok _ 1 1 aliveA S0 (Zwf_well_founded 0 (mmeasure aliveA 1)) eq_refl init_MI) as F.
  set (best := main_loop saA nbrA wtA xp Xv 1 1 aliveA S0 (Zwf_well_founded 0 (mmeasure aliveA 1))) in *.
  pose proof (sum_loop_ok best F _ 1 0 (Zwf_well_founded 0 (gap n1 1)) eq_refl
                ltac:(change (φ 1) with 1%Z; clear - NB; lia) ltac:(reflexivity)) as Sm.
  exists (Z.to_N (φ (sum_loop best n1 1 0 (Zwf_well_founded 0 (gap n1 1))))).
  split; [reflexivity|].
  exists (fun u => Z.to_N (φ (best.[ni u]))). split.
  - intros u Hu. assert (Hu' : (1 <= Z.of_N u <= nZ)%Z) by (unfold nZ, len in *; clear - Hu; lia).
    pose proof (best_bound best F u Hu') as BBd.
    destruct F as [_ [Low Wit]].
    destruct (Wit u Hu') as [Inf | (vs & ks & W & Hd & Cw)].
    { exfalso. rewrite INF_val in Inf. clear - Inf BBd. lia. }
    destruct (shortcut eu ev ew vs ks W) as (vs' & ks' & W' & Hd' & Hl' & ND & Sk).
    rewrite Hd in Hd'.
    pose proof (Low u Hu' vs' ks' W' Hd') as Lw.
    assert (Ne : vs' <> []) by (apply (walk_nonnil eu ev _ _ W')).
    assert (Hlast : last vs' 0%N = last vs 0%N) by apply Hl'.
    split.
    + exists (last vs' u), vs', ks'. split; [repeat split; auto|].
      unfold cost. change (fold_right (fun k acc => (Prelude.get ew k + acc)%N) 0%N ks') with (wsum ew ks').
      rewrite (last_any vs' u 0%N Ne). unfold P in *. rewrite Hlast in Lw |- *.
      apply N2Z.inj. rewrite Z2N.id by apply to_Z_bounded. rewrite N2Z.inj_add, N2Z.inj_mul.
      assert (Z.of_N (wsum ew ks') <= Z.of_N (wsum ew ks))%Z by (clear - Sk; lia).
      clear - Lw Cw H. lia.
    + intros v vs2 ks2 (W2 & H2 & L2 & ND2).
      pose proof (Low u Hu' vs2 ks2 W2 H2) as L.
      assert (Ne2 : vs2 <> []) by (apply (walk_nonnil eu ev _ _ W2)).
      rewrite (last_any vs2 0%N u Ne2), L2 in L. unfold cost.
      change (fold_right (fun k acc => (Prelude.get ew k + acc)%N) 0%N ks2) with (wsum ew ks2).
      unfold P in L. apply N2Z.inj_le. rewrite Z2N.id by apply to_Z_bounded. rewrite N2Z.inj_add, N2Z.inj_mul.
      exact L.
  - apply N2Z.inj. rewrite Z2N.id by apply to_Z_bounded. rewrite Sm. reflexivity.
Qed.


End Main.

Definition yatp_correct :
  forall (p eu ev ew : list N) (xp xu xv xw : array uint),
  valid_input p eu ev ew ->
  repr xp p -> repr xu eu -> repr xv ev -> repr xw ew ->
  exists s : N, repr (yatp xp xu xv xw) s /\ yatp_spec p eu ev ew s
  := fun p eu ev ew xp xu xv xw HV Rp Ru Rv Rw =>
       impl_correct p eu ev ew xp xu xv xw HV Rp Ru Rv Rw.
