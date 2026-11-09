(* Correctness proofs for chesstournament_implem.v. *)
(* Implementation of chesstournament (chesstournament.spec): union-find
   over the draws, then Kahn's topological sort of the win graph contracted
   onto the class representatives.

   Code (chess_impl), all on Uint63 ints and flat PArrays, no nat, no Z:
   1. iota: parent p[x] = x; rank array rk = 0.
   2. uf_loop: for every draw j, unite: two finds (path compression, find
      is recursive, depth O(log n) under union by rank) and a union by
      rank of the two roots.
   3. rep_loop: rep[x] = find x for every player (compressing further).
   4. deg_loop: out- and in-degree of rep[k_j] -> rep[l_j] for every win.
   5. pre_loop: CSR offsets st (prefix sums of the out-degrees, n+1 cells)
      and the fill cursors pos.
   6. fill_loop: adj[pos[rep k_j]++] = rep l_j for every win, in match order.
   7. init_loop + kahn/inner: the queue q (one flat array) receives every
      node whose in-degree is 0, then every node whose in-degree drops to 0
      while popping; the answer is (number of nodes queued = n).
   Termination: every loop recurses on an erased Acc (Zwf 0) (meas i),
   meas i = 2^63 - i, the counter i growing below a bound tested at every
   step; find recurses on an erased Acc (child p) x, the accessibility of
   x in the parent forest, which every phase carries as a Prop argument
   (forest_ok p) and re-establishes after each find / union (find_ok,
   unite_ok, uf_loop_ok).

   Proof: generic forest theory (anc, root_of, compress_*, link_root,
   union_roots); phase 1 keeps the roots inside draw classes (UF.uf_deq)
   and the two players of every processed draw in one class (UF.uf_draw);
   the graph section proves the degrees, offsets and CSR segments as
   counts / filters of the edge list EM, and Kahn's invariant (KI, II):
   in-degree = number of edges from not-yet-popped sources, queued iff
   in-degree 0, every edge into a queued node comes from an earlier
   popped node.  Queue complete -> the negated queue position is a skill
   function; queue incomplete -> every unqueued node has an unqueued
   stronger predecessor under any skill function, impossible on a finite
   set (no_ascent). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Relations Wellfounded.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export chesstournament_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make_ok : forall (n b : int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Definition bounded (N : int) (p : array int) : Prop :=
  forall y, ((φ y) < (φ N))%Z -> ((φ (p.[y])) < (φ N))%Z.

Lemma anc_trans : forall p x y z, anc p x y -> anc p y z -> anc p x z.
Proof.
  intros p x y z H. induction H as [x | x y' y Hs H IH]; intros Hz; [exact Hz|].
  eapply Relation_Operators.rt1n_trans; [exact Hs | apply IH; exact Hz].
Qed.

Lemma anc_root_eq : forall p r z, p.[r] = r -> anc p r z -> z = r.
Proof.
  intros p r z Hr H. induction H as [x | x y z Hs H IH]; [reflexivity|].
  subst y. rewrite Hr in *. apply IH; exact Hr.
Qed.

Lemma anc_det : forall p y z r, anc p y z -> anc p y r -> anc p z r \/ anc p r z.
Proof.
  intros p y z r H. revert r.
  induction H as [x | x y z Hs H IH]; intros r Hr.
  - left. exact Hr.
  - inversion Hr as [ | x' y' r' Hs' H' ]; subst.
    + right. eapply Relation_Operators.rt1n_trans; [reflexivity | exact H].
    + apply IH. assumption.
Qed.

Lemma root_unique : forall p y r1 r2, root_of p y r1 -> root_of p y r2 -> r1 = r2.
Proof.
  intros p y r1 r2 [A1 R1] [A2 R2].
  destruct (anc_det p y r1 r2 A1 A2) as [H | H].
  - symmetry. apply (anc_root_eq p r1 r2 R1 H).
  - apply (anc_root_eq p r2 r1 R2 H).
Qed.

Lemma root_exists : forall p y, Acc (child p) y -> exists r, root_of p y r.
Proof.
  intros p y H. induction H as [y _ IH].
  destruct (bdec (p.[y] =? y)) as [E | E].
  - exists y. split; [apply anc_refl | apply eqb_spec; exact E].
  - destruct (IH _ (child_step p y E)) as [r [Ha Hr]].
    exists r. split; [apply anc_step; exact Ha | exact Hr].
Qed.

Lemma anc_bounded : forall N p y z, bounded N p -> anc p y z ->
  ((φ y) < (φ N))%Z -> ((φ z) < (φ N))%Z.
Proof.
  intros N p y z Hb H. induction H as [x | x z' z Hs H IH]; intros Hy; [exact Hy|].
  subst z'. apply IH. apply Hb. exact Hy.
Qed.

Lemma compress_roots : forall p p',
  forest_ok p ->
  (forall y, p'.[y] = y <-> p.[y] = y) ->
  (forall y, anc p y p'.[y]) ->
  forall y r, root_of p y r -> root_of p' y r.
Proof.
  intros p p' Hp Hfix Hanc.
  pose proof (compress_ok p p' Hp Hfix Hanc) as Hp'.
  intros y. induction (Hp' y) as [y _ IH]. intros r [Ha Hr].
  destruct (bdec (p'.[y] =? y)) as [E | E].
  - apply eqb_spec in E. pose proof E as E'. apply Hfix in E'.
    pose proof (anc_root_eq p y r E' Ha). subst r.
    split; [apply anc_refl | exact E].
  - destruct (anc_det p y (p'.[y]) r (Hanc y) Ha) as [H | H].
    + destruct (IH _ (child_step p' y E) r (conj H Hr)) as [H1 H2].
      split; [apply anc_step; exact H1 | exact H2].
    + pose proof (anc_root_eq p r _ Hr H) as Hz.
      destruct (IH _ (child_step p' y E) r (conj (eq_ind_r (fun z => anc p z r) (anc_refl p r) Hz) Hr)) as [H1 H2].
      split; [apply anc_step; exact H1 | exact H2].
Qed.

Lemma compress_roots_iff : forall p p',
  forest_ok p ->
  (forall y, p'.[y] = y <-> p.[y] = y) ->
  (forall y, anc p y p'.[y]) ->
  forall y r, root_of p' y r <-> root_of p y r.
Proof.
  intros p p' Hp Hfix Hanc y r. split.
  - intros H. destruct (root_exists p y (Hp y)) as [r0 H0].
    pose proof (compress_roots p p' Hp Hfix Hanc y r0 H0) as H1.
    rewrite (root_unique p' y r r0 H H1). exact H0.
  - apply compress_roots; assumption.
Qed.

Lemma compress_bounded : forall N p p',
  bounded N p -> (forall y, anc p y p'.[y]) -> bounded N p'.
Proof.
  intros N p p' Hb Hanc y Hy. exact (anc_bounded N p y _ Hb (Hanc y) Hy).
Qed.

Lemma link_root : forall p a b, p.[a] = a -> p.[b] = b -> a <> b ->
  ((φ a) < (φ (PArray.length p)))%Z ->
  forall y r, root_of p y r -> root_of p.[a <- b] y (if r =? a then b else r).
Proof.
  intros p a b Ha Hb Hab Hal.
  assert (G : forall y, p.[a <- b].[y] = if y =? a then b else p.[y]).
  { intros y. rewrite aget_set_cases.
    destruct (y =? a) eqn:E1.
    - apply eqb_spec in E1. subst y. rewrite eqb_refl.
      replace (a <? PArray.length p) with true by (symmetry; apply ltb_spec; exact Hal).
      reflexivity.
    - replace (a =? y) with false; [reflexivity|].
      symmetry. apply eqb_false. intro F. subst. rewrite eqb_refl in E1. discriminate. }
  intros y r [H Hr]. induction H as [y | y z r Hs H IH].
  - destruct (y =? a) eqn:E.
    + apply eqb_spec in E. subst y. split.
      * apply anc_step. rewrite G, eqb_refl. apply anc_refl.
      * rewrite G. replace (b =? a) with false; [exact Hb|].
        symmetry. apply eqb_false. intro F. apply Hab. symmetry. exact F.
    + split; [apply anc_refl|]. rewrite G, E. exact Hr.
  - subst z. destruct (y =? a) eqn:E.
    + apply eqb_spec in E. subst y. rewrite Ha in IH. exact (IH Hr).
    + destruct (IH Hr) as [H1 H2]. split; [|exact H2].
      apply anc_step. rewrite G, E. exact H1.
Qed.

Lemma union_roots : forall p rk a b, p.[a] = a -> p.[b] = b ->
  ((φ a) < (φ (PArray.length p)))%Z -> ((φ b) < (φ (PArray.length p)))%Z ->
  exists c, (c = a \/ c = b) /\
  forall y r, root_of p y r ->
    root_of (fst (union p rk a b)) y (if orb (r =? a) (r =? b) then c else r).
Proof.
  intros p rk a b Ha Hb Hal Hbl. unfold union.
  destruct (a =? b) eqn:E.
  - apply eqb_spec in E. subst b. exists a. split; [left; reflexivity|].
    intros y r H. simpl. destruct (r =? a) eqn:E1; simpl; [|exact H].
    apply eqb_spec in E1. subst. exact H.
  - apply eqb_false in E.
    assert (E' : b <> a) by (intro F; apply E; symmetry; exact F).
    assert (K1 : forall y r, root_of p y r ->
              root_of p.[a <- b] y (if orb (r =? a) (r =? b) then b else r)).
    { intros y r H. pose proof (link_root p a b Ha Hb E Hal y r H) as H1.
      destruct (r =? a) eqn:E1; [exact H1|]. simpl.
      destruct (r =? b) eqn:E2; [|exact H1]. apply eqb_spec in E2. subst. exact H1. }
    assert (K2 : forall y r, root_of p y r ->
              root_of p.[b <- a] y (if orb (r =? a) (r =? b) then a else r)).
    { intros y r H. pose proof (link_root p b a Hb Ha E' Hbl y r H) as H1.
      destruct (r =? a) eqn:E1; simpl.
      - apply eqb_spec in E1. subst r.
        replace (a =? b) with false in H1 by (symmetry; apply eqb_false; exact E).
        exact H1.
      - exact H1. }
    destruct (rk.[a] <? rk.[b]); [exists b; split; [right; reflexivity | exact K1]|].
    destruct (rk.[b] <? rk.[a]); exists a; (split; [left; reflexivity | exact K2]).
Qed.

Lemma union_length : forall p rk a b,
  PArray.length (fst (union p rk a b)) = PArray.length p.
Proof.
  intros. unfold union. destruct (a =? b); [reflexivity|].
  destruct (rk.[a] <? rk.[b]); [apply alength_set|].
  destruct (rk.[b] <? rk.[a]); apply alength_set.
Qed.

Lemma union_bounded : forall N p rk a b, bounded N p ->
  ((φ a) < (φ N))%Z -> ((φ b) < (φ N))%Z -> bounded N (fst (union p rk a b)).
Proof.
  intros N p rk a b Hp Ha Hb y Hy. unfold union.
  destruct (a =? b); [apply Hp; exact Hy|].
  destruct (rk.[a] <? rk.[b]);
    [|destruct (rk.[b] <? rk.[a])]; simpl; rewrite aget_set_cases;
    match goal with |- context [if ?c then _ else _] => destruct c end;
    auto.
Qed.

Lemma unite_spec : forall N p rk k l (Hp : forest_ok p),
  bounded N p -> PArray.length p = N -> ((φ k) < (φ N))%Z -> ((φ l) < (φ N))%Z ->
  let p' := fst (unite p rk k l Hp) in
  bounded N p' /\ PArray.length p' = N /\
  exists a b c, root_of p k a /\ root_of p l b /\ (c = a \/ c = b) /\
  forall y r, root_of p y r -> root_of p' y (if orb (r =? a) (r =? b) then c else r).
Proof.
  intros N p rk k l Hp Hb Hl Hk Hl' p'. unfold p', unite.
  set (H1 := Hp k). set (f1 := find p k H1).
  set (H2 := find_ok p k H1 Hp l). set (f2 := find (fst f1) l H2).
  destruct (find_spec p k H1) as [R1 [F1 [A1 L1]]]. fold f1 in R1, F1, A1, L1.
  destruct (find_spec (fst f1) l H2) as [R2 [F2 [A2 L2]]]. fold f2 in R2, F2, A2, L2.
  pose proof (find_ok p k H1 Hp) as Hp1. fold f1 in Hp1.
  assert (Ba : ((φ (snd f1)) < (φ N))%Z) by exact (anc_bounded N p k _ Hb (proj1 R1) Hk).
  assert (Bp1 : bounded N (fst f1)) by exact (compress_bounded N p _ Hb A1).
  assert (Bb : ((φ (snd f2)) < (φ N))%Z) by exact (anc_bounded N _ l _ Bp1 (proj1 R2) Hl').
  assert (Bp2 : bounded N (fst f2)) by exact (compress_bounded N _ _ Bp1 A2).
  assert (Lp2 : PArray.length (fst f2) = N) by (rewrite L2, L1; exact Hl).
  assert (Iff : forall y r, root_of (fst f2) y r <-> root_of p y r).
  { intros y r. rewrite (compress_roots_iff _ _ Hp1 F2 A2).
    apply (compress_roots_iff _ _ Hp F1 A1). }
  split; [apply union_bounded; assumption|].
  split; [rewrite union_length; exact Lp2|].
  assert (Ra : (fst f2).[snd f1] = snd f1) by (apply F2; apply F1; exact (proj2 R1)).
  assert (Rb : (fst f2).[snd f2] = snd f2) by (apply F2; exact (proj2 R2)).
  destruct (union_roots (fst f2) rk (snd f1) (snd f2) Ra Rb
              ltac:(rewrite Lp2; exact Ba) ltac:(rewrite Lp2; exact Bb)) as [c [Hc Hu]].
  exists (snd f1), (snd f2), c.
  split; [exact R1|].
  split; [apply (compress_roots_iff _ _ Hp F1 A1); exact R2|]. split; [exact Hc|].
  intros y r Hr. apply Hu. apply Iff. exact Hr.
Qed.

Lemma rep_loop_eq : forall n x p rep Hp H,
  rep_loop n x p rep Hp H =
  match bdec (x <? n) with
  | left Hx =>
      let f := find p x (Hp x) in
      rep_loop n (x + 1) (fst f) rep.[x <- snd f] (find_ok p x (Hp x) Hp)
        (Acc_inv H (dec_step x n Hx))
  | right _ => rep
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma deg_loop_eq : forall rep ks wins ls m j od id H,
  deg_loop rep ks wins ls m j od id H =
  match bdec (j <? m) with
  | left Hj =>
      if wins.[j] then
        let a := rep.[ks.[j]] in
        let b := rep.[ls.[j]] in
        deg_loop rep ks wins ls m (j + 1) od.[a <- od.[a] + 1] id.[b <- id.[b] + 1]
          (Acc_inv H (dec_step j m Hj))
      else deg_loop rep ks wins ls m (j + 1) od id (Acc_inv H (dec_step j m Hj))
  | right _ => (od, id)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma pre_loop_eq : forall od n u s st pos H,
  pre_loop od n u s st pos H =
  match bdec (u <? n) with
  | left Hu =>
      let s' := s + od.[u] in
      pre_loop od n (u + 1) s' st.[u + 1 <- s'] pos.[u <- s]
        (Acc_inv H (dec_step u n Hu))
  | right _ => (st, pos)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_loop_eq : forall rep ks wins ls m j pos adj H,
  fill_loop rep ks wins ls m j pos adj H =
  match bdec (j <? m) with
  | left Hj =>
      if wins.[j] then
        let a := rep.[ks.[j]] in
        let pa := pos.[a] in
        fill_loop rep ks wins ls m (j + 1) pos.[a <- pa + 1] adj.[pa <- rep.[ls.[j]]]
          (Acc_inv H (dec_step j m Hj))
      else fill_loop rep ks wins ls m (j + 1) pos adj (Acc_inv H (dec_step j m Hj))
  | right _ => adj
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_loop_eq : forall id n v q t H,
  init_loop id n v q t H =
  match bdec (v <? n) with
  | left Hv =>
      if id.[v] =? 0 then init_loop id n (v + 1) q.[t <- v] (t + 1) (Acc_inv H (dec_step v n Hv))
      else init_loop id n (v + 1) q t (Acc_inv H (dec_step v n Hv))
  | right _ => (q, t)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma inner_eq : forall adj hi e d q t H,
  inner adj hi e d q t H =
  match bdec (e <? hi) with
  | left He =>
      let v := adj.[e] in
      let dv := d.[v] - 1 in
      if dv =? 0 then
        inner adj hi (e + 1) d.[v <- dv] q.[t <- v] (t + 1) (Acc_inv H (dec_step e hi He))
      else inner adj hi (e + 1) d.[v <- dv] q t (Acc_inv H (dec_step e hi He))
  | right _ => ((d, q), t)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma kahn_eq : forall adj st h d q t H,
  kahn adj st h d q t H =
  match bdec (h <? t) with
  | left Hh =>
      let u := q.[h] in
      let r := inner adj st.[u + 1] st.[u] d q t (Zwf_well_founded 0 (meas st.[u])) in
      kahn adj st (h + 1) (fst (fst r)) (snd (fst r)) (snd r) (Acc_inv H (dec_step h t Hh))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: lists                                                    *)
(* ------------------------------------------------------------------ *)

Definition cnt {A} (f : A -> bool) (l : list A) : nat := List.length (filter f l).

Lemma cnt_app : forall {A} (f : A -> bool) l1 l2, cnt f (l1 ++ l2) = (cnt f l1 + cnt f l2)%nat.
Proof. intros. unfold cnt. rewrite filter_app, length_app. reflexivity. Qed.

Lemma cnt_nil : forall {A} (f : A -> bool), cnt f [] = 0%nat.
Proof. reflexivity. Qed.

Lemma cnt_cons : forall {A} (f : A -> bool) a l,
  cnt f (a :: l) = ((if f a then 1 else 0) + cnt f l)%nat.
Proof. intros. unfold cnt. simpl. destruct (f a); reflexivity. Qed.

Lemma cnt_le_len : forall {A} (f : A -> bool) l, (cnt f l <= List.length l)%nat.
Proof.
  intros A f l. induction l as [|a l IH]; [rewrite cnt_nil; simpl; lia|].
  rewrite cnt_cons. simpl. destruct (f a); lia.
Qed.

Lemma cnt_mono : forall {A} (f g : A -> bool) l,
  (forall x, In x l -> f x = true -> g x = true) -> (cnt f l <= cnt g l)%nat.
Proof.
  intros A f g l. induction l as [|a l IH]; intros H; [rewrite !cnt_nil; lia|].
  rewrite !cnt_cons. specialize (IH (fun x Hx => H x (or_intror Hx))).
  destruct (f a) eqn:E.
  - rewrite (H a (or_introl eq_refl) E). lia.
  - destruct (g a); lia.
Qed.

Lemma cnt_ext : forall {A} (f g : A -> bool) l,
  (forall x, In x l -> f x = g x) -> cnt f l = cnt g l.
Proof.
  intros A f g l. induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite !cnt_cons. rewrite (H a (or_introl eq_refl)).
  rewrite IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma cnt_split : forall {A} (f g h : A -> bool) l,
  (forall x, f x = orb (g x) (h x)) -> (forall x, andb (g x) (h x) = false) ->
  cnt f l = (cnt g l + cnt h l)%nat.
Proof.
  intros A f g h l Hf Hd. induction l as [|a l IH]; [reflexivity|].
  rewrite !cnt_cons, IH, Hf. specialize (Hd a).
  destruct (g a), (h a); simpl in *; try discriminate; lia.
Qed.

Lemma cnt_eq_all : forall {A} (f g : A -> bool) l,
  (forall x, f x = true -> g x = true) -> cnt f l = cnt g l ->
  forall x, In x l -> g x = true -> f x = true.
Proof.
  intros A f g l Hfg. induction l as [|a l IH]; intros Heq x Hx Hg; [destruct Hx|].
  rewrite !cnt_cons in Heq.
  assert (M : (cnt f l <= cnt g l)%nat) by (apply cnt_mono; intros; apply Hfg; assumption).
  destruct (f a) eqn:Ef.
  - rewrite (Hfg a Ef) in Heq.
    destruct Hx as [Hx | Hx]; [subst; exact Ef|]. apply IH; [lia | exact Hx | exact Hg].
  - destruct (g a) eqn:Eg; [lia|].
    destruct Hx as [Hx | Hx]; [subst; rewrite Hg in Eg; discriminate|].
    apply IH; [lia | exact Hx | exact Hg].
Qed.

Lemma cnt_pos : forall {A} (f : A -> bool) l, (0 < cnt f l)%nat ->
  exists x, In x l /\ f x = true.
Proof.
  intros A f l. induction l as [|a l IH]; intros H; [rewrite cnt_nil in H; lia|].
  rewrite cnt_cons in H. destruct (f a) eqn:E.
  - exists a. split; [left; reflexivity | exact E].
  - destruct (IH ltac:(lia)) as [x [Hx Hf]]. exists x. split; [right; exact Hx | exact Hf].
Qed.

Lemma cnt_filter : forall {A} (f g : A -> bool) l,
  cnt g (filter f l) = cnt (fun x => andb (f x) (g x)) l.
Proof.
  intros A f g l. induction l as [|a l IH]; [reflexivity|].
  simpl. destruct (f a) eqn:E; simpl.
  - rewrite cnt_cons, IH, cnt_cons, E. reflexivity.
  - rewrite IH, cnt_cons, E. simpl. reflexivity.
Qed.

Lemma cnt_map : forall {A B} (g : B -> bool) (h : A -> B) l,
  cnt g (map h l) = cnt (fun x => g (h x)) l.
Proof.
  intros A B g h l. induction l as [|a l IH]; [reflexivity|].
  simpl. rewrite !cnt_cons, IH. reflexivity.
Qed.

Lemma cnt_firstn_le : forall {A} (f : A -> bool) i l, (cnt f (firstn i l) <= cnt f l)%nat.
Proof.
  intros A f i l. rewrite <- (firstn_skipn i l) at 2. rewrite cnt_app. lia.
Qed.

Lemma firstn_S_nth : forall {A} (d : A) i l, (i < List.length l)%nat ->
  firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros A d i. induction i as [|i IH]; intros l H; destruct l as [|a l]; simpl in *; try lia.
  - reflexivity.
  - rewrite (IH l) by lia. reflexivity.
Qed.

Lemma NoDup_snoc : forall {A} (l : list A) v, NoDup l -> ~ In v l -> NoDup (l ++ [v]).
Proof.
  intros A l v. induction l as [|a l IH]; intros H Hv.
  - constructor; [intros []|constructor].
  - inversion H as [|a' l' Ha Hl]; subst. simpl. constructor.
    + intros F. apply in_app_or in F. destruct F as [F | [F | []]]; [exact (Ha F)|].
      subst. apply Hv. left. reflexivity.
    + apply IH; [exact Hl|]. intros F. apply Hv. right. exact F.
Qed.

Definition memb (x : int) (l : list int) : bool := existsb (fun y => y =? x) l.

Lemma memb_spec : forall x l, memb x l = true <-> In x l.
Proof.
  intros x l. unfold memb. rewrite existsb_exists. split.
  - intros [y [Hy E]]. apply eqb_spec in E. subst. exact Hy.
  - intros H. exists x. split; [exact H | apply eqb_refl].
Qed.

Lemma memb_snoc : forall x l u, memb x (l ++ [u]) = orb (memb x l) (u =? x).
Proof.
  intros. unfold memb. rewrite existsb_app. simpl. rewrite Bool.orb_false_r. reflexivity.
Qed.

Fixpoint idx (v : int) (l : list int) : nat :=
  match l with
  | [] => 0
  | a :: l => if a =? v then 0 else S (idx v l)
  end.

Lemma idx_nth : forall l i v, NoDup l -> nth_error l i = Some v -> idx v l = i.
Proof.
  intros l. induction l as [|a l IH]; intros i v Hd Hi; [destruct i; discriminate|].
  inversion Hd as [|a' l' Ha Hl]; subst.
  destruct i as [|i]; simpl in Hi.
  - injection Hi as Hi. subst. simpl. rewrite eqb_refl. reflexivity.
  - simpl. destruct (a =? v) eqn:E.
    + apply eqb_spec in E. subst. exfalso. apply Ha. apply nth_error_In in Hi. exact Hi.
    + f_equal. apply IH; assumption.
Qed.

(* the first t cells of the queue *)
Definition Q (q : array int) (t : int) : list int :=
  map (fun i => q.[of_Z (Z.of_nat i)]) (seq 0 (Z.to_nat (φ t))).

Lemma Q_length : forall q t, List.length (Q q t) = Z.to_nat (φ t).
Proof. intros. unfold Q. rewrite length_map, length_seq. reflexivity. Qed.

Lemma of_Z_nat : forall i : nat, (Z.of_nat i < wB)%Z -> (φ (of_Z (Z.of_nat i))) = Z.of_nat i.
Proof. intros i H. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma In_Q : forall q t x, In x (Q q t) <-> exists i, ((φ i) < (φ t))%Z /\ q.[i] = x.
Proof.
  intros q t x. unfold Q. rewrite in_map_iff. pose proof (to_Z_bounded t). split.
  - intros [j [Hj Hs]]. apply in_seq in Hs.
    exists (of_Z (Z.of_nat j)). rewrite of_Z_nat by lia. split; [lia | exact Hj].
  - intros [i [Hi Hx]]. pose proof (to_Z_bounded i).
    exists (Z.to_nat (φ i)). rewrite Z2Nat.id by lia. rewrite of_to_Z. split; [exact Hx|].
    apply in_seq. lia.
Qed.

Lemma nth_error_Q : forall q t i, ((φ i) < (φ t))%Z ->
  nth_error (Q q t) (Z.to_nat (φ i)) = Some q.[i].
Proof.
  intros q t i H. pose proof (to_Z_bounded i). pose proof (to_Z_bounded t). unfold Q.
  rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec (Z.to_nat (φ i)) (Z.to_nat (φ t))); [|lia].
  simpl. rewrite Z2Nat.id by lia. rewrite of_to_Z. reflexivity.
Qed.

Lemma Q_succ : forall q t b, ((φ t) < (φ b))%Z -> Q q (t + 1) = Q q t ++ [q.[t]].
Proof.
  intros q t b H. pose proof (succ_spec t b H) as E. pose proof (to_Z_bounded t).
  unfold Q. rewrite E. replace (Z.to_nat ((φ t) + 1)) with (S (Z.to_nat (φ t))) by lia.
  rewrite seq_S, map_app. simpl. rewrite Z2Nat.id by lia. rewrite of_to_Z. reflexivity.
Qed.

Lemma Q_set : forall q t i v, ((φ t) <= (φ i))%Z -> Q q.[i <- v] t = Q q t.
Proof.
  intros q t i v H. unfold Q. apply map_ext_in. intros j Hj. apply in_seq in Hj.
  pose proof (to_Z_bounded t). apply aget_set_other.
  intros F. assert (G := f_equal to_Z F). rewrite of_Z_nat in G by lia. lia.
Qed.

Lemma Q_nodup_inj : forall q t i i', NoDup (Q q t) -> ((φ i) < (φ t))%Z -> ((φ i') < (φ t))%Z ->
  q.[i] = q.[i'] -> i = i'.
Proof.
  intros q t i i' Hd Hi Hi' E. pose proof (to_Z_bounded i). pose proof (to_Z_bounded i').
  pose proof (proj1 (NoDup_nth_error (Q q t)) Hd (Z.to_nat (φ i)) (Z.to_nat (φ i'))) as K.
  apply to_Z_inj. enough (Z.to_nat (φ i) = Z.to_nat (φ i')) by lia.
  apply K; [rewrite Q_length; lia|].
  rewrite !nth_error_Q by assumption. rewrite E. reflexivity.
Qed.

(* NoDup lists of nodes below N: at most N of them, and N of them are all. *)
Definition nodes (N : int) : list int := map (fun i => of_Z (Z.of_nat i)) (seq 0 (Z.to_nat (φ N))).

Lemma In_nodes : forall N x, In x (nodes N) <-> ((φ x) < (φ N))%Z.
Proof.
  intros N x. unfold nodes. rewrite in_map_iff. pose proof (to_Z_bounded N).
  pose proof (to_Z_bounded x). split.
  - intros [j [Hj Hs]]. apply in_seq in Hs. subst. rewrite of_Z_nat by lia. lia.
  - intros Hx. exists (Z.to_nat (φ x)). rewrite Z2Nat.id by lia. rewrite of_to_Z.
    split; [reflexivity|]. apply in_seq. lia.
Qed.

Lemma nodes_length : forall N, List.length (nodes N) = Z.to_nat (φ N).
Proof. intros. unfold nodes. rewrite length_map, length_seq. reflexivity. Qed.


Lemma NoDup_map_in : forall {A B} (f : A -> B) l,
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l. induction l as [|a l IH]; intros Hi Hd; simpl; [constructor|].
  inversion Hd as [|a' l' Ha Hl]; subst. constructor.
  - intros F. apply in_map_iff in F. destruct F as [b [Hb Hbl]].
    assert (b = a) by (apply Hi; [right; exact Hbl | left; reflexivity | exact Hb]).
    subst. exact (Ha Hbl).
  - apply IH; [|exact Hl]. intros x y Hx Hy. apply Hi; right; assumption.
Qed.

Lemma NoDup_nodes : forall N, NoDup (nodes N).
Proof.
  intros N. unfold nodes. pose proof (to_Z_bounded N).
  apply NoDup_map_in; [|apply seq_NoDup].
  intros a b Ha Hb E. apply in_seq in Ha, Hb.
  apply (f_equal to_Z) in E. rewrite !of_Z_nat in E by lia. lia.
Qed.

Lemma pigeon_le : forall N l, NoDup l -> (forall x, In x l -> ((φ x) < (φ N))%Z) ->
  (List.length l <= Z.to_nat (φ N))%nat.
Proof.
  intros N l Hd Hb. rewrite <- nodes_length. apply NoDup_incl_length; [exact Hd|].
  intros x Hx. apply In_nodes. apply Hb. exact Hx.
Qed.

Lemma pigeon_all : forall N l, NoDup l -> (forall x, In x l -> ((φ x) < (φ N))%Z) ->
  List.length l = Z.to_nat (φ N) -> forall x, ((φ x) < (φ N))%Z -> In x l.
Proof.
  intros N l Hd Hb Hl x Hx.
  apply (NoDup_length_incl (l' := nodes N) Hd); [rewrite nodes_length; lia | | apply In_nodes; exact Hx].
  intros y Hy. apply In_nodes. apply Hb. exact Hy.
Qed.

Lemma pigeon_miss : forall N l, (forall x, ((φ x) < (φ N))%Z -> In x l) ->
  (Z.to_nat (φ N) <= List.length l)%nat.
Proof.
  intros N l H. rewrite <- nodes_length. apply NoDup_incl_length; [apply NoDup_nodes|].
  intros x Hx. apply H. apply In_nodes. exact Hx.
Qed.

(* No infinite ascent on a finite set. *)
Lemma bounded_above : forall (T : int -> Z) (k : nat),
  exists M, forall x, ((φ x) < Z.of_nat k)%Z -> (T x <= M)%Z.
Proof.
  intros T k. induction k as [|k [M IH]].
  - exists 0%Z. intros x Hx. pose proof (to_Z_bounded x). lia.
  - exists (Z.max M (T (of_Z (Z.of_nat k)))). intros x Hx.
    destruct (Z.eq_dec (φ x) (Z.of_nat k)) as [E | E].
    + replace x with (of_Z (Z.of_nat k)) by (rewrite <- E; apply of_to_Z). lia.
    + specialize (IH x ltac:(lia)). lia.
Qed.

Lemma no_ascent : forall (P : int -> Prop) (T : int -> Z) (N : int),
  (forall x, P x -> ((φ x) < (φ N))%Z) ->
  (forall x, P x -> exists y, P y /\ (T x < T y)%Z) ->
  forall x, ~ P x.
Proof.
  intros P T N Hb Hs.
  destruct (bounded_above T (Z.to_nat (φ N))) as [M HM].
  assert (Hm : forall x, P x -> (T x <= M)%Z).
  { intros x Hx. apply HM. pose proof (Hb x Hx). pose proof (to_Z_bounded N). lia. }
  intros x. remember (Z.to_nat (M - T x)) as k eqn:Ek. revert x Ek.
  induction k as [k IH] using (well_founded_ind lt_wf).
  intros x Ek Hx. destruct (Hs x Hx) as [y [Hy Ht]].
  pose proof (Hm x Hx). pose proof (Hm y Hy).
  apply (IH (Z.to_nat (M - T y))) with (x := y); [lia | reflexivity | exact Hy].
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the contracted win graph and its CSR                     *)
(* ------------------------------------------------------------------ *)

Lemma incr_get : forall (c : array int) a u N,
  PArray.length c = N -> ((φ a) < (φ N))%Z -> ((φ (c.[a])) < 4611686018427387903)%Z ->
  (φ ((c.[a <- c.[a] + 1]).[u])) = ((φ (c.[u])) + if Uint63.eqb a u then 1 else 0)%Z.
Proof.
  intros c a u N Hl Ha Hc. rewrite aget_set_cases.
  destruct (a =? u) eqn:E; simpl.
  - apply eqb_spec in E. subst u.
    replace (a <? PArray.length c) with true by (symmetry; apply ltb_true; rewrite Hl; exact Ha).
    pose proof (to_Z_bounded c.[a]). sia.
  - lia.
Qed.

Lemma cnt_single : forall {A} (f : A -> bool) x, cnt f [x] = if f x then 1%nat else 0%nat.
Proof. intros. rewrite cnt_cons, cnt_nil. destruct (f x); reflexivity. Qed.

Lemma cnt_all : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = true) ->
  cnt f l = List.length l.
Proof.
  intros A f l. induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite cnt_cons, (H a (or_introl eq_refl)), IH; [reflexivity|].
  intros x Hx. apply H. right. exact Hx.
Qed.

Section Graph.

Variables (n m : int) (ks ls rep : array int) (wins : array bool).
Hypothesis Hn : ((φ n) <= 50000)%Z.
Hypothesis Hm : ((φ m) <= 250000)%Z.
Hypothesis Hks : forall j, ((φ j) < (φ m))%Z -> ((φ (ks.[j])) < (φ n))%Z.
Hypothesis Hls : forall j, ((φ j) < (φ m))%Z -> ((φ (ls.[j])) < (φ n))%Z.
Hypothesis Hrep : forall x, ((φ x) < (φ n))%Z -> ((φ (rep.[x])) < (φ n))%Z.

Definition edge_of (j : nat) : list (int * int) :=
  let j' := of_Z (Z.of_nat j) in
  if wins.[j'] then [(rep.[ks.[j']], rep.[ls.[j']])] else [].

Definition E (k : nat) : list (int * int) := flat_map edge_of (seq 0 k).

Definition EM : list (int * int) := E (Z.to_nat (φ m)).

Lemma E_S : forall k, E (S k) = E k ++ edge_of k.
Proof.
  intros k. unfold E. rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma edge_of_len : forall j, (List.length (edge_of j) <= 1)%nat.
Proof. intros j. unfold edge_of. destruct (wins.[_]); simpl; lia. Qed.

Lemma E_len : forall k, (List.length (E k) <= k)%nat.
Proof.
  intros k. induction k as [|k IH]; [simpl; lia|].
  rewrite E_S, length_app. pose proof (edge_of_len k). lia.
Qed.

Lemma E_prefix : forall k d, exists r, E (k + d) = E k ++ r.
Proof.
  intros k d. induction d as [|d [r IH]].
  - exists []. rewrite Nat.add_0_r, app_nil_r. reflexivity.
  - exists (r ++ edge_of (k + d)). rewrite Nat.add_succ_r, E_S, IH, app_assoc. reflexivity.
Qed.

Lemma In_E : forall k e, In e (E k) <-> exists j, (j < k)%nat /\ In e (edge_of j).
Proof.
  intros k e. unfold E. rewrite in_flat_map. split.
  - intros [j [Hj He]]. apply in_seq in Hj. exists j. split; [lia | exact He].
  - intros [j [Hj He]]. exists j. split; [apply in_seq; lia | exact He].
Qed.

Lemma edge_of_int : forall j, ((φ j) < (φ m))%Z ->
  edge_of (Z.to_nat (φ j)) = if wins.[j] then [(rep.[ks.[j]], rep.[ls.[j]])] else [].
Proof.
  intros j Hj. unfold edge_of. pose proof (to_Z_bounded j).
  rewrite Z2Nat.id by lia. rewrite of_to_Z. reflexivity.
Qed.

Lemma E_int_S : forall j, ((φ j) < (φ m))%Z ->
  E (Z.to_nat (φ (j + 1))) = E (Z.to_nat (φ j)) ++
    (if wins.[j] then [(rep.[ks.[j]], rep.[ls.[j]])] else []).
Proof.
  intros j Hj. rewrite (succ_spec j m Hj). pose proof (to_Z_bounded j).
  replace (Z.to_nat ((φ j) + 1)) with (S (Z.to_nat (φ j))) by lia.
  rewrite E_S, edge_of_int by exact Hj. reflexivity.
Qed.

Lemma In_edge_of : forall j u v, (j < Z.to_nat (φ m))%nat -> In (u, v) (edge_of j) ->
  exists j', ((φ j') < (φ m))%Z /\ wins.[j'] = true /\ u = rep.[ks.[j']] /\ v = rep.[ls.[j']].
Proof.
  intros j u v Hj H. unfold edge_of in H.
  exists (of_Z (Z.of_nat j)). rewrite of_Z_nat by (rewrite wB_val; lia).
  split; [lia|].
  destruct (wins.[of_Z (Z.of_nat j)]); [|destruct H].
  destruct H as [H | []]. injection H as H1 H2. subst.
  split; [reflexivity | split; reflexivity].
Qed.

Lemma In_E_bound : forall k u v, (k <= Z.to_nat (φ m))%nat -> In (u, v) (E k) ->
  ((φ u) < (φ n))%Z /\ ((φ v) < (φ n))%Z.
Proof.
  intros k u v Hk H. apply In_E in H. destruct H as [j [Hj H]].
  destruct (In_edge_of j u v ltac:(lia) H) as [j' [Hj' [_ [Hu Hv]]]]. subst.
  split; apply Hrep; [apply Hks | apply Hls]; exact Hj'.
Qed.

Lemma In_EM : forall u v, In (u, v) EM <->
  exists j, ((φ j) < (φ m))%Z /\ wins.[j] = true /\ u = rep.[ks.[j]] /\ v = rep.[ls.[j]].
Proof.
  intros u v. split.
  - intros H. apply In_E in H. destruct H as [j [Hj H]].
    exact (In_edge_of j u v Hj H).
  - intros [j [Hj [W [Hu Hv]]]]. apply In_E. pose proof (to_Z_bounded j).
    exists (Z.to_nat (φ j)). split; [lia|].
    rewrite edge_of_int by exact Hj. rewrite W. left. subst. reflexivity.
Qed.

Lemma EM_len : (Z.of_nat (List.length EM) <= (φ m))%Z.
Proof. unfold EM. pose proof (E_len (Z.to_nat (φ m))). pose proof (to_Z_bounded m). lia. Qed.

(* --- degrees --- *)

Definition outc (k : nat) (u : int) : nat := cnt (fun e => fst e =? u) (E k).
Definition inc (k : nat) (u : int) : nat := cnt (fun e => snd e =? u) (E k).

Lemma deg_loop_spec : forall z j od id H, meas j = z ->
  ((φ j) <= (φ m))%Z -> PArray.length od = n -> PArray.length id = n ->
  (forall u, ((φ u) < (φ n))%Z ->
     (φ (od.[u])) = Z.of_nat (outc (Z.to_nat (φ j)) u) /\
     (φ (id.[u])) = Z.of_nat (inc (Z.to_nat (φ j)) u)) ->
  let r := deg_loop rep ks wins ls m j od id H in
  PArray.length (fst r) = n /\ PArray.length (snd r) = n /\
  forall u, ((φ u) < (φ n))%Z ->
     (φ ((fst r).[u])) = Z.of_nat (outc (Z.to_nat (φ m)) u) /\
     (φ ((snd r).[u])) = Z.of_nat (inc (Z.to_nat (φ m)) u).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j od id H Hz Hj Lo Li Inv r. unfold r. clear r. rewrite deg_loop_eq.
  destruct (bdec (j <? m)) as [Hjm | Hjm].
  - pose proof (proj1 (ltb_true _ _) Hjm) as Hjm'.
    pose proof (succ_spec j m Hjm') as Hs.
    pose proof (E_int_S j Hjm') as EK.
    assert (Bk : forall f, (Z.of_nat (cnt f (E (Z.to_nat (φ j)))) <= 250000)%Z).
    { intros f. pose proof (cnt_le_len f (E (Z.to_nat (φ j)))).
      pose proof (E_len (Z.to_nat (φ j))). pose proof (to_Z_bounded j). lia. }
    destruct (wins.[j]) eqn:W; cbv zeta.
    + pose proof (Hrep _ (Hks j Hjm')) as Ba. pose proof (Hrep _ (Hls j Hjm')) as Bb.
      eapply IH; [rewrite <- Hz; apply (dec_step j m Hjm) | reflexivity | lia
                 | rewrite alength_set; exact Lo | rewrite alength_set; exact Li | ].
      intros u Hu. unfold outc, inc. rewrite EK, !cnt_app, !cnt_single. simpl fst; simpl snd.
      destruct (Inv u Hu) as [I1 I2].
      destruct (Inv _ Ba) as [J1 _]. destruct (Inv _ Bb) as [_ J2].
      unfold outc, inc in I1, I2, J1, J2.
      rewrite (incr_get od _ u n Lo Ba) by (rewrite J1; specialize (Bk (fun e => fst e =? rep.[ks.[j]])); lia).
      rewrite (incr_get id _ u n Li Bb) by (rewrite J2; specialize (Bk (fun e => snd e =? rep.[ls.[j]])); lia).
      rewrite I1, I2. split; [destruct (rep.[ks.[j]] =? u) | destruct (rep.[ls.[j]] =? u)]; lia.
    + eapply IH; [rewrite <- Hz; apply (dec_step j m Hjm) | reflexivity | lia | exact Lo | exact Li | ].
      intros u Hu. unfold outc, inc. rewrite EK, app_nil_r. exact (Inv u Hu).
  - apply ltb_false in Hjm. replace (Z.to_nat (φ m)) with (Z.to_nat (φ j)) by lia.
    split; [exact Lo|]. split; [exact Li|]. exact Inv.
Qed.

(* --- offsets --- *)

Definition start (u : int) : nat := cnt (fun e => fst e <? u) EM.

Definition seg (u : int) : list int := map snd (filter (fun e => fst e =? u) EM).

Lemma seg_length : forall u, List.length (seg u) = outc (Z.to_nat (φ m)) u.
Proof. intros. unfold seg, outc, cnt. rewrite length_map. reflexivity. Qed.

Lemma start_S : forall u, ((φ u) < (φ n))%Z ->
  start (u + 1) = (start u + outc (Z.to_nat (φ m)) u)%nat.
Proof.
  intros u Hu. unfold start, outc. fold EM. apply cnt_split.
  - intros [x y]. simpl. pose proof (succ_spec u n Hu) as S.
    destruct (x <? u + 1) eqn:E1, (x <? u) eqn:E2, (x =? u) eqn:E3; simpl; try reflexivity;
      rewrite ?ltb_true, ?ltb_false in *; rewrite ?eqb_spec, ?eqb_false in *;
      try (subst; lia); try lia.
  - intros [x y]. simpl. destruct (x <? u) eqn:E2, (x =? u) eqn:E3; try reflexivity.
    apply ltb_true in E2. apply eqb_spec in E3. subst. lia.
Qed.

Lemma start_mono : forall u u', ((φ u) <= (φ u'))%Z -> (start u <= start u')%nat.
Proof.
  intros u u' H. apply cnt_mono. intros [x y] _. simpl. rewrite !ltb_true. lia.
Qed.

Lemma start_n : start n = List.length EM.
Proof.
  apply cnt_all. intros [x y] Hx. apply ltb_true.
  exact (proj1 (In_E_bound _ x y (le_n _) Hx)).
Qed.

Lemma start_le : forall u, (Z.of_nat (start u) <= (φ m))%Z.
Proof.
  intros u. pose proof (cnt_le_len (fun e => fst e <? u) EM). pose proof EM_len.
  unfold start. lia.
Qed.

Lemma pre_loop_spec : forall od, PArray.length od = n ->
  (forall u, ((φ u) < (φ n))%Z -> (φ (od.[u])) = Z.of_nat (outc (Z.to_nat (φ m)) u)) ->
  forall z u s st pos H, meas u = z ->
  ((φ u) <= (φ n))%Z -> PArray.length st = n + 1 -> PArray.length pos = n ->
  (φ s) = Z.of_nat (start u) ->
  (forall u', ((φ u') <= (φ u))%Z -> (φ (st.[u'])) = Z.of_nat (start u')) ->
  (forall u', ((φ u') < (φ u))%Z -> (φ (pos.[u'])) = Z.of_nat (start u')) ->
  let r := pre_loop od n u s st pos H in
  PArray.length (fst r) = n + 1 /\ PArray.length (snd r) = n /\
  (forall u', ((φ u') <= (φ n))%Z -> (φ ((fst r).[u'])) = Z.of_nat (start u')) /\
  (forall u', ((φ u') < (φ n))%Z -> (φ ((snd r).[u'])) = Z.of_nat (start u')).
Proof.
  intros od Lod Hod z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u s st pos H Hz Hu Lst Lpos Hs Ist Ipos r. unfold r. clear r. rewrite pre_loop_eq.
  pose proof (to_Z_bounded n) as Bn.
  assert (Ln1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  destruct (bdec (u <? n)) as [Hun | Hun].
  - pose proof (proj1 (ltb_true _ _) Hun) as Hun'.
    pose proof (succ_spec u n Hun') as Hs1.
    pose proof (start_S u Hun') as SS.
    pose proof (start_le (u + 1)) as SL.
    assert (Hs' : (φ (s + od.[u])) = Z.of_nat (start (u + 1))).
    { rewrite SS, Nat2Z.inj_add, <- Hs, <- (Hod u Hun'). rewrite SS in SL.
      rewrite Nat2Z.inj_add, <- Hs, <- (Hod u Hun') in SL. pose proof (to_Z_bounded m). sia. }
    cbv zeta. eapply IH; [rewrite <- Hz; apply (dec_step u n Hun) | reflexivity | lia
                         | rewrite alength_set; exact Lst | rewrite alength_set; exact Lpos
                         | exact Hs' | | ].
    + intros u' Hu'. rewrite aget_set_cases.
      destruct (andb (u + 1 =? u') (u + 1 <? PArray.length st)) eqn:C.
      * apply andb_prop in C. destruct C as [C _]. apply eqb_spec in C. subst u'. exact Hs'.
      * apply Ist. destruct (Z.eq_dec (φ u') ((φ u) + 1)) as [F | F]; [|lia].
        exfalso. assert (u' = u + 1) by (apply to_Z_inj; lia). subst u'.
        rewrite eqb_refl in C. simpl in C. apply ltb_false in C. rewrite Lst in C. lia.
    + intros u' Hu'. rewrite aget_set_cases.
      destruct (andb (u =? u') (u <? PArray.length pos)) eqn:C.
      * apply andb_prop in C. destruct C as [C _]. apply eqb_spec in C. subst u'. exact Hs.
      * apply Ipos. destruct (Z.eq_dec (φ u') (φ u)) as [F | F]; [|lia].
        exfalso. assert (u' = u) by (apply to_Z_inj; lia). subst u'.
        rewrite eqb_refl in C. simpl in C. apply ltb_false in C. rewrite Lpos in C. lia.
  - apply ltb_false in Hun.
    split; [exact Lst|]. split; [exact Lpos|]. split.
    + intros u' Hu'. apply Ist. lia.
    + intros u' Hu'. apply Ipos. lia.
Qed.

(* --- the CSR targets --- *)

Definition sg (k : nat) (u : int) : list int := map snd (filter (fun e => fst e =? u) (E k)).

Lemma sg_length : forall k u, List.length (sg k u) = outc k u.
Proof. intros. unfold sg, outc, cnt. rewrite length_map. reflexivity. Qed.

Lemma outc_le : forall k u, (k <= Z.to_nat (φ m))%nat -> (outc k u <= outc (Z.to_nat (φ m)) u)%nat.
Proof.
  intros k u Hk. destruct (E_prefix k (Z.to_nat (φ m) - k)) as [r Er].
  unfold outc. replace (Z.to_nat (φ m)) with (k + (Z.to_nat (φ m) - k))%nat by lia.
  rewrite Er, cnt_app. lia.
Qed.

Lemma fill_loop_spec : forall st,
  (forall u', ((φ u') <= (φ n))%Z -> (φ (st.[u'])) = Z.of_nat (start u')) ->
  forall z j pos adj H, meas j = z ->
  ((φ j) <= (φ m))%Z -> PArray.length pos = n -> PArray.length adj = m ->
  (forall u, ((φ u) < (φ n))%Z ->
     (φ (pos.[u])) = (Z.of_nat (start u) + Z.of_nat (outc (Z.to_nat (φ j)) u))%Z) ->
  (forall u e, ((φ u) < (φ n))%Z ->
     (Z.of_nat (start u) <= (φ e) < Z.of_nat (start u) + Z.of_nat (outc (Z.to_nat (φ j)) u))%Z ->
     adj.[e] = nth (Z.to_nat ((φ e) - Z.of_nat (start u))) (sg (Z.to_nat (φ j)) u) 0) ->
  let r := fill_loop rep ks wins ls m j pos adj H in
  PArray.length r = m /\
  (forall u e, ((φ u) < (φ n))%Z ->
     (Z.of_nat (start u) <= (φ e) < Z.of_nat (start (u + 1)))%Z ->
     r.[e] = nth (Z.to_nat ((φ e) - Z.of_nat (start u))) (seg u) 0).
Proof.
  intros st Hst z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j pos adj H Hz Hj Lpos Ladj Ipos Iadj r. unfold r. clear r. rewrite fill_loop_eq.
  destruct (bdec (j <? m)) as [Hjm | Hjm].
  - pose proof (proj1 (ltb_true _ _) Hjm) as Hjm'.
    pose proof (succ_spec j m Hjm') as Hs.
    pose proof (E_int_S j Hjm') as EK.
    pose proof (to_Z_bounded j) as Bj.
    destruct (wins.[j]) eqn:W; cbv zeta.
    + set (a := rep.[ks.[j]]). set (b := rep.[ls.[j]]).
      pose proof (Hrep _ (Hks j Hjm')) as Ba. fold a in Ba.
      assert (OS : forall u, outc (Z.to_nat (φ (j + 1))) u =
                   (outc (Z.to_nat (φ j)) u + if Uint63.eqb a u then 1 else 0)%nat).
      { intros u. unfold outc. rewrite EK, cnt_app, cnt_single. reflexivity. }
      assert (SG : forall u, sg (Z.to_nat (φ (j + 1))) u =
                   sg (Z.to_nat (φ j)) u ++ (if a =? u then [b] else [])).
      { intros u. unfold sg. rewrite EK, filter_app, map_app. simpl.
        unfold a, b. destruct (rep.[ks.[j]] =? u); reflexivity. }
      assert (Ca : (outc (Z.to_nat (φ j)) a < outc (Z.to_nat (φ m)) a)%nat).
      { pose proof (outc_le (Z.to_nat (φ (j + 1))) a ltac:(lia)) as K.
        rewrite OS, eqb_refl in K. lia. }
      pose proof (start_S a Ba) as SSa.
      pose proof (start_le (a + 1)) as SLa.
      pose proof (Ipos a Ba) as Pa.
      assert (Hpa : ((φ (pos.[a])) < (φ m))%Z) by lia.
      eapply IH; [rewrite <- Hz; apply (dec_step j m Hjm) | reflexivity | lia
                 | rewrite alength_set; exact Lpos | rewrite alength_set; exact Ladj | | ].
      * intros u Hu. rewrite (incr_get pos a u n Lpos Ba) by lia.
        rewrite Ipos by exact Hu. rewrite OS. destruct (a =? u); lia.
      * intros u e Hu He. rewrite aget_set_cases. rewrite OS in He. rewrite SG.
        destruct (andb (pos.[a] =? e) (pos.[a] <? PArray.length adj)) eqn:C.
        -- apply andb_prop in C. destruct C as [C _]. apply eqb_spec in C. subst e.
           destruct (a =? u) eqn:Eau.
           ++ apply eqb_spec in Eau. subst u.
              rewrite app_nth2; rewrite sg_length; [|lia].
              replace (Z.to_nat ((φ (pos.[a])) - Z.of_nat (start a)) - outc (Z.to_nat (φ j)) a)%nat
                with 0%nat by lia. reflexivity.
           ++ exfalso. apply eqb_false in Eau.
              assert (Fu : (φ u) <> (φ a)) by (intro F; apply Eau; apply to_Z_inj; symmetry; exact F).
              pose proof (outc_le (Z.to_nat (φ j)) u ltac:(lia)).
              destruct (Z.lt_ge_cases (φ u) (φ a)) as [L | L].
              ** pose proof (start_S u Hu). pose proof (succ_spec u n Hu).
                 pose proof (start_mono (u + 1) a ltac:(lia)). lia.
              ** pose proof (start_mono (a + 1) u ltac:(pose proof (succ_spec a n Ba); lia)).
                 lia.
        -- assert (Ne : e <> pos.[a] \/ ((φ (pos.[a])) >= (φ m))%Z).
           { destruct (pos.[a] =? e) eqn:C1; simpl in C.
             - right. apply ltb_false in C. rewrite Ladj in C. lia.
             - left. intro F. subst. rewrite eqb_refl in C1. discriminate. }
           destruct Ne as [Ne | Ne]; [|lia].
           assert (Fe : (φ e) <> (φ (pos.[a]))) by (intro F; apply Ne; apply to_Z_inj; exact F).
           assert (He' : (Z.of_nat (start u) <= (φ e) <
                          Z.of_nat (start u) + Z.of_nat (outc (Z.to_nat (φ j)) u))%Z).
           { destruct (a =? u) eqn:Eau; [|lia].
             apply eqb_spec in Eau. subst u. lia. }
           rewrite (Iadj u e Hu He'). rewrite app_nth1; [reflexivity|].
           rewrite sg_length. lia.
    + eapply IH; [rewrite <- Hz; apply (dec_step j m Hjm) | reflexivity | lia
                 | exact Lpos | exact Ladj | | ].
      * intros u Hu. unfold outc. rewrite EK, app_nil_r. apply Ipos. exact Hu.
      * intros u e Hu He. unfold outc, sg in *. rewrite EK, app_nil_r in *.
        apply Iadj; assumption.
  - apply ltb_false in Hjm. assert (Ej : Z.to_nat (φ j) = Z.to_nat (φ m)) by lia.
    split; [exact Ladj|].
    intros u e Hu He. rewrite (start_S u Hu) in He.
    unfold seg, EM. rewrite <- Ej. apply Iadj; [exact Hu|]. rewrite Ej. lia.
Qed.

(* --- Kahn --- *)

Lemma cnt_In_pos : forall {A} (f : A -> bool) l x, In x l -> f x = true -> (0 < cnt f l)%nat.
Proof.
  intros A f l x. induction l as [|a l IH]; intros H Hf; [destruct H|].
  rewrite cnt_cons. destruct H as [H | H]; [subst; rewrite Hf; lia|].
  specialize (IH H Hf). destruct (f a); lia.
Qed.

Lemma In_EM_bound : forall w v, In (w, v) EM -> ((φ w) < (φ n))%Z /\ ((φ v) < (φ n))%Z.
Proof. intros w v H. exact (In_E_bound _ w v (le_n _) H). Qed.

(* the edges into v whose source is not yet popped *)
Definition cntU (P : list int) (v : int) : nat :=
  cnt (fun e => andb (snd e =? v) (negb (memb (fst e) P))) EM.

Lemma cntU_nil : forall v, cntU [] v = inc (Z.to_nat (φ m)) v.
Proof.
  intros v. unfold cntU, inc. fold EM. apply cnt_ext. intros e _.
  simpl. rewrite Bool.andb_true_r. reflexivity.
Qed.

Lemma seg_cnt : forall u v,
  cnt (fun w => Uint63.eqb w v) (seg u) = cnt (fun e => andb (fst e =? u) (snd e =? v)) EM.
Proof. intros. unfold seg. rewrite cnt_map, cnt_filter. reflexivity. Qed.

Lemma seg_le_cntU : forall u P v, ~ In u P ->
  (cnt (fun w => Uint63.eqb w v) (seg u) <= cntU P v)%nat.
Proof.
  intros u P v Hu. rewrite seg_cnt. unfold cntU. apply cnt_mono.
  intros [x y] _ H. simpl in *. apply andb_prop in H. destruct H as [H1 H2].
  apply eqb_spec in H1. subst x. rewrite H2. simpl.
  destruct (memb u P) eqn:M; [apply memb_spec in M; contradiction | reflexivity].
Qed.

Lemma cntU_snoc : forall u P v, ~ In u P ->
  cntU P v = (cntU (P ++ [u]) v + cnt (fun w => Uint63.eqb w v) (seg u))%nat.
Proof.
  intros u P v Hu. rewrite seg_cnt. unfold cntU. apply cnt_split.
  - intros [x y]. simpl. rewrite memb_snoc.
    destruct (u =? x) eqn:E1.
    + apply eqb_spec in E1. subst x. rewrite eqb_refl.
      destruct (memb u P) eqn:M; [apply memb_spec in M; contradiction|].
      simpl. rewrite Bool.andb_false_r. destruct (y =? v); reflexivity.
    + replace (x =? u) with false.
      * rewrite Bool.orb_false_r. simpl. rewrite Bool.orb_false_r. reflexivity.
      * symmetry. apply eqb_false. intro F. subst. rewrite eqb_refl in E1. discriminate.
  - intros [x y]. simpl. rewrite memb_snoc.
    destruct (x =? u) eqn:E1; [|rewrite !Bool.andb_false_r; reflexivity].
    apply eqb_spec in E1. subst x. rewrite eqb_refl. simpl.
    rewrite Bool.orb_true_r. simpl. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma seg_In : forall u v, In v (seg u) -> ((φ v) < (φ n))%Z.
Proof.
  intros u v H. unfold seg in H. apply in_map_iff in H. destruct H as [[x y] [Hy H]].
  simpl in Hy. subst y. apply filter_In in H. destruct H as [H _].
  exact (proj2 (In_EM_bound x v H)).
Qed.

Lemma push_Q : forall q t v, PArray.length q = n -> ((φ t) < (φ n))%Z ->
  Q q.[t <- v] (t + 1) = Q q t ++ [v].
Proof.
  intros q t v Lq Ht. rewrite (Q_succ _ t n Ht), Q_set by lia.
  rewrite aget_set_same; [reflexivity|]. apply ltb_true. rewrite Lq. exact Ht.
Qed.

Lemma get_push : forall (q : array int) (t v i : int), PArray.length q = n -> ((φ t) < (φ n))%Z ->
  q.[t <- v].[i] = if i =? t then v else q.[i].
Proof.
  intros q t v i Lq Ht. rewrite aget_set_cases.
  destruct (i =? t) eqn:E.
  - apply eqb_spec in E. subst i. rewrite eqb_refl.
    replace (t <? PArray.length q) with true; [reflexivity|].
    symmetry. apply ltb_true. rewrite Lq. exact Ht.
  - replace (t =? i) with false; [reflexivity|].
    symmetry. apply eqb_false. intro F. subst i. rewrite eqb_refl in E. discriminate.
Qed.

Lemma dec_get : forall (d : array int) v v', PArray.length d = n -> ((φ v) < (φ n))%Z ->
  (1 <= (φ (d.[v])))%Z ->
  (φ (d.[v <- d.[v] - 1].[v'])) = ((φ (d.[v'])) - if Uint63.eqb v v' then 1 else 0)%Z.
Proof.
  intros d v v' Ld Hv H1. rewrite aget_set_cases.
  destruct (v =? v') eqn:E; simpl.
  - apply eqb_spec in E. subst v'.
    replace (v <? PArray.length d) with true by (symmetry; apply ltb_true; rewrite Ld; exact Hv).
    sia.
  - lia.
Qed.

Lemma zero_iff : forall x : int, x = 0 <-> (φ x) = 0%Z.
Proof.
  intros x. split; [intros; subst; reflexivity|].
  intros H. apply to_Z_inj. rewrite H. reflexivity.
Qed.

Section Kahn.

Variables (st adj : array int).
Hypothesis Hst : forall u, ((φ u) <= (φ n))%Z -> (φ (st.[u])) = Z.of_nat (start u).
Hypothesis Hadj : forall u e, ((φ u) < (φ n))%Z ->
  (Z.of_nat (start u) <= (φ e) < Z.of_nat (start (u + 1)))%Z ->
  adj.[e] = nth (Z.to_nat ((φ e) - Z.of_nat (start u))) (seg u) 0.

Record KI (d q : array int) (h t : int) : Prop := {
  ki_ld : PArray.length d = n;
  ki_lq : PArray.length q = n;
  ki_ht : ((φ h) <= (φ t))%Z;
  ki_nd : NoDup (Q q t);
  ki_qb : forall i, ((φ i) < (φ t))%Z -> ((φ (q.[i])) < (φ n))%Z;
  ki_d : forall v, ((φ v) < (φ n))%Z -> (φ (d.[v])) = Z.of_nat (cntU (Q q h) v);
  ki_k4 : forall v, ((φ v) < (φ n))%Z -> (In v (Q q t) <-> d.[v] = 0);
  ki_k5 : forall i, ((φ i) < (φ t))%Z -> forall w, In (w, q.[i]) EM ->
          exists i', ((φ i') < (φ i))%Z /\ ((φ i') < (φ h))%Z /\ q.[i'] = w
}.

Section Inner.

Variables (u h : int) (P : list int).
Hypothesis Hu : ((φ u) < (φ n))%Z.
Hypothesis HuP : ~ In u P.

Record II (d q : array int) (t e : int) : Prop := {
  ii_ld : PArray.length d = n;
  ii_lq : PArray.length q = n;
  ii_ht : ((φ h) < (φ t))%Z;
  ii_nd : NoDup (Q q t);
  ii_qb : forall i, ((φ i) < (φ t))%Z -> ((φ (q.[i])) < (φ n))%Z;
  ii_P : Q q h = P;
  ii_u : q.[h] = u;
  ii_d : forall v, ((φ v) < (φ n))%Z ->
         (φ (d.[v])) = (Z.of_nat (cntU P v) -
           Z.of_nat (cnt (fun w => Uint63.eqb w v)
             (firstn (Z.to_nat ((φ e) - Z.of_nat (start u))) (seg u))))%Z;
  ii_k4 : forall v, ((φ v) < (φ n))%Z -> (In v (Q q t) <-> d.[v] = 0);
  ii_k5 : forall i, ((φ i) < (φ t))%Z -> forall w, In (w, q.[i]) EM ->
          exists i', ((φ i') < (φ i))%Z /\ ((φ i') <= (φ h))%Z /\ q.[i'] = w
}.

Lemma Q_bound : forall q t, (forall i, ((φ i) < (φ t))%Z -> ((φ (q.[i])) < (φ n))%Z) ->
  forall x, In x (Q q t) -> ((φ x) < (φ n))%Z.
Proof.
  intros q t Hb x Hx. apply In_Q in Hx. destruct Hx as [i [Hi Hx]]. subst. apply Hb. exact Hi.
Qed.

Lemma inner_spec : forall z e d q t H, meas e = z ->
  (Z.of_nat (start u) <= (φ e) <= Z.of_nat (start (u + 1)))%Z ->
  II d q t e ->
  let r := inner adj st.[u + 1] e d q t H in
  II (fst (fst r)) (snd (fst r)) (snd r) st.[u + 1].
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros e d q t H Hz He Inv r. unfold r. clear r. rewrite inner_eq.
  pose proof (succ_spec u n Hu) as Hu1.
  assert (Hhi : (φ (st.[u + 1])) = Z.of_nat (start (u + 1))) by (apply Hst; lia).
  pose proof (start_S u Hu) as SS. rewrite <- seg_length in SS.
  destruct Inv as [Ld Lq Ht Nd Qb HP Hqu Id K4 K5].
  destruct (bdec (e <? st.[u + 1])) as [Hlt | Hlt].
  - pose proof (proj1 (ltb_true _ _) Hlt) as Hlt'.
    pose proof (succ_spec e _ Hlt') as Hs.
    set (i := Z.to_nat ((φ e) - Z.of_nat (start u))).
    assert (Hi : (i < List.length (seg u))%nat) by (unfold i; lia).
    assert (Hv : adj.[e] = nth i (seg u) 0) by (apply Hadj; [exact Hu | lia]).
    set (v := adj.[e]) in *.
    assert (Bv : ((φ v) < (φ n))%Z) by (apply (seg_In u); rewrite Hv; apply nth_In; exact Hi).
    assert (Fi : Z.to_nat ((φ (e + 1)) - Z.of_nat (start u)) = S i) by (unfold i; lia).
    assert (FS : firstn (S i) (seg u) = firstn i (seg u) ++ [v])
      by (rewrite Hv; apply firstn_S_nth; exact Hi).
    assert (Cnew : forall v', cnt (fun w => Uint63.eqb w v') (firstn (S i) (seg u)) =
               (cnt (fun w => Uint63.eqb w v') (firstn i (seg u)) + if Uint63.eqb v v' then 1 else 0)%nat).
    { intros v'. rewrite FS, cnt_app, cnt_single. reflexivity. }
    pose proof (seg_le_cntU u P v HuP) as Lseg.
    pose proof (cnt_firstn_le (fun w => Uint63.eqb w v) (S i) (seg u)) as Lfi.
    pose proof (Cnew v) as Cv. rewrite eqb_refl in Cv.
    pose proof (Id v Bv) as Dv. fold i in Dv.
    assert (D1 : (1 <= (φ (d.[v])))%Z) by lia.
    assert (Dnz : d.[v] <> 0) by (intro F; rewrite F in D1; simpl in D1; lia).
    assert (NotIn : ~ In v (Q q t)) by (intro F; apply Dnz; apply (K4 v Bv); exact F).
    assert (Id' : forall v', ((φ v') < (φ n))%Z ->
              (φ (d.[v <- d.[v] - 1].[v'])) = (Z.of_nat (cntU P v') -
                Z.of_nat (cnt (fun w => Uint63.eqb w v')
                  (firstn (Z.to_nat ((φ (e + 1)) - Z.of_nat (start u))) (seg u))))%Z).
    { intros v' Hv'. rewrite (dec_get d v v' Ld Bv D1), Fi, Cnew, (Id v' Hv').
      fold i. destruct (v =? v'); lia. }
    assert (Dv' : (φ (d.[v <- d.[v] - 1].[v])) = ((φ (d.[v])) - 1)%Z)
      by (rewrite (dec_get d v v Ld Bv D1), eqb_refl; lia).
    assert (Dother : forall v', v' <> v -> d.[v <- d.[v] - 1].[v'] = d.[v'])
      by (intros v' Hne; apply aget_set_other; intro F; apply Hne; symmetry; exact F).
    cbv zeta. destruct (d.[v] - 1 =? 0) eqn:Z0.
    + (* v reaches in-degree 0: it is pushed *)
      apply eqb_spec in Z0.
      assert (Pt : ((φ t) < (φ n))%Z).
      { pose proof (pigeon_le n (Q q t ++ [v]) (NoDup_snoc _ v Nd NotIn)) as K.
        rewrite length_app, Q_length in K. simpl in K.
        assert (K' : (Z.to_nat (φ t) + 1 <= Z.to_nat (φ n))%nat).
        { apply K. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [Hx | []]].
          - exact (Q_bound q t Qb x Hx).
          - subst. exact Bv. }
        pose proof (to_Z_bounded t). lia. }
      pose proof (succ_spec t n Pt) as Ht1.
      assert (Ecount : cnt (fun e => andb (fst e =? u) (snd e =? v)) EM = cntU P v).
      { rewrite <- seg_cnt.
        assert ((φ (d.[v] - 1)) = 0%Z) by (rewrite Z0; reflexivity).
        assert ((φ (d.[v] - 1)) = ((φ (d.[v])) - 1)%Z) by sia. lia. }
      eapply IH; [rewrite <- Hz; apply (dec_step e _ Hlt) | reflexivity | lia | ].
      constructor.
      * rewrite alength_set. exact Ld.
      * rewrite alength_set. exact Lq.
      * lia.
      * rewrite push_Q by assumption. apply NoDup_snoc; assumption.
      * intros i' Hi'. rewrite get_push by assumption.
        destruct (i' =? t) eqn:Et; [exact Bv|]. apply Qb.
        apply eqb_false in Et. assert ((φ i') <> (φ t)) by (intro F; apply Et; apply to_Z_inj; exact F).
        lia.
      * rewrite Q_set by lia. exact HP.
      * rewrite get_push by assumption.
        replace (h =? t) with false; [exact Hqu|].
        symmetry. apply eqb_false. intro F. subst. lia.
      * exact Id'.
      * intros v' Hv'. rewrite push_Q by assumption.
        split.
        -- intros Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Hin | []]].
           ++ assert (v' <> v) by (intro F; subst; exact (NotIn Hin)).
              rewrite Dother by assumption. apply (K4 v' Hv'). exact Hin.
           ++ subst v'. rewrite aget_set_same; [exact Z0|].
              apply ltb_true. rewrite Ld. exact Bv.
        -- intros H0. apply in_or_app.
           destruct (eqb_spec v' v) as [_ ?].
           destruct (v' =? v) eqn:Evv.
           ++ right. left. apply eqb_spec in Evv. symmetry. exact Evv.
           ++ left. apply eqb_false in Evv. rewrite Dother in H0 by exact Evv.
              apply (K4 v' Hv'). exact H0.
      * intros i' Hi' w Hw. rewrite get_push in Hw by assumption.
        destruct (i' =? t) eqn:Et.
        -- apply eqb_spec in Et. subst i'.
           destruct (memb w P) eqn:M.
           ++ apply memb_spec in M. rewrite <- HP in M. apply In_Q in M.
              destruct M as [i'' [Hi'' Hw'']]. exists i''.
              split; [lia|]. split; [lia|]. rewrite get_push by assumption.
              replace (i'' =? t) with false; [exact Hw''|].
              symmetry. apply eqb_false. intro F. subst. lia.
           ++ assert (Fw : andb (fst (w, v) =? u) (snd (w, v) =? v) = true).
              { apply (cnt_eq_all (fun e => andb (fst e =? u) (snd e =? v))
                         (fun e => andb (snd e =? v) (negb (memb (fst e) P))) EM)
                  with (x := (w, v)); [ | exact Ecount | exact Hw | ].
                - intros [x y] Hxy. simpl in *. apply andb_prop in Hxy.
                  destruct Hxy as [H1 H2]. apply eqb_spec in H1. subst x. rewrite H2. simpl.
                  destruct (memb u P) eqn:M'; [apply memb_spec in M'; contradiction|reflexivity].
                - simpl. rewrite eqb_refl, M. reflexivity. }
              simpl in Fw. apply andb_prop in Fw. destruct Fw as [Fw _]. apply eqb_spec in Fw.
              subst w. exists h. split; [lia|]. split; [lia|].
              rewrite get_push by assumption.
              replace (h =? t) with false; [exact Hqu|].
              symmetry. apply eqb_false. intro F. subst. lia.
        -- apply eqb_false in Et. assert (Et' : (φ i') <> (φ t)) by (intro F; apply Et; apply to_Z_inj; exact F).
           destruct (K5 i' ltac:(lia) w Hw) as [i'' [A1 [A2 A3]]].
           exists i''. split; [exact A1|]. split; [exact A2|].
           rewrite get_push by assumption.
           replace (i'' =? t) with false; [exact A3|].
           symmetry. apply eqb_false. intro F. subst. lia.
    + (* not pushed *)
      apply eqb_false in Z0.
      eapply IH; [rewrite <- Hz; apply (dec_step e _ Hlt) | reflexivity | lia | ].
      constructor; try assumption.
      * rewrite alength_set. exact Ld.
      * intros v' Hv'. destruct (v' =? v) eqn:Evv.
        -- apply eqb_spec in Evv. subst v'. split; [intro F; contradiction|].
           intros F. exfalso. apply Z0. rewrite aget_set_same in F; [exact F|].
           apply ltb_true. rewrite Ld. exact Bv.
        -- apply eqb_false in Evv. rewrite Dother by exact Evv. apply K4. exact Hv'.
  - apply ltb_false in Hlt.
    assert (Ee : e = st.[u + 1]) by (apply to_Z_inj; lia). subst e.
    constructor; assumption.
Qed.

End Inner.

Lemma kahn_spec : forall z h d q t H, meas h = z -> KI d q h t ->
  exists d' q', KI d' q' (kahn adj st h d q t H) (kahn adj st h d q t H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h d q t H Hz Inv. rewrite kahn_eq.
  destruct (bdec (h <? t)) as [Hh | Hh].
  - pose proof (proj1 (ltb_true _ _) Hh) as Hh'.
    pose proof (succ_spec h t Hh') as Hs.
    destruct Inv as [Ld Lq Ht Nd Qb Id K4 K5].
    set (u := q.[h]).
    assert (Bu : ((φ u) < (φ n))%Z) by (apply Qb; exact Hh').
    assert (HuP : ~ In u (Q q h)).
    { intros F. apply In_Q in F. destruct F as [i' [Hi' Fi]].
      assert (i' = h) by (apply (Q_nodup_inj q t); [exact Nd | lia | exact Hh' | exact Fi]).
      subst. lia. }
    pose proof (succ_spec u n Bu) as Hu1.
    assert (Hs0 : (φ (st.[u])) = Z.of_nat (start u)) by (apply Hst; lia).
    pose proof (start_S u Bu) as SS. rewrite <- seg_length in SS.
    assert (I0 : II u h (Q q h) d q t st.[u]).
    { constructor; try assumption; try reflexivity.
      - intros v Hv. rewrite Hs0, Z.sub_diag. simpl. rewrite (Id v Hv). lia.
      - intros i Hi w Hw. destruct (K5 i Hi w Hw) as [i' [A1 [A2 A3]]].
        exists i'. split; [exact A1|]. split; [lia | exact A3]. }
    pose proof (inner_spec u h (Q q h) Bu HuP _ st.[u] d q t
                  (Zwf_well_founded 0 (meas st.[u])) eq_refl
                  ltac:(rewrite Hs0; lia) I0) as I1.
    cbv zeta. fold u.
    set (r := inner adj st.[u + 1] st.[u] d q t (Zwf_well_founded 0 (meas st.[u]))) in *.
    destruct I1 as [Ld1 Lq1 Ht1 Nd1 Qb1 HP1 Hqu1 Id1 K41 K51].
    eapply IH; [rewrite <- Hz; apply (dec_step h t Hh) | reflexivity | ].
    assert (Q1 : Q (snd (fst r)) (h + 1) = Q q h ++ [u])
      by (rewrite (Q_succ _ h (snd r) Ht1), HP1, Hqu1; reflexivity).
    constructor; try assumption.
    + lia.
    + intros v Hv. rewrite (Id1 v Hv), Q1, (cntU_snoc u (Q q h) v HuP).
      assert (Ef : Z.to_nat ((φ (st.[u + 1])) - Z.of_nat (start u)) = List.length (seg u))
        by (rewrite Hst by lia; lia).
      rewrite Ef, firstn_all. lia.
    + intros i Hi w Hw. destruct (K51 i Hi w Hw) as [i' [A1 [A2 A3]]].
      exists i'. split; [exact A1|]. split; [lia | exact A3].
  - apply ltb_false in Hh. destruct Inv as [Ld Lq Ht Nd Qb Id K4 K5].
    assert (h = t) by (apply to_Z_inj; lia). subst h.
    exists d, q. constructor; assumption.
Qed.

Lemma kahn_correct : forall d q t, KI d q 0 t ->
  let t' := kahn adj st 0 d q t (Zwf_well_founded 0 (meas 0)) in
  t' = n <-> exists T : int -> Z, forall w v, In (w, v) EM -> (T v < T w)%Z.
Proof.
  intros d q t Inv t'.
  destruct (kahn_spec _ 0 d q t (Zwf_well_founded 0 (meas 0)) eq_refl Inv) as [d' [q' K]].
  fold t' in K. destruct K as [Ld Lq _ Nd Qb Id K4 K5].
  assert (Qb' := Q_bound q' t' Qb).
  pose proof (pigeon_le n _ Nd Qb') as Tle. rewrite Q_length in Tle.
  split.
  - intros Et.
    assert (All : forall x, ((φ x) < (φ n))%Z -> In x (Q q' t')).
    { apply pigeon_all; [exact Nd | exact Qb' | rewrite Q_length, Et; reflexivity]. }
    exists (fun x => (- Z.of_nat (idx x (Q q' t')))%Z).
    intros w v Hwv. destruct (In_EM_bound w v Hwv) as [Bw Bv].
    pose proof (All v Bv) as Iv. apply In_Q in Iv. destruct Iv as [i [Hi Hqi]].
    rewrite <- Hqi in Hwv. destruct (K5 i Hi w Hwv) as [i' [A1 [A2 A3]]].
    rewrite (idx_nth (Q q' t') (Z.to_nat (φ i)) v Nd) by (rewrite nth_error_Q by exact Hi; rewrite Hqi; reflexivity).
    rewrite (idx_nth (Q q' t') (Z.to_nat (φ i')) w Nd) by (rewrite nth_error_Q by lia; rewrite A3; reflexivity).
    pose proof (to_Z_bounded i'). lia.
  - intros [T HT].
    assert (All : forall x, ((φ x) < (φ n))%Z -> In x (Q q' t')).
    { intros x Hx. destruct (memb x (Q q' t')) eqn:M; [apply memb_spec; exact M|].
      assert (I : ~ In x (Q q' t')) by (intro F; apply memb_spec in F; rewrite F in M; discriminate).
      exfalso.
      apply (no_ascent (fun x => ((φ x) < (φ n))%Z /\ ~ In x (Q q' t')) T n)
        with (x := x); [ | | split; assumption].
      - intros y [Hy _]. exact Hy.
      - intros y [Hy Ny].
        assert (Dy : d'.[y] <> 0) by (intro F; apply Ny; apply (K4 y Hy); exact F).
        assert (Cy : (0 < cntU (Q q' t') y)%nat).
        { pose proof (Id y Hy) as E1. destruct (cntU (Q q' t') y); [|lia].
          exfalso. apply Dy. apply zero_iff. exact E1. }
        apply cnt_pos in Cy. destruct Cy as [[w y'] [Hin Hf]]. simpl in Hf.
        apply andb_prop in Hf. destruct Hf as [H1 H2]. apply eqb_spec in H1. subst y'.
        exists w. destruct (In_EM_bound w y Hin) as [Bw _].
        split; [split; [exact Bw|] | exact (HT w y Hin)].
        intro F. apply memb_spec in F. rewrite F in H2. discriminate. }
    pose proof (pigeon_miss n _ All) as Tge. rewrite Q_length in Tge.
    apply to_Z_inj. pose proof (to_Z_bounded t'). pose proof (to_Z_bounded n). lia.
Qed.

End Kahn.

Lemma cnt_none : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = false) -> cnt f l = 0%nat.
Proof.
  intros A f l. induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite cnt_cons, (H a (or_introl eq_refl)), IH; [reflexivity|].
  intros x Hx. apply H. right. exact Hx.
Qed.

Lemma start_0 : start 0 = 0%nat.
Proof.
  apply cnt_none. intros [x y] _. simpl. apply ltb_false. change (φ 0) with 0%Z.
  pose proof (to_Z_bounded x). lia.
Qed.

Lemma Q_0 : forall q, Q q 0 = [].
Proof. reflexivity. Qed.

Lemma init_loop_spec : forall id, PArray.length id = n ->
  forall z v q t H, meas v = z -> ((φ v) <= (φ n))%Z -> PArray.length q = n ->
  ((φ t) <= (φ v))%Z -> NoDup (Q q t) ->
  (forall w, In w (Q q t) <-> ((φ w) < (φ v))%Z /\ id.[w] = 0) ->
  let r := init_loop id n v q t H in
  PArray.length (fst r) = n /\ NoDup (Q (fst r) (snd r)) /\
  (forall w, In w (Q (fst r) (snd r)) <-> ((φ w) < (φ n))%Z /\ id.[w] = 0).
Proof.
  intros id Lid z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v q t H Hz Hv Lq Ht Nd Iff r. unfold r. clear r. rewrite init_loop_eq.
  destruct (bdec (v <? n)) as [Hvn | Hvn].
  - pose proof (proj1 (ltb_true _ _) Hvn) as Hvn'.
    pose proof (succ_spec v n Hvn') as Hs.
    assert (NotIn : ~ In v (Q q t)) by (intro F; apply Iff in F; lia).
    destruct (id.[v] =? 0) eqn:E0.
    + apply eqb_spec in E0.
      assert (Pt : ((φ t) < (φ n))%Z) by lia.
      pose proof (succ_spec t n Pt) as Ht1.
      eapply IH; [rewrite <- Hz; apply (dec_step v n Hvn) | reflexivity | lia
                 | rewrite alength_set; exact Lq | lia | | ].
      * rewrite push_Q by assumption. apply NoDup_snoc; assumption.
      * intros w. rewrite push_Q by assumption. split.
        -- intros Hw. apply in_app_or in Hw. destruct Hw as [Hw | [Hw | []]].
           ++ apply Iff in Hw. lia.
           ++ subst w. split; [lia | exact E0].
        -- intros [Hw Iw]. apply in_or_app.
           destruct (Z.eq_dec (φ w) (φ v)) as [F | F].
           ++ right. left. symmetry. apply to_Z_inj. exact F.
           ++ left. apply Iff. split; [lia | exact Iw].
    + apply eqb_false in E0.
      eapply IH; [rewrite <- Hz; apply (dec_step v n Hvn) | reflexivity | lia
                 | exact Lq | lia | exact Nd | ].
      intros w. rewrite Iff. split.
      * intros [Hw Iw]. split; [lia | exact Iw].
      * intros [Hw Iw]. split; [|exact Iw].
        destruct (Z.eq_dec (φ w) (φ v)) as [F | F]; [|lia].
        exfalso. apply E0. apply to_Z_inj in F. subst w. exact Iw.
  - apply ltb_false in Hvn.
    split; [exact Lq|]. split; [exact Nd|].
    intros w. rewrite Iff. split; intros [Hw Iw]; (split; [lia | exact Iw]).
Qed.

Lemma graph_ok :
  let dg := deg_loop rep ks wins ls m 0 (PArray.make n 0) (PArray.make n 0)
              (Zwf_well_founded 0 (meas 0)) in
  let sp := pre_loop (fst dg) n 0 0 (PArray.make (n + 1) 0) (PArray.make n 0)
              (Zwf_well_founded 0 (meas 0)) in
  let adj := fill_loop rep ks wins ls m 0 (snd sp) (PArray.make m 0)
              (Zwf_well_founded 0 (meas 0)) in
  let qi := init_loop (snd dg) n 0 (PArray.make n 0) 0 (Zwf_well_founded 0 (meas 0)) in
  let t := kahn adj (fst sp) 0 (snd dg) (fst qi) (snd qi) (Zwf_well_founded 0 (meas 0)) in
  t = n <-> exists T : int -> Z, forall w v, In (w, v) EM -> (T v < T w)%Z.
Proof.
  intros dg sp adj qi t.
  pose proof (to_Z_bounded n) as Bn. pose proof (to_Z_bounded m) as Bm.
  assert (Ln : PArray.length (PArray.make n 0) = n) by (apply alength_make_ok; lia).
  assert (Lm : PArray.length (PArray.make m 0) = m) by (apply alength_make_ok; lia).
  assert (Hn1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  assert (Ln1 : PArray.length (PArray.make (n + 1) 0) = n + 1) by (apply alength_make_ok; lia).
  change (φ 0) with 0%Z in *.
  destruct (deg_loop_spec _ 0 (PArray.make n 0) (PArray.make n 0) (Zwf_well_founded 0 (meas 0))
              eq_refl ltac:(lia) Ln Ln
              ltac:(intros u Hu; rewrite !aget_make; split; reflexivity))
    as [Lod [Lid Ideg]].
  fold dg in Lod, Lid, Ideg.
  destruct (pre_loop_spec (fst dg) Lod (fun u Hu => proj1 (Ideg u Hu)) _ 0 0
              (PArray.make (n + 1) 0) (PArray.make n 0) (Zwf_well_founded 0 (meas 0))
              eq_refl ltac:(lia) Ln1 Ln ltac:(rewrite start_0; reflexivity)
              ltac:(intros u' Hu'; assert (u' = 0) by (apply to_Z_inj; pose proof (to_Z_bounded u'); lia);
                    subst u'; rewrite aget_make, start_0; reflexivity)
              ltac:(intros u' Hu'; pose proof (to_Z_bounded u'); lia))
    as [Lst [Lpos [Ist Ipos]]].
  fold sp in Lst, Lpos, Ist, Ipos.
  destruct (fill_loop_spec (fst sp) Ist _ 0 (snd sp) (PArray.make m 0)
              (Zwf_well_founded 0 (meas 0)) eq_refl ltac:(lia) Lpos Lm
              ltac:(intros u Hu; rewrite (Ipos u Hu); change (Z.to_nat (φ 0)) with 0%nat;
                    unfold outc; simpl; lia)
              ltac:(intros u e Hu He; change (Z.to_nat (φ 0)) with 0%nat in He;
                    unfold outc in He; simpl in He; lia))
    as [Ladj Iadj].
  fold adj in Ladj, Iadj.
  destruct (init_loop_spec (snd dg) Lid _ 0 (PArray.make n 0) 0 (Zwf_well_founded 0 (meas 0))
              eq_refl ltac:(lia) Ln ltac:(lia) ltac:(rewrite Q_0; constructor)
              ltac:(intros w; rewrite Q_0; pose proof (to_Z_bounded w); split; [intros [] | lia]))
    as [Lq [Nd Iff]].
  fold qi in Lq, Nd, Iff.
  apply (kahn_correct (fst sp) adj Ist Iadj).
  constructor.
  - exact Lid.
  - exact Lq.
  - pose proof (to_Z_bounded (snd qi)). lia.
  - exact Nd.
  - intros i Hi. assert (In (fst qi).[i] (Q (fst qi) (snd qi))) by (apply In_Q; exists i; split; [exact Hi | reflexivity]).
    apply Iff in H. exact (proj1 H).
  - intros v Hv. rewrite Q_0, cntU_nil. exact (proj2 (Ideg v Hv)).
  - intros v Hv. rewrite Iff. split; [intros [_ H]; exact H | intros H; split; assumption].
  - intros i Hi w Hw. exfalso.
    assert (In (fst qi).[i] (Q (fst qi) (snd qi))) by (apply In_Q; exists i; split; [exact Hi | reflexivity]).
    apply Iff in H. destruct H as [Hb Hz].
    pose proof (proj2 (Ideg _ Hb)) as D. rewrite Hz in D. change (φ 0) with 0%Z in D.
    pose proof (cnt_In_pos (fun e => snd e =? (fst qi).[i]) EM (w, (fst qi).[i]) Hw
                  ltac:(simpl; apply eqb_refl)) as P.
    unfold inc in D. fold EM in D. lia.
Qed.

End Graph.

(* ------------------------------------------------------------------ *)
(* Prop side: phases 1 and 2, the classes of the draws                 *)
(* ------------------------------------------------------------------ *)

Section UF.

Variables (n m : int) (ks ls : array int) (wins : array bool).
Hypothesis Hks : forall j, ((φ j) < (φ m))%Z -> ((φ (ks.[j])) < (φ n))%Z.
Hypothesis Hls : forall j, ((φ j) < (φ m))%Z -> ((φ (ls.[j])) < (φ n))%Z.

(* the two players of a draw *)
Definition dstep (a b : int) : Prop :=
  exists j, ((φ j) < (φ m))%Z /\ wins.[j] = false /\ a = ks.[j] /\ b = ls.[j].

Definition deq : int -> int -> Prop := clos_refl_sym_trans int dstep.

Lemma deq_S : forall S : int -> Z,
  (forall j, ((φ j) < (φ m))%Z -> wins.[j] = false -> S ks.[j] = S ls.[j]) ->
  forall a b, deq a b -> S a = S b.
Proof.
  intros S HS a b H. induction H as [a b Hs | a | a b _ IH | a b c _ IH1 _ IH2].
  - destruct Hs as [j [Hj [W [Ha Hb]]]]. subst. apply HS; assumption.
  - reflexivity.
  - symmetry. exact IH.
  - rewrite IH1. exact IH2.
Qed.

Record UF (j0 : int) (p : array int) : Prop := {
  uf_len : PArray.length p = n;
  uf_b : bounded n p;
  uf_deq : forall y r, ((φ y) < (φ n))%Z -> root_of p y r -> deq y r;
  uf_draw : forall j, ((φ j) < (φ j0))%Z -> wins.[j] = false ->
            forall r1 r2, root_of p ks.[j] r1 -> root_of p ls.[j] r2 -> r1 = r2
}.

Lemma uf_loop_spec : forall z j p rk Hp H, meas j = z -> ((φ j) <= (φ m))%Z -> UF j p ->
  UF m (uf_loop ks wins ls m j p rk Hp H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j p rk Hp H Hz Hj Inv. rewrite uf_loop_eq.
  destruct (bdec (j <? m)) as [Hjm | Hjm].
  - pose proof (proj1 (ltb_true _ _) Hjm) as Hjm'.
    pose proof (succ_spec j m Hjm') as Hs.
    destruct Inv as [Lp Bp Dp Rp].
    destruct (wins.[j]) eqn:W.
    + eapply IH; [rewrite <- Hz; apply (dec_step j m Hjm) | reflexivity | lia | ].
      constructor; try assumption.
      intros j' Hj' W'. destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
      * apply to_Z_inj in E. subst j'. rewrite W in W'. discriminate.
      * apply Rp; [lia | exact W'].
    + cbv zeta.
      pose proof (Hks j Hjm') as Bk. pose proof (Hls j Hjm') as Bl.
      destruct (unite_spec n p rk ks.[j] ls.[j] Hp Bp Lp Bk Bl)
        as [Bp' [Lp' [a [b [c [Ra [Rb [Hc Hg]]]]]]]].
      pose proof (unite_ok p rk ks.[j] ls.[j] Hp) as Hp'.
      set (p' := fst (unite p rk ks.[j] ls.[j] Hp)) in *.
      set (g := fun r => if orb (r =? a) (r =? b) then c else r).
      assert (NR : forall y r', root_of p' y r' -> exists r0, root_of p y r0 /\ r' = g r0).
      { intros y r' H'. destruct (root_exists p y (Hp y)) as [r0 H0].
        exists r0. split; [exact H0|]. apply (root_unique p' y); [exact H'|]. apply Hg. exact H0. }
      assert (Dab : deq a b).
      { eapply rst_trans; [apply rst_sym; apply (Dp _ _ Bk Ra)|].
        eapply rst_trans; [apply rst_step; exists j; split; [exact Hjm'|]; split; [exact W|]; split; reflexivity|].
        apply (Dp _ _ Bl Rb). }
      assert (Dxy : forall x y, (x = a \/ x = b) -> (y = a \/ y = b) -> deq x y).
      { intros x y [Hx | Hx] [Hy | Hy]; subst; try apply rst_refl; [exact Dab | apply rst_sym; exact Dab]. }
      assert (Gab : forall r, orb (r =? a) (r =? b) = true -> r = a \/ r = b).
      { intros r G. apply Bool.orb_true_iff in G. destruct G as [G | G]; apply eqb_spec in G; auto. }
      eapply IH; [rewrite <- Hz; apply (dec_step j m Hjm) | reflexivity | lia | ].
      constructor; try assumption.
      * intros y r' Hy H'. destruct (NR y r' H') as [r0 [H0 E]]. subst r'.
        pose proof (Dp y r0 Hy H0) as D0. unfold g.
        destruct (orb (r0 =? a) (r0 =? b)) eqn:G; [|exact D0].
        eapply rst_trans; [exact D0|]. apply Dxy; [apply Gab; exact G | exact Hc].
      * intros j' Hj' W' r1 r2 H1 H2.
        destruct (NR _ _ H1) as [s1 [S1 E1]]. destruct (NR _ _ H2) as [s2 [S2 E2]]. subst r1 r2.
        destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
        -- apply to_Z_inj in E. subst j'.
           rewrite (root_unique p _ s1 a S1 Ra), (root_unique p _ s2 b S2 Rb).
           unfold g. rewrite eqb_refl. simpl. rewrite eqb_refl, Bool.orb_true_r. reflexivity.
        -- rewrite (Rp j' ltac:(lia) W' s1 s2 S1 S2). reflexivity.
  - apply ltb_false in Hjm.
    assert (j = m) by (apply to_Z_inj; lia). subst j. exact Inv.
Qed.

Lemma rep_loop_spec : forall p1, bounded n p1 ->
  forall z x p rep Hp H, meas x = z -> PArray.length rep = n ->
  (forall y r, root_of p y r <-> root_of p1 y r) ->
  (forall x', ((φ x') < (φ x))%Z -> root_of p1 x' rep.[x']) ->
  let r := rep_loop n x p rep Hp H in
  PArray.length r = n /\ forall x', ((φ x') < (φ n))%Z -> root_of p1 x' r.[x'].
Proof.
  intros p1 Bp1 z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x p rep Hp H Hz Lr Iff Inv r. unfold r. clear r. rewrite rep_loop_eq.
  destruct (bdec (x <? n)) as [Hxn | Hxn].
  - pose proof (proj1 (ltb_true _ _) Hxn) as Hxn'.
    pose proof (succ_spec x n Hxn') as Hs.
    cbv zeta.
    destruct (find_spec p x (Hp x)) as [R [F [A _]]].
    eapply IH; [rewrite <- Hz; apply (dec_step x n Hxn) | reflexivity | rewrite alength_set; exact Lr | | ].
    + intros y r. rewrite (compress_roots_iff p _ Hp F A). apply Iff.
    + intros x' Hx'. rewrite aget_set_cases.
      destruct (andb (x =? x') (x <? PArray.length rep)) eqn:C.
      * apply andb_prop in C. destruct C as [C _]. apply eqb_spec in C. subst x'.
        apply Iff. exact R.
      * apply Inv. destruct (Z.eq_dec (φ x') (φ x)) as [E | E]; [|lia].
        exfalso. apply to_Z_inj in E. subst x'. rewrite eqb_refl in C. simpl in C.
        apply ltb_false in C. rewrite Lr in C. lia.
  - apply ltb_false in Hxn. split; [exact Lr|].
    intros x' Hx'. apply Inv. lia.
Qed.

End UF.

(* ------------------------------------------------------------------ *)
(* The whole function, on machine values                               *)
(* ------------------------------------------------------------------ *)

Lemma chess_impl_correct : forall (n : int) (ks ls : array int) (wins : array bool),
  ((φ n) <= 50000)%Z -> ((φ (PArray.length ks)) <= 250000)%Z ->
  (forall j, ((φ j) < (φ (PArray.length ks)))%Z -> ((φ (ks.[j])) < (φ n))%Z) ->
  (forall j, ((φ j) < (φ (PArray.length ks)))%Z -> ((φ (ls.[j])) < (φ n))%Z) ->
  chess_impl n ks wins ls = true <->
  exists S : int -> Z, forall j, ((φ j) < (φ (PArray.length ks)))%Z ->
    if wins.[j] then (S ls.[j] < S ks.[j])%Z else S ks.[j] = S ls.[j].
Proof.
  intros n ks ls wins Hn Hm Hks Hls.
  unfold chess_impl. cbv zeta.
  set (m := PArray.length ks) in *.
  pose proof (to_Z_bounded n) as Bn.
  (* the initial forest *)
  destruct (iota_spec n) as [Li [_ Fi]].
  assert (Ln : PArray.length (PArray.make n 0) = n) by (apply alength_make_ok; lia).
  rewrite Ln in Li.
  assert (U0 : UF n m ks ls wins 0 (iota n)).
  { constructor.
    - exact Li.
    - intros y Hy. rewrite Fi by (rewrite Li; exact Hy). exact Hy.
    - intros y r Hy [Ha Hr].
      assert (Fy : (iota n).[y] = y) by (apply Fi; rewrite Li; exact Hy).
      rewrite (anc_root_eq _ y r Fy Ha). apply rst_refl.
    - intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia. }
  pose proof (uf_loop_spec n m ks ls wins Hks Hls _ 0 (iota n) (PArray.make n 0) (iota_ok n)
                (Zwf_well_founded 0 (meas 0)) eq_refl ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded m); lia) U0)
    as U1.
  set (p1 := uf_loop ks wins ls m 0 (iota n) (PArray.make n 0) (iota_ok n)
               (Zwf_well_founded 0 (meas 0))) in *.
  destruct U1 as [Lp1 Bp1 Dp1 Rp1].
  set (Hp1 := uf_loop_ok ks wins ls m (meas 0) 0 (iota n) (PArray.make n 0) (iota_ok n)
                (Zwf_well_founded 0 (meas 0)) eq_refl).
  destruct (rep_loop_spec n p1 Bp1 _ 0 p1 (PArray.make n 0) Hp1 (Zwf_well_founded 0 (meas 0))
              eq_refl Ln ltac:(intros; reflexivity)
              ltac:(intros x' Hx'; change (φ 0) with 0%Z in Hx'; pose proof (to_Z_bounded x'); lia))
    as [Lrep Rrep].
  set (rep := rep_loop n 0 p1 (PArray.make n 0) Hp1 (Zwf_well_founded 0 (meas 0))) in *.
  assert (Hrep : forall x, ((φ x) < (φ n))%Z -> ((φ (rep.[x])) < (φ n))%Z)
    by (intros x Hx; exact (anc_bounded n p1 x _ Bp1 (proj1 (Rrep x Hx)) Hx)).
  pose proof (graph_ok n m ks ls rep wins Hn Hm Hks Hls Hrep) as G.
  cbv zeta in G.
  rewrite eqb_spec. refine (iff_trans G _). clear G.
  split.
  - intros [T HT]. exists (fun x => T rep.[x]). intros j Hj.
    destruct (wins.[j]) eqn:W.
    + apply HT. apply (In_EM n m ks ls rep wins Hm).
      exists j. split; [exact Hj|]. split; [exact W|]. split; reflexivity.
    + f_equal. apply (Rp1 j Hj W); apply Rrep; auto.
  - intros [S HS]. exists S. intros w v Hwv.
    apply (In_EM n m ks ls rep wins Hm) in Hwv.
    destruct Hwv as [j [Hj [W [Hw Hv]]]]. subst w v.
    assert (SD : forall a b, deq m ks ls wins a b -> S a = S b).
    { apply deq_S. intros j' Hj' W'. specialize (HS j' Hj'). rewrite W' in HS. exact HS. }
    rewrite <- (SD _ _ (Dp1 _ _ (Hks j Hj) (Rrep _ (Hks j Hj)))).
    rewrite <- (SD _ _ (Dp1 _ _ (Hls j Hj) (Rrep _ (Hls j Hj)))).
    specialize (HS j Hj). rewrite W in HS. exact HS.
Qed.

(* ------------------------------------------------------------------ *)
(* From machine values to the math side of the spec                    *)
(* ------------------------------------------------------------------ *)

Lemma read_uint : forall (x : array uint) (l : list N), repr x l ->
  forall j : int, ((φ j) < Z.of_N (len l))%Z ->
  (φ (x.[j])) = Z.of_N (at_ 0%N l (Z.to_N (φ j))).
Proof.
  intros x l [Hl Hc] j Hj.
  assert (Hl' : Z.of_nat (List.length l) = (φ (PArray.length x))) by exact Hl.
  pose proof (to_Z_bounded j) as Bj. unfold len in Hj.
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as [v [Hv Hr]].
  assert (Hr' : Z.to_N (φ (x.[j])) = v).
  { unfold repr, repr_uint in Hr. rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
    exact Hr. }
  unfold at_. rewrite Z_N_nat. rewrite (nth_error_nth l (Z.to_nat (φ j)) 0%N Hv).
  rewrite <- Hr'. pose proof (to_Z_bounded (x.[j])). lia.
Qed.

Lemma read_bool : forall (x : array bool) (l : list bool), repr x l ->
  forall j : int, ((φ j) < Z.of_N (len l))%Z ->
  x.[j] = at_ false l (Z.to_N (φ j)).
Proof.
  intros x l [Hl Hc] j Hj.
  assert (Hl' : Z.of_nat (List.length l) = (φ (PArray.length x))) by exact Hl.
  pose proof (to_Z_bounded j) as Bj. unfold len in Hj.
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as [v [Hv Hr]].
  assert (Hr' : x.[j] = v).
  { unfold repr, repr_bool in Hr. rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
    exact Hr. }
  unfold at_. rewrite Z_N_nat. rewrite (nth_error_nth l (Z.to_nat (φ j)) false Hv).
  exact Hr'.
Qed.

Lemma repr_len_uint : forall (x : array uint) (l : list N), repr x l ->
  (φ (PArray.length x)) = Z.of_N (len l).
Proof.
  intros x l [Hl _].
  assert (Hl' : Z.of_nat (List.length l) = (φ (PArray.length x))) by exact Hl.
  unfold len. lia.
Qed.

Lemma repr_len_bool : forall (x : array bool) (l : list bool), repr x l ->
  (φ (PArray.length x)) = Z.of_N (len l).
Proof.
  intros x l [Hl _].
  assert (Hl' : Z.of_nat (List.length l) = (φ (PArray.length x))) by exact Hl.
  unfold len. lia.
Qed.

Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P [H1 H2]; [exact (H1 eq_refl)|intros HP; discriminate (H2 HP)].
Qed.

Lemma chess_impl_spec :
  forall (n : N) (ks : list N) (wins : list bool) (ls : list N)
         (xn : uint) (xks : array uint) (xwins : array bool) (xls : array uint),
  valid_input n ks wins ls ->
  repr xn n -> repr xks ks -> repr xwins wins -> repr xls ls ->
  exists b : bool, repr (chess_impl xn xks xwins xls) b /\
                   chess_consistent_spec n ks wins ls b.
Proof.
  intros n ks wins ls xn xks xwins xls Hv Rn Rks Rwins Rls.
  exists (chess_impl xn xks xwins xls). split; [reflexivity|].
  destruct Hv as [Vn Vm Vw Vl Vks Vls _ _].
  assert (Hxn : (φ xn) = Z.of_N n).
  { unfold repr, repr_uint in Rn. pose proof (to_Z_bounded xn). lia. }
  pose proof (repr_len_uint xks ks Rks) as Lks.
  pose proof (repr_len_bool xwins wins Rwins) as Lw.
  pose proof (repr_len_uint xls ls Rls) as Ll.
  assert (Bnth : forall (l : list N) j, Forall (fun k => (k < n)%N) l ->
            (j < len l)%N -> (at_ 0%N l j < n)%N).
  { intros l j Hf Hj. rewrite Forall_forall in Hf. apply Hf. unfold at_.
    apply nth_In. unfold len in Hj. lia. }
  assert (RW : forall j : int, ((φ j) < Z.of_N (len ks))%Z ->
            PArray.get@{Set} xwins j = at_ false wins (Z.to_N (φ j)))
    by (intros j Hj; exact (read_bool xwins wins Rwins j ltac:(lia))).
  assert (RK : forall j : int, ((φ j) < Z.of_N (len ks))%Z ->
            (φ (@PArray.get@{Set} int xks j)) = Z.of_N (at_ 0%N ks (Z.to_N (φ j))))
    by (intros j Hj; exact (read_uint xks ks Rks j Hj)).
  assert (RL : forall j : int, ((φ j) < Z.of_N (len ks))%Z ->
            (φ (@PArray.get@{Set} int xls j)) = Z.of_N (at_ 0%N ls (Z.to_N (φ j))))
    by (intros j Hj; exact (read_uint xls ls Rls j ltac:(lia))).
  assert (LS : (φ (PArray.length@{Set} xks)) = Z.of_N (len ks)) by exact Lks.
  assert (LS2 : (φ (@PArray.length@{Set} int xks)) = Z.of_N (len ks)) by exact Lks.
  assert (Hks : forall j, ((φ j) < (φ (@PArray.length@{Set} int xks)))%Z ->
            ((φ (@PArray.get@{Set} int xks j)) < (φ xn))%Z).
  { intros j Hj. rewrite (RK j ltac:(lia)), Hxn.
    pose proof (Bnth ks (Z.to_N (φ j)) Vks ltac:(lia)). lia. }
  assert (Hls : forall j, ((φ j) < (φ (@PArray.length@{Set} int xks)))%Z ->
            ((φ (@PArray.get@{Set} int xls j)) < (φ xn))%Z).
  { intros j Hj. rewrite (RL j ltac:(lia)), Hxn.
    pose proof (Bnth ls (Z.to_N (φ j)) Vls ltac:(lia)). lia. }
  unfold chess_consistent_spec. apply bool_match_of_iff.
  assert (B1 : ((φ xn) <= 50000)%Z) by lia.
  assert (B2 : ((φ (@PArray.length@{Set} int xks)) <= 250000)%Z) by lia.
  rewrite (chess_impl_correct xn xks xls xwins B1 B2 Hks Hls).
  unfold consistent, explains.
  split.
  - intros [S HS]. exists (fun x => S (of_Z (Z.of_N x))). intros j Hj.
    set (jj := of_Z (Z.of_N j)).
    assert (Hjj : (φ jj) = Z.of_N j) by (unfold jj; rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
    assert (Ej : Z.to_N (φ jj) = j) by lia.
    assert (Hjm : ((φ jj) < (φ (PArray.length@{Set} xks)))%Z) by lia.
    specialize (HS jj Hjm).
    rewrite (RW jj ltac:(lia)), Ej in HS.
    assert (Ek : @PArray.get@{Set} int xks jj = of_Z (Z.of_N (at_ 0%N ks j))).
    { rewrite <- Ej. rewrite <- (RK jj ltac:(lia)). symmetry. apply of_to_Z. }
    assert (El : @PArray.get@{Set} int xls jj = of_Z (Z.of_N (at_ 0%N ls j))).
    { rewrite <- Ej. rewrite <- (RL jj ltac:(lia)). symmetry. apply of_to_Z. }
    rewrite Ek, El in HS.
    destruct (at_ false wins j); lia.
  - intros [s Hs]. exists (fun x => s (Z.to_N (φ x))). intros jj Hjj.
    pose proof (to_Z_bounded jj).
    assert (Hjn : (Z.to_N (φ jj) < len ks)%N) by lia.
    specialize (Hs (Z.to_N (φ jj)) Hjn).
    rewrite (RW jj ltac:(lia)).
    assert (Ek : Z.to_N (φ (@PArray.get@{Set} int xks jj)) = at_ 0%N ks (Z.to_N (φ jj)))
      by (rewrite (RK jj ltac:(lia)); lia).
    assert (El : Z.to_N (φ (@PArray.get@{Set} int xls jj)) = at_ 0%N ls (Z.to_N (φ jj)))
      by (rewrite (RL jj ltac:(lia)); lia).
    rewrite Ek, El.
    destruct (at_ false wins (Z.to_N (φ jj))); lia.
Qed.

Definition chess_consistent_correct :
  forall (n : N) (ks : list N) (wins : list bool) (ls : list N)
         (xn : uint) (xks : array uint) (xwins : array bool)
         (xls : array uint),
  valid_input n ks wins ls ->
  repr xn n -> repr xks ks -> repr xwins wins -> repr xls ls ->
  exists b : bool, repr (chess_consistent xn xks xwins xls) b /\
                   chess_consistent_spec n ks wins ls b
  := chess_impl_spec.
