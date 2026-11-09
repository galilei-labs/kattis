(* Executable implementation and its required termination dependencies.
   Correctness proofs are in catenyms_proofs.v. *)
(* Implementation of catenyms (catenyms.spec): Hierholzer's algorithm on
   the letter multigraph, out-edges taken in increasing word order.

   Code (Part 3).  The word indices 0..n-1 are sorted by
   PrimString.compare with a top-down merge sort over one int array and
   one scratch array.  Scanning the sorted order from its end builds, for
   each first letter c (a byte code, 256 letters), a linked list head[c]
   -> nxt[..] of the words starting with c, in increasing order (flat int
   tables, n is the end of a list).  The out- and in-degrees of the
   letters are counted; the degree condition is checked letter by letter
   (no letter off by more than one, as many +1 as -1 letters, at most
   one).  The start letter is the +1 letter, or the first letter of the
   smallest word.  Hierholzer then runs iteratively: an explicit stack of
   edges stk[0..sp), ptr[c] the next unused out-edge of c; an edge is
   popped when its head letter has no unused out-edge and is written into
   the result from the end.  The answer is the result when all n edges
   were popped, otherwise None (this count replaces a separate
   reachability DFS: with the degree condition, every edge is consumed
   exactly when all are reachable from the start).  The words are never
   copied: the result holds the input strings.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] (template/polymul1); the Hierholzer measure is
   2 (n - pushes) + sp, the push being guarded by pushes < n.  No nat in
   the code.

   Proof.  Part 1 states Hierholzer recursively ([Hrel]: at x take the
   smallest unused out-edge e, run from its head (trail A), run from x
   again (trail B), output B ++ e :: A) over an abstract graph, and proves:
   under the degree condition the output is a trail ([Hrel_trail]); it
   covers every edge reachable from the start ([Hrel_covers]); it is
   lexicographically at most every trail from the start through as many
   remaining edges ([Hrel_lex], by induction on Hrel: when B is not empty
   it lives on letters the first run never reaches, so any competing
   trail splits the same way); in a balanced graph it starts with the
   smallest out-edge ([Hrel_circuit]); and the iterative stack machine
   reproduces it ([Hrel_mstar]).  Part 2 relates PrimString.compare to
   String.compare and the order of the printed line to the order of word
   sequences ([text_lt]).  Part 4 proves each loop against its math
   model ([merge_loop_spec], [msort_spec], [build_loop_spec],
   [deg_loop_spec], [chk_loop_spec], [hier_sim]); [main_run] and
   [catenyms_impl_correct] assemble the contract. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii Permutation Sorted.
From Stdlib Require PrimString PString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ================================================================== *)
(* Part 1. Euler trails and Hierholzer's procedure, on the math side.  *)
(* ================================================================== *)

Section Graph.

Variable NV : nat.
Variables tl hd : nat -> nat.
Hypothesis Htl : forall e, (tl e < NV)%nat.
Hypothesis Hhd : forall e, (hd e < NV)%nat.

Local Open Scope nat_scope.

(* trail v l w : the edges of l, in order, walk from v to w. *)
Inductive trail : nat -> list nat -> nat -> Prop :=
| tr_nil : forall v, trail v [] v
| tr_cons : forall v e l w, tl e = v -> trail (hd e) l w -> trail v (e :: l) w.

Lemma trail_cons_inv : forall v e l w, trail v (e :: l) w -> tl e = v /\ trail (hd e) l w.
Proof. intros v e l w H. inversion H; subst. split; auto. Qed.

Lemma trail_nil_inv : forall v w, trail v [] w -> v = w.
Proof. intros v w H. inversion H; auto. Qed.

Lemma trail_app : forall a l1 b l2 c, trail a l1 b -> trail b l2 c -> trail a (l1 ++ l2) c.
Proof.
  intros a l1 b l2 c H1 H2. induction H1; simpl; [exact H2|].
  constructor; auto.
Qed.

Lemma trail_app_inv : forall l1 l2 a c, trail a (l1 ++ l2) c ->
  exists b, trail a l1 b /\ trail b l2 c.
Proof.
  induction l1 as [|e l1 IH]; simpl; intros l2 a c H.
  - exists a. split; [constructor|exact H].
  - apply trail_cons_inv in H as [H1 H2].
    destruct (IH _ _ _ H2) as (b & Hb1 & Hb2).
    exists b. split; [constructor; auto|exact Hb2].
Qed.

Lemma trail_last : forall v l u, trail v l u -> u = v \/ In u (map hd l).
Proof.
  intros v l u H. induction H as [v|v e l w He Hl IH]; [left; reflexivity|].
  right. simpl. destruct IH as [->|IH]; [left; reflexivity|right; exact IH].
Qed.

Lemma trail_tails : forall v l u, trail v l u ->
  forall a, In a l -> tl a = v \/ In (tl a) (map hd l).
Proof.
  intros v l u H. induction H as [v|v e l w He Hl IH]; intros a Ha; [destruct Ha|].
  destruct Ha as [<-|Ha]; [left; exact He|].
  right. simpl. destruct (IH a Ha) as [E|E]; [left; symmetry; exact E|right; exact E].
Qed.

Lemma trail_heads : forall v l u, trail v l u ->
  forall b, In b l -> hd b = u \/ In (hd b) (map tl l).
Proof.
  intros v l u H. induction H as [v|v e l w He Hl IH]; intros b Hb; [destruct Hb|].
  destruct Hb as [<-|Hb].
  - destruct l as [|f l].
    + left. apply trail_nil_inv in Hl. exact Hl.
    + apply trail_cons_inv in Hl as [Hf _]. right. right. left. exact Hf.
  - destruct (IH b Hb) as [E|E]; [left; exact E|right; right; exact E].
Qed.

(* degrees *)
Definition cnt (f : nat -> nat) (v : nat) (l : list nat) : Z :=
  Z.of_nat (List.length (filter (fun e => Nat.eqb (f e) v) l)).
Definition dg (l : list nat) (v : nat) : Z := (cnt tl v l - cnt hd v l)%Z.
Definition ind (b : bool) : Z := if b then 1%Z else 0%Z.
(* the degree condition of an Euler trail from s to t *)
Definition D (l : list nat) (s t : nat) : Prop :=
  forall v, dg l v = (ind (Nat.eqb v s) - ind (Nat.eqb v t))%Z.

Ltac eqbs := unfold ind in *;
  repeat match goal with
  | |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b)
  | H : context [Nat.eqb ?a ?b] |- _ => destruct (Nat.eqb_spec a b)
  end; lia.

Lemma cnt_cons : forall f v e l, cnt f v (e :: l) = (ind (Nat.eqb (f e) v) + cnt f v l)%Z.
Proof. intros. unfold cnt, ind. simpl. destruct (Nat.eqb (f e) v) eqn:E0; [rewrite length_cons|]; lia. Qed.

Lemma cnt_app : forall f v l1 l2, cnt f v (l1 ++ l2) = (cnt f v l1 + cnt f v l2)%Z.
Proof. intros. unfold cnt. rewrite filter_app, length_app. lia. Qed.

Lemma cnt_perm : forall f v l1 l2, Permutation l1 l2 -> cnt f v l1 = cnt f v l2.
Proof.
  intros f v l1 l2 HP. induction HP; rewrite ?cnt_cons; try lia.
Qed.

Lemma cnt_none : forall f v l, (forall e, In e l -> f e <> v) -> cnt f v l = 0%Z.
Proof.
  intros f v l H. induction l as [|e l IH]; [reflexivity|].
  rewrite cnt_cons, IH by (intros g Hg; apply H; right; exact Hg).
  pose proof (H e (or_introl eq_refl)). eqbs.
Qed.

Lemma cnt_nonneg : forall f v l, (0 <= cnt f v l)%Z.
Proof. intros. unfold cnt. lia. Qed.

Lemma dg_cons : forall l e v, dg (e :: l) v = (ind (Nat.eqb (tl e) v) - ind (Nat.eqb (hd e) v) + dg l v)%Z.
Proof. intros. unfold dg. rewrite !cnt_cons. lia. Qed.

Lemma dg_app : forall l1 l2 v, dg (l1 ++ l2) v = (dg l1 v + dg l2 v)%Z.
Proof. intros. unfold dg. rewrite !cnt_app. lia. Qed.

Lemma dg_perm : forall l1 l2 v, Permutation l1 l2 -> dg l1 v = dg l2 v.
Proof. intros. unfold dg. rewrite (cnt_perm tl v l1 l2), (cnt_perm hd v l1 l2); auto. Qed.

Lemma trail_D : forall a l b, trail a l b -> D l a b.
Proof.
  intros a l b H. induction H as [v|v e l w He Hl IH]; intros u.
  - unfold dg, cnt. simpl. eqbs.
  - rewrite dg_cons, IH. subst v. eqbs.
Qed.

Lemma D_cons : forall e l v t, D (e :: l) v t -> tl e = v -> D l (hd e) t.
Proof.
  intros e l v t H He u. specialize (H u). rewrite dg_cons in H. subst v. eqbs.
Qed.

Lemma D_perm : forall l1 l2 s t, Permutation l1 l2 -> D l1 s t -> D l2 s t.
Proof. intros l1 l2 s t HP H u. rewrite <- (dg_perm _ _ u HP). apply H. Qed.

Lemma D_rest : forall A l w t, D (A ++ l) w t -> trail w A t -> forall x, D l x x.
Proof.
  intros A l w t H HA x u. pose proof (trail_D _ _ _ HA u) as H1. specialize (H u).
  rewrite dg_app in H. eqbs.
Qed.

(* the remaining edges : rem c lists the unused out-edges of c *)
Definition E (rem : nat -> list nat) : list nat := flat_map rem (seq 0 NV).
Definition upd (rem : nat -> list nat) (x : nat) (r : list nat) : nat -> list nat :=
  fun c => if Nat.eqb c x then r else rem c.
Definition Inv (rem : nat -> list nat) : Prop := forall c e, In e (rem c) -> tl e = c.

Lemma flat_map_upd_notin : forall l rem x r, ~ In x l ->
  flat_map (upd rem x r) l = flat_map rem l.
Proof.
  induction l as [|c l IH]; intros rem x r Hn; [reflexivity|]. simpl.
  rewrite IH by (intro H; apply Hn; right; exact H).
  unfold upd at 1. destruct (Nat.eqb_spec c x); [exfalso; apply Hn; left; auto|reflexivity].
Qed.

Lemma flat_map_upd : forall l rem x e r, NoDup l -> In x l -> rem x = e :: r ->
  Permutation (flat_map rem l) (e :: flat_map (upd rem x r) l).
Proof.
  induction l as [|c l IH]; intros rem x e r Hnd Hin Hx; [destruct Hin|].
  apply NoDup_cons_iff in Hnd as [Hc Hnd']. simpl.
  destruct (Nat.eqb_spec c x) as [->|Hne].
  - replace (upd rem x r x) with r by (unfold upd; rewrite Nat.eqb_refl; reflexivity).
    rewrite Hx, flat_map_upd_notin by exact Hc. simpl. apply Permutation_refl.
  - destruct Hin as [E1|Hin]; [exfalso; apply Hne; exact E1|].
    replace (upd rem x r c) with (rem c) by (unfold upd; destruct (Nat.eqb_spec c x); congruence).
    eapply perm_trans; [apply Permutation_app_head, (IH rem x e r Hnd' Hin Hx)|].
    apply Permutation_sym, Permutation_middle.
Qed.

Lemma E_upd : forall rem x e r, rem x = e :: r -> x < NV ->
  Permutation (E rem) (e :: E (upd rem x r)).
Proof.
  intros rem x e r Hx Hlt. unfold E. apply flat_map_upd; auto.
  - apply seq_NoDup.
  - apply in_seq. lia.
Qed.

Lemma Inv_upd : forall rem x e r, Inv rem -> rem x = e :: r -> Inv (upd rem x r).
Proof.
  intros rem x e r HI Hx c f Hf. unfold upd in Hf.
  destruct (Nat.eqb_spec c x) as [->|]; [apply HI; rewrite Hx; right; exact Hf|apply HI; exact Hf].
Qed.

Lemma StronglySorted_app_r : forall (R : nat -> nat -> Prop) pre l,
  StronglySorted R (pre ++ l) -> StronglySorted R l.
Proof.
  intros R pre. induction pre as [|a pre IH]; intros l H; [exact H|].
  apply IH. apply StronglySorted_inv in H. apply H.
Qed.


Lemma In_E : forall rem f, Inv rem -> In f (E rem) -> In f (rem (tl f)).
Proof.
  intros rem f HI Hf. unfold E in Hf. apply in_flat_map in Hf as (c & _ & Hc).
  rewrite (HI c f Hc). exact Hc.
Qed.

Lemma E_In : forall rem c f, Inv rem -> In f (rem c) -> In f (E rem).
Proof.
  intros rem c f HI Hf. unfold E. apply in_flat_map. exists c. split; [|exact Hf].
  apply in_seq. rewrite <- (HI c f Hf). pose proof (Htl f). lia.
Qed.

(* Hierholzer's procedure, recursively: at x, take the smallest unused
   out-edge e, run from its head, then run from x again ; the trail is
   the second run, then e, then the first run. *)
Inductive Hrel : (nat -> list nat) -> nat -> list nat -> (nat -> list nat) -> Prop :=
| H_stop : forall rem x, rem x = [] -> Hrel rem x [] rem
| H_go : forall rem x e r A rem' B rem'',
    rem x = e :: r ->
    Hrel (upd rem x r) (hd e) A rem' ->
    Hrel rem' x B rem'' ->
    Hrel rem x (B ++ e :: A) rem''.

Lemma Hrel_suffix : forall rem x P rem'', Hrel rem x P rem'' ->
  forall c, exists pre, rem c = pre ++ rem'' c.
Proof.
  intros rem x P rem'' H. induction H as [rem x Hx|rem x e r A rem' B rem'' Hx HA IHA HB IHB];
    intros c; [exists []; reflexivity|].
  destruct (IHA c) as (p1 & E1). destruct (IHB c) as (p2 & E2).
  unfold upd in E1. destruct (Nat.eqb_spec c x) as [->|Hne].
  - exists (e :: p1 ++ p2). rewrite Hx, E1, E2, app_assoc. reflexivity.
  - exists (p1 ++ p2). rewrite E1, E2, app_assoc. reflexivity.
Qed.

Lemma Hrel_Inv : forall rem x P rem'', Hrel rem x P rem'' -> Inv rem -> Inv rem''.
Proof.
  intros rem x P rem'' H HI c f Hf. destruct (Hrel_suffix _ _ _ _ H c) as (pre & E1).
  apply HI. rewrite E1. apply in_or_app. right. exact Hf.
Qed.


Lemma Hrel_done : forall rem x P rem'', Hrel rem x P rem'' ->
  rem'' x = [] /\ forall e, In e P -> rem'' (hd e) = [].
Proof.
  intros rem x P rem'' H.
  induction H as [rem x Hx|rem x e r A rem' B rem'' Hx HA IHA HB IHB];
    [split; [exact Hx|intros e []]|].
  destruct IHA as [HA1 HA2]. destruct IHB as [HB1 HB2].
  assert (Hnil : forall c, rem' c = [] -> rem'' c = []).
  { intros c Hc. destruct (Hrel_suffix _ _ _ _ HB c) as (pre & E1).
    rewrite Hc in E1. symmetry in E1. apply app_eq_nil in E1. apply E1. }
  split; [exact HB1|]. intros f Hf. apply in_app_or in Hf as [Hf|[<-|Hf]].
  - apply HB2. exact Hf.
  - apply Hnil. exact HA1.
  - apply Hnil. apply HA2. exact Hf.
Qed.

Lemma Hrel_perm : forall rem x P rem'', Hrel rem x P rem'' -> Inv rem ->
  Permutation (E rem) (P ++ E rem'').
Proof.
  intros rem x P rem'' H.
  induction H as [rem x Hx|rem x e r A rem' B rem'' Hx HA IHA HB IHB]; intros HI;
    [apply Permutation_refl|].
  assert (Hte : tl e = x) by (apply (HI x e); rewrite Hx; left; reflexivity).
  assert (HI1 : Inv (upd rem x r)) by (apply (Inv_upd rem x e r HI Hx)).
  assert (HI' : Inv rem') by (apply (Hrel_Inv _ _ _ _ HA HI1)).
  eapply perm_trans; [apply (E_upd rem x e r Hx); rewrite <- Hte; apply Htl|].
  eapply perm_trans; [apply perm_skip, (IHA HI1)|].
  eapply perm_trans; [apply perm_skip, Permutation_app_head, (IHB HI')|].
  rewrite <- app_assoc. simpl.
  eapply perm_trans; [|apply Permutation_middle].
  apply perm_skip. rewrite !app_assoc.
  apply Permutation_app_tail, Permutation_app_comm.
Qed.

Lemma Hrel_trail : forall rem x P rem'', Hrel rem x P rem'' -> Inv rem ->
  forall t, D (E rem) x t -> trail x P t.
Proof.
  intros rem x P rem'' H.
  induction H as [rem x Hx|rem x e r A rem' B rem'' Hx HA IHA HB IHB]; intros HI t HD.
  - assert (Hc : cnt tl x (E rem) = 0%Z).
    { apply cnt_none. intros f Hf Hfx. apply (In_E rem f HI) in Hf. rewrite Hfx, Hx in Hf. destruct Hf. }
    specialize (HD x). unfold dg in HD. rewrite Hc in HD.
    pose proof (cnt_nonneg hd x (E rem)).
    assert (x = t) as -> by eqbs. constructor.
  - assert (Hte : tl e = x) by (apply (HI x e); rewrite Hx; left; reflexivity).
    assert (HI1 : Inv (upd rem x r)) by (apply (Inv_upd rem x e r HI Hx)).
    assert (HI' : Inv rem') by (apply (Hrel_Inv _ _ _ _ HA HI1)).
    assert (HP1 : Permutation (E rem) (e :: E (upd rem x r)))
      by (apply E_upd; [exact Hx|rewrite <- Hte; apply Htl]).
    assert (HD1 : D (E (upd rem x r)) (hd e) t)
      by (apply D_cons with x; [apply (D_perm _ _ _ _ HP1 HD)|exact Hte]).
    assert (HtA : trail (hd e) A t) by (apply IHA; auto).
    assert (HD' : D (E rem') x x).
    { apply (D_rest A (E rem') (hd e) t); [|exact HtA].
      apply (D_perm _ _ _ _ (Hrel_perm _ _ _ _ HA HI1) HD1). }
    assert (HtB : trail x B x) by (apply IHB; auto).
    apply (trail_app _ _ _ _ _ HtB). constructor; auto.
Qed.

Lemma Hrel_exists : forall m rem x, Inv rem -> List.length (E rem) <= m ->
  exists P rem'', Hrel rem x P rem''.
Proof.
  induction m as [|m IH]; intros rem x HI Hl.
  - destruct (rem x) as [|e r] eqn:Hx; [exists [], rem; constructor; exact Hx|].
    exfalso. assert (In e (E rem)) by (apply (E_In rem x); [exact HI|rewrite Hx; left; reflexivity]).
    destruct (E rem); [destruct H|simpl in Hl; lia].
  - destruct (rem x) as [|e r] eqn:Hx; [exists [], rem; constructor; exact Hx|].
    assert (Hte : tl e = x) by (apply (HI x e); rewrite Hx; left; reflexivity).
    assert (HI1 : Inv (upd rem x r)) by (apply (Inv_upd rem x e r HI Hx)).
    assert (HP1 : Permutation (E rem) (e :: E (upd rem x r)))
      by (apply E_upd; [exact Hx|rewrite <- Hte; apply Htl]).
    apply Permutation_length in HP1. simpl in HP1.
    destruct (IH (upd rem x r) (hd e) HI1 ltac:(lia)) as (A & rem' & HA).
    pose proof (Permutation_length (Hrel_perm _ _ _ _ HA HI1)) as HlA.
    rewrite length_app in HlA.
    destruct (IH rem' x (Hrel_Inv _ _ _ _ HA HI1) ltac:(lia)) as (B & rem'' & HB).
    exists (B ++ e :: A), rem''. econstructor; eauto.
Qed.

Variable wlt : nat -> nat -> Prop.

Definition Srt (rem : nat -> list nat) : Prop := forall c, StronglySorted wlt (rem c).

Lemma Srt_upd : forall rem x e r, Srt rem -> rem x = e :: r -> Srt (upd rem x r).
Proof.
  intros rem x e r HS Hx c. unfold upd.
  destruct (Nat.eqb_spec c x) as [->|]; [|apply HS].
  apply (StronglySorted_app_r _ [e]). simpl. rewrite <- Hx. apply HS.
Qed.

Lemma Hrel_Srt : forall rem x P rem'', Hrel rem x P rem'' -> Srt rem -> Srt rem''.
Proof.
  intros rem x P rem'' H HS c. destruct (Hrel_suffix _ _ _ _ H c) as (pre & E1).
  apply (StronglySorted_app_r _ pre). rewrite <- E1. apply HS.
Qed.

(* lexicographic order on edge sequences *)
Definition lexlt (l1 l2 : list nat) : Prop :=
  exists p a b r1 r2, l1 = p ++ a :: r1 /\ l2 = p ++ b :: r2 /\ wlt a b.
Definition lexle (l1 l2 : list nat) : Prop := l1 = l2 \/ lexlt l1 l2.

Lemma lexle_cons : forall e l1 l2, lexle l1 l2 -> lexle (e :: l1) (e :: l2).
Proof.
  intros e l1 l2 [->|(p & a & b & r1 & r2 & E1 & E2 & H)]; [left; reflexivity|].
  right. exists (e :: p), a, b, r1, r2. subst. auto.
Qed.

Lemma lexle_head : forall e f l1 l2, wlt e f -> lexle (e :: l1) (f :: l2).
Proof. intros e f l1 l2 H. right. exists [], e, f, l1, l2. auto. Qed.

Lemma lexle_app : forall B T1 X Y, lexle B T1 -> lexle X Y -> lexle (B ++ X) (T1 ++ Y).
Proof.
  intros B T1 X Y [<-|(p & a & b & r1 & r2 & E1 & E2 & H)] H2.
  - destruct H2 as [<-|(p & a & b & r1 & r2 & E1 & E2 & H)]; [left; reflexivity|].
    right. exists (B ++ p), a, b, r1, r2. subst. rewrite <- !app_assoc. auto.
  - right. exists p, a, b, (r1 ++ X), (r2 ++ Y). subst. rewrite <- !app_assoc. auto.
Qed.

Lemma trail_in : forall (X Q Pl : list nat) e,
  (forall f, In f Pl -> In (tl f) X -> f <> e -> In f Q) ->
  (forall q, In q Q -> In (hd q) X) ->
  forall T z y, trail z T y -> In z X -> incl T Pl -> ~ In e T -> incl T Q.
Proof.
  intros X Q Pl e H1 H2 T z y HT.
  induction HT as [v|v f l w Hf Hl IH]; intros Hz Hi Hn; [intros g []|].
  assert (HfQ : In f Q).
  { apply H1; [apply Hi; left; reflexivity|rewrite Hf; exact Hz|].
    intro E'; apply Hn; left; exact E'. }
  intros g [<-|Hg]; [exact HfQ|].
  apply (IH (H2 f HfQ)); [intros h Hh; apply Hi; right; exact Hh| |exact Hg].
  intro E'; apply Hn; right; exact E'.
Qed.

Lemma trail_stays : forall (S Pl : list nat) (good : nat -> Prop),
  (forall p, In p Pl -> In (hd p) S) ->
  (forall f, good f -> In (tl f) S -> In f Pl) ->
  forall T z y, trail z T y -> In z S -> (forall f, In f T -> good f) -> incl T Pl.
Proof.
  intros S Pl good H1 H2 T z y HT.
  induction HT as [v|v f l w Hf Hl IH]; intros Hz Hg; [intros g []|].
  assert (HfP : In f Pl) by (apply H2; [apply Hg; left; reflexivity|rewrite Hf; exact Hz]).
  intros g [<-|Hgl]; [exact HfP|].
  apply (IH (H1 f HfP)); [intros h Hh; apply Hg; right; exact Hh|exact Hgl].
Qed.

(* Every edge out of a vertex the run has visited has been consumed : a
   trail from x through the remaining edges stays inside the run's
   trail. *)
Lemma Hrel_covers : forall rem x P rem'', Hrel rem x P rem'' -> Inv rem ->
  forall T z y, trail z T y -> In z (x :: map hd P) -> incl T (E rem) -> incl T P.
Proof.
  intros rem x P rem'' HH HI T z y HT Hz HiT.
  destruct (Hrel_done _ _ _ _ HH) as [Hd1 Hd2].
  pose proof (Hrel_perm _ _ _ _ HH HI) as HPm.
  pose proof (Hrel_Inv _ _ _ _ HH HI) as HI''.
  apply (trail_stays (x :: map hd P) P (fun f => In f (E rem))) with (z := z) (y := y); auto.
  - intros p Hp. right. apply in_map. exact Hp.
  - intros f Hf Hs. apply (Permutation_in _ HPm) in Hf. apply in_app_or in Hf as [Hf|Hf]; [exact Hf|].
    exfalso. apply (In_E rem'' f HI'') in Hf.
    destruct Hs as [E1|Hs]; [rewrite <- E1, Hd1 in Hf; destruct Hf|].
    apply in_map_iff in Hs as (p & Hp & Hp').
    rewrite <- Hp, (Hd2 p Hp') in Hf. destruct Hf.
Qed.

(* The facts behind both the minimality proof and the circuit lemma :
   when the second run B is non-empty, it lives on vertices the first run
   (e, then A) never reaches. *)
Lemma B_avoids : forall rem x e r A rem' B rem'',
  rem x = e :: r -> Hrel (upd rem x r) (hd e) A rem' -> Hrel rem' x B rem'' ->
  Inv rem -> forall b, In b B -> ~ In (tl b) (hd e :: map hd A).
Proof.
  intros rem x e r A rem' B rem'' Hx HA HB HI b Hb HY.
  assert (HI1 : Inv (upd rem x r)) by (apply (Inv_upd rem x e r HI Hx)).
  assert (HI' : Inv rem') by (apply (Hrel_Inv _ _ _ _ HA HI1)).
  destruct (Hrel_done _ _ _ _ HA) as [HdA1 HdA2].
  assert (Hb' : In b (E rem')).
  { apply (Permutation_in _ (Permutation_sym (Hrel_perm _ _ _ _ HB HI'))).
    apply in_or_app. left. exact Hb. }
  apply (In_E rem' b HI') in Hb'.
  destruct HY as [HY|HY].
  - rewrite <- HY, HdA1 in Hb'. destruct Hb'.
  - apply in_map_iff in HY as (a & Ha & Ha'). rewrite <- Ha, (HdA2 a Ha') in Hb'. destruct Hb'.
Qed.

(* Minimality : the trail Hierholzer produces is lexicographically at most
   every trail from x through the same number of remaining edges. *)
Lemma Hrel_lex : forall rem x P rem'', Hrel rem x P rem'' ->
  Inv rem -> Srt rem -> forall t, D (E rem) x t ->
  forall T y, trail x T y -> NoDup T -> incl T (E rem) ->
  List.length T = List.length P -> lexle P T.
Proof.
  intros rem x P rem'' HH.
  induction HH as [rem x Hx|rem x e r A rem' B rem'' Hx HA IHA HB IHB];
    intros HI HS t HD T y HT HnT HiT HlT.
  { destruct T; [left; reflexivity|discriminate]. }
  assert (HH : Hrel rem x (B ++ e :: A) rem'') by (econstructor; eauto).
  assert (Hte : tl e = x) by (apply (HI x e); rewrite Hx; left; reflexivity).
  set (rem1 := upd rem x r) in *.
  assert (HI1 : Inv rem1) by (apply (Inv_upd rem x e r HI Hx)).
  assert (HS1 : Srt rem1) by (apply (Srt_upd rem x e r HS Hx)).
  assert (HP1 : Permutation (E rem) (e :: E rem1))
    by (apply E_upd; [exact Hx|rewrite <- Hte; apply Htl]).
  assert (HD1 : D (E rem1) (hd e) t)
    by (apply D_cons with x; [apply (D_perm _ _ _ _ HP1 HD)|exact Hte]).
  assert (HtA : trail (hd e) A t) by (apply (Hrel_trail _ _ _ _ HA HI1 t HD1)).
  assert (HPA : Permutation (E rem1) (A ++ E rem')) by (apply (Hrel_perm _ _ _ _ HA HI1)).
  assert (HI' : Inv rem') by (apply (Hrel_Inv _ _ _ _ HA HI1)).
  assert (HS' : Srt rem') by (apply (Hrel_Srt _ _ _ _ HA HS1)).
  assert (HD' : D (E rem') x x) by (apply (D_rest A (E rem') (hd e) t); [apply (D_perm _ _ _ _ HPA HD1)|exact HtA]).
  assert (HtB : trail x B x) by (apply (Hrel_trail _ _ _ _ HB HI' x HD')).
  assert (HPB : Permutation (E rem') (B ++ E rem'')) by (apply (Hrel_perm _ _ _ _ HB HI')).
  assert (HBc : B = [] \/ exists b0 B', B = b0 :: B') by (destruct B; eauto).
  destruct HBc as [->|(b0 & B' & EB)].
  - (* B empty : P = e :: A *)
    simpl. destruct T as [|f T']; [simpl in HlT; discriminate|].
    apply trail_cons_inv in HT as [Hf HT'].
    assert (Hfx : In f (rem x)) by (rewrite <- Hf; apply In_E; [exact HI|apply HiT; left; reflexivity]).
    rewrite Hx in Hfx. destruct Hfx as [<-|Hfr].
    + apply lexle_cons. apply NoDup_cons_iff in HnT as [HnT1 HnT2].
      apply (IHA HI1 HS1 t HD1 T' y HT' HnT2); [|simpl in HlT; lia].
      intros g Hg. assert (Hg' : In g (E rem)) by (apply HiT; right; exact Hg).
      apply (Permutation_in _ HP1) in Hg' as [<-|Hg']; [contradiction|exact Hg'].
    + apply lexle_head. pose proof (HS x) as HSx. rewrite Hx in HSx.
      apply StronglySorted_inv in HSx as [_ HF]. rewrite Forall_forall in HF. apply HF. exact Hfr.
  - set (Y := hd e :: map hd A).
    set (X := map tl B).
    assert (HBY : forall b, In b B -> ~ In (tl b) Y) by (apply (B_avoids rem x e r A rem' B rem'' Hx HA HB HI)).
    assert (HxX : In x X).
    { unfold X. rewrite EB in HtB |- *. apply trail_cons_inv in HtB as [Hb0 _].
      left. exact Hb0. }
    assert (HBh : forall b, In b B -> In (hd b) X).
    { intros b Hb. destruct (trail_heads _ _ _ HtB b Hb) as [E1|E1]; [rewrite E1; exact HxX|exact E1]. }
    assert (HAt : forall a, In a A -> In (tl a) Y).
    { intros a Ha. destruct (trail_tails _ _ _ HtA a Ha) as [E1|E1]; [left; symmetry; exact E1|right; exact E1]. }
    assert (HAh : forall a, In a A -> In (hd a) Y) by (intros a Ha; right; apply in_map; exact Ha).
    assert (HTP : incl T (B ++ e :: A)).
    { apply (Hrel_covers _ _ _ _ HH HI T x y HT); [left; reflexivity|exact HiT]. }
    assert (HXB : forall f, In f (B ++ e :: A) -> In (tl f) X -> f <> e -> In f B).
    { intros f Hf HfX Hfe. apply in_app_or in Hf as [Hf|[Hf|Hf]]; [exact Hf|congruence|].
      exfalso. unfold X in HfX. apply in_map_iff in HfX as (b & Hb & Hb').
      apply (HBY b Hb'). rewrite Hb. apply HAt. exact Hf. }
    assert (HYA : forall f, In f (B ++ e :: A) -> In (tl f) Y -> f <> e -> In f A).
    { intros f Hf HfY Hfe. apply in_app_or in Hf as [Hf|[Hf|Hf]]; [|congruence|exact Hf].
      exfalso. apply (HBY f Hf HfY). }
    destruct (in_dec Nat.eq_dec e T) as [HeT|HeT].
    + apply in_split in HeT as (T1 & T3 & ET). subst T.
      pose proof (NoDup_remove_2 _ _ _ HnT) as Hn1.
      pose proof (NoDup_remove_1 _ _ _ HnT) as Hn2.
      assert (HeT1 : ~ In e T1) by (intro E1; apply Hn1, in_or_app; left; exact E1).
      assert (HeT3 : ~ In e T3) by (intro E1; apply Hn1, in_or_app; right; exact E1).
      destruct (trail_app_inv _ _ _ _ HT) as (z & HT1 & HT3).
      apply trail_cons_inv in HT3 as [Hz HT3]. rewrite Hte in Hz. subst z.
      assert (HiT1 : incl T1 B).
      { apply (trail_in X B (B ++ e :: A) e HXB HBh T1 x x HT1 HxX); [|exact HeT1].
        intros g Hg. apply HTP, in_or_app. left. exact Hg. }
      assert (HiT3 : incl T3 A).
      { apply (trail_in Y A (B ++ e :: A) e HYA HAh T3 (hd e) y HT3); [left; reflexivity| |exact HeT3].
        intros g Hg. apply HTP, in_or_app. right. right. exact Hg. }
      assert (HnT1 : NoDup T1) by (apply (NoDup_app_remove_r _ _ Hn2)).
      assert (HnT3 : NoDup T3) by (apply (NoDup_app_remove_l _ _ Hn2)).
      pose proof (NoDup_incl_length HnT1 HiT1) as L1.
      pose proof (NoDup_incl_length HnT3 HiT3) as L3.
      rewrite !length_app in HlT. simpl in HlT.
      apply lexle_app.
      * apply (IHB HI' HS' x HD' T1 x HT1 HnT1); [|lia].
        intros g Hg. apply (Permutation_in _ (Permutation_sym HPB)), in_or_app. left. apply HiT1. exact Hg.
      * apply lexle_cons. apply (IHA HI1 HS1 t HD1 T3 y HT3 HnT3); [|lia].
        intros g Hg. apply (Permutation_in _ (Permutation_sym HPA)), in_or_app. left. apply HiT3. exact Hg.
    + exfalso.
      assert (HiT1 : incl T B) by (apply (trail_in X B (B ++ e :: A) e HXB HBh T x y HT HxX HTP HeT)).
      pose proof (NoDup_incl_length HnT HiT1) as L1.
      rewrite length_app in HlT. simpl in HlT. lia.
Qed.

(* In a balanced graph, the trail starts with the smallest out-edge of x. *)
Lemma Hrel_circuit : forall rem x P rem'', Hrel rem x P rem'' -> Inv rem ->
  D (E rem) x x -> forall e r, rem x = e :: r -> exists A, P = e :: A.
Proof.
  intros rem x P rem'' HH HI HD e0 r0 Hx0.
  destruct HH as [rem x Hx|rem x e r A rem' B rem'' Hx HA HB].
  { rewrite Hx in Hx0. discriminate. }
  rewrite Hx in Hx0. injection Hx0 as -> ->.
  assert (Hte : tl e0 = x) by (apply (HI x e0); rewrite Hx; left; reflexivity).
  assert (HI1 : Inv (upd rem x r0)) by (apply (Inv_upd rem x e0 r0 HI Hx)).
  assert (HP1 : Permutation (E rem) (e0 :: E (upd rem x r0)))
    by (apply E_upd; [exact Hx|rewrite <- Hte; apply Htl]).
  assert (HD1 : D (E (upd rem x r0)) (hd e0) x)
    by (apply D_cons with x; [apply (D_perm _ _ _ _ HP1 HD)|exact Hte]).
  assert (HtA : trail (hd e0) A x) by (apply (Hrel_trail _ _ _ _ HA HI1 x HD1)).
  assert (HI' : Inv rem') by (apply (Hrel_Inv _ _ _ _ HA HI1)).
  assert (HD' : D (E rem') x x).
  { apply (D_rest A (E rem') (hd e0) x); [|exact HtA].
    apply (D_perm _ _ _ _ (Hrel_perm _ _ _ _ HA HI1) HD1). }
  assert (HtB : trail x B x) by (apply (Hrel_trail _ _ _ _ HB HI' x HD')).
  destruct B as [|b0 B']; [exists A; reflexivity|].
  exfalso. apply (B_avoids rem x e0 r0 A rem' (b0 :: B') rem'' Hx HA HB HI b0 (or_introl eq_refl)).
  apply trail_cons_inv in HtB as [Hb0 _]. rewrite Hb0.
  destruct (trail_last _ _ _ HtA) as [E1|E1]; [left; symmetry; exact E1|right; exact E1].
Qed.

(* The iterative procedure : a stack K of edges (top first) and the
   emitted edges O (last emitted first). *)
Definition cur (s : nat) (K : list nat) : nat := match K with [] => s | e :: _ => hd e end.

Inductive mstar (s : nat) : (nat -> list nat) -> list nat -> list nat ->
                            (nat -> list nat) -> list nat -> list nat -> Prop :=
| ms_refl : forall rem K O, mstar s rem K O rem K O
| ms_push : forall rem K O e r rem2 K2 O2, rem (cur s K) = e :: r ->
    mstar s (upd rem (cur s K) r) (e :: K) O rem2 K2 O2 -> mstar s rem K O rem2 K2 O2
| ms_pop : forall rem e K O rem2 K2 O2, rem (hd e) = [] ->
    mstar s rem K (e :: O) rem2 K2 O2 -> mstar s rem (e :: K) O rem2 K2 O2.

Lemma mstar_trans : forall s rem K O rem2 K2 O2 rem3 K3 O3,
  mstar s rem K O rem2 K2 O2 -> mstar s rem2 K2 O2 rem3 K3 O3 -> mstar s rem K O rem3 K3 O3.
Proof.
  intros s rem K O rem2 K2 O2 rem3 K3 O3 H1 H2. induction H1.
  - exact H2.
  - eapply ms_push; eauto.
  - eapply ms_pop; eauto.
Qed.

Lemma Hrel_mstar : forall s rem x P rem'', Hrel rem x P rem'' ->
  forall K O, cur s K = x -> mstar s rem K O rem'' K (P ++ O).
Proof.
  intros s rem x P rem'' HH.
  induction HH as [rem x Hx|rem x e r A rem' B rem'' Hx HA IHA HB IHB]; intros K O HK.
  - apply ms_refl.
  - eapply ms_push; [rewrite HK; exact Hx|]. rewrite HK.
    eapply mstar_trans; [apply (IHA (e :: K) O); reflexivity|].
    eapply ms_pop; [apply (proj1 (Hrel_done _ _ _ _ HA))|].
    rewrite <- app_assoc. simpl. apply IHB. exact HK.
Qed.

End Graph.

(* ================================================================== *)
(* Part 3. The program.                                                *)
(* ================================================================== *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

(* termination measures *)
Definition pgap (m j : int) : Z := Z.max 0 ((φ m) - (φ j)).

Lemma pgap_step : forall m i, (i <? m) = true ->
  (0 <= pgap m (i + 1) /\ pgap m (i + 1) < pgap m i)%Z.
Proof. intros m i H. rewrite ltb_spec in H. unfold pgap. sia. Qed.

Lemma dec_step : forall m i, (i <? m) = true -> Zwf 0 (pgap m (i + 1)) (pgap m i).
Proof. intros m i H. destruct (pgap_step m i H). unfold Zwf. lia. Qed.

Definition mg (iend i jend j : int) : Z := (pgap iend i + pgap jend j)%Z.

Lemma dec_mi : forall iend i jend j, (i <? iend) = true ->
  Zwf 0 (mg iend (i + 1) jend j) (mg iend i jend j).
Proof.
  intros iend i jend j H. destruct (pgap_step iend i H). unfold Zwf, mg.
  assert (0 <= pgap jend j)%Z by (unfold pgap; lia). lia.
Qed.

Lemma dec_mj : forall iend i jend j, (j <? jend) = true ->
  Zwf 0 (mg iend i jend (j + 1)) (mg iend i jend j).
Proof.
  intros iend i jend j H. destruct (pgap_step jend j H). unfold Zwf, mg.
  assert (0 <= pgap iend i)%Z by (unfold pgap; lia). lia.
Qed.

Definition splitc (lo hi : int) : bool := andb (lo <? hi) (1 <? hi - lo).
Definition midp (lo hi : int) : int := lo + (hi - lo) / 2.

Lemma splitc_spec : forall lo hi, splitc lo hi = true ->
  ((φ lo) < (φ hi) /\ 1 < (φ hi) - (φ lo) /\ (φ lo) < (φ (midp lo hi)) < (φ hi))%Z.
Proof.
  intros lo hi H. unfold splitc in H. apply andb_prop in H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold midp.
  assert ((φ (hi - lo)) = (φ hi) - (φ lo))%Z by sia. sia.
Qed.

Lemma dec_ms1 : forall lo hi, splitc lo hi = true -> Zwf 0 (pgap (midp lo hi) lo) (pgap hi lo).
Proof. intros lo hi H. apply splitc_spec in H. unfold Zwf, pgap. lia. Qed.

Lemma dec_ms2 : forall lo hi, splitc lo hi = true -> Zwf 0 (pgap hi (midp lo hi)) (pgap hi lo).
Proof. intros lo hi H. apply splitc_spec in H. unfold Zwf, pgap. lia. Qed.

Definition hg (n q sp : int) : Z := (2 * (φ (n - q)) + (φ sp))%Z.

Lemma dec_push : forall n q sp p, (andb (p <? n) (q <? n)) = true ->
  Zwf 0 (hg n (q + 1) (sp + 1)) (hg n q sp).
Proof.
  intros n q sp p H. apply andb_prop in H as [_ H]. rewrite ltb_spec in H.
  unfold Zwf, hg.
  assert ((φ (n - (q + 1))) = (φ (n - q)) - 1)%Z by sia.
  assert ((φ (sp + 1)) <= (φ sp) + 1)%Z by sia.
  pose proof (to_Z_bounded (sp + 1)). pose proof (to_Z_bounded (n - (q + 1))). lia.
Qed.

Lemma dec_pop : forall n q sp, (0 <? sp) = true -> Zwf 0 (hg n q (sp - 1)) (hg n q sp).
Proof.
  intros n q sp H. rewrite ltb_spec in H. unfold Zwf, hg.
  assert ((φ (sp - 1)) = (φ sp) - 1)%Z by sia. pose proof (to_Z_bounded (n - q)). lia.
Qed.

(* ord[k] = k *)
Fixpoint init_loop (a : array int) (n k : int) (H : Acc (Zwf 0) (pgap n k)) {struct H} : array int :=
  match bdec (k <? n) with
  | left Hk => init_loop a.[k <- k] n (k + 1) (Acc_inv H (dec_step n k Hk))
  | right _ => a
  end.

(* word i <= word j *)
Definition cmpw (x : array PrimString.string) (i j : int) : bool :=
  match PrimString.compare x.[i] x.[j] with Gt => false | _ => true end.

(* merge the sorted runs src[i..iend) and src[j..jend) into dst from k *)
Fixpoint merge_loop (x : array PrimString.string) (src dst : array int) (iend jend : int)
    (i j k : int) (H : Acc (Zwf 0) (mg iend i jend j)) {struct H} : array int :=
  match bdec (i <? iend) with
  | left Hi =>
      match bdec (j <? jend) with
      | left Hj =>
          if cmpw x src.[i] src.[j]
          then merge_loop x src dst.[k <- src.[i]] iend jend (i + 1) j (k + 1)
                 (Acc_inv H (dec_mi iend i jend j Hi))
          else merge_loop x src dst.[k <- src.[j]] iend jend i (j + 1) (k + 1)
                 (Acc_inv H (dec_mj iend i jend j Hj))
      | right _ =>
          merge_loop x src dst.[k <- src.[i]] iend jend (i + 1) j (k + 1)
            (Acc_inv H (dec_mi iend i jend j Hi))
      end
  | right _ =>
      match bdec (j <? jend) with
      | left Hj =>
          merge_loop x src dst.[k <- src.[j]] iend jend i (j + 1) (k + 1)
            (Acc_inv H (dec_mj iend i jend j Hj))
      | right _ => dst
      end
  end.

(* dst[k..hi) := src[k..hi) *)
Fixpoint copy_loop (src dst : array int) (hi k : int) (H : Acc (Zwf 0) (pgap hi k)) {struct H}
    : array int :=
  match bdec (k <? hi) with
  | left Hk => copy_loop src dst.[k <- src.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* top-down merge sort of a[lo..hi) with the scratch array t *)
Fixpoint msort (x : array PrimString.string) (a t : array int) (lo hi : int)
    (H : Acc (Zwf 0) (pgap hi lo)) {struct H} : array int * array int :=
  match bdec (splitc lo hi) with
  | left Hs =>
      match msort x a t lo (midp lo hi) (Acc_inv H (dec_ms1 lo hi Hs)) with
      | (a1, t1) =>
          match msort x a1 t1 (midp lo hi) hi (Acc_inv H (dec_ms2 lo hi Hs)) with
          | (a2, t2) =>
              let t3 := merge_loop x a2 t2 (midp lo hi) hi lo (midp lo hi) lo
                          (Zwf_well_founded 0 _) in
              (copy_loop t3 a2 hi lo (Zwf_well_founded 0 _), t3)
          end
      end
  | right _ => (a, t)
  end.

Definition fst_ch (w : PrimString.string) : int := PrimString.get w 0.
Definition lst_ch (w : PrimString.string) : int := PrimString.get w (PrimString.length w - 1).

(* the adjacency : for each first letter c, a linked list from head[c]
   through nxt, in increasing word order ; n is the end of a list.  Built
   by scanning the sorted order from its end. *)
Fixpoint build_loop (x : array PrimString.string) (ord : array int) (n : int)
    (nxt head : array int) (k : int) (H : Acc (Zwf 0) (pgap n k)) {struct H}
    : array int * array int :=
  match bdec (k <? n) with
  | left Hk =>
      let e := ord.[n - 1 - k] in
      let c := fst_ch x.[e] in
      let h := head.[c] in
      build_loop x ord n nxt.[e <- h] head.[c <- e] (k + 1) (Acc_inv H (dec_step n k Hk))
  | right _ => (nxt, head)
  end.

(* out- and in-degrees of the letters *)
Fixpoint deg_loop (x : array PrimString.string) (n : int) (outd ind : array int) (k : int)
    (H : Acc (Zwf 0) (pgap n k)) {struct H} : array int * array int :=
  match bdec (k <? n) with
  | left Hk =>
      let a := fst_ch x.[k] in
      let b := lst_ch x.[k] in
      let oa := outd.[a] in
      let ib := ind.[b] in
      deg_loop x n outd.[a <- oa + 1] ind.[b <- ib + 1] (k + 1) (Acc_inv H (dec_step n k Hk))
  | right _ => (outd, ind)
  end.

(* the degree condition, letter by letter : the number of letters with
   one more out- than in-edge, of those with one more in- than out-edge,
   the last of the former, and whether some letter is off by more *)
Fixpoint chk_loop (outd ind : array int) (c plus minus sv : int) (bad : bool)
    (H : Acc (Zwf 0) (pgap 256 c)) {struct H} : int * int * int * bool :=
  match bdec (c <? 256) with
  | left Hc =>
      let o := outd.[c] in
      let i := ind.[c] in
      if o =? i then chk_loop outd ind (c + 1) plus minus sv bad (Acc_inv H (dec_step 256 c Hc))
      else if o =? i + 1 then chk_loop outd ind (c + 1) (plus + 1) minus c bad (Acc_inv H (dec_step 256 c Hc))
      else if i =? o + 1 then chk_loop outd ind (c + 1) plus (minus + 1) sv bad (Acc_inv H (dec_step 256 c Hc))
      else chk_loop outd ind (c + 1) plus minus sv true (Acc_inv H (dec_step 256 c Hc))
  | right _ => (plus, minus, sv, bad)
  end.

(* Hierholzer, iteratively : the stack stk[0..sp) of edges (the current
   letter is the last letter of the top edge, s on an empty stack), ptr
   the next unused out-edge of each letter ; an edge popped is written to
   res from the end. q counts the pushes. *)
Fixpoint hier_loop (x : array PrimString.string) (nxt : array int) (n s : int)
    (ptr stk : array int) (sp q : int) (res : array PrimString.string) (cnt : int)
    (H : Acc (Zwf 0) (hg n q sp)) {struct H} : array PrimString.string * int :=
  let v := if sp =? 0 then s else lst_ch x.[stk.[sp - 1]] in
  let p := ptr.[v] in
  match bdec (andb (p <? n) (q <? n)) with
  | left Hp =>
      let np := nxt.[p] in
      hier_loop x nxt n s ptr.[v <- np] stk.[sp <- p] (sp + 1) (q + 1) res cnt
        (Acc_inv H (dec_push n q sp p Hp))
  | right _ =>
      match bdec (0 <? sp) with
      | left Hs =>
          let e := stk.[sp - 1] in
          hier_loop x nxt n s ptr stk (sp - 1) q res.[n - 1 - cnt <- x.[e]] (cnt + 1)
            (Acc_inv H (dec_pop n q sp Hs))
      | right _ => (res, cnt)
      end
  end.

Definition catenyms_impl (x : array PrimString.string) : option (array PrimString.string) :=
  let n := PArray.length x in
  let ord0 := init_loop (PArray.make n 0) n 0 (Zwf_well_founded 0 _) in
  match msort x ord0 (PArray.make n 0) 0 n (Zwf_well_founded 0 _) with
  | (ord, _) =>
    match build_loop x ord n (PArray.make n 0) (PArray.make 256 n) 0 (Zwf_well_founded 0 _) with
    | (nxt, head) =>
      match deg_loop x n (PArray.make 256 0) (PArray.make 256 0) 0 (Zwf_well_founded 0 _) with
      | (outd, ind) =>
        match chk_loop outd ind 0 0 0 0 false (Zwf_well_founded 0 _) with
        | (plus, minus, sv, bad) =>
          if bad then None
          else if negb (plus =? minus) then None
          else if negb (plus <=? 1) then None
          else
            let s := if plus =? 1 then sv else fst_ch x.[ord.[0]] in
            match hier_loop x nxt n s head (PArray.make n 0) 0 0
                    (PArray.make n (PrimString.make 0%uint63 0%uint63)) 0 (Zwf_well_founded 0 _) with
            | (res, cnt) => if cnt =? n then Some res else None
            end
        end
      end
    end
  end.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition catenyms : array PrimString.string -> option (array PrimString.string) := catenyms_impl.
