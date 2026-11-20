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

From Catenyms.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii Permutation Sorted.
From Stdlib Require PrimString PString.
From KattisLib Require Import Cost.
Import PrimString.PStringNotations.
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

Ltac eqbs := unfold ind in *;
  repeat match goal with
  | |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b)
  | H : context [Nat.eqb ?a ?b] |- _ => destruct (Nat.eqb_spec a b)
  end; lia.

(* ================================================================== *)
(* Part 2. Strings : the primitive comparison is String.compare, and   *)
(* the printed line orders as the word sequence.                       *)
(* ================================================================== *)

Lemma sapp_nil_r : forall s : string, String.append s EmptyString = s.
Proof. induction s as [|c s IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma sapp_assoc : forall s1 s2 s3 : string,
  String.append (String.append s1 s2) s3 = String.append s1 (String.append s2 s3).
Proof. induction s1 as [|c s IH]; intros; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma ascii_compare_refl : forall c, Ascii.compare c c = Eq.
Proof. intros c. unfold Ascii.compare. apply N.compare_refl. Qed.

Lemma scompare_refl : forall s, String.compare s s = Eq.
Proof. induction s as [|c s IH]; simpl; [reflexivity|rewrite ascii_compare_refl; exact IH]. Qed.

Lemma scompare_app_l : forall u s1 s2,
  String.compare (String.append u s1) (String.append u s2) = String.compare s1 s2.
Proof. induction u as [|c u IH]; intros; simpl; [reflexivity|rewrite ascii_compare_refl; apply IH]. Qed.

Definition tailok (t : string) : Prop := t = EmptyString \/ exists u, t = String "."%char u.

Lemma lowercase_tail : forall c b, lowercase (String c b) -> lowercase b.
Proof. intros c b H k d Hk. apply (H (S k) d). exact Hk. Qed.

Lemma cmp_lt_app : forall a b t1 t2, String.compare a b = Lt -> lowercase b -> tailok t1 ->
  String.compare (String.append a t1) (String.append b t2) = Lt.
Proof.
  induction a as [|c a IH]; intros b t1 t2 H Hb Ht.
  - destruct b as [|d b]; [discriminate|]. simpl.
    destruct Ht as [->|(u & ->)]; [reflexivity|]. simpl.
    assert (Hd := Hb 0%nat d eq_refl). unfold Ascii.compare.
    change (N_of_ascii "."%char) with 46%N.
    destruct (N.compare_spec 46 (N_of_ascii d)); [lia|reflexivity|lia].
  - destruct b as [|d b]; [discriminate|]. simpl in H |- *.
    destruct (Ascii.compare c d); [|reflexivity|discriminate].
    apply IH; [exact H|apply (lowercase_tail d b Hb)|exact Ht].
Qed.

Definition pfx (p : list string) : string :=
  fold_right (fun x acc => String.append x (String.append "." acc)) EmptyString p.

Definition tl_of (r : list string) : string :=
  match r with [] => EmptyString | _ :: _ => String.append "." (String.concat "." r) end.

Lemma concat_cons : forall a r, String.concat "." (a :: r) = String.append a (tl_of r).
Proof. intros a [|b r]; simpl; [rewrite sapp_nil_r; reflexivity|reflexivity]. Qed.

Lemma concat_app : forall p a r,
  String.concat "." (p ++ a :: r) = String.append (pfx p) (String.concat "." (a :: r)).
Proof.
  induction p as [|x p IH]; intros a r; [reflexivity|].
  change ((x :: p) ++ a :: r) with (x :: (p ++ a :: r)).
  rewrite concat_cons. simpl pfx. rewrite sapp_assoc. f_equal.
  destruct p as [|y p]; [reflexivity|].
  change (tl_of ((y :: p) ++ a :: r)) with (String.append "." (String.concat "." ((y :: p) ++ a :: r))).
  rewrite IH. reflexivity.
Qed.

Lemma text_lt : forall p a b r1 r2, String.compare a b = Lt -> lowercase b ->
  String.compare (text (p ++ a :: r1)) (text (p ++ b :: r2)) = Lt.
Proof.
  intros p a b r1 r2 H Hb. unfold text. rewrite !concat_app, scompare_app_l, !concat_cons.
  apply cmp_lt_app; auto. destruct r1; [left; reflexivity|right; eexists; reflexivity].
Qed.

(* the primitive string and the math string *)
Definition chr (c : ascii) : int := of_Z (Z.of_N (N_of_ascii c)).

Lemma chr_spec : forall c, (φ (chr c)) = Z.of_N (N_of_ascii c).
Proof.
  intros c. unfold chr. rewrite of_Z_spec. apply Z.mod_small.
  pose proof (N_ascii_bounded c). split; [lia|]. change wB with 9223372036854775808%Z. lia.
Qed.

Lemma list_compare_chr : forall L1 L2,
  list_compare PrimInt63.compare (map chr L1) (map chr L2)
  = String.compare (string_of_list_ascii L1) (string_of_list_ascii L2).
Proof.
  induction L1 as [|a L1 IH]; intros [|b L2]; simpl; try reflexivity.
  replace (PrimInt63.compare (chr a) (chr b)) with (Ascii.compare a b).
  - destruct (Ascii.compare a b); auto.
  - change (PrimInt63.compare (chr a) (chr b)) with (Uint63.compare (chr a) (chr b)).
    rewrite Uint63.compare_spec, !chr_spec, N2Z.inj_compare. reflexivity.
Qed.

Lemma length_list_ascii : forall w, List.length (list_ascii_of_string w) = String.length w.
Proof. induction w as [|c w IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma get_list_ascii : forall w k, (k < String.length w)%nat ->
  String.get k w = Some (nth k (list_ascii_of_string w) Ascii.zero).
Proof.
  induction w as [|c w IH]; intros k Hk; simpl in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma repr_str_len : forall (p : PrimString.string) (w : string), repr p w ->
  (φ (PrimString.length p)) = Z.of_nat (String.length w).
Proof. intros p w [H _]. symmetry. exact H. Qed.

Lemma repr_str_get : forall (p : PrimString.string) (w : string), repr p w ->
  forall k c, String.get k w = Some c -> (φ (PrimString.get p (of_Z (Z.of_nat k)))) = Z.of_N (N_of_ascii c).
Proof.
  intros p w [Hl Hg] k c Hk.
  assert (Hlt : (k < String.length w)%nat).
  { destruct (Nat.lt_ge_cases k (String.length w)) as [H|H]; [exact H|].
    exfalso. clear -Hk H. revert k Hk H. induction w as [|d w IH]; intros k Hk H; [discriminate|].
    destruct k; simpl in *; [lia|]. apply (IH k Hk). lia. }
  destruct (Hg k Hlt) as (c' & Hc' & Hr). rewrite Hk in Hc'. injection Hc' as <-.
  unfold repr, repr_uint in Hr. rewrite <- Hr. pose proof (to_Z_bounded (PrimString.get p (of_Z (Z.of_nat k)))). lia.
Qed.

Lemma to_list_repr : forall (p : PrimString.string) (w : string), repr p w ->
  PrimStringAxioms.to_list p = map chr (list_ascii_of_string w).
Proof.
  intros p w Hr. pose proof (repr_str_len p w Hr) as Hl.
  apply (nth_ext _ _ 0 0).
  - rewrite length_map, length_list_ascii, <- PrimStringAxioms.length_spec. lia.
  - intros k Hk. rewrite <- PrimStringAxioms.length_spec in Hk.
    assert (Hk' : (k < String.length w)%nat) by lia.
    assert (E1 : nth k (PrimStringAxioms.to_list p) 0 = PrimString.get p (of_Z (Z.of_nat k))).
    { rewrite PrimStringAxioms.get_spec. f_equal. rewrite of_Z_spec, Z.mod_small; [lia|].
      split; [lia|]. pose proof (to_Z_bounded (PrimString.length p)). lia. }
    etransitivity; [exact E1|]. rewrite (nth_indep _ 0 (chr Ascii.zero)) by (rewrite length_map, length_list_ascii; exact Hk').
    rewrite map_nth. apply to_Z_inj. rewrite chr_spec.
    apply (repr_str_get p w Hr). apply get_list_ascii. exact Hk'.
Qed.

Lemma repr_str_compare : forall (p q : PrimString.string) (w v : string), repr p w -> repr q v ->
  PrimString.compare p q = String.compare w v.
Proof.
  intros p q w v Hp Hq. rewrite PrimStringAxioms.compare_spec, (to_list_repr p w Hp), (to_list_repr q v Hq).
  rewrite list_compare_chr, !string_of_list_ascii_of_string. reflexivity.
Qed.

Lemma repr_str_inj : forall (p : PrimString.string) (w w' : string), repr p w -> repr p w' -> w = w'.
Proof.
  intros p w w' H1 H2. apply String.compare_eq_iff.
  rewrite <- (repr_str_compare p p w w' H1 H2). apply PString.compare_refl.
Qed.

(* ================================================================== *)
(* Part 3. The program.                                                *)
(* ================================================================== *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.
Elpi complexity sumbool.
Elpi complexity bdec.

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
Elpi complexity andb.
Arguments andb_cost : simpl never.
Elpi complexity splitc.
Arguments splitc_cost : simpl never.
Elpi complexity midp.
Arguments midp_cost : simpl never.

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
Elpi complexity init_loop.
Arguments init_loop_cost : simpl never.

(* word i <= word j *)
Definition cmpw (x : array PrimString.string) (i j : int) : bool :=
  match PrimString.compare x.[i] x.[j] with Gt => false | _ => true end.
Elpi complexity cmpw.
Arguments cmpw_cost : simpl never.

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
Elpi complexity merge_loop.
Arguments merge_loop_cost : simpl never.

(* dst[k..hi) := src[k..hi) *)
Fixpoint copy_loop (src dst : array int) (hi k : int) (H : Acc (Zwf 0) (pgap hi k)) {struct H}
    : array int :=
  match bdec (k <? hi) with
  | left Hk => copy_loop src dst.[k <- src.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Elpi complexity copy_loop.
Arguments copy_loop_cost : simpl never.

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
Elpi complexity msort.
Arguments msort_cost : simpl never.

Definition fst_ch (w : PrimString.string) : int := PrimString.get w 0.
Definition lst_ch (w : PrimString.string) : int := PrimString.get w (PrimString.length w - 1).
Elpi complexity fst_ch.
Arguments fst_ch_cost : simpl never.
Elpi complexity lst_ch.
Arguments lst_ch_cost : simpl never.

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
Elpi complexity build_loop.
Arguments build_loop_cost : simpl never.

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
Elpi complexity deg_loop.
Arguments deg_loop_cost : simpl never.

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
Elpi complexity chk_loop.
Arguments chk_loop_cost : simpl never.

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
Elpi complexity hier_loop.
Arguments hier_loop_cost : simpl never.

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
                    (PArray.make n ""%pstring) 0 (Zwf_well_founded 0 _) with
            | (res, cnt) => if cnt =? n then Some res else None
            end
        end
      end
    end
  end.
Elpi complexity negb.
Arguments negb_cost : simpl never.
Elpi complexity catenyms_impl.
Arguments catenyms_impl_cost : simpl never.

(* ================================================================== *)
(* Part 4. Proofs of the loops.                                        *)
(* ================================================================== *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma slength_bound : forall (t : array PrimString.string), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length PrimString.string t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make : forall (n : int) (v : int), ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H. pose proof (length_make int n v) as E. etransitivity; [exact E|].
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma slength_make : forall (n : int) (v : PrimString.string), ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H. pose proof (length_make PrimString.string n v) as E. etransitivity; [exact E|].
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Definition ix (k : nat) : int := of_Z (Z.of_nat k).
Definition nt (i : int) : nat := Z.to_nat (φ i).

Lemma ix_spec : forall k, (Z.of_nat k <= 4194304)%Z -> (φ (ix k)) = Z.of_nat k.
Proof. intros k H. unfold ix. rewrite of_Z_spec, wB_val. apply Z.mod_small. lia. Qed.

Lemma ix_nt : forall i, ix (nt i) = i.
Proof.
  intros i. unfold ix, nt. pose proof (to_Z_bounded i). rewrite Z2Nat.id by lia. apply of_to_Z.
Qed.

Lemma nt_spec : forall i, Z.of_nat (nt i) = (φ i).
Proof. intros i. unfold nt. pose proof (to_Z_bounded i). lia. Qed.

Lemma ix_inj : forall k l, (Z.of_nat k <= 4194304)%Z -> (Z.of_nat l <= 4194304)%Z -> ix k = ix l -> k = l.
Proof.
  intros k l Hk Hl E. apply (f_equal to_Z) in E. rewrite !ix_spec in E by lia. lia.
Qed.

Lemma ix_succ : forall i, ((φ i) < 4194304)%Z -> i + 1 = ix (S (nt i)).
Proof.
  intros i H. apply to_Z_inj. rewrite ix_spec by (pose proof (nt_spec i); lia).
  rewrite Nat2Z.inj_succ, nt_spec. sia.
Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (v : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. rewrite <- ltb_spec in H. exact (get_set_same int t i v H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.

Lemma sget_set_same : forall (t : array PrimString.string) (i : int) (v : PrimString.string),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. rewrite <- ltb_spec in H. exact (get_set_same PrimString.string t i v H). Qed.

Lemma sget_set_other : forall (t : array PrimString.string) (i j : int) (v : PrimString.string),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other PrimString.string t i j v H). Qed.

Lemma slength_set : forall (t : array PrimString.string) (i : int) (v : PrimString.string),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set PrimString.string t i v). Qed.

Lemma ix_neq : forall k l, (Z.of_nat k <= 4194304)%Z -> (Z.of_nat l <= 4194304)%Z -> k <> l -> ix k <> ix l.
Proof. intros k l Hk Hl H E. apply H. apply ix_inj; auto. Qed.

(* ------------------------------------------------------------------ *)
(* init_loop                                                           *)
(* ------------------------------------------------------------------ *)

Lemma init_loop_eq : forall a n k H, init_loop a n k H =
  match bdec (k <? n) with
  | left Hk => init_loop a.[k <- k] n (k + 1) (Acc_inv H (dec_step n k Hk))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_loop_spec : forall n z k (a : array int) H, pgap n k = z ->
  PArray.length a = n -> ((φ k) <= (φ n))%Z ->
  (forall j, ((φ j) < (φ k))%Z -> a.[j] = j) ->
  PArray.length (init_loop a n k H) = n /\
  forall j, ((φ j) < (φ n))%Z -> (init_loop a n k H).[j] = j.
Proof.
  intros n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k a H Hz Hl Hk Ha. rewrite init_loop_eq.
  destruct (bdec (k <? n)) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'.
    assert ((φ (k + 1)) = (φ k) + 1)%Z by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hc|reflexivity| |lia|].
    + rewrite alength_set. exact Hl.
    + intros j Hj. destruct (Z.eq_dec (φ j) (φ k)) as [E|E].
      * apply to_Z_inj in E. subst j. apply aget_set_same. rewrite Hl. exact Hc'.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity). apply Ha. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
    split; [exact Hl|]. intros j Hj. apply Ha. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the order on word indices                                           *)
(* ------------------------------------------------------------------ *)

Lemma merge_loop_eq : forall x src dst iend jend i j k H,
  merge_loop x src dst iend jend i j k H =
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
Proof. intros. destruct H. reflexivity. Qed.

Section Sort.

Variable x : array PrimString.string.

Definition le (u v : int) : Prop := cmpw x u v = true.

Lemma le_refl : forall u, le u u.
Proof. intros u. unfold le, cmpw. rewrite PString.compare_refl. reflexivity. Qed.

Lemma le_trans : forall u v w, le u v -> le v w -> le u w.
Proof.
  unfold le, cmpw. intros u v w H1 H2.
  destruct (PrimString.compare x.[u] x.[v]) eqn:E1; try discriminate;
  destruct (PrimString.compare x.[v] x.[w]) eqn:E2; try discriminate.
  - apply PString.compare_eq in E1, E2. rewrite E1, E2, PString.compare_refl. reflexivity.
  - apply PString.compare_eq in E1. rewrite E1, E2. reflexivity.
  - apply PString.compare_eq in E2. rewrite <- E2, E1. reflexivity.
  - rewrite (PString.compare_trans Lt _ _ _ E1 E2). reflexivity.
Qed.

Lemma le_total : forall u v, cmpw x u v = false -> le v u.
Proof.
  unfold le, cmpw. intros u v H.
  destruct (PrimString.compare x.[u] x.[v]) eqn:E1; try discriminate.
  rewrite PString.compare_antisym, E1. reflexivity.
Qed.

Local Open Scope nat_scope.

Definition seg (a : array int) (lo hi : nat) : list int :=
  map (fun k => a.[ix k]) (seq lo (hi - lo)).

Definition sorted (a : array int) (lo hi : nat) : Prop :=
  forall p q, lo <= p -> p <= q -> q < hi -> le a.[ix p] a.[ix q].

Lemma seg_split : forall a lo mid hi, lo <= mid <= hi ->
  seg a lo hi = seg a lo mid ++ seg a mid hi.
Proof.
  intros a lo mid hi H. unfold seg. rewrite <- map_app.
  replace (hi - lo) with ((mid - lo) + (hi - mid)) by lia.
  rewrite seq_app. f_equal. f_equal. f_equal. lia.
Qed.

Lemma seg_snoc : forall a lo k, lo <= k -> seg a lo (S k) = seg a lo k ++ [a.[ix k]].
Proof.
  intros a lo k H. rewrite (seg_split a lo k (S k)) by lia. f_equal.
  unfold seg. replace (S k - k) with 1 by lia. reflexivity.
Qed.

Lemma seg_ext : forall a b lo hi, (forall k, lo <= k < hi -> a.[ix k] = b.[ix k]) ->
  seg a lo hi = seg b lo hi.
Proof.
  intros a b lo hi H. unfold seg. apply map_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

Lemma seg_empty : forall a lo, seg a lo lo = [].
Proof. intros. unfold seg. rewrite Nat.sub_diag. reflexivity. Qed.

(* the invariant of the merge *)
Definition MInv (src dst : array int) (lo mid hi ni nj : nat) : Prop :=
  Permutation (seg dst lo (ni + nj - mid)) (seg src lo ni ++ seg src mid nj) /\
  sorted dst lo (ni + nj - mid) /\
  (forall p, lo <= p < ni + nj - mid ->
     (forall q, ni <= q < mid -> le dst.[ix p] src.[ix q]) /\
     (forall q, nj <= q < hi -> le dst.[ix p] src.[ix q])).

Lemma MInv_step : forall src dst lo mid hi ni nj c ni' nj',
  lo <= ni <= mid -> mid <= nj <= hi -> (Z.of_nat hi <= 4194303)%Z ->
  (Z.of_nat hi <= (φ (PArray.length dst)))%Z ->
  sorted src lo mid -> sorted src mid hi ->
  MInv src dst lo mid hi ni nj ->
  ((c = ni /\ ni < mid /\ ni' = S ni /\ nj' = nj /\ (nj < hi -> le src.[ix ni] src.[ix nj])) \/
   (c = nj /\ nj < hi /\ ni' = ni /\ nj' = S nj /\ (ni < mid -> le src.[ix nj] src.[ix ni]))) ->
  MInv src dst.[ix (ni + nj - mid) <- src.[ix c]] lo mid hi ni' nj'.
Proof.
  intros src dst lo mid hi ni nj c ni' nj' Hi Hj Hh Hl Hs1 Hs2 (HP & HS & HB) Hc.
  set (K := ni + nj - mid) in *.
  set (dst' := dst.[ix K <- src.[ix c]]).
  assert (HK : ni' + nj' - mid = S K) by (unfold K; lia).
  assert (Hlt : K < hi) by (unfold K; lia).
  assert (Hd'K : dst'.[ix K] = src.[ix c]).
  { unfold dst'. apply aget_set_same. rewrite ix_spec by lia. lia. }
  assert (Hd'p : forall p, p < K -> dst'.[ix p] = dst.[ix p]).
  { intros p Hp. unfold dst'. apply aget_set_other. apply ix_neq; lia. }
  assert (Hseg : seg dst' lo K = seg dst lo K).
  { apply seg_ext. intros k Hk. apply Hd'p. lia. }
  unfold MInv. rewrite HK. split; [|split].
  - rewrite seg_snoc by lia. rewrite Hseg, Hd'K.
    destruct Hc as [(-> & Hni & -> & -> & _)|(-> & Hnj & -> & -> & _)].
    + rewrite (seg_snoc src lo ni) by lia.
      eapply perm_trans; [apply Permutation_app_tail, HP|].
      rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
    + rewrite (seg_snoc src mid nj) by lia.
      eapply perm_trans; [apply Permutation_app_tail, HP|].
      rewrite <- !app_assoc. apply Permutation_refl.
  - intros p q Hp Hpq Hq.
    destruct (Nat.eq_dec q K) as [->|Hq'].
    + rewrite Hd'K. destruct (Nat.eq_dec p K) as [->|Hp'].
      * rewrite Hd'K. apply le_refl.
      * rewrite Hd'p by lia. destruct (HB p ltac:(lia)) as [HB1 HB2].
        destruct Hc as [(-> & Hni & _)|(-> & Hnj & _)]; [apply HB1|apply HB2]; lia.
    + rewrite !Hd'p by lia. apply HS; lia.
  - intros p Hp. destruct (Nat.eq_dec p K) as [->|Hp'].
    + rewrite Hd'K.
      destruct Hc as [(-> & Hni & -> & -> & Hc)|(-> & Hnj & -> & -> & Hc)]; split; intros q Hq.
      * apply Hs1; lia.
      * apply le_trans with src.[ix nj]; [apply Hc; lia|apply Hs2; lia].
      * apply le_trans with src.[ix ni]; [apply Hc; lia|apply Hs1; lia].
      * apply Hs2; lia.
    + rewrite Hd'p by lia. destruct (HB p ltac:(lia)) as [HB1 HB2].
      destruct Hc as [(-> & Hni & -> & -> & _)|(-> & Hnj & -> & -> & _)];
        split; intros q Hq; [apply HB1|apply HB2|apply HB1|apply HB2]; lia.
Qed.


Lemma merge_loop_spec : forall src lo mid hi, lo <= mid <= hi -> (Z.of_nat hi <= 4194303)%Z ->
  sorted src lo mid -> sorted src mid hi ->
  forall z i j k dst H, mg (ix mid) i (ix hi) j = z ->
  lo <= nt i <= mid -> mid <= nt j <= hi -> nt k = nt i + nt j - mid ->
  (Z.of_nat hi <= (φ (PArray.length dst)))%Z ->
  MInv src dst lo mid hi (nt i) (nt j) ->
  let r := merge_loop x src dst (ix mid) (ix hi) i j k H in
  PArray.length r = PArray.length dst /\ Permutation (seg r lo hi) (seg src lo hi) /\ sorted r lo hi.
Proof.
  intros src lo mid hi Hlmh Hh Hs1 Hs2 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j k dst H Hz Hi Hj Hk Hl HM. cbv zeta. rewrite merge_loop_eq.
  assert (Hmid : (φ (ix mid)) = Z.of_nat mid) by (apply ix_spec; lia).
  assert (Hhi : (φ (ix hi)) = Z.of_nat hi) by (apply ix_spec; lia).
  pose proof (nt_spec i) as Ei. pose proof (nt_spec j) as Ej. pose proof (nt_spec k) as Ek.
  assert (Hki : k = ix (nt i + nt j - mid)) by (rewrite <- Hk, ix_nt; reflexivity).
  assert (Hi1 : forall (Hc : (i <? ix mid)%uint63 = true), nt (i + 1)%uint63 = S (nt i)).
  { intros Hc. rewrite ltb_spec in Hc. unfold nt. sia. }
  assert (Hj1 : forall (Hc : (j <? ix hi)%uint63 = true), nt (j + 1)%uint63 = S (nt j)).
  { intros Hc. rewrite ltb_spec in Hc. unfold nt. sia. }
  assert (Hk1 : nt (k + 1)%uint63 = S (nt k)) by (unfold nt; pose proof (to_Z_bounded k); sia).
  assert (Hgi : i = ix (nt i)) by (rewrite ix_nt; reflexivity).
  assert (Hgj : j = ix (nt j)) by (rewrite ix_nt; reflexivity).
  destruct (bdec (i <? ix mid)%uint63) as [Hc1|Hc1].
  - pose proof Hc1 as Hc1'. rewrite ltb_spec in Hc1'.
    destruct (bdec (j <? ix hi)%uint63) as [Hc2|Hc2].
    + pose proof Hc2 as Hc2'. rewrite ltb_spec in Hc2'.
      destruct (cmpw x src.[i] src.[j]) eqn:Ecmp.
      * edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mi; exact Hc1) (i + 1)%uint63 j (k + 1)%uint63 dst.[k <- src.[i]] (Acc_inv H (dec_mi (ix mid) i (ix hi) j Hc1)) eq_refl) as (R1 & R2 & R3);
          [rewrite (Hi1 Hc1); lia|lia|rewrite (Hi1 Hc1), Hk1; lia|rewrite alength_set; exact Hl| |].
        { rewrite (Hi1 Hc1). replace (dst.[k <- src.[i]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt i)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt i)); auto; try lia.
          left. repeat split; try lia. intros _. rewrite <- Hgi, <- Hgj. exact Ecmp. }
        { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
      * edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mj; exact Hc2) i (j + 1)%uint63 (k + 1)%uint63 dst.[k <- src.[j]] (Acc_inv H (dec_mj (ix mid) i (ix hi) j Hc2)) eq_refl) as (R1 & R2 & R3);
          [lia|rewrite (Hj1 Hc2); lia|rewrite (Hj1 Hc2), Hk1; lia|rewrite alength_set; exact Hl| |].
        { rewrite (Hj1 Hc2). replace (dst.[k <- src.[j]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt j)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt j)); auto; try lia.
          right. repeat split; try lia. intros _. rewrite <- Hgi, <- Hgj. apply le_total. exact Ecmp. }
        { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Hc2.
      edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mi; exact Hc1) (i + 1)%uint63 j (k + 1)%uint63 dst.[k <- src.[i]] (Acc_inv H (dec_mi (ix mid) i (ix hi) j Hc1)) eq_refl) as (R1 & R2 & R3);
        [rewrite (Hi1 Hc1); lia|lia|rewrite (Hi1 Hc1), Hk1; lia|rewrite alength_set; exact Hl| |].
      { rewrite (Hi1 Hc1). replace (dst.[k <- src.[i]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt i)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt i)); auto; try lia; left; repeat split; lia. }
      { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc1.
    destruct (bdec (j <? ix hi)%uint63) as [Hc2|Hc2].
    + pose proof Hc2 as Hc2'. rewrite ltb_spec in Hc2'.
      edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mj; exact Hc2) i (j + 1)%uint63 (k + 1)%uint63 dst.[k <- src.[j]] (Acc_inv H (dec_mj (ix mid) i (ix hi) j Hc2)) eq_refl) as (R1 & R2 & R3);
        [lia|rewrite (Hj1 Hc2); lia|rewrite (Hj1 Hc2), Hk1; lia|rewrite alength_set; exact Hl| |].
      { rewrite (Hj1 Hc2). replace (dst.[k <- src.[j]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt j)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt j)); auto; try lia; right; repeat split; lia. }
      { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Hc2.
      assert (nt i = mid) by lia. assert (nt j = hi) by lia.
      destruct HM as (HP & HS & _). rewrite H0, H1 in HP, HS.
      replace (mid + hi - mid) with hi in HP, HS by lia.
      split; [reflexivity|split; [|exact HS]].
      rewrite (seg_split src lo mid hi) by lia. exact HP.
Qed.

End Sort.


Lemma merge_loop_spec2 : forall x src lo iend jend, (lo <= nt iend <= nt jend)%nat ->
  (Z.of_nat (nt jend) <= 4194303)%Z ->
  sorted x src lo (nt iend) -> sorted x src (nt iend) (nt jend) ->
  forall i j k dst H,
  (lo <= nt i <= nt iend)%nat -> (nt iend <= nt j <= nt jend)%nat -> nt k = (nt i + nt j - nt iend)%nat ->
  (Z.of_nat (nt jend) <= (φ (PArray.length dst)))%Z ->
  MInv x src dst lo (nt iend) (nt jend) (nt i) (nt j) ->
  let r := merge_loop x src dst iend jend i j k H in
  PArray.length r = PArray.length dst /\ Permutation (seg r lo (nt jend)) (seg src lo (nt jend)) /\
  sorted x r lo (nt jend).
Proof.
  intros x src lo iend jend.
  generalize (ix_nt iend) (ix_nt jend). generalize (nt iend) (nt jend). intros mid hi E1 E2.
  subst iend jend. intros. eapply merge_loop_spec; eauto.
Qed.

Lemma copy_loop_eq : forall src dst hi k H, copy_loop src dst hi k H =
  match bdec (k <? hi) with
  | left Hk => copy_loop src dst.[k <- src.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma copy_loop_spec : forall src hi z k dst H, pgap hi k = z ->
  ((φ hi) <= (φ (PArray.length dst)))%Z ->
  let r := copy_loop src dst hi k H in
  PArray.length r = PArray.length dst /\
  (forall j, ((φ k) <= (φ j) < (φ hi))%Z -> r.[j] = src.[j]) /\
  (forall j, ((φ j) < (φ k) \/ (φ hi) <= (φ j))%Z -> r.[j] = dst.[j]).
Proof.
  intros src hi z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k dst H Hz Hl. cbv zeta. rewrite copy_loop_eq.
  destruct (bdec (k <? hi)) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'.
    assert (Hk1 : ((φ (k + 1)) = (φ k) + 1)%Z) by sia.
    edestruct (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hc) (k + 1) dst.[k <- src.[k]]
                 (Acc_inv H (dec_step hi k Hc)) eq_refl) as (R1 & R2 & R3);
      [rewrite alength_set; exact Hl|].
    split; [rewrite R1, alength_set; reflexivity|split].
    + intros j Hj. destruct (Z.eq_dec (φ j) (φ k)) as [E|E].
      * rewrite R3 by lia. apply to_Z_inj in E. subst j. apply aget_set_same. lia.
      * apply R2. lia.
    + intros j Hj. rewrite R3 by lia. apply aget_set_other.
      intro F. subst j. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
    split; [reflexivity|split; [intros j Hj; lia|intros; reflexivity]].
Qed.

Lemma msort_eq : forall x a t lo hi H, msort x a t lo hi H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma sorted_ext : forall x a b lo hi, (forall k, (lo <= k < hi)%nat -> a.[ix k] = b.[ix k]) ->
  sorted x a lo hi -> sorted x b lo hi.
Proof. intros x a b lo hi E H p q Hp Hpq Hq. rewrite <- !E by lia. apply H; lia. Qed.

Lemma msort_spec : forall x z lo hi a t H a' t', pgap hi lo = z ->
  ((φ lo) <= (φ hi))%Z -> ((φ hi) <= (φ (PArray.length a)))%Z -> PArray.length t = PArray.length a ->
  msort x a t lo hi H = (a', t') ->
  PArray.length a' = PArray.length a /\ PArray.length t' = PArray.length t /\
  (forall j, ((φ j) < (φ lo) \/ (φ hi) <= (φ j))%Z -> a'.[j] = a.[j]) /\
  Permutation (seg a' (nt lo) (nt hi)) (seg a (nt lo) (nt hi)) /\
  sorted x a' (nt lo) (nt hi).
Proof.
  intros x z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi a t H a' t' Hz Hlh Hha Hta Hm. rewrite msort_eq in Hm.
  pose proof (alength_bound a) as Ba.
  pose proof (nt_spec lo) as Elo. pose proof (nt_spec hi) as Ehi.
  destruct (bdec (splitc lo hi)) as [Hs|Hs].
  - pose proof (splitc_spec lo hi Hs) as (S1 & S2 & S3 & S4).
    set (mid := midp lo hi) in *.
    pose proof (nt_spec mid) as Emid.
    revert Hm.
    lazymatch goal with |- context [msort x a t lo ?m ?P] => destruct (msort x a t lo m P) as [a1 t1] eqn:E1 end.
    destruct (IH _ ltac:(rewrite <- Hz; apply dec_ms1; exact Hs) lo mid a t _ a1 t1 eq_refl
               ltac:(lia) ltac:(lia) Hta E1) as (A1 & A2 & A3 & A4 & A5).
    lazymatch goal with |- context [msort x a1 t1 ?m hi ?P] => destruct (msort x a1 t1 m hi P) as [a2 t2] eqn:E2 end.
    destruct (IH _ ltac:(rewrite <- Hz; apply dec_ms2; exact Hs) mid hi a1 t1 _ a2 t2 eq_refl
               ltac:(lia) ltac:(rewrite A1; lia) ltac:(rewrite A2, A1; exact Hta) E2) as (B1 & B2 & B3 & B4 & B5).
    intros Hm. cbv zeta in Hm. injection Hm as <- <-.
    set (t3 := merge_loop x a2 t2 mid hi lo mid lo (Zwf_well_founded 0 _)).
    (* the left run is untouched by the second sort *)
    assert (L2 : forall k, (nt lo <= k < nt mid)%nat -> a2.[ix k] = a1.[ix k]).
    { intros k Hk. apply B3. rewrite ix_spec by lia. lia. }
    assert (R1 : forall k, (nt mid <= k < nt hi)%nat -> a1.[ix k] = a.[ix k]).
    { intros k Hk. apply A3. rewrite ix_spec by lia. lia. }
    assert (Hsl : sorted x a2 (nt lo) (nt mid)).
    { apply (sorted_ext x a1); [intros k Hk; symmetry; apply L2; exact Hk|exact A5]. }
    assert (HM : PArray.length t3 = PArray.length t2 /\
                 Permutation (seg t3 (nt lo) (nt hi)) (seg a2 (nt lo) (nt hi)) /\
                 sorted x t3 (nt lo) (nt hi)).
    { unfold t3.
      apply (merge_loop_spec2 x a2 (nt lo) mid hi); try lia.
      - exact Hsl.
      - exact B5.
      - unfold MInv.
        replace (nt lo + nt mid - nt mid)%nat with (nt lo) by lia.
        rewrite !seg_empty. split; [apply Permutation_refl|split].
        + intros p q Hp Hpq Hq. lia.
        + intros p Hp. lia. }
    destruct HM as (M1 & M2 & M3).
    destruct (copy_loop_spec t3 hi _ lo a2 (Zwf_well_founded 0 (pgap hi lo)) eq_refl
               ltac:(rewrite B1, A1; lia)) as (C1 & C2 & C3).
    set (r := copy_loop t3 a2 hi lo (Zwf_well_founded 0 (pgap hi lo))) in *.
    assert (Hr : forall k, (nt lo <= k < nt hi)%nat -> r.[ix k] = t3.[ix k]).
    { intros k Hk. apply C2. rewrite ix_spec by lia. lia. }
    split; [rewrite C1, B1, A1; reflexivity|].
    split; [rewrite M1, B2, A2; reflexivity|].
    split; [intros j Hj; rewrite C3, B3, A3 by lia; reflexivity|].
    split.
    + rewrite (seg_ext r t3) by exact Hr.
      eapply perm_trans; [exact M2|].
      rewrite (seg_split a2 (nt lo) (nt mid) (nt hi)) by lia.
      rewrite (seg_split a (nt lo) (nt mid) (nt hi)) by lia.
      rewrite (seg_ext a2 a1 (nt lo) (nt mid)) by exact L2.
      apply Permutation_app; [exact A4|].
      eapply perm_trans; [exact B4|].
      rewrite (seg_ext a1 a (nt mid) (nt hi)) by exact R1. apply Permutation_refl.
    + apply (sorted_ext x t3); [intros k Hk; symmetry; apply Hr; exact Hk|exact M3].
  - injection Hm as <- <-.
    unfold splitc in Hs. apply Bool.andb_false_iff in Hs.
    assert (Hsm : ((φ hi) - (φ lo) <= 1)%Z).
    { destruct Hs as [Hs|Hs]; rewrite <- Bool.not_true_iff_false, ltb_spec in Hs; [lia|].
      assert ((φ (hi - lo)) = (φ hi) - (φ lo))%Z by sia. lia. }
    split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [apply Permutation_refl|]]]].
    intros p q Hp Hpq Hq. assert (p = q) by lia. subst q. apply le_refl.
Qed.

Lemma aget_make : forall (n v i : int), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make int v n i). Qed.

Lemma sget_make : forall (n i : int) (v : PrimString.string), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make PrimString.string v n i). Qed.

(* the linked list of nodes from p *)
Fixpoint chain (nx : array int) (nI : int) (p : int) (l : list nat) : Prop :=
  match l with
  | [] => p = nI
  | e :: l' => p = ix e /\ chain nx nI nx.[p] l'
  end.

Lemma chain_upd : forall nx nI i v l p, (forall f, In f l -> ix f <> i) ->
  chain nx.[i <- v] nI p l <-> chain nx nI p l.
Proof.
  intros nx nI i v l. induction l as [|e l IH]; intros p Hl; simpl; [reflexivity|].
  split; intros [Hp Hc]; split; auto.
  - rewrite aget_set_other in Hc by (subst p; intro E; apply (Hl e (or_introl eq_refl)); symmetry; exact E).
    apply IH; [intros f Hf; apply Hl; right; exact Hf|exact Hc].
  - rewrite aget_set_other by (subst p; intro E; apply (Hl e (or_introl eq_refl)); symmetry; exact E).
    apply IH; [intros f Hf; apply Hl; right; exact Hf|exact Hc].
Qed.

Definition code (o : option ascii) : nat :=
  match o with Some c => N.to_nat (N_of_ascii c) | None => 0%nat end.

Lemma code_lt : forall o, (code o < 256)%nat.
Proof. intros [c|]; simpl; [pose proof (N_ascii_bounded c); lia|lia]. Qed.

Lemma code_inj : forall c d, code (Some c) = code (Some d) -> c = d.
Proof.
  intros c d H. simpl in H. rewrite <- (ascii_N_embedding c), <- (ascii_N_embedding d).
  f_equal. lia.
Qed.


Lemma skipn_cons_nth : forall (L : list nat) m, (m < List.length L)%nat ->
  skipn m L = nth m L 0%nat :: skipn (S m) L.
Proof.
  induction L as [|a L IH]; intros m Hm; simpl in Hm; [lia|].
  destruct m as [|m]; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma in_skipn_l : forall (L : list nat) k a, In a (skipn k L) -> In a L.
Proof. intros L k a H. rewrite <- (firstn_skipn k L). apply in_or_app. right. exact H. Qed.


Lemma cnt_le : forall f v l, (cnt f v l <= Z.of_nat (List.length l))%Z.
Proof.
  intros f v l. induction l as [|e l IH]; [unfold cnt; simpl; lia|].
  rewrite cnt_cons, length_cons. unfold ind. destruct (Nat.eqb (f e) v); lia.
Qed.

Lemma filter_len1_uniq : forall (p : nat -> bool) l a b, NoDup l -> List.length (filter p l) = 1%nat ->
  In a l -> p a = true -> In b l -> p b = true -> a = b.
Proof.
  intros p l a b Hn Hl Ha Hpa Hb Hpb.
  assert (Ha' : In a (filter p l)) by (apply filter_In; auto).
  assert (Hb' : In b (filter p l)) by (apply filter_In; auto).
  destruct (filter p l) as [|y [|y' r]]; simpl in Hl; try lia.
  destruct Ha' as [<-|[]]; destruct Hb' as [<-|[]]; reflexivity.
Qed.

Lemma filter_len1_ex : forall (p : nat -> bool) l, List.length (filter p l) = 1%nat ->
  exists a, In a l /\ p a = true.
Proof.
  intros p l Hl. destruct (filter p l) as [|y r] eqn:E; simpl in Hl; [lia|].
  exists y. apply filter_In. rewrite E. left. reflexivity.
Qed.

Lemma filter_len0 : forall (p : nat -> bool) l a, List.length (filter p l) = 0%nat ->
  In a l -> p a = false.
Proof.
  intros p l a Hl Ha. destruct (p a) eqn:E; [|reflexivity].
  assert (In a (filter p l)) by (apply filter_In; auto).
  destruct (filter p l); [destruct H|simpl in Hl; lia].
Qed.

Lemma filter_len_exact1 : forall (p : nat -> bool) l a, NoDup l -> In a l -> p a = true ->
  (forall c, In c l -> p c = true -> c = a) -> List.length (filter p l) = 1%nat.
Proof.
  intros p l a Hn Ha Hpa Hu.
  assert (Hnd : NoDup (filter p l)) by (apply NoDup_filter; exact Hn).
  assert (Hin : In a (filter p l)) by (apply filter_In; auto).
  destruct (filter p l) as [|y [|y' r]] eqn:E; [destruct Hin|reflexivity|].
  exfalso. assert (Hy : In y (filter p l)) by (rewrite E; left; reflexivity).
  assert (Hy' : In y' (filter p l)) by (rewrite E; right; left; reflexivity).
  apply filter_In in Hy as [Hy1 Hy2]. apply filter_In in Hy' as [Hy1' Hy2'].
  apply NoDup_cons_iff in Hnd as [Hnd _]. apply Hnd. left.
  rewrite (Hu y Hy1 Hy2), (Hu y' Hy1' Hy2'). reflexivity.
Qed.

Lemma filter_len_exact0 : forall (p : nat -> bool) l, (forall c, In c l -> p c = false) ->
  List.length (filter p l) = 0%nat.
Proof.
  intros p l H. induction l as [|a l IH]; [reflexivity|]. simpl.
  rewrite (H a (or_introl eq_refl)). apply IH. intros c Hc. apply H. right. exact Hc.
Qed.


Lemma filter_snoc : forall (p : nat -> bool) l a,
  Z.of_nat (List.length (filter p (l ++ [a]))) = (Z.of_nat (List.length (filter p l)) + if p a then 1 else 0)%Z.
Proof. intros. rewrite filter_app, length_app. simpl. destruct (p a); simpl; lia. Qed.

Lemma existsb_snoc : forall (p : nat -> bool) l a, existsb p (l ++ [a]) = orb (existsb p l) (p a).
Proof. intros. rewrite existsb_app. simpl. rewrite Bool.orb_false_r. reflexivity. Qed.


Lemma add1_small : forall a, ((φ a) < 4194304)%Z -> (φ (a + 1)) = ((φ a) + 1)%Z.
Proof. intros a H. rewrite add_spec, Z.mod_small; [reflexivity|]. change (φ 1) with 1%Z. rewrite wB_val. pose proof (to_Z_bounded a). lia. Qed.

Lemma int_ix : forall (a : int) k, (φ a) = Z.of_nat k -> (Z.of_nat k <= 4194304)%Z -> a = ix k.
Proof. intros a k H1 H2. apply to_Z_inj. rewrite ix_spec by exact H2. exact H1. Qed.


Lemma flat_map_filter_perm : forall (f : nat -> nat) (cs L : list nat), NoDup cs ->
  (forall e, In e L -> In (f e) cs) ->
  Permutation (flat_map (fun c => filter (fun e => Nat.eqb (f e) c) L) cs) L.
Proof.
  intros f cs L Hnd. induction L as [|e L IH]; intros HL.
  - clear HL. induction cs as [|c cs IHc]; [reflexivity|]. simpl. apply IHc.
    apply NoDup_cons_iff in Hnd. apply Hnd.
  - set (rem := fun c => filter (fun e0 => Nat.eqb (f e0) c) (e :: L)).
    change (flat_map (fun c => filter (fun e0 => Nat.eqb (f e0) c) (e :: L)) cs) with (flat_map rem cs).
    assert (Hx : rem (f e) = e :: filter (fun e0 => Nat.eqb (f e0) (f e)) L)
      by (unfold rem; simpl; rewrite Nat.eqb_refl; reflexivity).
    eapply perm_trans; [apply (flat_map_upd cs rem (f e) e _ Hnd (HL e (or_introl eq_refl)) Hx)|].
    apply perm_skip.
    rewrite (flat_map_ext _ (fun c => filter (fun e0 => Nat.eqb (f e0) c) L)).
    + apply IH. intros g Hg. apply HL. right. exact Hg.
    + intros c. unfold upd, rem. destruct (Nat.eqb_spec c (f e)) as [->|Hne]; [reflexivity|].
      simpl. destruct (Nat.eqb_spec (f e) c); [congruence|reflexivity].
Qed.

Lemma SS_filter : forall (R : nat -> nat -> Prop) (p : nat -> bool) l,
  StronglySorted R l -> StronglySorted R (filter p l).
Proof.
  intros R p l H. induction H as [|a l Hl IH Hf]; simpl; [constructor|].
  destruct (p a); [|exact IH]. constructor; [exact IH|].
  rewrite Forall_forall in Hf |- *. intros y Hy. apply filter_In in Hy as [Hy _]. apply Hf. exact Hy.
Qed.

Lemma SS_of_nth : forall (R : nat -> nat -> Prop) l,
  (forall p q, (p < q < List.length l)%nat -> R (nth p l 0%nat) (nth q l 0%nat)) -> StronglySorted R l.
Proof.
  intros R l. induction l as [|a l IH]; intros H; constructor.
  - apply IH. intros p q Hpq. apply (H (S p) (S q)). simpl. lia.
  - rewrite Forall_forall. intros y Hy. apply In_nth with (d := 0%nat) in Hy as (j & Hj & <-).
    apply (H 0%nat (S j)). simpl. lia.
Qed.

Lemma nth_map_seq : forall (A : Type) (f : nat -> A) k m d, (k < m)%nat -> nth k (map f (seq 0 m)) d = f k.
Proof.
  intros A f k m d H. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Section Main.

Variable W : list string.
Variable x : array PrimString.string.
Hypothesis HV : valid_input W.
Hypothesis HR : repr x W.

Local Open Scope nat_scope.

Definition n := List.length W.
Definition word (e : nat) : string := nth e W EmptyString.
Definition tlW (e : nat) : nat := code (String.get 0 (word e)).
Definition hdW (e : nat) : nat := code (String.get (String.length (word e) - 1) (word e)).
Definition nI : int := PArray.length x.

Lemma tlW_lt : forall e, tlW e < 256.
Proof. intros. apply code_lt. Qed.
Lemma hdW_lt : forall e, hdW e < 256.
Proof. intros. apply code_lt. Qed.

Lemma n_bounds : 3 <= n <= 1000.
Proof. destruct HV as [Hn _ _ _]. unfold len in Hn. unfold n. lia. Qed.

Lemma nI_spec : (φ nI) = Z.of_nat n.
Proof. destruct HR as [HL _]. symmetry. exact HL. Qed.

Lemma x_repr : forall e, e < n -> repr x.[ix e] (word e).
Proof.
  intros e He. destruct HR as [_ Hc]. destruct (Hc e He) as (m & Hm & Hr).
  unfold word. rewrite (nth_error_nth _ _ _ Hm). exact Hr.
Qed.

Lemma word_in : forall e, e < n -> In (word e) W.
Proof. intros e He. apply nth_In. exact He. Qed.

Lemma word_len : forall e, e < n -> 1 <= String.length (word e) <= 20.
Proof.
  intros e He. destruct HV as [_ Hw _ _]. rewrite Forall_forall in Hw.
  specialize (Hw _ (word_in e He)). unfold slen in Hw. lia.
Qed.

Lemma word_lower : forall e, e < n -> lowercase (word e).
Proof.
  intros e He. destruct HV as [_ _ Hw _]. rewrite Forall_forall in Hw. apply Hw, word_in, He.
Qed.

Lemma fst_ch_spec : forall e, e < n -> (φ (fst_ch x.[ix e])) = Z.of_nat (tlW e).
Proof.
  intros e He. pose proof (word_len e He) as Hl.
  unfold tlW. rewrite (get_list_ascii (word e) 0) by lia. simpl code.
  unfold fst_ch. pose proof (repr_str_get _ _ (x_repr e He) 0 _ (get_list_ascii (word e) 0 ltac:(lia))) as E.
  change (of_Z (Z.of_nat 0)) with 0%uint63 in E. rewrite E. lia.
Qed.

Lemma lst_ch_spec : forall e, e < n -> (φ (lst_ch x.[ix e])) = Z.of_nat (hdW e).
Proof.
  intros e He. pose proof (word_len e He) as Hl. unfold hdW.
  set (k := String.length (word e) - 1).
  rewrite (get_list_ascii (word e) k) by lia. simpl code.
  unfold lst_ch.
  replace (PrimString.length x.[ix e] - 1)%uint63 with (of_Z (Z.of_nat k)).
  - rewrite (repr_str_get _ _ (x_repr e He) k _ (get_list_ascii (word e) k ltac:(lia))). lia.
  - apply to_Z_inj. pose proof (repr_str_len _ _ (x_repr e He)) as E.
    rewrite of_Z_spec, sub_spec, E. change (φ 1) with 1%Z.
    unfold k. rewrite !Z.mod_small by (rewrite wB_val; lia). lia.
Qed.

Lemma fst_ch_ix : forall e, e < n -> fst_ch x.[ix e] = ix (tlW e).
Proof. intros e He. apply to_Z_inj. rewrite fst_ch_spec by exact He. rewrite ix_spec by (pose proof (tlW_lt e); lia). reflexivity. Qed.

Lemma lst_ch_ix : forall e, e < n -> lst_ch x.[ix e] = ix (hdW e).
Proof. intros e He. apply to_Z_inj. rewrite lst_ch_spec by exact He. rewrite ix_spec by (pose proof (hdW_lt e); lia). reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* build_loop                                                          *)
(* ------------------------------------------------------------------ *)

Lemma build_loop_eq : forall ord nn nxt head k H, build_loop x ord nn nxt head k H =
  match bdec (k <? nn)%uint63 with
  | left Hk =>
      let e := ord.[nn - 1 - k] in
      let c := fst_ch x.[e] in
      let h := head.[c] in
      build_loop x ord nn nxt.[e <- h] head.[c <- e] (k + 1) (Acc_inv H (dec_step nn k Hk))
  | right _ => (nxt, head)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_loop_spec : forall (ord : array int) (L : list nat),
  List.length L = n -> NoDup L -> (forall e, In e L -> e < n) ->
  (forall k, k < n -> ord.[ix k] = ix (nth k L 0)) ->
  forall z k nxt head H nxt' head', pgap nI k = z ->
  ((φ k) <= Z.of_nat n)%Z -> (φ (PArray.length nxt)) = Z.of_nat n -> (φ (PArray.length head)) = 256%Z ->
  (forall c, c < 256 -> chain nxt nI head.[ix c] (filter (fun e => Nat.eqb (tlW e) c) (skipn (n - nt k) L))) ->
  build_loop x ord nI nxt head k H = (nxt', head') ->
  (φ (PArray.length nxt')) = Z.of_nat n /\ (φ (PArray.length head')) = 256%Z /\
  forall c, c < 256 -> chain nxt' nI head'.[ix c] (filter (fun e => Nat.eqb (tlW e) c) L).
Proof.
  intros ord L HL HnL HbL Hord z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k nxt head H nxt' head' Hz Hk Hln Hlh Hch Hb.
  rewrite build_loop_eq in Hb. pose proof nI_spec as EN. pose proof n_bounds as NB.
  destruct (bdec (k <? nI)%uint63) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec, EN in Hc'.
    pose proof (nt_spec k) as Ek.
    set (m := n - 1 - nt k) in *.
    assert (Hm : (nI - 1 - k)%uint63 = ix m).
    { apply to_Z_inj. rewrite ix_spec by lia. unfold m. rewrite !sub_spec, EN. change (φ 1) with 1%Z.
      rewrite (Z.mod_small (_ - 1)) by (rewrite wB_val; lia). rewrite Z.mod_small by (rewrite wB_val; lia). lia. }
    set (e := nth m L 0) in *.
    assert (HeL : In e L) by (apply nth_In; lia).
    assert (Hen : e < n) by (apply HbL; exact HeL).
    rewrite Hm, (Hord m) in Hb by lia. fold e in Hb. cbv zeta in Hb.
    rewrite (fst_ch_ix e Hen) in Hb.
    assert (Hk1 : nt (k + 1)%uint63 = S (nt k)) by (unfold nt; sia).
    assert (Hsk : skipn (n - nt (k + 1)%uint63) L = e :: skipn (n - nt k) L).
    { rewrite Hk1. replace (n - S (nt k)) with m by lia. replace (n - nt k) with (S m) by lia.
      apply skipn_cons_nth. lia. }
    assert (Hnd : ~ In e (skipn (n - nt k) L)).
    { replace (n - nt k) with (S m) by lia.
      assert (HN : NoDup (skipn m L)) by (rewrite <- (firstn_skipn m L) in HnL; apply (NoDup_app_remove_l _ _ HnL)).
      rewrite (skipn_cons_nth L m) in HN by lia. apply NoDup_cons_iff in HN. apply HN. }
    assert (Hnot : forall c, forall f, In f (filter (fun e0 => Nat.eqb (tlW e0) c) (skipn (n - nt k) L)) -> ix f <> ix e).
    { intros c f Hf. apply filter_In in Hf as [Hf _].
      assert (Hfn : f < n) by (apply HbL; apply (in_skipn_l _ _ _ Hf)).
      apply ix_neq; try lia. intro E. subst f. contradiction. }
    assert (Hte : ix (tlW e) <> ix (tlW e) -> False) by auto.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hc|reflexivity| | | | |exact Hb].
    + assert ((φ (k + 1)) = (φ k) + 1)%Z by sia. lia.
    + rewrite alength_set. exact Hln.
    + rewrite alength_set. exact Hlh.
    + intros c Hc0. rewrite Hsk. simpl filter.
      pose proof (tlW_lt e) as Hte'.
      destruct (Nat.eqb_spec (tlW e) c) as [<-|Hne].
      * simpl. rewrite aget_set_same by (rewrite Hlh, ix_spec; lia).
        split; [reflexivity|].
        rewrite aget_set_same by (rewrite Hln, ix_spec; lia).
        apply chain_upd; [apply Hnot|]. apply Hch. exact Hc0.
      * rewrite aget_set_other by (apply ix_neq; lia).
        apply chain_upd; [apply Hnot|]. apply Hch. exact Hc0.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, EN in Hc. injection Hb as <- <-.
    split; [exact Hln|split; [exact Hlh|]].
    intros c Hc0. specialize (Hch c Hc0). replace (n - nt k) with 0 in Hch by (pose proof (nt_spec k); lia).
    exact Hch.
Qed.


(* ------------------------------------------------------------------ *)
(* deg_loop                                                            *)
(* ------------------------------------------------------------------ *)

Lemma deg_loop_eq : forall nn outd ind k H, deg_loop x nn outd ind k H =
  match bdec (k <? nn)%uint63 with
  | left Hk =>
      let a := fst_ch x.[k] in
      let b := lst_ch x.[k] in
      let oa := outd.[a] in
      let ib := ind.[b] in
      deg_loop x nn outd.[a <- (oa + 1)%uint63] ind.[b <- (ib + 1)%uint63] (k + 1)%uint63 (Acc_inv H (dec_step nn k Hk))
  | right _ => (outd, ind)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition dO (c : nat) : Z := cnt tlW c (seq 0 n).
Definition dI (c : nat) : Z := cnt hdW c (seq 0 n).

Lemma deg_loop_spec : forall z k outd ini H outd' ini', pgap nI k = z ->
  ((φ k) <= Z.of_nat n)%Z -> (φ (PArray.length outd)) = 256%Z -> (φ (PArray.length ini)) = 256%Z ->
  (forall c, c < 256 -> (φ (outd.[ix c])) = cnt tlW c (seq 0 (nt k)) /\ (φ (ini.[ix c])) = cnt hdW c (seq 0 (nt k))) ->
  deg_loop x nI outd ini k H = (outd', ini') ->
  (φ (PArray.length outd')) = 256%Z /\ (φ (PArray.length ini')) = 256%Z /\
  forall c, c < 256 -> (φ (outd'.[ix c])) = dO c /\ (φ (ini'.[ix c])) = dI c.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k outd ini H outd' ini' Hz Hk Ho Hi Hinv Hd.
  rewrite deg_loop_eq in Hd. pose proof nI_spec as EN.
  destruct (bdec (k <? nI)%uint63) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec, EN in Hc'.
    pose proof (nt_spec k) as Ek. set (e := nt k) in *.
    assert (He : e < n) by lia.
    assert (Hke : k = ix e) by (unfold e; rewrite ix_nt; reflexivity).
    replace (x.[k]) with (x.[ix e]) in Hd by (rewrite <- Hke; reflexivity).
    rewrite (fst_ch_ix e He), (lst_ch_ix e He) in Hd. cbv zeta in Hd.
    pose proof (tlW_lt e) as T1. pose proof (hdW_lt e) as T2.
    assert (Hk1 : nt (k + 1)%uint63 = S e) by (unfold e, nt; sia).
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hc|reflexivity| | | | |exact Hd].
    + assert ((φ (k + 1)) = (φ k) + 1)%Z by sia. lia.
    + rewrite alength_set. exact Ho.
    + rewrite alength_set. exact Hi.
    + intros c Hc0. rewrite Hk1, seq_S, !cnt_app, !cnt_cons. unfold cnt at 2 4. simpl filter. rewrite ?Nat.add_0_l.
      destruct (Hinv c Hc0) as [I1 I2].
      pose proof (cnt_le tlW c (seq 0 e)) as B1. pose proof (cnt_le hdW c (seq 0 e)) as B2.
      rewrite length_seq in B1, B2.
      split.
      * destruct (Nat.eqb_spec (tlW e) c) as [<-|Hne].
        -- rewrite aget_set_same by (rewrite Ho, ix_spec; lia).
           pose proof n_bounds. rewrite add1_small by lia. rewrite I1. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [|congruence] end. cbv iota beta. simpl Datatypes.length. lia.

        -- rewrite aget_set_other by (apply ix_neq; lia). rewrite I1. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [congruence|] end. cbv iota beta. simpl Datatypes.length. lia.
      * destruct (Nat.eqb_spec (hdW e) c) as [<-|Hne].
        -- rewrite aget_set_same by (rewrite Hi, ix_spec; lia).
           pose proof n_bounds. rewrite add1_small by lia. rewrite I2. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [|congruence] end. cbv iota beta. simpl Datatypes.length. lia.

        -- rewrite aget_set_other by (apply ix_neq; lia). rewrite I2. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [congruence|] end. cbv iota beta. simpl Datatypes.length. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, EN in Hc. injection Hd as <- <-.
    split; [exact Ho|split; [exact Hi|]].
    intros c Hc0. unfold dO, dI. replace n with (nt k) by (pose proof (nt_spec k); lia). apply Hinv. exact Hc0.
Qed.

(* ------------------------------------------------------------------ *)
(* chk_loop                                                            *)
(* ------------------------------------------------------------------ *)

Lemma chk_loop_eq : forall outd ini c plus minus sv bad H,
  chk_loop outd ini c plus minus sv bad H =
  match bdec (c <? 256)%uint63 with
  | left Hc =>
      let o := outd.[c] in
      let i := ini.[c] in
      (if (o =? i)%uint63 then chk_loop outd ini (c + 1) plus minus sv bad (Acc_inv H (dec_step 256 c Hc))
      else if (o =? i + 1)%uint63 then chk_loop outd ini (c + 1) (plus + 1) minus c bad (Acc_inv H (dec_step 256 c Hc))
      else if (i =? o + 1)%uint63 then chk_loop outd ini (c + 1) plus (minus + 1) sv bad (Acc_inv H (dec_step 256 c Hc))
      else chk_loop outd ini (c + 1) plus minus sv true (Acc_inv H (dec_step 256 c Hc)))%uint63
  | right _ => (plus, minus, sv, bad)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition dd (c : nat) : Z := (dO c - dI c)%Z.
Definition isP (c : nat) : bool := Z.eqb (dd c) 1.
Definition isM (c : nat) : bool := Z.eqb (dd c) (-1).
Definition isB (c : nat) : bool := orb (Z.ltb (dd c) (-1)) (Z.ltb 1 (dd c)).

Lemma dO_bound : forall c, (0 <= dO c <= 1000)%Z.
Proof. intros c. unfold dO. pose proof (cnt_le tlW c (seq 0 n)). pose proof (cnt_nonneg tlW c (seq 0 n)). rewrite length_seq in H. pose proof n_bounds. lia. Qed.
Lemma dI_bound : forall c, (0 <= dI c <= 1000)%Z.
Proof. intros c. unfold dI. pose proof (cnt_le hdW c (seq 0 n)). pose proof (cnt_nonneg hdW c (seq 0 n)). rewrite length_seq in H. pose proof n_bounds. lia. Qed.

Lemma chk_loop_spec : forall outd ini, (φ (PArray.length outd)) = 256%Z -> (φ (PArray.length ini)) = 256%Z ->
  (forall c, c < 256 -> (φ (outd.[ix c])) = dO c /\ (φ (ini.[ix c])) = dI c) ->
  forall z c plus minus sv bad H plus' minus' sv' bad', pgap 256 c = z ->
  ((φ c) <= 256)%Z ->
  (φ plus) = Z.of_nat (List.length (filter isP (seq 0 (nt c)))) ->
  (φ minus) = Z.of_nat (List.length (filter isM (seq 0 (nt c)))) ->
  bad = existsb isB (seq 0 (nt c)) ->
  ((1 <= (φ plus))%Z -> nt sv < nt c /\ isP (nt sv) = true) ->
  chk_loop outd ini c plus minus sv bad H = (plus', minus', sv', bad') ->
  (φ plus') = Z.of_nat (List.length (filter isP (seq 0 256))) /\
  (φ minus') = Z.of_nat (List.length (filter isM (seq 0 256))) /\
  bad' = existsb isB (seq 0 256) /\
  ((1 <= (φ plus'))%Z -> nt sv' < 256 /\ isP (nt sv') = true).
Proof.
  intros outd ini Ho Hi Hv z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros c plus minus sv bad H plus' minus' sv' bad' Hz Hc Hp Hm Hb Hs Hl.
  rewrite chk_loop_eq in Hl.
  destruct (bdec (c <? 256)%uint63) as [Hc0|Hc0].
  - pose proof Hc0 as Hc0'. rewrite ltb_spec in Hc0'. change (φ 256) with 256%Z in Hc0'.
    pose proof (nt_spec c) as Ec. set (v := nt c) in *.
    assert (Hcv : c = ix v) by (unfold v; rewrite ix_nt; reflexivity).
    destruct (Hv v ltac:(lia)) as [Ov Iv]. rewrite <- Hcv in Ov, Iv.
    pose proof (dO_bound v). pose proof (dI_bound v).
    assert (Hc1 : nt (c + 1)%uint63 = S v) by (unfold v, nt; sia).
    assert (Hseq : seq 0 (S v) = seq 0 v ++ [v]) by (apply seq_S).
    assert (Hlen1 : forall l, List.length (filter isP l) <= List.length l) by (intros; apply filter_length_le).
    pose proof (Hlen1 (seq 0 v)) as LP. rewrite length_seq in LP.
    assert (LM : List.length (filter isM (seq 0 v)) <= v) by (rewrite <- (length_seq v 0) at 2; apply filter_length_le).
    cbv zeta in Hl.
    assert (Hc1z : ((φ (c + 1)) = (φ c) + 1)%Z) by sia.
    assert (Hz' : Zwf 0 (pgap 256 (c + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hc0).
    assert (Hi1 : ((φ (ini.[c] + 1)) = (φ (ini.[c])) + 1)%Z) by (apply add1_small; rewrite Iv; pose proof (dI_bound v) as Bv; clear - Bv; lia).
    assert (Ho1 : ((φ (outd.[c] + 1)) = (φ (outd.[c])) + 1)%Z) by (apply add1_small; rewrite Ov; pose proof (dO_bound v) as Bv; clear - Bv; lia).
    assert (Hp1 : ((φ (plus + 1)) = (φ (plus)) + 1)%Z) by (apply add1_small; rewrite Hp; clear - LP Ec Hc0'; lia).
    assert (Hm1 : ((φ (minus + 1)) = (φ (minus)) + 1)%Z) by (apply add1_small; rewrite Hm; clear - LM Ec Hc0'; lia).
    destruct (outd.[c] =? ini.[c])%uint63 eqn:E1.
    { apply Uint63.eqb_spec in E1. assert (Hd : dd v = 0%Z) by (unfold dd; rewrite <- Ov, <- Iv, E1; lia).
      assert (HP : isP v = false) by (unfold isP; rewrite Hd; reflexivity).
      assert (HM : isM v = false) by (unfold isM; rewrite Hd; reflexivity).
      assert (HB : isB v = false) by (unfold isB; rewrite Hd; reflexivity).
      apply (IH _ Hz' (c + 1)%uint63 plus minus sv bad (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP. lia.
      - rewrite filter_snoc, HM. lia.
      - rewrite existsb_snoc, HB, Hb. symmetry. apply Bool.orb_false_r.
      - intros Hq. destruct (Hs Hq). split; [lia|assumption]. }
    destruct (outd.[c] =? ini.[c] + 1)%uint63 eqn:E2.
    { apply Uint63.eqb_spec in E2. apply Uint63.eqb_false_spec in E1.
      assert (Hd : dd v = 1%Z) by (unfold dd; rewrite <- Ov, <- Iv, E2, Hi1; lia).
      assert (HP : isP v = true) by (unfold isP; rewrite Hd; reflexivity).
      assert (HM : isM v = false) by (unfold isM; rewrite Hd; reflexivity).
      assert (HB : isB v = false) by (unfold isB; rewrite Hd; reflexivity).
      apply (IH _ Hz' (c + 1)%uint63 (plus + 1)%uint63 minus c bad (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP, Hp1. lia.
      - rewrite filter_snoc, HM. lia.
      - rewrite existsb_snoc, HB, Hb. symmetry. apply Bool.orb_false_r.
      - intros _. split; [lia|exact HP]. }
    destruct (ini.[c] =? outd.[c] + 1)%uint63 eqn:E3.
    { apply Uint63.eqb_spec in E3.
      assert (Hd : dd v = (-1)%Z) by (unfold dd; rewrite <- Ov, <- Iv, E3, Ho1; lia).
      assert (HP : isP v = false) by (unfold isP; rewrite Hd; reflexivity).
      assert (HM : isM v = true) by (unfold isM; rewrite Hd; reflexivity).
      assert (HB : isB v = false) by (unfold isB; rewrite Hd; reflexivity).
      apply (IH _ Hz' (c + 1)%uint63 plus (minus + 1)%uint63 sv bad (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP. lia.
      - rewrite filter_snoc, HM, Hm1. lia.
      - rewrite existsb_snoc, HB, Hb. symmetry. apply Bool.orb_false_r.
      - intros Hq. destruct (Hs Hq). split; [lia|assumption]. }
    { apply Uint63.eqb_false_spec in E1. apply Uint63.eqb_false_spec in E2. apply Uint63.eqb_false_spec in E3.
      assert (Hd1 : dd v <> 0%Z) by (unfold dd; rewrite <- Ov, <- Iv; intro F; apply E1, to_Z_inj; lia).
      assert (Hd2 : dd v <> 1%Z) by (unfold dd; rewrite <- Ov, <- Iv; intro F; apply E2, to_Z_inj; lia).
      assert (Hd3 : dd v <> (-1)%Z) by (unfold dd; rewrite <- Ov, <- Iv; intro F; apply E3, to_Z_inj; lia).
      assert (HP : isP v = false) by (unfold isP; apply Z.eqb_neq; exact Hd2).
      assert (HM : isM v = false) by (unfold isM; apply Z.eqb_neq; exact Hd3).
      assert (HB : isB v = true) by (unfold isB; apply Bool.orb_true_iff; lia).
      apply (IH _ Hz' (c + 1)%uint63 plus minus sv true (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP. lia.
      - rewrite filter_snoc, HM. lia.
      - rewrite existsb_snoc, HB. symmetry. apply Bool.orb_true_r.
      - intros Hq. destruct (Hs Hq). split; [lia|assumption]. }
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc0. change (φ 256) with 256%Z in Hc0.
    assert (Hv256 : nt c = 256) by (unfold nt; lia). rewrite Hv256 in Hp, Hm, Hb, Hs.
    injection Hl as <- <- <- <-. auto.
Qed.


(* ------------------------------------------------------------------ *)
(* hier_loop : it runs the iterative procedure of Part 1               *)
(* ------------------------------------------------------------------ *)

Lemma hier_loop_eq : forall nxt nn sI ptr stk sp q res cnt H,
  hier_loop x nxt nn sI ptr stk sp q res cnt H =
  let v := if (sp =? 0)%uint63 then sI else lst_ch x.[stk.[(sp - 1)%uint63]] in
  let p := ptr.[v] in
  match bdec (andb (p <? nn) (q <? nn))%uint63 with
  | left Hp =>
      let np := nxt.[p] in
      hier_loop x nxt nn sI ptr.[v <- np] stk.[sp <- p] (sp + 1)%uint63 (q + 1)%uint63 res cnt
        (Acc_inv H (dec_push nn q sp p Hp))
  | right _ =>
      match bdec (0 <? sp)%uint63 with
      | left Hs =>
          let e := stk.[(sp - 1)%uint63] in
          hier_loop x nxt nn sI ptr stk (sp - 1)%uint63 q res.[(nn - 1 - cnt)%uint63 <- x.[e]] (cnt + 1)%uint63
            (Acc_inv H (dec_pop nn q sp Hs))
      | right _ => (res, cnt)
      end
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Hier.

Variable nxt : array int.
Variable s : nat.
Hypothesis Hs256 : s < 256.

Definition sI : int := ix s.

Definition corr (ptr stk : array int) (sp q : int) (res : array PrimString.string) (cnt : int)
    (rem : nat -> list nat) (K O : list nat) : Prop :=
  (φ (PArray.length ptr)) = 256%Z /\
  (forall c, c < 256 -> chain nxt nI ptr.[ix c] (rem c)) /\
  Inv tlW rem /\
  (φ (PArray.length stk)) = Z.of_nat n /\
  (φ sp) = Z.of_nat (List.length K) /\
  (forall i, i < List.length K -> stk.[ix i] = ix (nth (List.length K - 1 - i) K 0)) /\
  (φ (PArray.length res)) = Z.of_nat n /\
  (φ cnt) = Z.of_nat (List.length O) /\
  (forall i, i < List.length O -> res.[ix (n - 1 - i)] = x.[ix (nth (List.length O - 1 - i) O 0)]) /\
  (φ q) = Z.of_nat (List.length K + List.length O) /\
  List.length K + List.length O + List.length (E 256 rem) = n /\
  (forall e, In e (E 256 rem) -> e < n) /\
  (forall e, In e K -> e < n).

Lemma cur_lt : forall K, cur hdW s K < 256.
Proof. intros [|e K]; simpl; [exact Hs256|apply hdW_lt]. Qed.

Lemma corr_v : forall ptr stk sp q res cnt rem K O, corr ptr stk sp q res cnt rem K O ->
  (if (sp =? 0)%uint63 then sI else lst_ch x.[stk.[(sp - 1)%uint63]]) = ix (cur hdW s K).
Proof.
  intros ptr stk sp q res cnt rem K O (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  pose proof n_bounds as NB.
  destruct K as [|e K'].
  - simpl in C5. assert (sp = 0%uint63) as -> by (apply to_Z_inj; exact C5). reflexivity.
  - cbn [Datatypes.length] in *. assert (Hsp : (sp =? 0)%uint63 = false) by (apply Uint63.eqb_false_spec; intro F; subst sp; change (φ 0) with 0%Z in C5; lia).
    rewrite Hsp. assert (Hs1 : (sp - 1)%uint63 = ix (List.length K')).
    { apply int_ix; [|lia]. rewrite sub_spec, C5. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|rewrite wB_val; lia]. }
    rewrite Hs1, C6 by lia. replace (S (List.length K') - 1 - List.length K') with 0 by lia.
    simpl. apply lst_ch_ix. apply C13. left. reflexivity.
Qed.

Lemma hier_sim : forall rem K O rem2 K2 O2, mstar hdW s rem K O rem2 K2 O2 ->
  forall ptr stk sp q res cnt H, corr ptr stk sp q res cnt rem K O ->
  exists ptr' stk' sp' q' res' cnt' H', corr ptr' stk' sp' q' res' cnt' rem2 K2 O2 /\
  hier_loop x nxt nI sI ptr stk sp q res cnt H = hier_loop x nxt nI sI ptr' stk' sp' q' res' cnt' H'.
Proof.
  intros rem K O rem2 K2 O2 HM.
  induction HM as [rem K O|rem K O e r rem2 K2 O2 Hx HM IH|rem e K O rem2 K2 O2 Hx HM IH];
    intros ptr stk sp q res cnt H HC.
  - exists ptr, stk, sp, q, res, cnt, H. split; [exact HC|reflexivity].
  - pose proof (corr_v _ _ _ _ _ _ _ _ _ HC) as Hv.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof n_bounds as NB. pose proof (cur_lt K) as Hcl.
    set (vv := cur hdW s K) in *.
    pose proof (C2 vv Hcl) as Hch0. rewrite Hx in Hch0. simpl in Hch0. destruct Hch0 as [Hpv Hch]. rewrite Hpv in Hch.
    assert (HeE : In e (E 256 rem)) by (apply (E_In 256 tlW tlW_lt rem vv); [exact C3|rewrite Hx; left; reflexivity]).
    assert (Hen : e < n) by (apply C12; exact HeE).
    assert (HP1 : Permutation (E 256 rem) (e :: E 256 (upd rem vv r))) by (apply E_upd; [exact Hx|exact Hcl]).
    pose proof (Permutation_length HP1) as HL1. simpl in HL1.
    rewrite hier_loop_eq. cbv zeta. rewrite Hv.
    destruct (bdec (andb (ptr.[ix vv] <? nI) (q <? nI))%uint63) as [Hb|Hb].
    2:{ exfalso. rewrite Hpv in Hb. apply Bool.andb_false_iff in Hb as [Hb|Hb];
        rewrite <- Bool.not_true_iff_false, ltb_spec in Hb; apply Hb; rewrite nI_spec;
        [rewrite ix_spec by lia; lia|rewrite C10; lia]. }
    assert (Hsp : sp = ix (List.length K)) by (apply int_ix; [exact C5|lia]).
    edestruct (IH (ptr.[ix vv <- nxt.[ptr.[ix vv]]]) (stk.[sp <- ptr.[ix vv]]) (sp + 1)%uint63 (q + 1)%uint63 res cnt)
      as (ptr' & stk' & sp' & q' & res' & cnt' & H' & HC' & Heq).
    2:{ exists ptr', stk', sp', q', res', cnt', H'. split; [exact HC'|]. rewrite <- Heq. reflexivity. }
    rewrite Hpv. unfold corr.
    split; [rewrite alength_set; exact C1|].
    split.
    { intros c Hc. unfold upd. destruct (Nat.eqb_spec c vv) as [->|Hne].
      - rewrite aget_set_same by (rewrite C1, ix_spec; lia). exact Hch.
      - rewrite aget_set_other by (apply ix_neq; lia). apply C2. exact Hc. }
    split; [apply (Inv_upd tlW rem vv e r C3 Hx)|].
    split; [rewrite alength_set; exact C4|].
    split; [cbn [Datatypes.length]; rewrite add1_small; [rewrite C5; lia|rewrite C5; lia]|].
    split.
    { intros i Hi. cbn [Datatypes.length] in Hi. rewrite Hsp. destruct (Nat.eq_dec i (List.length K)) as [->|Hne].
      - rewrite aget_set_same by (rewrite C4, ix_spec; lia).
        cbn [Datatypes.length]. replace (S (List.length K) - 1 - List.length K) with 0 by lia. reflexivity.
      - rewrite aget_set_other by (apply ix_neq; lia). rewrite C6 by lia.
        cbn [Datatypes.length]. replace (S (List.length K) - 1 - i) with (S (List.length K - 1 - i)) by lia. reflexivity. }
    split; [exact C7|].
    split; [exact C8|].
    split; [exact C9|].
    split; [cbn [Datatypes.length]; rewrite add1_small; [rewrite C10; lia|rewrite C10; lia]|].
    split; [cbn [Datatypes.length]; lia|].
    split; [intros f Hf; apply C12; apply (Permutation_in _ (Permutation_sym HP1)); right; exact Hf|].
    intros f [<-|Hf]; [exact Hen|apply C13; exact Hf].
  - pose proof (corr_v _ _ _ _ _ _ _ _ _ HC) as Hv.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof n_bounds as NB. simpl cur in Hv.
    pose proof (hdW_lt e) as Hhe.
    pose proof (C2 (hdW e) Hhe) as Hpv. rewrite Hx in Hpv. simpl in Hpv.
    cbn [Datatypes.length] in *.
    assert (Hen : e < n) by (apply C13; left; reflexivity).
    rewrite hier_loop_eq. cbv zeta. rewrite Hv, Hpv.
    destruct (bdec (andb (nI <? nI) (q <? nI))%uint63) as [Hb|Hb].
    { exfalso. apply andb_prop in Hb as [Hb _]. rewrite ltb_spec in Hb. lia. }
    destruct (bdec (0 <? sp)%uint63) as [Hs|Hs].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hs. change (φ 0) with 0%Z in Hs. lia. }
    assert (Hs1 : (sp - 1)%uint63 = ix (List.length K)).
    { apply int_ix; [|lia]. rewrite sub_spec, C5. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|rewrite wB_val; lia]. }
    assert (Hse : stk.[(sp - 1)%uint63] = ix e).
    { rewrite Hs1, C6 by lia. cbn [Datatypes.length]. replace (S (List.length K) - 1 - List.length K) with 0 by lia. reflexivity. }
    assert (Hci : (nI - 1 - cnt)%uint63 = ix (n - 1 - List.length O)).
    { apply int_ix; [|lia]. rewrite !sub_spec, nI_spec, C8. change (φ 1) with 1%Z.
      rewrite (Z.mod_small (_ - 1)) by (rewrite wB_val; lia). rewrite Z.mod_small by (rewrite wB_val; lia). lia. }
    edestruct (IH ptr stk (sp - 1)%uint63 q (res.[(nI - 1 - cnt)%uint63 <- x.[stk.[(sp - 1)%uint63]]]) (cnt + 1)%uint63)
      as (ptr' & stk' & sp' & q' & res' & cnt' & H' & HC' & Heq).
    2:{ exists ptr', stk', sp', q', res', cnt', H'. split; [exact HC'|]. rewrite <- Heq. reflexivity. }
    rewrite Hse, Hci. unfold corr.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [rewrite Hs1, ix_spec by lia; reflexivity|].
    split.
    { intros i Hi. rewrite C6 by lia. cbn [Datatypes.length]. replace (S (List.length K) - 1 - i) with (S (List.length K - 1 - i)) by lia. reflexivity. }
    split; [rewrite slength_set; exact C7|].
    split; [cbn [Datatypes.length]; rewrite add1_small; [rewrite C8; lia|rewrite C8; lia]|].
    split.
    { intros i Hi. cbn [Datatypes.length] in Hi. destruct (Nat.eq_dec i (List.length O)) as [->|Hne].
      - rewrite sget_set_same by (rewrite C7, ix_spec; lia).
        cbn [Datatypes.length]. replace (S (List.length O) - 1 - List.length O) with 0 by lia. reflexivity.
      - rewrite sget_set_other by (apply ix_neq; lia). rewrite C9 by lia.
        cbn [Datatypes.length]. replace (S (List.length O) - 1 - i) with (S (List.length O - 1 - i)) by lia. reflexivity. }
    split; [cbn [Datatypes.length]; rewrite C10; lia|].
    split; [cbn [Datatypes.length]; lia|].
    split; [exact C12|].
    intros f Hf. apply C13. right. exact Hf.
Qed.

Lemma hier_stop : forall ptr stk sp q res cnt rem O H, corr ptr stk sp q res cnt rem [] O ->
  rem s = [] -> hier_loop x nxt nI sI ptr stk sp q res cnt H = (res, cnt).
Proof.
  intros ptr stk sp q res cnt rem O H HC Hs.
  pose proof (corr_v _ _ _ _ _ _ _ _ _ HC) as Hv. simpl cur in Hv.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  pose proof (C2 s Hs256) as Hpv. rewrite Hs in Hpv. simpl in Hpv.
  rewrite hier_loop_eq. cbv zeta. rewrite Hv, Hpv.
  destruct (bdec (andb (nI <? nI) (q <? nI))%uint63) as [Hb|Hb].
  { exfalso. apply andb_prop in Hb as [Hb _]. rewrite ltb_spec in Hb. lia. }
  destruct (bdec (0 <? sp)%uint63) as [Hs'|Hs'].
  { exfalso. rewrite ltb_spec in Hs'. simpl in C5. change (φ 0) with 0%Z in Hs'. lia. }
  reflexivity.
Qed.

End Hier.


(* ------------------------------------------------------------------ *)
(* the math side of the answer                                         *)
(* ------------------------------------------------------------------ *)

Lemma W_map : W = map word (seq 0 n).
Proof.
  apply (nth_ext _ _ EmptyString EmptyString).
  - rewrite length_map, length_seq. reflexivity.
  - intros k Hk. rewrite nth_map_seq by exact Hk. reflexivity.
Qed.

Lemma catenym_iff : forall a b, a < n -> b < n ->
  (forms_catenym (word a) (word b) <-> hdW a = tlW b).
Proof.
  intros a b Ha Hb. pose proof (word_len a Ha). pose proof (word_len b Hb).
  unfold forms_catenym, hdW, tlW.
  rewrite (get_list_ascii (word a) (String.length (word a) - 1)) by lia.
  rewrite (get_list_ascii (word b) 0) by lia.
  split; [intros E; rewrite E; reflexivity|intros E; f_equal; apply code_inj; exact E].
Qed.

Lemma chain_of_trail : forall v T y, trail tlW hdW v T y ->
  forall j, S j < List.length T -> hdW (nth j T 0) = tlW (nth (S j) T 0).
Proof.
  intros v T y H. induction H as [v|v e l w He Hl IH]; intros j Hj; cbn [Datatypes.length] in Hj; [lia|].
  destruct j as [|j].
  - destruct l as [|f l]; cbn [Datatypes.length] in Hj; [lia|].
    apply trail_cons_inv in Hl as [Hf _]. simpl. symmetry. exact Hf.
  - simpl. apply IH. lia.
Qed.

Lemma trail_of_chain : forall T, T <> [] ->
  (forall j, S j < List.length T -> hdW (nth j T 0) = tlW (nth (S j) T 0)) ->
  exists y, trail tlW hdW (tlW (nth 0 T 0)) T y.
Proof.
  induction T as [|e T IH]; intros Hne H; [congruence|].
  destruct T as [|f T].
  - exists (hdW e). constructor; [reflexivity|constructor].
  - destruct (IH ltac:(discriminate)) as (y & Hy).
    + intros j Hj. apply (H (S j)). cbn [Datatypes.length] in *. lia.
    + exists y. constructor; [reflexivity|]. simpl.
      replace (hdW e) with (tlW f) by (symmetry; apply (H 0); cbn [Datatypes.length]; lia). exact Hy.
Qed.

(* an answer is a trail through all the word indices *)
Lemma answer_trail : forall c, is_answer W c ->
  exists T, c = map word T /\ Permutation (seq 0 n) T /\ T <> [] /\
  exists y, trail tlW hdW (tlW (nth 0 T 0)) T y.
Proof.
  intros c [[Hl Hch] HP]. rewrite W_map in HP.
  destruct (Permutation_map_inv _ _ HP) as (T & -> & HT).
  pose proof (Permutation_length HT) as HTl. rewrite length_seq in HTl.
  assert (HTb : forall e, In e T -> e < n) by (intros e He; apply (Permutation_in _ (Permutation_sym HT)) in He; apply in_seq in He; lia).
  pose proof n_bounds.
  exists T. split; [reflexivity|]. split; [exact HT|].
  split; [destruct T; [simpl in HTl; lia|discriminate]|].
  apply trail_of_chain; [destruct T; [simpl in HTl; lia|discriminate]|].
  intros j Hj. rewrite length_map in Hch.
  specialize (Hch j Hj).
  rewrite (nth_indep _ EmptyString (word 0)), map_nth in Hch by (rewrite length_map; lia).
  rewrite (nth_indep _ EmptyString (word 0)), map_nth in Hch by (rewrite length_map; lia).
  apply catenym_iff in Hch; [exact Hch| |]; apply HTb, nth_In; lia.
Qed.

Definition wlt (a b : nat) : Prop := PrimString.compare x.[ix a] x.[ix b] = Lt.

Lemma lexle_text : forall P T, lexle wlt P T -> (forall e, In e P -> e < n) -> (forall e, In e T -> e < n) ->
  String.compare (text (map word P)) (text (map word T)) <> Gt.
Proof.
  intros P T [<-|(p & a & b & r1 & r2 & E1 & E2 & Hab)] HP HT.
  - rewrite scompare_refl. discriminate.
  - subst P T. rewrite !map_app. simpl.
    assert (Ha : a < n) by (apply HP; apply in_or_app; right; left; reflexivity).
    assert (Hb : b < n) by (apply HT; apply in_or_app; right; left; reflexivity).
    unfold wlt in Hab. rewrite (repr_str_compare _ _ _ _ (x_repr a Ha) (x_repr b Hb)) in Hab.
    rewrite (text_lt _ _ _ _ _ Hab (word_lower b Hb)). discriminate.
Qed.

Lemma word_inj : forall a b, a < n -> b < n -> word a = word b -> a = b.
Proof.
  intros a b Ha Hb E. destruct HV as [_ _ _ Hnd].
  apply (proj1 (NoDup_nth W EmptyString) Hnd a b Ha Hb E).
Qed.

Lemma dd_dg : forall v, dd v = dg tlW hdW (seq 0 n) v.
Proof. reflexivity. Qed.

Lemma dd_out : forall v, 256 <= v -> dd v = 0%Z.
Proof.
  intros v Hv. unfold dd, dO, dI. rewrite !cnt_none; [reflexivity| |];
    intros e _; [pose proof (hdW_lt e)|pose proof (tlW_lt e)]; lia.
Qed.

(* the degree check accepts every input with an Euler trail *)
Lemma D_check : forall s t, D tlW hdW (seq 0 n) s t ->
  existsb isB (seq 0 256) = false /\
  List.length (filter isP (seq 0 256)) = List.length (filter isM (seq 0 256)) /\
  List.length (filter isP (seq 0 256)) <= 1.
Proof.
  intros s t HD.
  assert (Hd : forall v, dd v = (ind (Nat.eqb v s) - ind (Nat.eqb v t))%Z) by (intros v; rewrite dd_dg; apply HD).
  split.
  { apply Bool.not_true_iff_false. intro H. apply existsb_exists in H as (v & _ & Hv).
    unfold isB in Hv. rewrite Hd in Hv. apply Bool.orb_true_iff in Hv. rewrite !Z.ltb_lt in Hv. revert Hv. eqbs. }
  destruct (Nat.eq_dec s t) as [<-|Hst].
  - assert (H0 : forall v, dd v = 0%Z) by (intros v; rewrite Hd; eqbs).
    rewrite !filter_len_exact0; [lia| |]; intros c _; [unfold isM|unfold isP]; rewrite H0; reflexivity.
  - assert (Hs : dd s = 1%Z) by (rewrite Hd; eqbs).
    assert (Ht : dd t = (-1)%Z) by (rewrite Hd; eqbs).
    assert (Hs2 : s < 256) by (destruct (Nat.lt_ge_cases s 256); [assumption|rewrite dd_out in Hs by assumption; lia]).
    assert (Ht2 : t < 256) by (destruct (Nat.lt_ge_cases t 256); [assumption|rewrite dd_out in Ht by assumption; lia]).
    rewrite (filter_len_exact1 isP _ s), (filter_len_exact1 isM _ t); try lia.
    + apply seq_NoDup.
    + apply in_seq. lia.
    + unfold isM. rewrite Ht. reflexivity.
    + intros c _ Hc. unfold isM in Hc. apply Z.eqb_eq in Hc. rewrite Hd in Hc. revert Hc. eqbs.
    + apply seq_NoDup.
    + apply in_seq. lia.
    + unfold isP. rewrite Hs. reflexivity.
    + intros c _ Hc. unfold isP in Hc. apply Z.eqb_eq in Hc. rewrite Hd in Hc. revert Hc. eqbs.
Qed.

(* and what it accepts has one *)
Lemma check_D1 : forall sv, existsb isB (seq 0 256) = false ->
  List.length (filter isP (seq 0 256)) = 1 -> List.length (filter isM (seq 0 256)) = 1 ->
  sv < 256 -> isP sv = true -> exists t, D tlW hdW (seq 0 n) sv t.
Proof.
  intros sv HB HP HM Hsv Hp.
  destruct (filter_len1_ex isM _ HM) as (t & Ht & Hmt).
  exists t. intros v. rewrite <- dd_dg.
  unfold isP in Hp. unfold isM in Hmt. apply Z.eqb_eq in Hp, Hmt.
  apply in_seq in Ht.
  destruct (Nat.lt_ge_cases v 256) as [Hv|Hv]; [|rewrite dd_out by exact Hv; eqbs].
  assert (HvB : isB v = false).
  { destruct (isB v) eqn:E; [|reflexivity]. exfalso.
    assert (existsb isB (seq 0 256) = true) by (apply existsb_exists; exists v; split; [apply in_seq; lia|exact E]).
    congruence. }
  unfold isB in HvB. apply Bool.orb_false_iff in HvB as [B1 B2]. rewrite Z.ltb_ge in B1, B2.
  assert (U1 : dd v = 1%Z -> v = sv).
  { intros E. apply (filter_len1_uniq isP (seq 0 256) v sv (seq_NoDup _ _) HP);
      [apply in_seq; lia|unfold isP; rewrite E; reflexivity|apply in_seq; lia|unfold isP; rewrite Hp; reflexivity]. }
  assert (U2 : dd v = (-1)%Z -> v = t).
  { intros E. apply (filter_len1_uniq isM (seq 0 256) v t (seq_NoDup _ _) HM);
      [apply in_seq; lia|unfold isM; rewrite E; reflexivity|apply in_seq; lia|unfold isM; rewrite Hmt; reflexivity]. }
  assert (dd v = 1 \/ dd v = 0 \/ dd v = -1)%Z as [E|[E|E]] by lia.
  - pose proof (U1 E). subst v. destruct (Nat.eqb_spec sv t) as [E'|E']; [subst t; lia|]. rewrite E. eqbs.
  - rewrite E. destruct (Nat.eqb_spec v sv) as [->|H1]; [lia|]. destruct (Nat.eqb_spec v t) as [->|H2]; [lia|].
    unfold ind. lia.
  - pose proof (U2 E). subst v. destruct (Nat.eqb_spec t sv) as [E'|E']; [subst t; lia|]. rewrite E. eqbs.
Qed.

Lemma check_D0 : existsb isB (seq 0 256) = false ->
  List.length (filter isP (seq 0 256)) = 0 -> List.length (filter isM (seq 0 256)) = 0 ->
  forall s, D tlW hdW (seq 0 n) s s.
Proof.
  intros HB HP HM s v. rewrite <- dd_dg.
  destruct (Nat.lt_ge_cases v 256) as [Hv|Hv]; [|rewrite dd_out by exact Hv; eqbs].
  assert (HvB : isB v = false).
  { destruct (isB v) eqn:E; [|reflexivity]. exfalso.
    assert (existsb isB (seq 0 256) = true) by (apply existsb_exists; exists v; split; [apply in_seq; lia|exact E]).
    congruence. }
  pose proof (filter_len0 isP _ v HP ltac:(apply in_seq; lia)) as H1.
  pose proof (filter_len0 isM _ v HM ltac:(apply in_seq; lia)) as H2.
  unfold isB in HvB. apply Bool.orb_false_iff in HvB as [B1 B2]. rewrite Z.ltb_ge in B1, B2.
  unfold isP in H1. unfold isM in H2. apply Z.eqb_neq in H1, H2. eqbs.
Qed.


(* ------------------------------------------------------------------ *)
(* the run of Hierholzer meets the contract                            *)
(* ------------------------------------------------------------------ *)

Lemma main_run : forall (L : list nat) (nxt head : array int) s t,
  Permutation L (seq 0 n) -> StronglySorted wlt L ->
  s < 256 -> (φ (PArray.length head)) = 256%Z ->
  (forall c, c < 256 -> chain nxt nI head.[ix c] (filter (fun e => Nat.eqb (tlW e) c) L)) ->
  D tlW hdW (seq 0 n) s t ->
  (forall T y, Permutation (seq 0 n) T -> trail tlW hdW (tlW (nth 0 T 0)) T y -> T <> [] ->
     tlW (nth 0 T 0) = s \/ (t = s /\ s = tlW (nth 0 L 0))) ->
  forall H, exists o,
  repr (match hier_loop x nxt nI (ix s) head (PArray.make nI 0%uint63) 0%uint63 0%uint63
                (PArray.make nI ""%pstring) 0%uint63 H with
        | (res, cnt) => if (cnt =? nI)%uint63 then Some res else None
        end) o /\ catenyms_spec W o.
Proof.
  intros L nxt head s t HLp HLs Hs Hhl Hch HD Hstart H.
  pose proof n_bounds as NB. pose proof nI_spec as EN.
  set (rem0 := fun c => filter (fun e => Nat.eqb (tlW e) c) L).
  assert (HLb : forall e, In e L -> e < n) by (intros e He; apply (Permutation_in _ HLp), in_seq in He; lia).
  assert (HE0 : Permutation (E 256 rem0) L).
  { unfold E, rem0. apply flat_map_filter_perm; [apply seq_NoDup|]. intros e _. apply in_seq. pose proof (tlW_lt e). lia. }
  assert (HE0' : Permutation (E 256 rem0) (seq 0 n)) by (eapply perm_trans; [exact HE0|exact HLp]).
  assert (HEb : forall e, In e (E 256 rem0) -> e < n) by (intros e He; apply HLb; apply (Permutation_in _ HE0); exact He).
  assert (HInv0 : Inv tlW rem0).
  { intros c e He. unfold rem0 in He. apply filter_In in He as [_ He]. apply Nat.eqb_eq. exact He. }
  assert (HSrt0 : Srt wlt rem0) by (intros c; apply SS_filter; exact HLs).
  assert (HD0 : D tlW hdW (E 256 rem0) s t) by (apply (D_perm tlW hdW (seq 0 n)); [apply Permutation_sym; exact HE0'|exact HD]).
  pose proof (Permutation_length HE0') as HLE. rewrite length_seq in HLE.
  destruct (Hrel_exists 256 tlW hdW tlW_lt n rem0 s HInv0 ltac:(lia)) as (P & rem'' & HH).
  pose proof (Hrel_perm 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0) as HPm.
  pose proof (Permutation_length HPm) as HPl. rewrite length_app in HPl.
  pose proof (Hrel_trail 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0 t HD0) as Htr.
  destruct (Hrel_done hdW rem0 s P rem'' HH) as [Hd1 _].
  pose proof (Hrel_mstar hdW s rem0 s P rem'' HH [] [] eq_refl) as HMs. rewrite app_nil_r in HMs.
  assert (HPb : forall e, In e P -> e < n).
  { intros e He. apply HEb. apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. exact He. }
  assert (HC0 : corr nxt head (PArray.make nI 0%uint63) 0%uint63 0%uint63 (PArray.make nI ""%pstring) 0%uint63 rem0 [] []).
  { unfold corr. split; [exact Hhl|]. split; [exact Hch|]. split; [exact HInv0|].
    split; [rewrite alength_make; lia|]. split; [reflexivity|]. split; [intros i Hi; simpl in Hi; lia|].
    split; [rewrite slength_make; lia|]. split; [reflexivity|]. split; [intros i Hi; simpl in Hi; lia|].
    split; [reflexivity|]. split; [simpl; lia|]. split; [exact HEb|]. intros e []. }
  destruct (hier_sim nxt s Hs _ _ _ _ _ _ HMs _ _ _ _ _ _ H HC0)
    as (ptr' & stk' & sp' & q' & res' & cnt' & H' & HC' & Heq).
  pose proof (hier_stop nxt s Hs _ _ _ _ _ _ _ _ H' HC' Hd1) as Hst.
  unfold sI in Heq, Hst. rewrite Heq, Hst.
  destruct HC' as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  (* a trail of all the words from s is covered by the run *)
  assert (Hcov : forall T y, Permutation (seq 0 n) T -> trail tlW hdW s T y -> List.length P = n).
  { intros T y HT HTr.
    assert (Hi : incl T P).
    { apply (Hrel_covers 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0 T s y HTr); [left; reflexivity|].
      intros g Hg. apply (Permutation_in _ (Permutation_sym HE0')). apply (Permutation_in _ (Permutation_sym HT)). exact Hg. }
    pose proof (NoDup_incl_length (Permutation_NoDup HT (seq_NoDup n 0)) Hi) as Hle.
    rewrite <- (Permutation_length HT), length_seq in Hle. lia. }
  destruct (cnt' =? nI)%uint63 eqn:Ecn.
  - apply Uint63.eqb_spec in Ecn. rewrite Ecn, EN in C8.
    assert (HPn : List.length P = n) by lia.
    assert (HR0 : E 256 rem'' = []) by (destruct (E 256 rem''); [reflexivity|simpl in HPl; lia]).
    rewrite HR0, app_nil_r in HPm.
    assert (HPs : Permutation (seq 0 n) P) by (eapply perm_trans; [apply Permutation_sym, HE0'|exact HPm]).
    exists (Some (map word P)). split.
    + split.
      * rewrite length_map, HPn. symmetry. exact C7.
      * intros k Hk. rewrite length_map in Hk. exists (word (nth k P 0)). split.
        -- rewrite nth_error_map, (nth_error_nth' P 0 Hk). reflexivity.
        -- assert (Hres : res'.[ix k] = x.[ix (nth k P 0)]).
           { rewrite HPn in C9. replace k with (n - 1 - (n - 1 - k)) at 1 by lia.
             rewrite C9 by lia. f_equal. f_equal. f_equal. lia. }
           pose proof (x_repr (nth k P 0) (HPb _ (nth_In _ _ Hk))) as Hx. rewrite <- Hres in Hx. exact Hx.
    + split.
      { split.
        - split; [unfold len; rewrite length_map, HPn; lia|].
          intros j Hj. rewrite length_map in Hj.
          rewrite (nth_indep _ EmptyString (word 0)), map_nth by (rewrite length_map; lia).
          rewrite (nth_indep _ EmptyString (word 0)), map_nth by (rewrite length_map; lia).
          apply catenym_iff; [apply HPb, nth_In; lia|apply HPb, nth_In; lia|].
          apply (chain_of_trail _ _ _ Htr). exact Hj.
        - rewrite W_map. apply Permutation_map. apply Permutation_sym. exact HPs. }
      intros c' Hc'. destruct (answer_trail c' Hc') as (T & -> & HT & Hne & y & HTr).
      assert (HTb : forall e, In e T -> e < n) by (intros e He; apply (Permutation_in _ (Permutation_sym HT)), in_seq in He; lia).
      apply lexle_text; [|exact HPb|exact HTb].
      assert (HTnd : NoDup T) by (apply (Permutation_NoDup HT), seq_NoDup).
      assert (HTi : incl T (E 256 rem0)) by (intros g Hg; apply (Permutation_in _ (Permutation_sym HE0')), (Permutation_in _ (Permutation_sym HT)); exact Hg).
      assert (HTl : List.length T = List.length P) by (rewrite <- (Permutation_length HT), length_seq; lia).
      destruct (Nat.eq_dec (tlW (nth 0 T 0)) s) as [Es|Es].
      * rewrite Es in HTr. exact (Hrel_lex 256 tlW hdW tlW_lt wlt rem0 s P rem'' HH HInv0 HSrt0 t HD0 T y HTr HTnd HTi HTl).
      * destruct (Hstart T y HT HTr Hne) as [E1|[Et Es0]]; [contradiction|]. subst t.
        destruct L as [|l0 L']; [apply Permutation_length in HLp; rewrite length_seq in HLp; simpl in HLp; lia|].
        simpl in Es0.
        assert (Hr0 : rem0 s = l0 :: filter (fun e => Nat.eqb (tlW e) s) L')
          by (unfold rem0; simpl; rewrite <- Es0, Nat.eqb_refl; reflexivity).
        destruct (Hrel_circuit 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0 HD0 _ _ Hr0) as (A & ->).
        destruct T as [|f T']; [congruence|]. simpl in Es.
        apply lexle_head.
        assert (Hf : In f (l0 :: L')) by (apply (Permutation_in _ (Permutation_sym HLp)), (Permutation_in _ (Permutation_sym HT)); left; reflexivity).
        destruct Hf as [<-|Hf]; [rewrite <- Es0 in Es; congruence|].
        apply StronglySorted_inv in HLs as [_ HF]. rewrite Forall_forall in HF. apply HF. exact Hf.
  - exists None. split; [exact I|]. intros (c' & Hc').
    destruct (answer_trail c' Hc') as (T & -> & HT & Hne & y & HTr).
    assert (HPn : List.length P = n).
    { destruct (Nat.eq_dec (tlW (nth 0 T 0)) s) as [Es|Es]; [rewrite Es in HTr; apply (Hcov T y HT HTr)|].
      destruct (Hstart T y HT HTr Hne) as [E1|[Et Es0]]; [contradiction|]. subst t.
      set (s0 := tlW (nth 0 T 0)) in *.
      assert (HDT : D tlW hdW (seq 0 n) s0 y) by (apply (D_perm tlW hdW T); [apply Permutation_sym, HT|apply (trail_D _ _ _ _ _ HTr)]).
      assert (Hy : y = s0) by (specialize (HDT s0); specialize (HD s0); rewrite HD in HDT; revert HDT; eqbs).
      subst y.
      assert (Hl0 : In (nth 0 L 0) T).
      { apply (Permutation_in _ HT), (Permutation_in _ HLp), nth_In.
        rewrite (Permutation_length HLp), length_seq. lia. }
      apply in_split in Hl0 as (T1 & T3 & ET).
      rewrite ET in HTr. destruct (trail_app_inv tlW hdW _ _ _ _ HTr) as (z & HT1 & HT3).
      apply trail_cons_inv in HT3 as [Hz HT3]. rewrite <- Es0 in Hz. subst z.
      apply (Hcov ((nth 0 L 0 :: T3) ++ T1) s).
      + rewrite ET in HT. eapply perm_trans; [exact HT|]. apply Permutation_app_comm.
      + apply (trail_app tlW hdW _ _ s0); [|exact HT1]. constructor; [symmetry; exact Es0|exact HT3]. }
    assert (cnt' = nI) by (apply to_Z_inj; rewrite C8, EN; lia).
    rewrite H0, Uint63.eqb_refl in Ecn. discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(* the whole program                                                   *)
(* ------------------------------------------------------------------ *)

Lemma answer_D : forall c, is_answer W c -> exists s' t', D tlW hdW (seq 0 n) s' t'.
Proof.
  intros c Hc. destruct (answer_trail c Hc) as (T & _ & HT & _ & y & HTr).
  exists (tlW (nth 0 T 0)), y. apply (D_perm tlW hdW T); [apply Permutation_sym, HT|apply (trail_D _ _ _ _ _ HTr)].
Qed.

Theorem catenyms_impl_correct : exists o, repr (catenyms_impl x) o /\ catenyms_spec W o.
Proof.
  pose proof n_bounds as NB. pose proof nI_spec as EN.
  unfold catenyms_impl. cbv zeta. fold nI.
  (* the identity permutation *)
  lazymatch goal with |- context [init_loop ?a ?nn ?k ?H] => set (ord0 := init_loop a nn k H) in * end.
  assert (HI : PArray.length ord0 = nI /\ forall j, ((φ j) < (φ nI))%Z -> ord0.[j] = j).
  { unfold ord0. apply init_loop_spec with (z := pgap nI 0); [reflexivity|apply alength_make; lia|change (φ 0) with 0%Z; lia|].
    intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia. }
  destruct HI as [I1 I2].
  (* the sort *)
  lazymatch goal with |- context [msort x ord0 ?t ?lo ?hi ?H] => destruct (msort x ord0 t lo hi H) as [ord tmp] eqn:Ems end.
  destruct (msort_spec x _ 0%uint63 nI ord0 (PArray.make nI 0%uint63) _ ord tmp eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite I1; lia) ltac:(rewrite alength_make, I1 by lia; reflexivity) Ems) as (M1 & M2 & M3 & M4 & M5).
  replace (nt 0%uint63) with 0 in M4, M5 by reflexivity.
  replace (nt nI) with n in M4, M5 by (unfold nt; rewrite EN; lia).
  set (L := map nt (seg ord 0 n)).
  assert (HLn : forall k, k < n -> nth k L 0 = nt ord.[ix k]).
  { intros k Hk. unfold L, seg. rewrite Nat.sub_0_r, map_map. apply nth_map_seq. exact Hk. }
  assert (Hseg0 : seg ord0 0 n = map ix (seq 0 n)).
  { unfold seg. rewrite Nat.sub_0_r. apply map_ext_in. intros k Hk. apply in_seq in Hk.
    apply I2. rewrite EN, ix_spec by lia. lia. }
  assert (HLp : Permutation L (seq 0 n)).
  { unfold L. eapply perm_trans; [apply Permutation_map, M4|]. rewrite Hseg0, map_map.
    rewrite (map_ext_in _ (fun k => k)); [rewrite map_id; apply Permutation_refl|].
    intros k Hk. apply in_seq in Hk. unfold nt. rewrite ix_spec by lia. lia. }
  assert (HLl : List.length L = n) by (rewrite (Permutation_length HLp), length_seq; reflexivity).
  assert (HLnd : NoDup L) by (apply (Permutation_NoDup (Permutation_sym HLp)), seq_NoDup).
  assert (HLb : forall e, In e L -> e < n) by (intros e He; apply (Permutation_in _ HLp), in_seq in He; lia).
  assert (HLo : forall k, k < n -> ord.[ix k] = ix (nth k L 0)) by (intros k Hk; rewrite HLn, ix_nt by exact Hk; reflexivity).
  assert (HLs : StronglySorted wlt L).
  { apply SS_of_nth. intros p q Hpq. rewrite HLl in Hpq.
    pose proof (M5 p q ltac:(lia) ltac:(lia) ltac:(lia)) as Hle. unfold le, cmpw in Hle.
    rewrite !HLo in Hle by lia.
    assert (Hp : nth p L 0 < n) by (apply HLb, nth_In; lia).
    assert (Hq : nth q L 0 < n) by (apply HLb, nth_In; lia).
    unfold wlt. destruct (PrimString.compare x.[ix (nth p L 0)] x.[ix (nth q L 0)]) eqn:Ec;
      [|reflexivity|discriminate].
    exfalso. apply PString.compare_eq in Ec.
    pose proof (x_repr _ Hp) as Rp. rewrite Ec in Rp.
    pose proof (word_inj _ _ Hp Hq (repr_str_inj x.[ix (nth q L 0)] (word (nth p L 0)) (word (nth q L 0)) Rp (x_repr _ Hq))) as E.
    apply (proj1 (NoDup_nth L 0) HLnd p q ltac:(lia) ltac:(lia)) in E. lia. }
  (* the adjacency *)
  lazymatch goal with |- context [build_loop x ord ?nn ?nx ?hd ?k ?H] => destruct (build_loop x ord nn nx hd k H) as [nxt head] eqn:Eb end.
  destruct (build_loop_spec ord L HLl HLnd HLb HLo _ 0%uint63 (PArray.make nI 0%uint63) (PArray.make 256 nI) _ nxt head eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(rewrite alength_make; lia) ltac:(rewrite alength_make; reflexivity || lia)
              ltac:(intros c Hc; replace (n - nt 0%uint63) with n by (unfold nt; change (φ 0) with 0%Z; lia);
                    rewrite skipn_all2 by lia; exact (aget_make 256 nI (ix c))) Eb) as (B1 & B2 & B3).
  (* the degrees *)
  lazymatch goal with |- context [deg_loop x ?nn ?o ?i ?k ?H] => destruct (deg_loop x nn o i k H) as [outd ind0] eqn:Ed end.
  destruct (deg_loop_spec _ 0%uint63 (PArray.make 256 0%uint63) (PArray.make 256 0%uint63) _ outd ind0 eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite alength_make; reflexivity || lia) ltac:(rewrite alength_make; reflexivity || lia)
              ltac:(intros c _; rewrite !aget_make; split; reflexivity) Ed) as (D1 & D2 & D3).
  lazymatch goal with |- context [chk_loop outd ind0 ?c ?p ?m ?v ?b ?H] =>
    destruct (chk_loop outd ind0 c p m v b H) as [[[plus minus] sv] bad] eqn:Ec end.
  destruct (chk_loop_spec outd ind0 D1 D2 D3 _ 0%uint63 0%uint63 0%uint63 0%uint63 false _ plus minus sv bad eq_refl
              ltac:(change (φ 0) with 0%Z; lia) eq_refl eq_refl eq_refl
              ltac:(intros Hq; change (φ 0) with 0%Z in Hq; lia) Ec) as (K1 & K2 & K3 & K4).
  pose proof (filter_length_le isP (seq 0 256)) as LP. rewrite length_seq in LP.
  destruct bad.
  { exists None. split; [exact I|]. intros (c & Hc). destruct (answer_D c Hc) as (s' & t' & HD).
    destruct (D_check _ _ HD) as (X1 & _ & _). congruence. }
  destruct (negb (plus =? minus)%uint63) eqn:Epm.
  { exists None. split; [exact I|]. intros (c & Hc). destruct (answer_D c Hc) as (s' & t' & HD).
    destruct (D_check _ _ HD) as (_ & X2 & _).
    apply Bool.negb_true_iff, Uint63.eqb_false_spec in Epm. apply Epm, to_Z_inj. rewrite K1, K2, X2. reflexivity. }
  destruct (negb (plus <=? 1)%uint63) eqn:Ep1.
  { exists None. split; [exact I|]. intros (c & Hc). destruct (answer_D c Hc) as (s' & t' & HD).
    destruct (D_check _ _ HD) as (_ & _ & X3).
    apply Bool.negb_true_iff in Ep1. rewrite <- Bool.not_true_iff_false, leb_spec in Ep1. apply Ep1.
    rewrite K1. change (φ 1) with 1%Z. lia. }
  apply Bool.negb_false_iff, Uint63.eqb_spec in Epm. apply Bool.negb_false_iff in Ep1. rewrite leb_spec in Ep1.
  change (φ 1) with 1%Z in Ep1.
  assert (HPM : List.length (filter isP (seq 0 256)) = List.length (filter isM (seq 0 256))) by (rewrite Epm in K1; lia).
  assert (HL0 : nth 0 L 0 < n) by (apply HLb, nth_In; lia).
  destruct (plus =? 1)%uint63 eqn:Eq1.
  - (* an Euler path : it starts at the letter with one more out-edge *)
    apply Uint63.eqb_spec in Eq1. assert (Hpl : (φ plus) = 1%Z) by (rewrite Eq1; reflexivity).
    destruct (K4 ltac:(lia)) as [Hsv HPs].
    destruct (check_D1 (nt sv) (eq_sym K3) ltac:(lia) ltac:(lia) Hsv HPs) as (t & HD).
    rewrite <- (ix_nt sv).
    apply (main_run L nxt head (nt sv) t HLp HLs Hsv B2 B3 HD).
    intros T y HT HTr Hne. left.
    assert (HDT : D tlW hdW (seq 0 n) (tlW (nth 0 T 0)) y)
      by (apply (D_perm tlW hdW T); [apply Permutation_sym, HT|apply (trail_D _ _ _ _ _ HTr)]).
    unfold isP in HPs. apply Z.eqb_eq in HPs. rewrite dd_dg in HPs.
    rewrite HDT in HPs. revert HPs. eqbs.
  - (* an Euler circuit : it starts with the smallest word *)
    assert (Hp0 : (φ plus) = 0%Z).
    { apply Uint63.eqb_false_spec in Eq1. pose proof (to_Z_bounded plus).
      destruct (Z.eq_dec (φ plus) 1) as [E|E]; [exfalso; apply Eq1, to_Z_inj; exact E|lia]. }
    assert (Hs : fst_ch x.[ord.[0%uint63]] = ix (tlW (nth 0 L 0))).
    { change 0%uint63 with (ix 0). rewrite HLo by lia. apply fst_ch_ix. exact HL0. }
    rewrite Hs.
    pose proof (check_D0 (eq_sym K3) ltac:(lia) ltac:(lia) (tlW (nth 0 L 0))) as HD.
    apply (main_run L nxt head (tlW (nth 0 L 0)) (tlW (nth 0 L 0)) HLp HLs (tlW_lt _) B2 B3 HD).
    intros T y HT HTr Hne. right. split; reflexivity.
Qed.

End Main.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition catenyms : array PrimString.string -> option (array PrimString.string) := catenyms_impl.
Elpi complexity catenyms.

Definition catenyms_correct :
  forall (words : list string) (x : array PrimString.string),
  valid_input words -> repr x words ->
  exists o : option (list string), repr (catenyms x) o /\ catenyms_spec words o
  := fun words x Hv Hr => catenyms_impl_correct words x Hv Hr.


(* ================================================================== *)
(* Part 5. Cost: the bound catenyms_time.                              *)
(* ================================================================== *)

(* The cost translation is the Elpi complexity lines of Part 3 (sumbool,
   bdec, andb, splitc, midp, init_loop, cmpw, merge_loop, copy_loop,
   msort, fst_ch, lst_ch, build_loop, deg_loop, chk_loop, hier_loop,
   negb, catenyms_impl) and the one after catenyms.  One lemma per loop,
   by induction on a nat bound of its measure (pgap, mg, hg); the fix of
   the twin is abstracted after its first unfolding (absfix) so that
   cost_simpl does not traverse its body at every step.  msort is proven
   by induction on k with hi - lo <= 2^k: at most (hi - lo) * k * 400 + 60
   steps; catenyms_impl at most n * log2_up n * 400 + n * 400 + 22000. *)

From Stdlib Require Import ssreflect.

Arguments pgap : simpl never.
Arguments mg : simpl never.
Arguments hg : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma pgap_succ hi k : (k <? hi) = true -> (Z.to_nat (pgap hi (k + 1)) < Z.to_nat (pgap hi k))%nat.
Proof. intros H. destruct (pgap_step hi k H). lia. Qed.

Lemma pgap_stop hi k : (k <? hi) = false -> Z.to_nat (pgap hi k) = 0%nat.
Proof. intros H. assert (~ (φ k < φ hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence). unfold pgap. lia. Qed.

Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  | |- context [cost (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (set_cost a b c) d e) f g)) with 0%nat
  | |- context [cost (extract (set_cost ?a ?b ?c) ?d ?e)] =>
      change (cost (extract (set_cost a b c) d e)) with 0%nat
  | |- context [cost (set_cost ?a ?b ?c)] =>
      change (cost (set_cost a b c)) with 0%nat
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  | |- context [cost (extract (make_cost ?a ?b ?c) ?d ?e)] =>
      change (cost (extract (make_cost a b c) d e)) with 0%nat
  | |- context [cost (make_cost ?a ?b ?c)] =>
      change (cost (make_cost a b c)) with 0%nat
  end.

Ltac z0 f := repeat match goal with |- context [cost (f ?a ?b ?c)] => change (cost (f a b c)) with 0%nat end.
Ltac z1 f := repeat match goal with |- context [cost (extract (f ?a ?b ?c) ?d ?e)] =>
  change (cost (extract (f a b c) d e)) with 0%nat end.
Ltac z2 f := repeat match goal with |- context [cost (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1)] =>
  change (cost (extract (extract (f a b c) d e) d1 e1)) with 0%nat end.
Ltac z3 f := repeat match goal with |- context [cost (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2)] =>
  change (cost (extract (extract (extract (f a b c) d e) d1 e1) d2 e2)) with 0%nat end.
Ltac z4 f := repeat match goal with |- context [cost (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3)] =>
  change (cost (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3)) with 0%nat end.
Ltac z5 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4)] =>
  change (cost (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4)) with 0%nat end.
Ltac z6 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5)] =>
  change (cost (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5)) with 0%nat end.
Ltac z7 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5) ?d6 ?e6)] =>
  change (cost (extract (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5) d6 e6)) with 0%nat end.
Ltac z8 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5) ?d6 ?e6) ?d7 ?e7)] =>
  change (cost (extract (extract (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5) d6 e6) d7 e7)) with 0%nat end.
Ltac z9 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5) ?d6 ?e6) ?d7 ?e7) ?d8 ?e8)] =>
  change (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5) d6 e6) d7 e7) d8 e8)) with 0%nat end.
Ltac z10 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5) ?d6 ?e6) ?d7 ?e7) ?d8 ?e8) ?d9 ?e9)] =>
  change (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5) d6 e6) d7 e7) d8 e8) d9 e9)) with 0%nat end.

Lemma pgap_nonneg m j : (0 <= pgap m j)%Z.
Proof. unfold pgap. lia. Qed.

Lemma mg_i iend i jend j : (i <? iend) = true ->
  (Z.to_nat (mg iend (i + 1) jend j) < Z.to_nat (mg iend i jend j))%nat.
Proof.
  intros H. pose proof (dec_mi iend i jend j H) as D. unfold Zwf in D.
  assert (0 <= mg iend (i + 1) jend j)%Z by (unfold mg; pose proof (pgap_nonneg iend (i+1)); pose proof (pgap_nonneg jend j); lia).
  lia.
Qed.

Lemma mg_j iend i jend j : (j <? jend) = true ->
  (Z.to_nat (mg iend i jend (j + 1)) < Z.to_nat (mg iend i jend j))%nat.
Proof.
  intros H. pose proof (dec_mj iend i jend j H) as D. unfold Zwf in D.
  assert (0 <= mg iend i jend (j + 1))%Z by (unfold mg; pose proof (pgap_nonneg iend i); pose proof (pgap_nonneg jend (j+1)); lia).
  lia.
Qed.

Lemma mg_stop iend i jend j : (i <? iend) = false -> (j <? jend) = false ->
  Z.to_nat (mg iend i jend j) = 0%nat.
Proof.
  intros H1 H2. pose proof (pgap_stop _ _ H1). pose proof (pgap_stop _ _ H2).
  unfold mg. pose proof (pgap_nonneg iend i); pose proof (pgap_nonneg jend j). lia.
Qed.

Ltac absfix := match goal with |- context [?f] => is_fix f; let F := fresh "F" in set (F := f) in *; clearbody F end.
Ltac csimpl := cbn; cost_reduce; fold_cost; repeat (cost_rewrite; cost_reduce); cbn; fold_cost.
Ltac cstart := cost_unfold_fix; try absfix; csimpl.

Ltac dbdec := match goal with |- context [cost (bdec_cost stepsCM ?b ?w)] =>
  let HB := fresh "HB" in pose proof (bdec_time b w) as HB; cost_destruct (bdec b) end.
Ltac dif := match goal with |- context [if ?b then _ else _] => cost_destruct b end.

Lemma init_loop_time a aC n nC k kC H HC :
  (cost (extract (extract (extract (init_loop_cost stepsCM a aC) n nC) k kC) H HC)
     <= 20 * Z.to_nat (pgap n k) + 10)%nat.
Proof.
  unfold init_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G a aC n nC k kC H HC)] =>
    assert (HG : forall m a aC k kC H HC, (Z.to_nat (pgap n k) <= m)%nat ->
       (cost (G a aC n nC k kC H HC) <= 20 * Z.to_nat (pgap n k) + 10)%nat) end.
  { induction m as [|m IH]; intros a' aC' k' kC' [g] HC' Hm;
      cost_simpl;
      pose proof (bdec_time (k' <? n) (bool_w (k' <? n))) as HB;
      cost_destruct (bdec (k' <? n)); cost_simpl.
    - exfalso. pose proof (pgap_succ n k' e). lia.
    - lia.
    - pose proof (pgap_succ n k' e) as Hs. set_simpl.
      match goal with |- context [@cost ?T (?G' ?a2 ?aC2 n nC (k' + 1)%uint63 ?w ?h ?hc)] =>
        have HI := (IH a2 aC2 (k' + 1)%uint63 w h hc ltac:(lia) : (@cost T (G' a2 aC2 n nC (k' + 1)%uint63 w h hc) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G a aC n nC k kC H HC)] =>
    exact (HG _ a aC k kC H HC (le_n _) : (@cost T (G a aC n nC k kC H HC) <= _)%nat) end.
Qed.

Lemma copy_loop_time src srcC dst dstC hi hiC k kC H HC :
  (cost (extract (extract (extract (extract (copy_loop_cost stepsCM src srcC) dst dstC) hi hiC) k kC) H HC)
     <= 30 * Z.to_nat (pgap hi k) + 10)%nat.
Proof.
  unfold copy_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G src srcC dst dstC hi hiC k kC H HC)] =>
    assert (HG : forall m dst dstC k kC H HC, (Z.to_nat (pgap hi k) <= m)%nat ->
       (cost (G src srcC dst dstC hi hiC k kC H HC) <= 30 * Z.to_nat (pgap hi k) + 10)%nat) end.
  { induction m as [|m IH]; intros d' dC' k' kC' [g] HC' Hm;
      cost_simpl;
      pose proof (bdec_time (k' <? hi) (bool_w (k' <? hi))) as HB;
      cost_destruct (bdec (k' <? hi)); cost_simpl.
    - exfalso. pose proof (pgap_succ hi k' e). lia.
    - lia.
    - pose proof (pgap_succ hi k' e) as Hs. set_simpl.
      match goal with |- context [@cost ?T (?G' src srcC ?a2 ?aC2 hi hiC (k' + 1)%uint63 ?w ?h ?hc)] =>
        have HI := (IH a2 aC2 (k' + 1)%uint63 w h hc ltac:(lia) : (@cost T (G' src srcC a2 aC2 hi hiC (k' + 1)%uint63 w h hc) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G src srcC dst dstC hi hiC k kC H HC)] =>
    exact (HG _ dst dstC k kC H HC (le_n _) : (@cost T (G src srcC dst dstC hi hiC k kC H HC) <= _)%nat) end.
Qed.

Lemma cmpw_time x xC i iC j jC :
  (cost (extract (extract (cmpw_cost stepsCM x xC) i iC) j jC) <= 20)%nat.
Proof.
  unfold cmpw_cost. cost_simpl.
  cost_destruct (PrimString.compare x.[i] x.[j]); cost_simpl; lia.
Qed.


Ltac gen_cmpw := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (cmpw_cost stepsCM ?x ?xC) ?i ?iC) ?j ?jC =>
    let Hc := fresh "Hcmp" in
    have Hc := (cmpw_time x xC i iC j jC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma merge_loop_time x xC src srcC dst dstC iend iendC jend jendC i iC j jC k kC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (merge_loop_cost stepsCM x xC) src srcC) dst dstC) iend iendC) jend jendC) i iC) j jC) k kC) H HC)
     <= Z.to_nat (mg iend i jend j) * 100 + 20)%nat.
Proof.
  unfold merge_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC src srcC dst dstC iend iendC jend jendC i iC j jC k kC H HC)] =>
    assert (HG : forall m dst dstC i iC j jC k kC H HC, (Z.to_nat (mg iend i jend j) <= m)%nat ->
       (cost (G x xC src srcC dst dstC iend iendC jend jendC i iC j jC k kC H HC) <= Z.to_nat (mg iend i jend j) * 100 + 20)%nat) end.
  { induction m as [|m IH]; intros d' dC' i' iC' j' jC' k' kC' [g] HC' Hm;
      cstart;
      pose proof (bdec_time (i' <? iend) (bool_w (i' <? iend))) as HB;
      cost_destruct (bdec (i' <? iend)); csimpl.
    - exfalso. pose proof (mg_i iend i' jend j' e). lia.
    - pose proof (bdec_time (j' <? jend) (bool_w (j' <? jend))) as HB2;
      cost_destruct (bdec (j' <? jend)); csimpl.
      + exfalso. pose proof (mg_j iend i' jend j' e0). lia.
      + lia.
    - pose proof (mg_i iend i' jend j' e) as Hs.
      pose proof (bdec_time (j' <? jend) (bool_w (j' <? jend))) as HB2;
      cost_destruct (bdec (j' <? jend)); csimpl.
      + pose proof (mg_j iend i' jend j' e0) as Hs2.
        z0 cmpw_cost. z1 cmpw_cost. gen_cmpw.
        cost_destruct (cmpw x src.[i'] src.[j']); csimpl; set_simpl;
        match goal with |- context [@cost ?T (?G' x xC src srcC ?a2 ?aC2 iend iendC jend jendC ?i2 ?iC2 ?j2 ?jC2 ?k2 ?kC2 ?h ?hc)] =>
          have HI := (IH a2 aC2 i2 iC2 j2 jC2 k2 kC2 h hc ltac:(lia) : (@cost T (G' x xC src srcC a2 aC2 iend iendC jend jendC i2 iC2 j2 jC2 k2 kC2 h hc) <= _)%nat) end;
        lia.
      + set_simpl.
        match goal with |- context [@cost ?T (?G' x xC src srcC ?a2 ?aC2 iend iendC jend jendC ?i2 ?iC2 ?j2 ?jC2 ?k2 ?kC2 ?h ?hc)] =>
          have HI := (IH a2 aC2 i2 iC2 j2 jC2 k2 kC2 h hc ltac:(lia) : (@cost T (G' x xC src srcC a2 aC2 iend iendC jend jendC i2 iC2 j2 jC2 k2 kC2 h hc) <= _)%nat) end.
        lia.
    - pose proof (bdec_time (j' <? jend) (bool_w (j' <? jend))) as HB2;
      cost_destruct (bdec (j' <? jend)); csimpl.
      + pose proof (mg_j iend i' jend j' e0) as Hs2. set_simpl.
        match goal with |- context [@cost ?T (?G' x xC src srcC ?a2 ?aC2 iend iendC jend jendC ?i2 ?iC2 ?j2 ?jC2 ?k2 ?kC2 ?h ?hc)] =>
          have HI := (IH a2 aC2 i2 iC2 j2 jC2 k2 kC2 h hc ltac:(lia) : (@cost T (G' x xC src srcC a2 aC2 iend iendC jend jendC i2 iC2 j2 jC2 k2 kC2 h hc) <= _)%nat) end.
        lia.
      + lia. }
  match goal with |- context [@cost ?T (?G x xC src srcC dst dstC iend iendC jend jendC i iC j jC k kC H HC)] =>
    exact (HG _ dst dstC i iC j jC k kC H HC (le_n _) : (@cost T (G x xC src srcC dst dstC iend iendC jend jendC i iC j jC k kC H HC) <= _)%nat) end.
Qed.


Lemma fst_ch_time w wC : (cost (fst_ch_cost stepsCM w wC) <= 10)%nat.
Proof. unfold fst_ch_cost. csimpl. lia. Qed.

Lemma lst_ch_time w wC : (cost (lst_ch_cost stepsCM w wC) <= 10)%nat.
Proof. unfold lst_ch_cost. csimpl. lia. Qed.

Ltac gen_ch := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | fst_ch_cost stepsCM ?w ?wC =>
    let Hc := fresh "Hch" in
    have Hc := (fst_ch_time w wC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | lst_ch_cost stepsCM ?w ?wC =>
    let Hc := fresh "Hch" in
    have Hc := (lst_ch_time w wC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  end end.

Lemma build_loop_time x xC ord ordC n nC nxt nxtC head headC k kC H HC :
  (cost (extract (extract (extract (extract (extract (extract (build_loop_cost stepsCM x xC) ord ordC) n nC) nxt nxtC) head headC) k kC) H HC)
     <= Z.to_nat (pgap n k) * 60 + 10)%nat.
Proof.
  unfold build_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC ord ordC n nC nxt nxtC head headC k kC H HC)] =>
    assert (HG : forall m nxt nxtC head headC k kC H HC, (Z.to_nat (pgap n k) <= m)%nat ->
       (cost (G x xC ord ordC n nC nxt nxtC head headC k kC H HC) <= Z.to_nat (pgap n k) * 60 + 10)%nat) end.
  { induction m as [|m IH]; intros nx' nxC' hd' hdC' k' kC' [g] HC' Hm;
      cstart;
      pose proof (bdec_time (k' <? n) (bool_w (k' <? n))) as HB;
      cost_destruct (bdec (k' <? n)); csimpl.
    - exfalso. pose proof (pgap_succ n k' e). lia.
    - lia.
    - pose proof (pgap_succ n k' e) as Hs. set_simpl. gen_ch.
      match goal with |- context [@cost ?T (?G' x xC ord ordC n nC ?a2 ?aC2 ?b2 ?bC2 (k' + 1)%uint63 ?w ?h ?hc)] =>
        have HI := (IH a2 aC2 b2 bC2 (k' + 1)%uint63 w h hc ltac:(lia) : (@cost T (G' x xC ord ordC n nC a2 aC2 b2 bC2 (k' + 1)%uint63 w h hc) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC ord ordC n nC nxt nxtC head headC k kC H HC)] =>
    exact (HG _ nxt nxtC head headC k kC H HC (le_n _) : (@cost T (G x xC ord ordC n nC nxt nxtC head headC k kC H HC) <= _)%nat) end.
Qed.

Lemma deg_loop_time x xC n nC outd outdC ind indC k kC H HC :
  (cost (extract (extract (extract (extract (extract (deg_loop_cost stepsCM x xC) n nC) outd outdC) ind indC) k kC) H HC)
     <= Z.to_nat (pgap n k) * 80 + 10)%nat.
Proof.
  unfold deg_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC outd outdC ind indC k kC H HC)] =>
    assert (HG : forall m outd outdC ind indC k kC H HC, (Z.to_nat (pgap n k) <= m)%nat ->
       (cost (G x xC n nC outd outdC ind indC k kC H HC) <= Z.to_nat (pgap n k) * 80 + 10)%nat) end.
  { induction m as [|m IH]; intros o' oC' i' iC' k' kC' [g] HC' Hm;
      cstart;
      pose proof (bdec_time (k' <? n) (bool_w (k' <? n))) as HB;
      cost_destruct (bdec (k' <? n)); csimpl.
    - exfalso. pose proof (pgap_succ n k' e). lia.
    - lia.
    - pose proof (pgap_succ n k' e) as Hs. set_simpl. gen_ch.
      match goal with |- context [@cost ?T (?G' x xC n nC ?a2 ?aC2 ?b2 ?bC2 (k' + 1)%uint63 ?w ?h ?hc)] =>
        have HI := (IH a2 aC2 b2 bC2 (k' + 1)%uint63 w h hc ltac:(lia) : (@cost T (G' x xC n nC a2 aC2 b2 bC2 (k' + 1)%uint63 w h hc) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC outd outdC ind indC k kC H HC)] =>
    exact (HG _ outd outdC ind indC k kC H HC (le_n _) : (@cost T (G x xC n nC outd outdC ind indC k kC H HC) <= _)%nat) end.
Qed.


Lemma chk_loop_time outd outdC ind indC c cC plus plusC minus minusC sv svC bad badC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (chk_loop_cost stepsCM outd outdC) ind indC) c cC) plus plusC) minus minusC) sv svC) bad badC) H HC)
     <= Z.to_nat (pgap 256 c) * 80 + 20)%nat.
Proof.
  unfold chk_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G outd outdC ind indC c cC plus plusC minus minusC sv svC bad badC H HC)] =>
    assert (HG : forall m c cC plus plusC minus minusC sv svC bad badC H HC, (Z.to_nat (pgap 256 c) <= m)%nat ->
       (cost (G outd outdC ind indC c cC plus plusC minus minusC sv svC bad badC H HC) <= Z.to_nat (pgap 256 c) * 80 + 20)%nat) end.
  { induction m as [|m IH]; intros c' cC' p' pC' mi' miC' s' sC' b' bC' [g] HC' Hm;
      cstart; dbdec; csimpl.
    - exfalso. pose proof (pgap_succ 256 c' e). lia.
    - lia.
    - pose proof (pgap_succ 256 c' e) as Hs.
      repeat (dif; csimpl);
      match goal with |- context [@cost ?T (?G' outd outdC ind indC (c' + 1)%uint63 ?w ?a2 ?aC2 ?b2 ?bC2 ?d2 ?dC2 ?e2 ?eC2 ?h ?hc)] =>
        have HI := (IH (c' + 1)%uint63 w a2 aC2 b2 bC2 d2 dC2 e2 eC2 h hc ltac:(lia) : (@cost T (G' outd outdC ind indC (c' + 1)%uint63 w a2 aC2 b2 bC2 d2 dC2 e2 eC2 h hc) <= _)%nat) end;
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G outd outdC ind indC c cC plus plusC minus minusC sv svC bad badC H HC)] =>
    exact (HG _ c cC plus plusC minus minusC sv svC bad badC H HC (le_n _) : (@cost T (G outd outdC ind indC c cC plus plusC minus minusC sv svC bad badC H HC) <= _)%nat) end.
Qed.


Lemma andb_time a aC b bC : (cost (extract (andb_cost stepsCM a aC) b bC) <= 5)%nat.
Proof. unfold andb_cost. csimpl. destruct a; csimpl; lia. Qed.

Ltac gen_andb := z0 andb_cost; repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (andb_cost stepsCM ?a ?aC) ?b ?bC =>
    let Hc := fresh "Hand" in
    have Hc := (andb_time a aC b bC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma hg_nonneg n q sp : (0 <= hg n q sp)%Z.
Proof. unfold hg. pose proof (to_Z_bounded (n - q)). pose proof (to_Z_bounded sp). lia. Qed.

Lemma hg_push n q sp p : (andb (p <? n) (q <? n)) = true ->
  (Z.to_nat (hg n (q + 1) (sp + 1)) < Z.to_nat (hg n q sp))%nat.
Proof. intros H. pose proof (dec_push n q sp p H) as D. unfold Zwf in D. pose proof (hg_nonneg n (q+1) (sp+1)). lia. Qed.

Lemma hg_pop n q sp : (0 <? sp) = true ->
  (Z.to_nat (hg n q (sp - 1)) < Z.to_nat (hg n q sp))%nat.
Proof. intros H. pose proof (dec_pop n q sp H) as D. unfold Zwf in D. pose proof (hg_nonneg n q (sp-1)). lia. Qed.

Lemma hier_loop_time x xC nxt nxtC n nC s sC ptr ptrC stk stkC sp spC q qC res resC cnt cntC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (hier_loop_cost stepsCM x xC) nxt nxtC) n nC) s sC) ptr ptrC) stk stkC) sp spC) q qC) res resC) cnt cntC) H HC)
     <= Z.to_nat (hg n q sp) * 100 + 100)%nat.
Proof.
  unfold hier_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC nxt nxtC n nC s sC ptr ptrC stk stkC sp spC q qC res resC cnt cntC H HC)] =>
    assert (HG : forall m ptr ptrC stk stkC sp spC q qC res resC cnt cntC H HC, (Z.to_nat (hg n q sp) <= m)%nat ->
       (cost (G x xC nxt nxtC n nC s sC ptr ptrC stk stkC sp spC q qC res resC cnt cntC H HC) <= Z.to_nat (hg n q sp) * 100 + 100)%nat) end.
  { induction m as [|m IH]; intros p' pC' st' stC' sp' spC' q' qC' r' rC' c' cC' [g] HC' Hm;
      cstart; set_simpl; gen_ch; gen_andb; (dif; csimpl); gen_ch; gen_andb; dbdec; csimpl.
    all: try (dbdec; csimpl).
    all: set_simpl; gen_ch.
    all: try (match goal with e : (_ && _)%bool = true |- _ => pose proof (hg_push n q' sp' _ e) end).
    all: try (match goal with e : (0 <? _) = true |- _ => pose proof (hg_pop n q' sp' e) end).
    all: try lia.
    all: match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?a1 ?b1 ?a2 ?b2 ?a3 ?b3 ?a4 ?b4 ?a5 ?b5 ?a6 ?b6 ?h ?hc)] =>
        is_var G';
        have HI := (IH a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 h hc ltac:(lia) : (@cost T (G' x1 x2 x3 x4 x5 x6 x7 x8 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 h hc) <= _)%nat) end.
    all: lia. }
  match goal with |- context [@cost ?T (?G x xC nxt nxtC n nC s sC ptr ptrC stk stkC sp spC q qC res resC cnt cntC H HC)] =>
    exact (HG _ ptr ptrC stk stkC sp spC q qC res resC cnt cntC H HC (le_n _) : (@cost T (G x xC nxt nxtC n nC s sC ptr ptrC stk stkC sp spC q qC res resC cnt cntC H HC) <= _)%nat) end.
Qed.


Lemma splitc_time lo loC hi hiC : (cost (extract (splitc_cost stepsCM lo loC) hi hiC) <= 30)%nat.
Proof. unfold splitc_cost, andb_cost. csimpl. destruct (lo <? hi); csimpl; lia. Qed.

Lemma midp_time lo loC hi hiC : (cost (extract (midp_cost stepsCM lo loC) hi hiC) <= 20)%nat.
Proof. unfold midp_cost. csimpl. lia. Qed.

Ltac gen_sm := z0 splitc_cost; z0 midp_cost; repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (splitc_cost stepsCM ?a ?aC) ?b ?bC =>
    let Hc := fresh "Hsp" in
    have Hc := (splitc_time a aC b bC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | extract (midp_cost stepsCM ?a ?aC) ?b ?bC =>
    let Hc := fresh "Hmid" in
    have Hc := (midp_time a aC b bC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  end end.

Ltac gen_mc := z0 merge_loop_cost; z1 merge_loop_cost; z2 merge_loop_cost; z3 merge_loop_cost;
  z4 merge_loop_cost; z5 merge_loop_cost; z6 merge_loop_cost; z7 merge_loop_cost;
  z0 copy_loop_cost; z1 copy_loop_cost; z2 copy_loop_cost; z3 copy_loop_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (extract (extract (extract (extract (extract (extract (extract (merge_loop_cost stepsCM ?x ?xC) ?s ?sC) ?d ?dC) ?ie ?ieC) ?je ?jeC) ?i ?iC) ?j ?jC) ?k ?kC) ?H ?HC =>
    let Hc := fresh "Hmerge" in
    have Hc := (merge_loop_time x xC s sC d dC ie ieC je jeC i iC j jC k kC H HC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | extract (extract (extract (extract (copy_loop_cost stepsCM ?s ?sC) ?d ?dC) ?h ?hC) ?k ?kC) ?H ?HC =>
    let Hc := fresh "Hcopy" in
    have Hc := (copy_loop_time s sC d dC h hC k kC H HC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  end end.

Lemma midp_val lo hi : splitc lo hi = true ->
  φ (midp lo hi) = (φ lo + (φ hi - φ lo) / 2)%Z.
Proof.
  intros H. unfold splitc in H. apply andb_prop in H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold midp.
  assert ((φ (hi - lo)) = (φ hi) - (φ lo))%Z by sia. sia.
Qed.

Lemma halves lo hi k : splitc lo hi = true -> (Z.to_nat (pgap hi lo) <= 2 ^ S k)%nat ->
  (Z.to_nat (pgap (midp lo hi) lo) <= 2 ^ k)%nat /\ (Z.to_nat (pgap hi (midp lo hi)) <= 2 ^ k)%nat /\
  (Z.to_nat (pgap (midp lo hi) lo) + Z.to_nat (pgap hi (midp lo hi)) = Z.to_nat (pgap hi lo))%nat /\
  (2 <= Z.to_nat (pgap hi lo))%nat /\
  Z.to_nat (mg (midp lo hi) lo hi (midp lo hi)) = Z.to_nat (pgap hi lo).
Proof.
  intros H Hk. pose proof (midp_val lo hi H) as M. apply splitc_spec in H.
  unfold mg, pgap in *. rewrite Nat.pow_succ_r' in Hk.
  set (P := (2 ^ k)%nat) in *. clearbody P.
  set (d := (φ hi - φ lo)%Z) in *.
  assert (0 <= d / 2 /\ 2 * (d / 2) <= d <= 2 * (d / 2) + 1)%Z by (split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 2); pose proof (Z.mod_pos_bound d 2); lia]).
  lia.
Qed.


Lemma msort_time x xC a aC t tC lo loC hi hiC H HC k :
  (Z.to_nat (pgap hi lo) <= 2 ^ k)%nat ->
  (cost (extract (extract (extract (extract (extract (msort_cost stepsCM x xC) a aC) t tC) lo loC) hi hiC) H HC)
     <= Z.to_nat (pgap hi lo) * k * 400 + 60)%nat.
Proof.
  unfold msort_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC a aC t tC lo loC hi hiC H HC)] =>
    assert (HG : forall k a aC t tC lo loC hi hiC H HC, (Z.to_nat (pgap hi lo) <= 2 ^ k)%nat ->
       (cost (G x xC a aC t tC lo loC hi hiC H HC) <= Z.to_nat (pgap hi lo) * k * 400 + 60)%nat) end.
  { clear. induction k as [|k IH]; intros a' aC' t' tC' lo' loC' hi' hiC' [g] HC' Hk;
      cstart; gen_sm; dbdec; csimpl.
    - exfalso. pose proof (splitc_spec _ _ e). unfold pgap in Hk. rewrite Nat.pow_0_r in Hk. lia.
    - lia.
    - pose proof (halves lo' hi' k e Hk) as [Hk1 [Hk2 [Hsum [H2 Hmg]]]].
      unfold midp in Hk1, Hk2, Hsum, Hmg.
      match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?a1 ?b1 ?a2 ?b2 ?a3 ?b3 ?a4 ?b4 ?h ?hc)] =>
        is_var G';
        have HI1 := (IH a1 b1 a2 b2 a3 b3 a4 b4 h hc ltac:(lia) : (@cost T (G' x1 x2 a1 b1 a2 b2 a3 b3 a4 b4 h hc) <= _)%nat) end.
      match goal with |- context [msort x a' t' lo' ?m ?h] =>
        cost_destruct_witness (msort x a' t' lo' m h) as [a1 aC1 t1 tC1] eqn:E1 end.
      csimpl.
      match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?a1 ?b1 ?a2 ?b2 ?a3 ?b3 ?a4 ?b4 ?h ?hc)] =>
        is_var G';
        have HI2 := (IH a1 b1 a2 b2 a3 b3 a4 b4 h hc ltac:(lia) : (@cost T (G' x1 x2 a1 b1 a2 b2 a3 b3 a4 b4 h hc) <= _)%nat) end.
      match goal with |- context [msort x a1 t1 ?l ?m ?h] =>
        cost_destruct_witness (msort x a1 t1 l m h) as [a2 aC2 t2 tC2] eqn:E2 end.
      csimpl. gen_mc. rewrite Hmg in Hmerge.
      clear -Hmerge Hcopy HI1 HI2 Hsum H2 HB Hmid Hsp.
      revert Hmerge Hcopy HI1 HI2 Hsum H2.
      generalize (Z.to_nat (pgap (lo' + (hi' - lo') / 2) lo')) (Z.to_nat (pgap hi' (lo' + (hi' - lo') / 2))) (Z.to_nat (pgap hi' lo')).
      intros m1 m2 m0 ? ? ? ? Hs ?.
      assert (E : (m1 * k * 400 + m2 * k * 400 = m0 * k * 400)%nat) by (rewrite <- Hs; nia).
      assert (E' : (m0 * S k * 400 = m0 * k * 400 + m0 * 400)%nat) by nia.
      rewrite E'. lia.
    - lia. }
  intros Hk.
  match goal with |- context [@cost ?T (?G x xC a aC t tC lo loC hi hiC H HC)] =>
    exact (HG k a aC t tC lo loC hi hiC H HC Hk : (@cost T (G x xC a aC t tC lo loC hi hiC H HC) <= _)%nat) end.
Qed.


Lemma negb_time b bC : (cost (negb_cost stepsCM b bC) <= 5)%nat.
Proof. unfold negb_cost. csimpl. destruct b; csimpl; lia. Qed.

Lemma pow_log2_up N : (N <= 2 ^ Nat.log2_up N)%nat.
Proof.
  destruct (Nat.le_gt_cases N 1) as [H|H].
  - rewrite Nat.log2_up_eqn0; [lia|]. cbn. lia.
  - apply Nat.log2_up_spec. lia.
Qed.

Lemma pgap0 a : Z.to_nat (pgap a 0) = Z.to_nat (φ a).
Proof. unfold pgap. change (φ 0) with 0%Z. lia. Qed.

Lemma hg00 a : Z.to_nat (hg a 0 0) = (2 * Z.to_nat (φ a))%nat.
Proof. unfold hg. change (φ 0) with 0%Z. rewrite Z.add_0_r. assert (φ (a - 0) = φ a) by sia. pose proof (to_Z_bounded a). lia. Qed.

Lemma size_eq (x : array PrimString.string) N : N = size x -> Z.to_nat (φ (PArray.length x)) = N.
Proof. intros ->. reflexivity. Qed.

Lemma pow_log2_up_eq (x : array PrimString.string) N : N = size x -> (Z.to_nat (pgap (PArray.length x) 0) <= 2 ^ Nat.log2_up N)%nat.
Proof. intros E. rewrite pgap0 (size_eq _ _ E). apply pow_log2_up. Qed.

Ltac gen_main N :=
  z0 init_loop_cost; z1 init_loop_cost; z2 init_loop_cost; z3 init_loop_cost;
  z0 msort_cost; z1 msort_cost; z2 msort_cost; z3 msort_cost; z4 msort_cost;
  z0 build_loop_cost; z1 build_loop_cost; z2 build_loop_cost; z3 build_loop_cost; z4 build_loop_cost; z5 build_loop_cost;
  z0 deg_loop_cost; z1 deg_loop_cost; z2 deg_loop_cost; z3 deg_loop_cost; z4 deg_loop_cost;
  z0 chk_loop_cost; z1 chk_loop_cost; z2 chk_loop_cost; z3 chk_loop_cost; z4 chk_loop_cost; z5 chk_loop_cost; z6 chk_loop_cost;
  z0 hier_loop_cost; z1 hier_loop_cost; z2 hier_loop_cost; z3 hier_loop_cost; z4 hier_loop_cost; z5 hier_loop_cost;
  z6 hier_loop_cost; z7 hier_loop_cost; z8 hier_loop_cost; z9 hier_loop_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (extract (extract (init_loop_cost stepsCM ?a ?aC) ?n ?nC) ?k ?kC) ?H ?HC =>
    let Hc := fresh "Hinit" in
    have Hc := (init_loop_time a aC n nC k kC H HC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | extract (extract (extract (extract (extract (msort_cost stepsCM ?x ?xC) ?a ?aC) ?t ?tC) ?lo ?loC) ?hi ?hiC) ?H ?HC =>
    let Hc := fresh "Hms" in
    have Hc := (msort_time x xC a aC t tC lo loC hi hiC H HC (Nat.log2_up N) : _ -> (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | extract (extract (extract (extract (extract (extract (build_loop_cost stepsCM ?x ?xC) ?o ?oC) ?n ?nC) ?a ?aC) ?b ?bC) ?k ?kC) ?H ?HC =>
    let Hc := fresh "Hbuild" in
    have Hc := (build_loop_time x xC o oC n nC a aC b bC k kC H HC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | extract (extract (extract (extract (extract (deg_loop_cost stepsCM ?x ?xC) ?n ?nC) ?a ?aC) ?b ?bC) ?k ?kC) ?H ?HC =>
    let Hc := fresh "Hdeg" in
    have Hc := (deg_loop_time x xC n nC a aC b bC k kC H HC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | extract (extract (extract (extract (extract (extract (extract (chk_loop_cost stepsCM ?o ?oC) ?i ?iC) ?c ?cC) ?p ?pC) ?m ?mC) ?s ?sC) ?b ?bC) ?H ?HC =>
    let Hc := fresh "Hchk" in
    have Hc := (chk_loop_time o oC i iC c cC p pC m mC s sC b bC H HC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (hier_loop_cost stepsCM ?x ?xC) ?a1 ?b1) ?a2 ?b2) ?a3 ?b3) ?a4 ?b4) ?a5 ?b5) ?a6 ?b6) ?a7 ?b7) ?a8 ?b8) ?a9 ?b9) ?H ?HC =>
    let Hc := fresh "Hhier" in
    have Hc := (hier_loop_time x xC a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 H HC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  | negb_cost stepsCM ?b ?bC =>
    let Hc := fresh "Hneg" in
    have Hc := (negb_time b bC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc
  end end.

Opaque PArray.make.
Lemma catenyms_impl_time x xC :
  (cost (catenyms_impl_cost stepsCM x xC) <= size x * Nat.log2_up (size x) * 400 + size x * 400 + 22 * 1000)%nat.
Proof.
  remember (size x) as N eqn:EN.
  remember (N * Nat.log2_up N * 400 + N * 400 + 22 * 1000)%nat as R eqn:ER.
  unfold catenyms_impl_cost. csimpl. set_simpl. gen_main N.
  match goal with |- context [msort x ?a ?t ?lo ?hi ?h] =>
    cost_destruct_witness (msort x a t lo hi h) as [ord ordC t0 t0C] eqn:Em end.
  csimpl. set_simpl. gen_main N.
  match goal with |- context [build_loop x ?o ?n ?a ?b ?k ?h] =>
    cost_destruct_witness (build_loop x o n a b k h) as [nxt nxtC hd hdC] eqn:Eb end.
  csimpl. set_simpl. gen_main N.
  match goal with |- context [deg_loop x ?n ?a ?b ?k ?h] =>
    cost_destruct_witness (deg_loop x n a b k h) as [outd outdC ind indC] eqn:Ed end.
  csimpl. set_simpl. gen_main N.
  match goal with |- context [chk_loop ?o ?i ?c ?p ?m ?s ?b ?h] =>
    cost_destruct_witness (chk_loop o i c p m s b h) as [a3 aC3 bad badC] eqn:Ec end.
  destruct aC3 as [a4 aC4 sv svC]. destruct aC4 as [pl plC mi miC].
  csimpl. set_simpl. gen_main N.
  repeat (first [ dif
                | match goal with |- context [hier_loop x ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?h] =>
                    cost_destruct_witness (hier_loop x a1 a2 a3 a4 a5 a6 a7 a8 a9 h) as [res resC cnt cntC] eqn:Eh end ];
          csimpl; set_simpl; gen_ch; gen_main N).
  all: specialize (Hms (pow_log2_up_eq _ _ EN)).
  all: rewrite pgap0 (size_eq _ _ EN) in Hinit; rewrite pgap0 (size_eq _ _ EN) in Hbuild;
       rewrite pgap0 (size_eq _ _ EN) in Hdeg; rewrite pgap0 (size_eq _ _ EN) in Hms;
       rewrite hg00 (size_eq _ _ EN) in Hhier; rewrite pgap0 in Hchk; change (Z.to_nat (φ 256)) with 256%nat in Hchk.
  all: subst R; lia.
Qed.


Theorem catenyms_time : exists c1 c2 : nat,
  forall (words : list String.string)
  (words_arr : array PrimString.string),
  valid_input words -> repr words_arr words ->
  (cost1 catenyms_cost words_arr <= c1 * ((size words_arr + 1) * (Nat.log2 (size words_arr) + 1)) + c2)%nat.
Proof.
  exists 800%nat, (23 * 1000)%nat. intros words x _ _.
  match goal with |- (_ <= ?R)%nat => remember R as RHS eqn:ER end.
  unfold cost1, catenyms_cost. csimpl.
  z0 catenyms_impl_cost.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with catenyms_impl_cost stepsCM ?a ?aC =>
      have Hc := (catenyms_impl_time a aC : (@cost T X <= _)%nat);
      revert Hc; generalize (@cost T X); intros ? Hc end end.
  subst RHS. remember (size x) as N eqn:EN. clear EN.
  pose proof (Nat.le_log2_up_succ_log2 N) as L.
  assert (A : (N * Nat.log2_up N <= (N + 1) * (Nat.log2 N + 1))%nat) by nia.
  assert (B : (N <= (N + 1) * (Nat.log2 N + 1))%nat) by nia.
  lia.
Qed.

Transparent PArray.make.
