(* Correctness proofs for cardhand_implem.v. *)
(* Implementation of cardhand (cardhand.spec). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import PrimString String Ascii Sorted Permutation.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Unset Lia Cache.

Require Export cardhand_implem.



(* ================================================================== *)
(* Part 1. Subsequences                                                *)
(* ================================================================== *)

Inductive sub {A : Type} : list A -> list A -> Prop :=
| sub_nil : forall l, sub [] l
| sub_cons : forall x s l, sub s l -> sub (x :: s) (x :: l)
| sub_skip : forall x s l, sub s l -> sub s (x :: l).

Section Sub.
Context {A : Type}.

Lemma sub_refl : forall l : list A, sub l l.
Proof. induction l; constructor; auto. Qed.

Lemma sub_length : forall s l : list A, sub s l -> (List.length s <= List.length l)%nat.
Proof. intros s l H; induction H; simpl; lia. Qed.

Lemma sub_in : forall (s l : list A) x, sub s l -> In x s -> In x l.
Proof.
  intros s l x H; induction H; simpl; intros Hi; [contradiction | destruct Hi; auto | auto].
Qed.

Lemma sub_tail : forall (x : A) s l, sub (x :: s) l -> sub s l.
Proof.
  intros x s l H. remember (x :: s) as s0. revert x s Heqs0.
  induction H; intros y s' E; try discriminate.
  - injection E as -> ->. constructor. exact H.
  - constructor. eapply IHsub; eauto.
Qed.

Lemma sub_trans : forall s m l : list A, sub s m -> sub m l -> sub s l.
Proof.
  intros s m l H1 H2. revert s H1. induction H2; intros s0 H1.
  - inversion H1; subst. constructor.
  - inversion H1; subst.
    + constructor.
    + constructor. auto.
    + constructor. auto.
  - constructor. auto.
Qed.

Lemma sub_eq_length : forall s l : list A, sub s l -> List.length s = List.length l -> s = l.
Proof.
  intros s l H; induction H; simpl; intros E.
  - destruct l; [reflexivity | discriminate].
  - f_equal. auto.
  - apply sub_length in H. lia.
Qed.

Lemma sub_app : forall s1 l1 s2 l2 : list A,
  sub s1 l1 -> sub s2 l2 -> sub (s1 ++ s2) (l1 ++ l2).
Proof.
  intros s1 l1 s2 l2 H1 H2. induction H1; simpl.
  - induction l; simpl; [exact H2 | constructor; exact IHl].
  - constructor. exact IHsub.
  - constructor. exact IHsub.
Qed.

Lemma sub_app_split : forall (l s1 s2 : list A), sub (s1 ++ s2) l ->
  exists c d, l = c ++ d /\ sub s1 c /\ sub s2 d.
Proof.
  induction l as [| y l IH]; intros s1 s2 H.
  - inversion H. destruct s1; [| discriminate]. destruct s2; [| discriminate].
    exists [], []. repeat split; constructor.
  - inversion H; subst.
    + destruct s1; [| discriminate]. destruct s2; [| discriminate].
      exists [], (y :: l). repeat split; constructor.
    + destruct s1 as [| z s1].
      * exists [], (y :: l). simpl in *. subst.
        split; [reflexivity | split; [constructor | constructor; exact H2]].
      * simpl in H0. injection H0 as -> E. subst.
        destruct (IH s1 s2 H2) as (c & d & -> & Hc & Hd).
        exists (z :: c), d. split; [reflexivity | split; [constructor; exact Hc | exact Hd]].
    + destruct (IH s1 s2 H2) as (c & d & -> & Hc & Hd).
      exists (y :: c), d. split; [reflexivity | split; [apply sub_skip; exact Hc | exact Hd]].
Qed.

Lemma sub_remove_mid : forall (a : list A) x b s,
  sub s (a ++ x :: b) -> ~ In x s -> sub s (a ++ b).
Proof.
  induction a as [| y a IH]; simpl; intros x b s H Hn.
  - inversion H; subst; [constructor | | exact H2].
    exfalso. apply Hn. left. reflexivity.
  - inversion H; subst.
    + constructor.
    + constructor. eapply IH; [exact H2 |]. intro F. apply Hn. right. exact F.
    + constructor. eapply IH; eauto.
Qed.

Lemma sub_insert_mid : forall (a : list A) x b s,
  sub s (a ++ b) -> sub s (a ++ x :: b).
Proof.
  induction a as [| y a IH]; simpl; intros x b s H.
  - constructor. exact H.
  - inversion H; subst; constructor; auto.
Qed.

Lemma sub_drop_one : forall (c : list A) x d s, sub s (c ++ x :: d) ->
  exists s0, sub s0 (c ++ d) /\ sub s0 s /\ (List.length s <= S (List.length s0))%nat.
Proof.
  induction c as [| y c IH]; simpl; intros x d s H.
  - inversion H; subst.
    + exists []. repeat split; [constructor | constructor | simpl; lia].
    + exists s0. repeat split; [exact H2 | constructor; apply sub_refl | simpl; lia].
    + exists s. repeat split; [exact H2 | apply sub_refl | lia].
  - inversion H; subst.
    + exists []. repeat split; [constructor | constructor | simpl; lia].
    + destruct (IH x d s0 H2) as (s1 & H1 & H3 & H4).
      exists (y :: s1). repeat split; [constructor; exact H1 | constructor; exact H3 | simpl; lia].
    + destruct (IH x d s H2) as (s1 & H1 & H3 & H4).
      exists s1. repeat split; [constructor; exact H1 | exact H3 | exact H4].
Qed.

Lemma sub_insert : forall (s l : list A) x, sub s l -> In x l -> ~ In x s ->
  exists s1 s2, s = s1 ++ s2 /\ sub (s1 ++ x :: s2) l.
Proof.
  intros s l x H; induction H; intros Hi Hn.
  - exists [], []. simpl. split; [reflexivity|].
    destruct (in_split x l Hi) as (l1 & l2 & ->).
    clear. induction l1; simpl; [constructor; constructor | constructor; assumption].
  - destruct Hi as [E | Hi].
    + subst. exfalso. apply Hn. left. reflexivity.
    + destruct IHsub as (s1 & s2 & -> & Hs); [exact Hi | intro F; apply Hn; right; exact F |].
      exists (x0 :: s1), s2. split; [reflexivity|]. simpl. constructor. exact Hs.
  - destruct Hi as [E | Hi].
    + subst. exists [], s. split; [reflexivity|]. simpl. constructor. exact H.
    + destruct IHsub as (s1 & s2 & -> & Hs); [exact Hi | exact Hn |].
      exists s1, s2. split; [reflexivity|]. constructor. exact Hs.
Qed.

Lemma sub_map : forall {B} (f : A -> B) s l, sub s l -> sub (map f s) (map f l).
Proof. intros B f s l H; induction H; simpl; constructor; auto. Qed.

Lemma sub_map_inv : forall {B} (f : A -> B) (l : list A) s, sub s (map f l) ->
  exists S, sub S l /\ map f S = s.
Proof.
  intros B f l; induction l as [| y l IH]; simpl; intros s H.
  - inversion H; subst. exists []. split; [constructor | reflexivity].
  - inversion H; subst.
    + exists []. split; [constructor | reflexivity].
    + destruct (IH s0 H2) as (S & HS & E). exists (y :: S). split; [constructor; exact HS|].
      simpl. rewrite E. reflexivity.
    + destruct (IH s H2) as (S & HS & E). exists S. split; [constructor; exact HS | exact E].
Qed.

Lemma sub_filter : forall (f : A -> bool) l, sub (filter f l) l.
Proof.
  intros f l; induction l as [| y l IH]; simpl; [constructor|].
  destruct (f y); constructor; exact IH.
Qed.

Lemma SS_sub : forall (R : A -> A -> Prop) s l,
  StronglySorted R l -> sub s l -> StronglySorted R s.
Proof.
  intros R s l HS H; induction H.
  - constructor.
  - inversion HS; subst. constructor; [auto|].
    rewrite Forall_forall in *. intros z Hz. apply H3. eapply sub_in; eauto.
  - inversion HS; subst. auto.
Qed.

Lemma sub_of_sorted : forall (R : A -> A -> Prop),
  (forall x y : A, {x = y} + {x <> y}) ->
  (forall x y, R x y -> R y x -> False) ->
  forall l s, (forall x, In x s -> In x l) ->
  StronglySorted R s -> StronglySorted R l -> sub s l.
Proof.
  intros R dec Ras l; induction l as [| y l IH]; intros s Hi Hs Hl.
  - destruct s as [| x s]; [constructor|]. exfalso. exact (Hi x (or_introl eq_refl)).
  - destruct s as [| x s]; [constructor|].
    inversion Hs; subst. inversion Hl; subst.
    rewrite Forall_forall in *.
    destruct (dec x y) as [-> | Nxy].
    + constructor. apply IH; auto.
      intros z Hz. destruct (Hi z (or_intror Hz)) as [E | Hz']; [| exact Hz'].
      subst. exfalso. pose proof (H2 z Hz). eapply Ras; eauto.
    + constructor. apply IH; auto.
      intros z [E | Hz].
      * subst. destruct (Hi z (or_introl eq_refl)) as [E | Hz]; [congruence | exact Hz].
      * destruct (Hi z (or_intror Hz)) as [E | Hz']; [| exact Hz'].
        subst. exfalso. destruct (Hi x (or_introl eq_refl)) as [E | Hx]; [congruence|].
        eapply Ras; [exact (H2 z Hz) | exact (H4 x Hx)].
Qed.

Lemma in_or_incl : (forall x y : A, {x = y} + {x <> y}) ->
  forall h s : list A, (exists x, In x h /\ ~ In x s) \/ incl h s.
Proof.
  intros dec h s. induction h as [| y h IH].
  - right. intros z [].
  - destruct (in_dec dec y s) as [Hy | Hy].
    + destruct IH as [(x & Hx & Hn) | Hinc].
      * left. exists x. split; [right; exact Hx | exact Hn].
      * right. intros z [E | Hz]; [subst; exact Hy | exact (Hinc z Hz)].
    + left. exists y. split; [left; reflexivity | exact Hy].
Qed.

End Sub.

(* ================================================================== *)
(* Part 2. Moves                                                       *)
(* ================================================================== *)

Lemma move_perm : forall h m, move h m -> Permutation h m.
Proof.
  intros h m (a & x & b & c & d & -> & E & ->).
  eapply perm_trans; [apply Permutation_sym, Permutation_middle|].
  rewrite E. apply Permutation_middle.
Qed.

Lemma moves_perm : forall k h h', moves k h h' -> Permutation h h'.
Proof.
  induction k as [| k IH]; simpl; intros h h' H.
  - subst. apply Permutation_refl.
  - destruct H as (m & Hm & Hk). eapply perm_trans; [apply move_perm; exact Hm | auto].
Qed.

(* The cards never moved form a common subsequence. *)
Lemma moves_lower : forall k h h', moves k h h' ->
  exists S, sub S h /\ sub S h' /\ (List.length h <= List.length S + k)%nat.
Proof.
  induction k as [| k IH]; simpl; intros h h' H.
  - subst. exists h'. repeat split; [apply sub_refl | apply sub_refl | lia].
  - destruct H as (m & (a & x & b & c & d & -> & E & ->) & Hk).
    destruct (IH _ _ Hk) as (S' & H1 & H2 & H3).
    destruct (sub_drop_one c x d S' H1) as (S0 & H4 & H5 & H6).
    exists S0. repeat split.
    + apply sub_insert_mid. rewrite E. exact H4.
    + eapply sub_trans; eauto.
    + assert (E' : List.length (a ++ b) = List.length (c ++ d)) by (rewrite E; reflexivity).
      rewrite !length_app in *. simpl in *. lia.
Qed.

(* A common subsequence of h and a permutation h' of h stays put while
   the other cards are moved, one move each. *)
Lemma moves_upper : forall k (h h' S : list String.string),
  List.length h = (k + List.length S)%nat -> NoDup h -> Permutation h h' ->
  sub S h -> sub S h' -> moves k h h'.
Proof.
  induction k as [| k IH]; simpl; intros h h' S Hl Hd Hp H1 H2.
  - pose proof (sub_eq_length S h H1 ltac:(lia)) as E1.
    pose proof (Permutation_length Hp) as Hl'.
    pose proof (sub_eq_length S h' H2 ltac:(lia)) as E2. congruence.
  - destruct (in_or_incl string_dec h S) as [(x & Hx & Hn) | Hinc].
    2:{ exfalso. pose proof (NoDup_incl_length Hd Hinc). lia. }
    destruct (in_split x h Hx) as (a & b & ->).
    pose proof (sub_remove_mid a x b S H1 Hn) as Hab.
    assert (Hx' : In x h') by (eapply Permutation_in; [exact Hp | exact Hx]).
    destruct (sub_insert S h' x H2 Hx' Hn) as (S1 & S2 & -> & Hs).
    destruct (sub_app_split (a ++ b) S1 S2 Hab) as (c & d & E & Hc & Hd').
    exists (c ++ x :: d). split.
    + exists a, x, b, c, d. repeat split; exact E.
    + assert (Hm : move (a ++ x :: b) (c ++ x :: d))
        by (exists a, x, b, c, d; repeat split; exact E).
      pose proof (move_perm _ _ Hm) as Pm.
      apply IH with (S := S1 ++ x :: S2).
      * pose proof (Permutation_length Pm) as E'.
        rewrite !length_app in *. simpl in *. lia.
      * eapply Permutation_NoDup; [exact Pm | exact Hd].
      * eapply perm_trans; [apply Permutation_sym; exact Pm | exact Hp].
      * apply sub_app; [exact Hc | constructor; exact Hd'].
      * exact Hs.
Qed.

(* ================================================================== *)
(* Part 3. Cards                                                       *)
(* ================================================================== *)

Lemma char_in_cons : forall ch c s,
  char_in ch (String c s) <-> c = ch \/ char_in ch s.
Proof.
  intros ch c s. split.
  - intros [[| k] Hk]; simpl in Hk.
    + left. congruence.
    + right. exists k. exact Hk.
  - intros [-> | [k Hk]]; [exists 0%nat; reflexivity | exists (S k); exact Hk].
Qed.

Lemma char_in_empty : forall ch, ~ char_in ch EmptyString.
Proof. intros ch [k Hk]. destruct k; discriminate. Qed.

Lemma pos_lt : forall ch s, char_in ch s -> (pos ch s < String.length s)%nat.
Proof.
  intros ch s; induction s as [| c s IH]; intros H.
  - exfalso. exact (char_in_empty ch H).
  - simpl. destruct (Ascii.eqb_spec c ch); [lia|].
    apply char_in_cons in H. destruct H as [E | H]; [congruence|].
    specialize (IH H). lia.
Qed.

Lemma get_pos : forall ch s, char_in ch s -> String.get (pos ch s) s = Some ch.
Proof.
  intros ch s; induction s as [| c s IH]; intros H.
  - exfalso. exact (char_in_empty ch H).
  - simpl. destruct (Ascii.eqb_spec c ch); [simpl; congruence|].
    apply char_in_cons in H. destruct H as [E | H]; [congruence|].
    simpl. exact (IH H).
Qed.

Lemma pos_inj : forall a b s, char_in a s -> char_in b s -> pos a s = pos b s -> a = b.
Proof.
  intros a b s Ha Hb E.
  pose proof (get_pos a s Ha) as Ga. pose proof (get_pos b s Hb) as Gb.
  rewrite E in Ga. congruence.
Qed.

Definition valid_card (c : String.string) : Prop :=
  String.length c = 2%nat /\
  (exists r, String.get 0 c = Some r /\ char_in r rank_order) /\
  (exists u, String.get 1 c = Some u /\ char_in u suit_chars).

Lemma valid_cards : forall h, valid_input h -> Forall valid_card h.
Proof.
  intros h [_ H2 H3 H4 _]. rewrite Forall_forall in *.
  intros c Hc. repeat split; auto.
Qed.

Definition sidx (c : String.string) : nat := pos (suit c) suit_chars.

Lemma valid_suit : forall c, valid_card c ->
  String.get 1 c = Some (suit c) /\ char_in (suit c) suit_chars.
Proof.
  intros c (_ & _ & u & Hu & Hi). unfold suit. rewrite Hu. auto.
Qed.

Lemma valid_rank : forall c, valid_card c -> exists r,
  String.get 0 c = Some r /\ rank c = pos r rank_order /\ char_in r rank_order.
Proof.
  intros c (_ & (r & Hr & Hi) & _). exists r. unfold rank. rewrite Hr. auto.
Qed.

Lemma rank_lt : forall c, valid_card c -> (rank c < 13)%nat.
Proof.
  intros c Hc. destruct (valid_rank c Hc) as (r & _ & -> & Hi).
  exact (pos_lt r rank_order Hi).
Qed.

Lemma sidx_lt : forall c, valid_card c -> (sidx c < 4)%nat.
Proof.
  intros c Hc. destruct (valid_suit c Hc) as [_ Hi]. exact (pos_lt _ suit_chars Hi).
Qed.

Lemma suit_of_sidx : forall x y, valid_card x -> valid_card y ->
  sidx x = sidx y -> suit x = suit y.
Proof.
  intros x y Hx Hy E. apply (pos_inj _ _ suit_chars);
    [exact (proj2 (valid_suit x Hx)) | exact (proj2 (valid_suit y Hy)) | exact E].
Qed.

Lemma card_eq : forall x y, valid_card x -> valid_card y ->
  rank x = rank y -> sidx x = sidx y -> x = y.
Proof.
  intros x y Hx Hy Er Es.
  pose proof (suit_of_sidx x y Hx Hy Es) as Eu.
  destruct (valid_rank x Hx) as (rx & Gx & Rx & Ix).
  destruct (valid_rank y Hy) as (ry & Gy & Ry & Iy).
  assert (rx = ry) by (apply (pos_inj _ _ rank_order); congruence). subst ry.
  destruct (valid_suit x Hx) as [Sx _]. destruct (valid_suit y Hy) as [Sy _].
  rewrite Eu in Sx.
  destruct Hx as (Lx & _). destruct Hy as (Ly & _).
  destruct x as [| a [| b [| ? ?]]]; try discriminate.
  destruct y as [| a' [| b' [| ? ?]]]; try discriminate.
  simpl in *. congruence.
Qed.

(* ================================================================== *)
(* Part 4. Target orders and keys                                      *)
(* ================================================================== *)

Open Scope Z_scope.

Definition sid (c : String.string) : Z := Z.of_nat (sidx c).
Definition rk (c : String.string) : Z := Z.of_nat (rank c).

(* Target t (0 <= t < 4096): suit s goes to block sgZ t s, ascending when
   drZ t s = 1. *)
Definition sgZ (t s : Z) : Z := (t / 4 ^ s) mod 4.
Definition drZ (t s : Z) : Z := (t / (256 * 2 ^ s)) mod 2.
Definition keyZ (t s r : Z) : Z :=
  sgZ t s * 13 + (if drZ t s =? 1 then r else 12 - r).
Definition key (t : Z) (c : String.string) : Z := keyZ t (sid c) (rk c).

Definition injb (t : Z) : bool :=
  let a := sgZ t 0 in let b := sgZ t 1 in let c := sgZ t 2 in let d := sgZ t 3 in
  negb (a =? b) && negb (a =? c) && negb (a =? d) &&
  negb (b =? c) && negb (b =? d) && negb (c =? d).

Lemma sg_range : forall t s, 0 <= sgZ t s < 4.
Proof. intros t s. unfold sgZ. apply Z.mod_pos_bound. lia. Qed.

Lemma four_cases : forall s, 0 <= s < 4 -> s = 0 \/ s = 1 \/ s = 2 \/ s = 3.
Proof. intros s H. lia. Qed.

Lemma inj_prop : forall t, injb t = true -> forall s s', 0 <= s < 4 -> 0 <= s' < 4 ->
  sgZ t s = sgZ t s' -> s = s'.
Proof.
  intros t H s s' Hs Hs' E. unfold injb in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  rewrite Bool.negb_true_iff, Z.eqb_neq in H1, H2, H3, H4, H5, H6.
  destruct (four_cases s Hs) as [-> | [-> | [-> | ->]]];
  destruct (four_cases s' Hs') as [-> | [-> | [-> | ->]]];
  try reflexivity; exfalso; congruence.
Qed.

Lemma sid_range : forall c, valid_card c -> 0 <= sid c < 4.
Proof. intros c Hc. unfold sid. pose proof (sidx_lt c Hc). lia. Qed.

Lemma rk_range : forall c, valid_card c -> 0 <= rk c < 13.
Proof. intros c Hc. unfold rk. pose proof (rank_lt c Hc). lia. Qed.

Lemma key_range : forall t c, valid_card c -> 0 <= key t c < 52.
Proof.
  intros t c Hc. unfold key, keyZ. pose proof (sg_range t (sid c)).
  pose proof (rk_range c Hc). destruct (drZ t (sid c) =? 1); lia.
Qed.

Lemma key_inj : forall t x y, injb t = true -> valid_card x -> valid_card y ->
  key t x = key t y -> x = y.
Proof.
  intros t x y Ht Hx Hy E. unfold key, keyZ in E.
  pose proof (sg_range t (sid x)). pose proof (sg_range t (sid y)).
  pose proof (rk_range x Hx). pose proof (rk_range y Hy).
  assert (Es : sgZ t (sid x) = sgZ t (sid y))
    by (destruct (drZ t (sid x) =? 1), (drZ t (sid y) =? 1); lia).
  pose proof (inj_prop t Ht _ _ (sid_range x Hx) (sid_range y Hy) Es) as Es'.
  rewrite Es' in E. apply card_eq; auto.
  - destruct (drZ t (sid y) =? 1); unfold rk in *; lia.
  - unfold sid in Es'. lia.
Qed.

Lemma SS_nth : forall {A} (R : A -> A -> Prop) l i j x y, StronglySorted R l ->
  (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
  intros A R l; induction l as [| c l IH]; intros i j x y HS Hij Hx Hy.
  - destruct i; discriminate.
  - inversion HS; subst. destruct i as [| i]; destruct j as [| j]; try lia.
    + simpl in Hx, Hy. injection Hx as ->. rewrite Forall_forall in H2.
      apply H2. eapply nth_error_In; eauto.
    + simpl in Hx, Hy. exact (IH i j x y H1 ltac:(lia) Hx Hy).
Qed.

Lemma nth_SS : forall {A} (R : A -> A -> Prop) l,
  (forall i j x y, (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y -> R x y) ->
  StronglySorted R l.
Proof.
  intros A R l; induction l as [| c l IH]; intros H; constructor.
  - apply IH. intros i j x y Hij Hx Hy. apply (H (S i) (S j)); simpl; auto. lia.
  - rewrite Forall_forall. intros y Hy. destruct (In_nth_error l y Hy) as [j Hj].
    apply (H 0%nat (S j)); simpl; auto. lia.
Qed.

Lemma SS_map : forall {A B} (R : A -> A -> Prop) (R' : B -> B -> Prop) (f : A -> B) l,
  StronglySorted R l ->
  (forall x y, In x l -> In y l -> R x y -> R' (f x) (f y)) ->
  StronglySorted R' (map f l).
Proof.
  intros A B R R' f l; induction l as [| c l IH]; intros HS H; simpl; constructor.
  - inversion HS; subst. apply IH; auto. intros x y Hx Hy. apply H; right; auto.
  - inversion HS; subst. rewrite Forall_forall in *. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as (y & <- & Hy).
    apply H; [left; reflexivity | right; exact Hy | auto].
Qed.

Lemma SS_map_inv : forall {A B} (R : B -> B -> Prop) (f : A -> B) l,
  StronglySorted R (map f l) -> StronglySorted (fun x y => R (f x) (f y)) l.
Proof.
  intros A B R f l; induction l as [| c l IH]; simpl; intros HS; constructor.
  - inversion HS; subst. auto.
  - inversion HS; subst. rewrite Forall_forall in *. intros y Hy.
    apply H2. apply in_map. exact Hy.
Qed.

(* A hand sorted by the keys of an admissible target is sorted. *)
Lemma keysorted_hand : forall t l, injb t = true -> Forall valid_card l ->
  StronglySorted (fun x y => key t x < key t y) l -> sorted_hand l.
Proof.
  intros t l Ht Hv HS. rewrite Forall_forall in Hv. split.
  - intros i j k x z Hijk Hx Hz Es.
    destruct (nth_error l j) as [y |] eqn:Hy.
    2:{ exfalso. apply nth_error_None in Hy.
        assert (nth_error l k <> None) by congruence.
        apply nth_error_Some in H. lia. }
    exists y. split; [reflexivity|].
    pose proof (nth_error_In _ _ Hx) as Ix. pose proof (nth_error_In _ _ Hy) as Iy.
    pose proof (nth_error_In _ _ Hz) as Iz.
    pose proof (SS_nth _ l i j x y HS ltac:(lia) Hx Hy) as K1.
    pose proof (SS_nth _ l j k y z HS ltac:(lia) Hy Hz) as K2.
    assert (Exz : sid x = sid z) by (unfold sid, sidx; rewrite Es; reflexivity).
    unfold key, keyZ in K1, K2. rewrite <- Exz in K2.
    pose proof (sg_range t (sid x)). pose proof (sg_range t (sid y)).
    pose proof (rk_range x (Hv x Ix)). pose proof (rk_range y (Hv y Iy)).
    pose proof (rk_range z (Hv z Iz)).
    assert (Eg : sgZ t (sid y) = sgZ t (sid x)).
    { destruct (drZ t (sid x) =? 1), (drZ t (sid y) =? 1); lia. }
    pose proof (inj_prop t Ht _ _ (sid_range y (Hv y Iy)) (sid_range x (Hv x Ix)) Eg) as E.
    apply suit_of_sidx; [apply Hv; auto | apply Hv; auto | unfold sid in E; lia].
  - intros u. unfold ranks_of_suit.
    pose proof (SS_sub _ _ _ HS (sub_filter (fun c => Ascii.eqb (suit c) u) l)) as HSf.
    assert (Hm : forall c, In c (filter (fun c => Ascii.eqb (suit c) u) l) ->
               In c l /\ suit c = u).
    { intros c Hc. apply filter_In in Hc. destruct Hc as [Hc Hu].
      apply Ascii.eqb_eq in Hu. auto. }
    remember (filter (fun c => Ascii.eqb (suit c) u) l) as f eqn:Ef. clear Ef.
    destruct f as [| c0 f'].
    + left. constructor.
    + assert (Hs0 : forall c, In c (c0 :: f') -> sid c = sid c0).
      { intros c Hc. destruct (Hm c Hc) as [_ E1]. destruct (Hm c0 (or_introl eq_refl)) as [_ E2].
        unfold sid, sidx. rewrite E1, E2. reflexivity. }
      destruct (drZ t (sid c0) =? 1) eqn:Ed.
      * left. apply StronglySorted_Sorted. eapply SS_map; [exact HSf|].
        intros x y Hx Hy Hk. unfold key, keyZ in Hk.
        rewrite (Hs0 x Hx), (Hs0 y Hy), Ed in Hk. unfold rk in Hk. lia.
      * right. apply StronglySorted_Sorted. eapply SS_map; [exact HSf|].
        intros x y Hx Hy Hk. unfold key, keyZ in Hk.
        rewrite (Hs0 x Hx), (Hs0 y Hy), Ed in Hk. unfold rk in Hk. lia.
Qed.

(* A sorted hand is sorted by the keys of some admissible target: the
   suits are ranked by first occurrence (absent suits last), each suit's
   direction is the one of its ranks. *)

Definition presb (l : list String.string) (s : Z) : bool :=
  existsb (fun c => sid c =? s) l.

Fixpoint fo (s : Z) (l : list String.string) : nat :=
  match l with
  | [] => 0%nat
  | c :: l' => if sid c =? s then 0%nat else S (fo s l')
  end.

Lemma fo_found : forall l s, presb l s = true ->
  exists c, nth_error l (fo s l) = Some c /\ sid c = s.
Proof.
  intros l s; induction l as [| c l IH]; simpl; intros H; [discriminate|].
  destruct (sid c =? s) eqn:E.
  - exists c. split; [reflexivity | apply Z.eqb_eq; exact E].
  - simpl in H. destruct (IH H) as (c' & H1 & H2). exists c'. auto.
Qed.

Lemma fo_min : forall l s i c, nth_error l i = Some c -> sid c = s -> (fo s l <= i)%nat.
Proof.
  intros l s; induction l as [| c0 l IH]; intros i c Hi Hs.
  - destruct i; discriminate.
  - simpl. destruct (sid c0 =? s) eqn:E; [lia|].
    destruct i as [| i]; simpl in Hi.
    + injection Hi as ->. rewrite Hs, Z.eqb_refl in E. discriminate.
    + specialize (IH i c Hi Hs). lia.
Qed.

Lemma fo_lt : forall l s, presb l s = true -> (fo s l < List.length l)%nat.
Proof.
  intros l s H. destruct (fo_found l s H) as (c & Hc & _).
  apply nth_error_Some. congruence.
Qed.

Lemma presb_intro : forall l i c, nth_error l i = Some c -> presb l (sid c) = true.
Proof.
  intros l i c H. unfold presb. apply existsb_exists. exists c.
  split; [eapply nth_error_In; eauto | apply Z.eqb_refl].
Qed.

Definition ind (b : bool) : Z := if b then 1 else 0.

Lemma ind_le : forall x y z, x < y -> ind (z <? x) <= ind (z <? y).
Proof.
  intros x y z H. unfold ind.
  destruct (Z.ltb_spec z x), (Z.ltb_spec z y); lia.
Qed.

Lemma ind_self : forall x, ind (x <? x) = 0.
Proof. intros x. unfold ind. rewrite Z.ltb_irrefl. reflexivity. Qed.

Lemma ind_lt : forall x y, x < y -> ind (x <? y) = 1.
Proof. intros x y H. unfold ind. rewrite (proj2 (Z.ltb_lt x y) H). reflexivity. Qed.

Lemma ind_range : forall b, 0 <= ind b <= 1.
Proof. intros []; simpl; lia. Qed.

Section Rank4.
Variable code : Z -> Z.

Definition sigma (s : Z) : Z :=
  ind (code 0 <? code s) + ind (code 1 <? code s) +
  ind (code 2 <? code s) + ind (code 3 <? code s).

Lemma sigma_mono : forall a b, 0 <= a < 4 -> code a < code b -> sigma a < sigma b.
Proof.
  intros a b Ha H. unfold sigma.
  pose proof (ind_le _ _ (code 0) H). pose proof (ind_le _ _ (code 1) H).
  pose proof (ind_le _ _ (code 2) H). pose proof (ind_le _ _ (code 3) H).
  pose proof (ind_self (code a)). pose proof (ind_lt _ _ H).
  destruct (four_cases a Ha) as [-> | [-> | [-> | ->]]]; lia.
Qed.

Lemma sigma_range : forall s, 0 <= s < 4 -> 0 <= sigma s < 4.
Proof.
  intros s Hs. unfold sigma.
  pose proof (ind_range (code 0 <? code s)). pose proof (ind_range (code 1 <? code s)).
  pose proof (ind_range (code 2 <? code s)). pose proof (ind_range (code 3 <? code s)).
  pose proof (ind_self (code s)).
  destruct (four_cases s Hs) as [-> | [-> | [-> | ->]]]; lia.
Qed.
End Rank4.

Lemma choose_dir : forall (P Q : Z -> Prop),
  (forall s, 0 <= s < 4 -> P s \/ Q s) ->
  exists d : Z -> Z, forall s, 0 <= s < 4 -> (d s = 1 /\ P s) \/ (d s = 0 /\ Q s).
Proof.
  intros P Q H.
  assert (G : forall n : nat, exists d : Z -> Z, forall s, 0 <= s < Z.of_nat n -> s < 4 ->
            (d s = 1 /\ P s) \/ (d s = 0 /\ Q s)).
  { induction n as [| n (d & Hd)].
    - exists (fun _ => 0). intros s Hs. lia.
    - destruct (Z.lt_ge_cases (Z.of_nat n) 4) as [Hn | Hn].
      + destruct (H (Z.of_nat n) ltac:(lia)) as [Hp | Hq].
        * exists (fun s => if s =? Z.of_nat n then 1 else d s). intros s Hs Hs4.
          destruct (Z.eqb_spec s (Z.of_nat n)); [subst; auto | apply Hd; lia].
        * exists (fun s => if s =? Z.of_nat n then 0 else d s). intros s Hs Hs4.
          destruct (Z.eqb_spec s (Z.of_nat n)); [subst; auto | apply Hd; lia].
      + exists d. intros s Hs Hs4. apply Hd; lia. }
  destruct (G 4%nat) as (d & Hd). exists d. intros s Hs. apply Hd; simpl; lia.
Qed.

Definition encode (sg d : Z -> Z) : Z :=
  sg 0 + 4 * sg 1 + 16 * sg 2 + 64 * sg 3 + 256 * (d 0 + 2 * d 1 + 4 * d 2 + 8 * d 3).

Lemma decode : forall sg d,
  (forall s, 0 <= s < 4 -> 0 <= sg s < 4) ->
  (forall s, 0 <= s < 4 -> d s = 0 \/ d s = 1) ->
  0 <= encode sg d < 4096 /\
  forall s, 0 <= s < 4 -> sgZ (encode sg d) s = sg s /\ drZ (encode sg d) s = d s.
Proof.
  intros sg d Hs Hd.
  pose proof (Hs 0 ltac:(lia)). pose proof (Hs 1 ltac:(lia)).
  pose proof (Hs 2 ltac:(lia)). pose proof (Hs 3 ltac:(lia)).
  pose proof (Hd 0 ltac:(lia)). pose proof (Hd 1 ltac:(lia)).
  pose proof (Hd 2 ltac:(lia)). pose proof (Hd 3 ltac:(lia)).
  unfold encode. split; [lia|].
  intros s Hs'. unfold sgZ, drZ.
  destruct (four_cases s Hs') as [-> | [-> | [-> | ->]]];
    [change (4 ^ 0) with 1; change (2 ^ 0) with 1
    | change (4 ^ 1) with 4; change (2 ^ 1) with 2
    | change (4 ^ 2) with 16; change (2 ^ 2) with 4
    | change (4 ^ 3) with 64; change (2 ^ 3) with 8];
    split; Z.to_euclidean_division_equations; lia.
Qed.

Definition us (s : Z) : ascii :=
  match String.get (Z.to_nat s) suit_chars with Some u => u | None => " "%char end.

Lemma us_sid : forall c, valid_card c -> us (sid c) = suit c.
Proof.
  intros c Hc. unfold us, sid. rewrite Nat2Z.id. unfold sidx.
  rewrite get_pos; [reflexivity | exact (proj2 (valid_suit c Hc))].
Qed.

Lemma filter_pair : forall {A B} (R : B -> B -> Prop) (g : A -> B) (f : A -> bool) l i j x y,
  StronglySorted R (map g (filter f l)) -> (i < j)%nat ->
  nth_error l i = Some x -> nth_error l j = Some y -> f x = true -> f y = true ->
  R (g x) (g y).
Proof.
  intros A B R g f l; induction l as [| c l IH]; intros i j x y HS Hij Hx Hy Fx Fy.
  - destruct i; discriminate.
  - destruct i as [| i]; destruct j as [| j]; try lia; simpl in Hx, Hy.
    + injection Hx as ->. simpl in HS. rewrite Fx in HS. simpl in HS.
      inversion HS; subst. rewrite Forall_forall in H2. apply H2.
      apply in_map. apply filter_In. split; [eapply nth_error_In; eauto | exact Fy].
    + apply (IH i j x y); auto; [| lia].
      simpl in HS. destruct (f c); [simpl in HS; inversion HS; auto | exact HS].
Qed.

Lemma sorted_keysorted : forall l, Forall valid_card l -> NoDup l -> sorted_hand l ->
  exists t, 0 <= t < 4096 /\ injb t = true /\
            StronglySorted (fun x y => key t x < key t y) l.
Proof.
  intros l Hv Hnd [Hg Hm]. rewrite Forall_forall in Hv.
  set (code := fun s => if presb l s then Z.of_nat (fo s l)
                        else Z.of_nat (List.length l) + s).
  assert (Hcode : forall s s', 0 <= s < 4 -> 0 <= s' < 4 -> s <> s' -> code s <> code s').
  { intros s s' Hs Hs' Ne. unfold code.
    destruct (presb l s) eqn:Ps, (presb l s') eqn:Ps'.
    - intro E. apply Nat2Z.inj in E.
      destruct (fo_found l s Ps) as (c & Hc & Ec).
      destruct (fo_found l s' Ps') as (c' & Hc' & Ec').
      rewrite E in Hc. congruence.
    - pose proof (fo_lt l s Ps). lia.
    - pose proof (fo_lt l s' Ps'). lia.
    - lia. }
  destruct (choose_dir (fun s => Sorted lt (ranks_of_suit (us s) l))
                       (fun s => Sorted gt (ranks_of_suit (us s) l))
                       (fun s _ => Hm (us s))) as (d & Hd).
  set (t := encode (sigma code) d).
  destruct (decode (sigma code) d (sigma_range code)
             ltac:(intros s Hs; destruct (Hd s Hs) as [[E _] | [E _]]; lia)) as [Ht Hdec].
  fold t in Ht, Hdec.
  assert (Hinj : injb t = true).
  { unfold injb.
    assert (N : forall s s', 0 <= s < 4 -> 0 <= s' < 4 -> s <> s' -> sgZ t s =? sgZ t s' = false).
    { intros s s' Hs Hs' Ne. apply Z.eqb_neq. rewrite (proj1 (Hdec s Hs)), (proj1 (Hdec s' Hs')).
      destruct (Z.lt_trichotomy (code s) (code s')) as [Lt | [Eq | Gt]].
      - pose proof (sigma_mono code s s' Hs Lt). lia.
      - exfalso. exact (Hcode s s' Hs Hs' Ne Eq).
      - pose proof (sigma_mono code s' s Hs' Gt). lia. }
    rewrite !N by lia. reflexivity. }
  exists t. split; [exact Ht|]. split; [exact Hinj|].
  apply nth_SS. intros i j x y Hij Hx Hy.
  pose proof (Hv x (nth_error_In _ _ Hx)) as Vx. pose proof (Hv y (nth_error_In _ _ Hy)) as Vy.
  pose proof (sid_range x Vx) as Rx. pose proof (sid_range y Vy) as Ry.
  pose proof (rk_range x Vx). pose proof (rk_range y Vy).
  unfold key, keyZ.
  destruct (Hdec (sid x) Rx) as [Sx Dx]. destruct (Hdec (sid y) Ry) as [Sy Dy].
  rewrite Sx, Sy, Dx, Dy.
  destruct (Z.eq_dec (sid x) (sid y)) as [Es | Ns].
  - (* same suit: the direction of the suit *)
    rewrite <- Es.
    assert (Fx : Ascii.eqb (suit x) (us (sid x)) = true)
      by (rewrite us_sid by exact Vx; apply Ascii.eqb_refl).
    assert (Fy : Ascii.eqb (suit y) (us (sid x)) = true)
      by (rewrite Es, us_sid by exact Vy; apply Ascii.eqb_refl).
    destruct (Hd (sid x) Rx) as [[E1 S1] | [E0 S0]].
    + rewrite E1, Z.eqb_refl.
      apply Sorted_StronglySorted in S1; [| intros a b c; lia].
      pose proof (filter_pair lt rank _ l i j x y S1 Hij Hx Hy Fx Fy). unfold rk. lia.
    + rewrite E0. replace (0 =? 1) with false by reflexivity.
      apply Sorted_StronglySorted in S0; [| intros a b c; unfold gt; lia].
      pose proof (filter_pair gt rank _ l i j x y S0 Hij Hx Hy Fx Fy). unfold rk. lia.
  - (* different suits: the suit of x occurs first *)
    assert (Hfo : (fo (sid x) l < fo (sid y) l)%nat).
    { pose proof (fo_min l (sid x) i x Hx eq_refl) as Mx.
      destruct (fo_found l (sid y) (presb_intro l j y Hy)) as (c & Hc & Ec).
      destruct (fo_found l (sid x) (presb_intro l i x Hx)) as (c' & Hc' & Ec').
      destruct (Nat.lt_ge_cases (fo (sid x) l) (fo (sid y) l)) as [Lt | Ge]; [exact Lt|].
      exfalso. destruct (Nat.eq_dec (fo (sid x) l) (fo (sid y) l)) as [Eq | Neq].
      - rewrite Eq in Hc'. congruence.
      - pose proof (Hv c (nth_error_In _ _ Hc)) as Vc.
        destruct (Hg (fo (sid y) l) i j c y ltac:(lia) Hc Hy
                    (suit_of_sidx c y Vc Vy ltac:(unfold sid in Ec; lia)))
          as (y' & Hy' & Ey').
        rewrite Hx in Hy'. injection Hy' as <-.
        apply Ns. unfold sid, sidx. rewrite Ey'. fold (sidx c). fold (sid c). exact Ec. }
    assert (Hc : code (sid x) < code (sid y)).
    { unfold code. rewrite (presb_intro l i x Hx), (presb_intro l j y Hy). lia. }
    pose proof (sigma_mono code _ _ Rx Hc).
    destruct (d (sid x) =? 1), (d (sid y) =? 1); lia.
Qed.

(* ================================================================== *)
(* Part 5. Longest common subsequence, target sequences, sorting       *)
(* ================================================================== *)

(* lcs a b: the length of a longest common subsequence (CLRS 15.4). *)
Fixpoint lcs (a b : list Z) : nat :=
  match a with
  | [] => 0%nat
  | x :: a' =>
      (fix go (b : list Z) : nat :=
         match b with
         | [] => 0%nat
         | y :: b' => if x =? y then S (lcs a' b') else Nat.max (lcs a' b) (go b')
         end) b
  end.

Lemma lcs_nil_l : forall b, lcs [] b = 0%nat.
Proof. reflexivity. Qed.

Lemma lcs_nil_r : forall a, lcs a [] = 0%nat.
Proof. intros [| x a]; reflexivity. Qed.

Lemma lcs_cc : forall x a y b, lcs (x :: a) (y :: b) =
  if x =? y then S (lcs a b) else Nat.max (lcs a (y :: b)) (lcs (x :: a) b).
Proof. reflexivity. Qed.

Lemma lcs_sound : forall a b, exists s, sub s a /\ sub s b /\ List.length s = lcs a b.
Proof.
  induction a as [| x a IHa]; intros b.
  - exists []. repeat split; constructor.
  - induction b as [| y b IHb].
    + exists []. rewrite lcs_nil_r. repeat split; constructor.
    + rewrite lcs_cc. destruct (Z.eqb_spec x y) as [-> | Ne].
      * destruct (IHa b) as (s & H1 & H2 & H3). exists (y :: s).
        repeat split; [constructor; auto | constructor; auto | simpl; lia].
      * destruct (IHa (y :: b)) as (s1 & H1 & H2 & H3).
        destruct IHb as (s2 & H4 & H5 & H6).
        destruct (Nat.le_ge_cases (lcs a (y :: b)) (lcs (x :: a) b)).
        -- exists s2. repeat split; [exact H4 | constructor; exact H5 | lia].
        -- exists s1. repeat split; [constructor; exact H1 | exact H2 | lia].
Qed.

Lemma lcs_complete : forall a b s, sub s a -> sub s b -> (List.length s <= lcs a b)%nat.
Proof.
  induction a as [| x a IHa]; intros b s Ha Hb.
  - inversion Ha; subst. simpl. lia.
  - revert s Ha Hb. induction b as [| y b IHb]; intros s Ha Hb.
    + inversion Hb; subst. simpl. lia.
    + rewrite lcs_cc. destruct s as [| z s]; [simpl; lia|].
      destruct (Z.eqb_spec x y) as [-> | Ne].
      * inversion Ha as [| ? ? ? Ha' | ? ? ? Ha']; subst;
          inversion Hb as [| ? ? ? Hb' | ? ? ? Hb']; subst.
        -- pose proof (IHa b s Ha' Hb'). simpl. lia.
        -- pose proof (IHa b s Ha' (sub_tail _ _ _ Hb')). simpl. lia.
        -- pose proof (IHa b s (sub_tail _ _ _ Ha') Hb'). simpl. lia.
        -- pose proof (IHa b (z :: s) Ha' Hb'). lia.
      * inversion Ha as [| ? ? ? Ha' | ? ? ? Ha']; subst.
        -- inversion Hb as [| ? ? ? Hb' | ? ? ? Hb']; subst; [congruence|].
           pose proof (IHb (x :: s) Ha Hb'). lia.
        -- pose proof (IHa (y :: b) (z :: s) Ha' Hb). lia.
Qed.

Lemma lcs_le : forall a b, (lcs a b <= List.length a)%nat.
Proof.
  intros a b. destruct (lcs_sound a b) as (s & H1 & _ & H3).
  pose proof (sub_length _ _ H1). lia.
Qed.

(* The integers lo, lo+1, ..., lo+n-1. *)
Fixpoint zrange (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S n => lo :: zrange (lo + 1) n end.

Lemma in_zrange : forall n lo k, In k (zrange lo n) <-> lo <= k < lo + Z.of_nat n.
Proof.
  induction n as [| n IH]; intros lo k; simpl; [lia|].
  rewrite IH. lia.
Qed.

Lemma zrange_sorted : forall n lo, StronglySorted Z.lt (zrange lo n).
Proof.
  induction n as [| n IH]; intros lo; simpl; constructor; [apply IH|].
  rewrite Forall_forall. intros k Hk. apply in_zrange in Hk. lia.
Qed.

Lemma zrange_snoc : forall n lo, zrange lo (S n) = zrange lo n ++ [lo + Z.of_nat n].
Proof.
  induction n as [| n IH]; intros lo.
  - simpl. f_equal. f_equal. lia.
  - change (zrange lo (S (S n))) with (lo :: zrange (lo + 1) (S n)).
    rewrite IH. simpl. do 3 f_equal. lia.
Qed.

Definition present (a : list Z) (k : Z) : bool := existsb (Z.eqb k) a.

(* The keys of a, in increasing order: the hand sorted in target order. *)
Definition bk (a : list Z) : list Z := filter (present a) (zrange 0 52).

Lemma bk_sorted : forall a, StronglySorted Z.lt (bk a).
Proof. intros a. eapply SS_sub; [apply zrange_sorted | apply sub_filter]. Qed.

Lemma in_bk : forall a k, In k (bk a) <-> In k a /\ 0 <= k < 52.
Proof.
  intros a k. unfold bk, present. rewrite filter_In, in_zrange, existsb_exists.
  split.
  - intros [Hr (y & Hy & E)]. apply Z.eqb_eq in E. subst. split; [exact Hy | lia].
  - intros [Hk Hr]. split; [lia|]. exists k. split; [exact Hk | apply Z.eqb_refl].
Qed.

(* Insertion sort by a key, used only in proofs. *)
Fixpoint ins {A} (f : A -> Z) (x : A) (l : list A) : list A :=
  match l with
  | [] => [x]
  | y :: l' => if f x <=? f y then x :: l else y :: ins f x l'
  end.

Fixpoint isort {A} (f : A -> Z) (l : list A) : list A :=
  match l with [] => [] | x :: l' => ins f x (isort f l') end.

Lemma ins_perm : forall {A} (f : A -> Z) x l, Permutation (ins f x l) (x :: l).
Proof.
  intros A f x l; induction l as [| y l IH]; simpl; [apply Permutation_refl|].
  destruct (f x <=? f y); [apply Permutation_refl|].
  eapply perm_trans; [apply perm_skip; exact IH | apply perm_swap].
Qed.

Lemma isort_perm : forall {A} (f : A -> Z) l, Permutation (isort f l) l.
Proof.
  intros A f l; induction l as [| x l IH]; simpl; [apply Permutation_refl|].
  eapply perm_trans; [apply ins_perm | apply perm_skip; exact IH].
Qed.

Lemma ins_sorted : forall {A} (f : A -> Z) x l,
  StronglySorted (fun a b => f a <= f b) l ->
  StronglySorted (fun a b => f a <= f b) (ins f x l).
Proof.
  intros A f x l; induction l as [| y l IH]; intros HS; simpl.
  - constructor; constructor.
  - inversion HS; subst. destruct (Z.leb_spec (f x) (f y)).
    + constructor; [exact HS|]. constructor; [exact H|].
      rewrite Forall_forall in *. intros z Hz. specialize (H2 z Hz). lia.
    + constructor; [apply IH; exact H1|].
      rewrite Forall_forall in *. intros z Hz.
      apply (Permutation_in _ (ins_perm f x l)) in Hz. destruct Hz as [<- | Hz]; [lia|].
      apply H2. exact Hz.
Qed.

Lemma isort_sorted : forall {A} (f : A -> Z) l,
  StronglySorted (fun a b => f a <= f b) (isort f l).
Proof.
  intros A f l; induction l as [| x l IH]; simpl; [constructor | apply ins_sorted; exact IH].
Qed.

Lemma SS_le_lt : forall {A} (f : A -> Z) l,
  StronglySorted (fun a b => f a <= f b) l -> NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  StronglySorted (fun a b => f a < f b) l.
Proof.
  intros A f l; induction l as [| x l IH]; intros HS Hd Hi; constructor.
  - inversion HS; inversion Hd; subst. apply IH; auto.
    intros a b Ha Hb. apply Hi; right; auto.
  - inversion HS; inversion Hd; subst. rewrite Forall_forall in *. intros y Hy.
    specialize (H2 y Hy). destruct (Z.eq_dec (f x) (f y)) as [E | E]; [| lia].
    exfalso. assert (x = y) by (apply Hi; [left | right | ]; auto). subst. contradiction.
Qed.

(* ================================================================== *)
(* Part 6. The answer                                                  *)
(* ================================================================== *)

(* The number of cards that can stay put for target t. *)
Definition Lt (h : list String.string) (t : Z) : nat :=
  lcs (map (key t) h) (bk (map (key t) h)).

Lemma upper_t : forall h t, valid_input h -> injb t = true ->
  exists h', moves (List.length h - Lt h t) h h' /\ sorted_hand h'.
Proof.
  intros h t Hv Ht. pose proof (valid_cards h Hv) as Vh.
  pose proof (vi_distinct h Hv) as Nd.
  destruct (lcs_sound (map (key t) h) (bk (map (key t) h))) as (s & H1 & H2 & H3).
  destruct (sub_map_inv (key t) h s H1) as (S & HS & <-).
  rewrite length_map in H3.
  assert (SSs : StronglySorted (fun x y => key t x < key t y) S)
    by (apply SS_map_inv; eapply SS_sub; [apply bk_sorted | exact H2]).
  set (h' := isort (key t) h).
  assert (Ph : Permutation h h') by (apply Permutation_sym, isort_perm).
  assert (Vh' : Forall valid_card h')
    by (rewrite Forall_forall in *; intros c Hc; apply Vh;
        eapply Permutation_in; [apply Permutation_sym; exact Ph | exact Hc]).
  assert (SSh : StronglySorted (fun x y => key t x < key t y) h').
  { apply SS_le_lt.
    - apply isort_sorted.
    - eapply Permutation_NoDup; [exact Ph | exact Nd].
    - rewrite Forall_forall in Vh'. intros x y Hx Hy E.
      apply (key_inj t); auto. }
  exists h'. split.
  - apply moves_upper with (S := S).
    + pose proof (sub_length _ _ HS). unfold Lt. lia.
    + exact Nd.
    + exact Ph.
    + exact HS.
    + apply (sub_of_sorted (fun x y => key t x < key t y) string_dec); auto.
      * intros x y; lia.
      * intros x Hx. eapply Permutation_in; [exact Ph | eapply sub_in; eauto].
  - exact (keysorted_hand t h' Ht Vh' SSh).
Qed.

Lemma lower_t : forall h k h', valid_input h -> moves k h h' -> sorted_hand h' ->
  exists t, 0 <= t < 4096 /\ injb t = true /\ (List.length h <= Lt h t + k)%nat.
Proof.
  intros h k h' Hv Hm Hs. pose proof (valid_cards h Hv) as Vh.
  pose proof (vi_distinct h Hv) as Nd.
  pose proof (moves_perm k h h' Hm) as Ph.
  destruct (moves_lower k h h' Hm) as (S & H1 & H2 & H3).
  assert (Vh' : Forall valid_card h')
    by (rewrite Forall_forall in *; intros c Hc; apply Vh;
        eapply Permutation_in; [apply Permutation_sym; exact Ph | exact Hc]).
  destruct (sorted_keysorted h' Vh' (Permutation_NoDup Ph Nd) Hs) as (t & Ht & Hi & SSh).
  exists t. split; [exact Ht|]. split; [exact Hi|].
  pose proof (SS_sub _ _ _ SSh H2) as SSS.
  assert (Hsub : sub (map (key t) S) (bk (map (key t) h))).
  { apply (sub_of_sorted Z.lt Z.eq_dec).
    - intros x y; lia.
    - intros z Hz. apply in_bk. apply in_map_iff in Hz. destruct Hz as (c & <- & Hc).
      pose proof (sub_in _ _ _ H1 Hc) as Hc'.
      split; [apply in_map; exact Hc'|].
      rewrite Forall_forall in Vh. apply key_range. apply Vh. exact Hc'.
    - eapply SS_map; [exact SSS | auto].
    - apply bk_sorted. }
  pose proof (lcs_complete _ _ _ (sub_map (key t) _ _ H1) Hsub) as Hc.
  rewrite length_map in Hc. unfold Lt. lia.
Qed.

Fixpoint bestn (h : list String.string) (T : nat) : nat :=
  match T with
  | O => O
  | S T' => Nat.max (bestn h T') (if injb (Z.of_nat T') then Lt h (Z.of_nat T') else O)
  end.

Lemma bestn_ge : forall h T T', (T' < T)%nat -> injb (Z.of_nat T') = true ->
  (Lt h (Z.of_nat T') <= bestn h T)%nat.
Proof.
  intros h T; induction T as [| T IH]; intros T' Hlt Hi; [lia|].
  simpl. destruct (Nat.eq_dec T' T) as [-> | Ne].
  - rewrite Hi. lia.
  - specialize (IH T' ltac:(lia) Hi). lia.
Qed.

Lemma bestn_att : forall h T, bestn h T = O \/
  exists T', (T' < T)%nat /\ injb (Z.of_nat T') = true /\ bestn h T = Lt h (Z.of_nat T').
Proof.
  intros h T; induction T as [| T IH]; simpl; [left; reflexivity|].
  destruct (injb (Z.of_nat T)) eqn:Ei.
  - destruct (Nat.le_ge_cases (bestn h T) (Lt h (Z.of_nat T))).
    + right. exists T. split; [lia|]. split; [exact Ei | lia].
    + destruct IH as [E | (T' & H1 & H2 & H3)].
      * left. lia.
      * right. exists T'. split; [lia|]. split; [exact H2 | lia].
  - rewrite Nat.max_0_r. destruct IH as [E | (T' & H1 & H2 & H3)]; [left; exact E|].
    right. exists T'. split; [lia | auto].
Qed.

Theorem answer_spec : forall h, valid_input h ->
  min_moves_spec h (N.of_nat (List.length h - bestn h (Z.to_nat 4096))).
Proof.
  intros h Hv. split.
  - rewrite Nat2N.id.
    destruct (bestn_att h (Z.to_nat 4096)) as [E | (T' & H1 & H2 & H3)].
    + assert (Hi : injb (Z.of_nat (Z.to_nat 228)) = true) by reflexivity.
      assert (Hl : (Z.to_nat 228 < Z.to_nat 4096)%nat) by (apply Z2Nat.inj_lt; lia).
      pose proof (bestn_ge h _ _ Hl Hi) as Hb.
      destruct (upper_t h (Z.of_nat (Z.to_nat 228)) Hv Hi) as (h' & Hm & Hs).
      exists h'. split; [| exact Hs].
      replace (bestn h (Z.to_nat 4096)) with (Lt h (Z.of_nat (Z.to_nat 228))) by lia.
      exact Hm.
    + destruct (upper_t h (Z.of_nat T') Hv H2) as (h' & Hm & Hs).
      exists h'. rewrite H3. auto.
  - intros k h' Hm Hs.
    destruct (lower_t h k h' Hv Hm Hs) as (t & Ht & Hi & Hk).
    rewrite <- (Z2Nat.id t) in Hi by lia.
    assert (Hl : (Z.to_nat t < Z.to_nat 4096)%nat) by (apply Z2Nat.inj_lt; lia).
    pose proof (bestn_ge h _ _ Hl Hi) as Hb.
    rewrite Z2Nat.id in Hb by lia.
    generalize dependent (bestn h (Z.to_nat 4096)). intros. lia.
Qed.

(* ================================================================== *)
(* Part 7. The program                                                 *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope Z_scope.
Open Scope array_scope.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make0 : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if (n <=? PArray.max_length)%uint63 then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma alength_make : forall (n : int) (b : int), (φ n) <= 4194303 ->
  PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite alength_make0.
  replace (n <=? PArray.max_length)%uint63 with true; [reflexivity|].
  symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303. exact H.
Qed.

Lemma aget_make : forall (n b i : int), (PArray.make n b).[i] = b.
Proof. intros n b i. exact (get_make int b n i). Qed.

Lemma set_get_same : forall (t : array int) (i j : int) (b : int),
  (φ i) = (φ j) -> (φ j) < (φ (PArray.length t)) -> t.[i <- b].[j] = b.
Proof.
  intros t i j b E H. assert (i = j) by (apply to_Z_inj; exact E). subst.
  apply aget_set_same. rewrite ltb_spec. exact H.
Qed.

Lemma set_get_other : forall (t : array int) (i j : int) (b : int),
  (φ i) <> (φ j) -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b E. apply aget_set_other. intro F. apply E. rewrite F. reflexivity. Qed.


(* ================================================================== *)
(* Part 8. The program meets the math                                  *)
(* ================================================================== *)

Lemma wB_value : wB = 9223372036854775808.
Proof. reflexivity. Qed.

Lemma eqb_Z : forall x y : int, (x =? y)%uint63 = ((φ x) =? (φ y)).
Proof.
  intros x y. destruct (Z.eqb_spec (φ x) (φ y)) as [E | E].
  - apply eqb_spec. apply to_Z_inj. exact E.
  - apply eqb_false_spec. intro F. apply E. rewrite F. reflexivity.
Qed.

Lemma ltb_Z : forall x y : int, (x <? y)%uint63 = ((φ x) <? (φ y)).
Proof.
  intros x y. destruct (Z.ltb_spec (φ x) (φ y)) as [E | E].
  - apply ltb_spec. exact E.
  - apply Bool.not_true_iff_false. rewrite ltb_spec. lia.
Qed.

Lemma imax_ok : forall u v, (φ (imax u v)) = Z.max (φ u) (φ v).
Proof.
  intros u v. unfold imax. rewrite ltb_Z. destruct (Z.ltb_spec (φ u) (φ v)); lia.
Qed.

Lemma int_cases4 : forall s : int, 0 <= (φ s) < 4 ->
  s = 0%uint63 \/ s = 1%uint63 \/ s = 2%uint63 \/ s = 3%uint63.
Proof.
  intros s H. destruct (four_cases _ H) as [E | [E | [E | E]]];
    [left | right; left | right; right; left | right; right; right];
    apply to_Z_inj; rewrite E; reflexivity.
Qed.

Lemma sg_m_ok : forall t s, 0 <= (φ s) < 4 -> (φ (sg_m t s)) = sgZ (φ t) (φ s).
Proof.
  intros t s Hs. unfold sg_m, sgZ. rewrite mod_spec, div_spec.
  destruct (int_cases4 s Hs) as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma dr_m_ok : forall t s, 0 <= (φ s) < 4 -> (φ (dr_m t s)) = drZ (φ t) (φ s).
Proof.
  intros t s Hs. unfold dr_m, drZ. rewrite mod_spec, div_spec.
  destruct (int_cases4 s Hs) as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma key_m_ok : forall t s r, 0 <= (φ s) < 4 -> 0 <= (φ r) < 13 ->
  (φ (key_m t s r)) = keyZ (φ t) (φ s) (φ r).
Proof.
  intros t s r Hs Hr. unfold key_m, keyZ.
  rewrite eqb_Z, dr_m_ok by exact Hs. change ((φ 1)%uint63) with 1.
  pose proof (sg_m_ok t s Hs) as E. pose proof (sg_range (φ t) (φ s)).
  destruct (drZ (φ t) (φ s) =? 1).
  - rewrite add_spec, mul_spec, E. change ((φ 13)%uint63) with 13.
    rewrite (Z.mod_small (_ * 13)) by (rewrite wB_value; lia).
    apply Z.mod_small. rewrite wB_value. lia.
  - assert ((φ (12 - r))%uint63 = 12 - (φ r)) by sia.
    rewrite add_spec, mul_spec, E, H0. change ((φ 13)%uint63) with 13.
    rewrite (Z.mod_small (_ * 13)) by (rewrite wB_value; lia).
    apply Z.mod_small. rewrite wB_value. lia.
Qed.

Lemma inj_m_ok : forall t, inj_m t = injb (φ t).
Proof.
  intros t. unfold inj_m, injb. rewrite !eqb_Z.
  rewrite !sg_m_ok by (cbv; split; congruence). reflexivity.
Qed.

(* reading the cards *)

Lemma suit_cases : forall u, char_in u suit_chars ->
  u = "s"%char \/ u = "h"%char \/ u = "d"%char \/ u = "c"%char.
Proof.
  intros u [k Hk].
  do 4 (destruct k as [| k]; [simpl in Hk; injection Hk as <-; tauto|]).
  destruct k; simpl in Hk; discriminate.
Qed.

Lemma rank_cases : forall u, char_in u rank_order ->
  u = "2"%char \/ u = "3"%char \/ u = "4"%char \/ u = "5"%char \/ u = "6"%char \/
  u = "7"%char \/ u = "8"%char \/ u = "9"%char \/ u = "T"%char \/ u = "J"%char \/
  u = "Q"%char \/ u = "K"%char \/ u = "A"%char.
Proof.
  intros u [k Hk].
  do 13 (destruct k as [| k]; [simpl in Hk; injection Hk as <-; tauto|]).
  destruct k; simpl in Hk; discriminate.
Qed.

Lemma repr_char : forall (w : PrimString.string) c k ch, repr w c ->
  (k < String.length c)%nat -> String.get k c = Some ch ->
  (φ (PrimString.get w (of_Z (Z.of_nat k)))) = Z.of_N (N_of_ascii ch).
Proof.
  intros w c k ch [Hl Hc] Hk Hch.
  destruct (Hc k Hk) as (ch' & Hch' & Hr). rewrite Hch in Hch'. injection Hch' as <-.
  unfold repr, repr_uint in Hr. rewrite <- Hr. rewrite Z2N.id; [reflexivity|].
  apply to_Z_bounded.
Qed.

Ltac pin_char E :=
  match type of E with
  | φ ?g = ?v =>
      let G := fresh "G" in
      assert (G : g = of_Z v) by (apply to_Z_inj; rewrite E; reflexivity);
      rewrite G; reflexivity
  end.

Lemma sidx_ok : forall (w : PrimString.string) c, valid_card c -> repr w c ->
  (φ (sidx_m (PrimString.get w 1))) = sid c.
Proof.
  intros w c Hc Hw. destruct (valid_suit c Hc) as [Hu Hi].
  pose proof (repr_char w c 1 _ Hw ltac:(destruct Hc as [L _]; lia) Hu) as E.
  change (of_Z (Z.of_nat 1)) with 1%uint63 in E.
  unfold sid, sidx.
  destruct (suit_cases _ Hi) as [Hs | [Hs | [Hs | Hs]]]; rewrite Hs in E |- *;
    pin_char E.
Qed.

Lemma rank_ok : forall (w : PrimString.string) c, valid_card c -> repr w c ->
  (φ (rank_m (PrimString.get w 0))) = rk c.
Proof.
  intros w c Hc Hw. destruct (valid_rank c Hc) as (r & Hr & Er & Hi).
  pose proof (repr_char w c 0 _ Hw ltac:(destruct Hc as [L _]; lia) Hr) as E.
  change (of_Z (Z.of_nat 0)) with 0%uint63 in E.
  unfold rk. rewrite Er.
  destruct (rank_cases _ Hi) as
    [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | Hs]]]]]]]]]]]];
    rewrite Hs in E |- *; pin_char E.
Qed.

Lemma repr_cell : forall (x : array PrimString.string) h, repr x h ->
  forall i : int, (φ i) < Z.of_nat (List.length h) ->
  repr x.[i] (nth (Z.to_nat (φ i)) h EmptyString).
Proof.
  intros x h [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  rewrite (nth_error_nth _ _ _ Hm).
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. exact Hr.
Qed.

Definition hc (h : list String.string) (j : int) : String.string :=
  nth (Z.to_nat (φ j)) h EmptyString.

Lemma valid_hc : forall h j, Forall valid_card h -> (φ j) < Z.of_nat (List.length h) ->
  valid_card (hc h j).
Proof.
  intros h j Hv Hj. rewrite Forall_forall in Hv. apply Hv. unfold hc.
  apply nth_In. lia.
Qed.

Lemma succ_int : forall i n : int, (φ i) < (φ n) -> (φ (i + 1))%uint63 = (φ i) + 1.
Proof. intros i n H. pose proof (to_Z_bounded n). sia. Qed.

Lemma prep_spec : forall (x : array PrimString.string) h, repr x h -> Forall valid_card h ->
  forall n : int, (φ n) = Z.of_nat (List.length h) -> (φ n) <= 4194303 ->
  forall z i SU RK H, gap n i = z -> (φ i) <= (φ n) ->
  PArray.length SU = n -> PArray.length RK = n ->
  (forall j : int, (φ j) < (φ i) -> (φ (SU.[j])) = sid (hc h j) /\ (φ (RK.[j])) = rk (hc h j)) ->
  forall SU' RK', prep x n i SU RK H = (SU', RK') ->
  PArray.length SU' = n /\ PArray.length RK' = n /\
  forall j : int, (φ j) < (φ n) -> (φ (SU'.[j])) = sid (hc h j) /\ (φ (RK'.[j])) = rk (hc h j).
Proof.
  intros x h Hx Hv n Hn Hmax z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i SU RK H Hz Hi Ls Lr Hinv SU' RK' Hr.
  rewrite prep_eq in Hr. destruct (bdec (i <? n)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'. cbv zeta in Hr.
    pose proof (succ_int i n Hlt') as Hi1.
    pose proof (valid_hc h i Hv ltac:(lia)) as Vc.
    pose proof (repr_cell x h Hx i ltac:(lia)) as Hw.
    eapply IH; [ | reflexivity | | | | | exact Hr].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + lia.
    + rewrite alength_set. exact Ls.
    + rewrite alength_set. exact Lr.
    + intros j Hj. rewrite Hi1 in Hj.
      destruct (Z.eq_dec (φ i) (φ j)) as [E | E].
      * rewrite !set_get_same by (try rewrite Ls; try rewrite Lr; lia).
        assert (j = i) by (apply to_Z_inj; lia). subst j.
        split; [apply sidx_ok | apply rank_ok]; auto.
      * rewrite !set_get_other by exact E. apply Hinv. lia.
  - injection Hr as <- <-. rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Ls|]. split; [exact Lr|].
    intros j Hj. apply Hinv. lia.
Qed.

Lemma firstn_snoc : forall (l : list Z) i, (i < List.length l)%nat ->
  firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  induction l as [| y l IH]; intros i Hi; [simpl in Hi; lia|].
  destruct i as [| i]; [reflexivity|]. simpl in Hi.
  change (firstn (S (S i)) (y :: l)) with (y :: firstn (S i) l).
  rewrite IH by lia. reflexivity.
Qed.

Lemma present_snoc : forall l v k, present (l ++ [v]) k = orb (present l k) (k =? v).
Proof.
  intros l v k. unfold present. rewrite existsb_app. simpl. rewrite Bool.orb_false_r.
  reflexivity.
Qed.

Lemma keys_spec : forall h (t : int) (SU RK : array int) (n : int),
  Forall valid_card h -> (φ n) = Z.of_nat (List.length h) ->
  (forall j : int, (φ j) < (φ n) -> (φ (SU.[j])) = sid (hc h j) /\ (φ (RK.[j])) = rk (hc h j)) ->
  forall z i K P H, gap n i = z -> (φ i) <= (φ n) ->
  PArray.length K = n -> PArray.length P = 52%uint63 ->
  (forall j : int, (φ j) < (φ i) -> (φ (K.[j])) = key (φ t) (hc h j)) ->
  (forall k : int, (φ k) < 52 ->
     (φ (P.[k])) = ind (present (firstn (Z.to_nat (φ i)) (map (key (φ t)) h)) (φ k))) ->
  forall K' P', keys t SU RK n i K P H = (K', P') ->
  PArray.length K' = n /\ PArray.length P' = 52%uint63 /\
  (forall j : int, (φ j) < (φ n) -> (φ (K'.[j])) = key (φ t) (hc h j)) /\
  (forall k : int, (φ k) < 52 -> (φ (P'.[k])) = ind (present (map (key (φ t)) h) (φ k))).
Proof.
  intros h t SU RK n Hv Hn Hc z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i K P H Hz Hi Lk Lp HK HP K' P' Hr.
  rewrite keys_eq in Hr. destruct (bdec (i <? n)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'. cbv zeta in Hr.
    pose proof (succ_int i n Hlt') as Hi1.
    pose proof (valid_hc h i Hv ltac:(lia)) as Vc.
    destruct (Hc i Hlt') as [Es Er].
    assert (Ek : (φ (key_m t SU.[i] RK.[i])) = key (φ t) (hc h i)).
    { rewrite key_m_ok; [unfold key; rewrite Es, Er; reflexivity | |];
        [rewrite Es; apply sid_range | rewrite Er; apply rk_range]; exact Vc. }
    pose proof (key_range (φ t) _ Vc) as Rk.
    eapply IH; [ | reflexivity | | | | | | exact Hr].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + lia.
    + rewrite alength_set. exact Lk.
    + rewrite alength_set. exact Lp.
    + intros j Hj. rewrite Hi1 in Hj.
      destruct (Z.eq_dec (φ i) (φ j)) as [E | E].
      * rewrite set_get_same by (try rewrite Lk; lia).
        assert (j = i) by (apply to_Z_inj; lia). subst j. exact Ek.
      * rewrite set_get_other by exact E. apply HK. lia.
    + intros k Hk. rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by lia.
      rewrite firstn_snoc by (rewrite length_map; lia).
      assert (En : nth (Z.to_nat (φ i)) (map (key (φ t)) h) 0 = key (φ t) (hc h i))
        by (unfold hc; rewrite (nth_indep _ 0 (key (φ t) EmptyString))
              by (rewrite length_map; lia); apply map_nth).
      rewrite present_snoc, En.
      destruct (Z.eq_dec (φ (key_m t SU.[i] RK.[i])) (φ k)) as [E | E].
      * rewrite set_get_same by (try rewrite Lp; try change ((φ 52)%uint63) with 52; lia).
        rewrite <- E, Ek, Z.eqb_refl, Bool.orb_true_r. reflexivity.
      * rewrite set_get_other by exact E. rewrite HP by exact Hk.
        replace ((φ k) =? key (φ t) (hc h i)) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite Bool.orb_false_r. reflexivity.
  - injection Hr as <- <-. rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    assert (Ei : (φ i) = (φ n)) by lia.
    split; [exact Lk|]. split; [exact Lp|]. split.
    + intros j Hj. apply HK. lia.
    + intros k Hk. rewrite HP by exact Hk. rewrite Ei, Hn, Nat2Z.id.
      rewrite firstn_all2 by (rewrite length_map; lia). reflexivity.
Qed.

Lemma zrange_length : forall n lo, List.length (zrange lo n) = n.
Proof. induction n as [| n IH]; intros lo; simpl; [| rewrite IH]; reflexivity. Qed.

Definition pre (a : list Z) (k : int) : list Z :=
  filter (present a) (zrange 0 (Z.to_nat (φ k))).

Lemma compact_spec : forall (a : list Z) (P : array int),
  (forall k : int, (φ k) < 52 -> (φ (P.[k])) = ind (present a (φ k))) ->
  forall z k B m H, gap 52 k = z -> (φ k) <= 52 ->
  PArray.length B = 52%uint63 ->
  (φ m) = Z.of_nat (List.length (pre a k)) ->
  (forall j : int, (φ j) < (φ m) -> (φ (B.[j])) = nth (Z.to_nat (φ j)) (pre a k) 0) ->
  forall B' m', compact P k B m H = (B', m') ->
  PArray.length B' = 52%uint63 /\ (φ m') = Z.of_nat (List.length (bk a)) /\
  (forall j : int, (φ j) < (φ m') -> (φ (B'.[j])) = nth (Z.to_nat (φ j)) (bk a) 0).
Proof.
  intros a P HP z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k B m H Hz Hk Lb Hm HB B' m' Hr.
  rewrite compact_eq in Hr. destruct (bdec (k <? 52)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'. change ((φ 52)%uint63) with 52 in Hlt'.
    assert (Hk1 : (φ (k + 1))%uint63 = (φ k) + 1) by sia.
    assert (Hpre : forall k1 : int, (φ k1) = (φ k) + 1 ->
              pre a k1 = pre a k ++ (if present a (φ k) then [(φ k)] else [])).
    { intros k1 E. unfold pre. rewrite E, Z2Nat.inj_add, Nat.add_1_r by lia.
      rewrite zrange_snoc, filter_app. simpl. rewrite Z2Nat.id by lia.
      destruct (present a (φ k)); reflexivity. }
    assert (Lpre : (List.length (pre a k) <= Z.to_nat (φ k))%nat).
    { unfold pre. rewrite <- (zrange_length (Z.to_nat (φ k)) 0) at 2.
      apply sub_length, sub_filter. }
    rewrite eqb_Z, HP in Hr by exact Hlt'. change ((φ 1)%uint63) with 1 in Hr.
    destruct (present a (φ k)) eqn:Ep; simpl in Hr.
    + assert (Hm1 : (φ (m + 1))%uint63 = (φ m) + 1) by (pose proof (to_Z_bounded m); sia).
      eapply IH; [ | reflexivity | | | | | exact Hr].
      * rewrite <- Hz. apply dec_step. exact Hlt.
      * lia.
      * rewrite alength_set. exact Lb.
      * rewrite Hm1, (Hpre _ Hk1), length_app. simpl. lia.
      * intros j Hj. rewrite Hm1 in Hj. rewrite (Hpre _ Hk1).
        destruct (Z.eq_dec (φ m) (φ j)) as [E | E].
        -- rewrite set_get_same by (try rewrite Lb; try change ((φ 52)%uint63) with 52; lia).
           rewrite app_nth2 by lia. replace (Z.to_nat (φ j) - List.length (pre a k))%nat with 0%nat by lia.
           reflexivity.
        -- rewrite set_get_other by exact E. rewrite app_nth1 by lia. apply HB. lia.
    + eapply IH; [ | reflexivity | | | | | exact Hr].
      * rewrite <- Hz. apply dec_step. exact Hlt.
      * lia.
      * exact Lb.
      * rewrite (Hpre _ Hk1), app_nil_r. exact Hm.
      * rewrite (Hpre _ Hk1), app_nil_r. exact HB.
  - injection Hr as <- <-. rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    change ((φ 52)%uint63) with 52 in Hge.
    assert (E : pre a k = bk a).
    { unfold pre, bk. replace (Z.to_nat (φ k)) with 52%nat by lia. reflexivity. }
    rewrite E in Hm, HB. auto.
Qed.

Lemma skipn_cons_nth : forall (l : list Z) i, (i < List.length l)%nat ->
  skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
  induction l as [| y l IH]; intros i Hi; [simpl in Hi; lia|].
  destruct i as [| i]; [reflexivity|]. simpl in Hi. simpl. apply IH. lia.
Qed.

(* cell (i, j) of the table: the LCS of the suffixes a[i..] and b[j..] *)
Definition cellv (a b : list Z) (i j : Z) : Z :=
  Z.of_nat (lcs (skipn (Z.to_nat i) a) (skipn (Z.to_nat j) b)).

Lemma cellv_bound : forall a b i j, 0 <= cellv a b i j <= Z.of_nat (List.length a).
Proof.
  intros a b i j. unfold cellv. pose proof (lcs_le (skipn (Z.to_nat i) a) (skipn (Z.to_nat j) b)).
  rewrite length_skipn in H. lia.
Qed.

Lemma digits : forall W i j i' j', 0 <= j < W -> 0 <= j' < W ->
  i * W + j = i' * W + j' -> i = i' /\ j = j'.
Proof.
  intros W i j i' j' Hj Hj' E.
  destruct (Z.lt_trichotomy i i') as [L | [-> | G]].
  - exfalso. assert ((i + 1) * W <= i' * W) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
  - lia.
  - exfalso. assert ((i' + 1) * W <= i * W) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

Lemma idx_ok : forall x y w : int, (φ x) <= 53 -> (φ y) <= 54 -> (φ w) <= 53 ->
  (φ (x * w + y))%uint63 = (φ x) * (φ w) + (φ y).
Proof.
  intros x y w Hx Hy Hw. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
  pose proof (to_Z_bounded w).
  rewrite add_spec, mul_spec.
  assert (0 <= (φ x) * (φ w) <= 53 * 53) by nia.
  rewrite (Z.mod_small ((φ x) * (φ w))) by (rewrite wB_value; lia).
  apply Z.mod_small. rewrite wB_value. lia.
Qed.

Lemma dp_spec : forall (a b : list Z) (K B : array int) (n m w : int),
  (φ n) = Z.of_nat (List.length a) -> (φ m) = Z.of_nat (List.length b) ->
  (φ n) <= 52 -> (φ m) <= 52 -> (φ w) = (φ m) + 1 ->
  (forall i : int, (φ i) < (φ n) -> (φ (K.[i])) = nth (Z.to_nat (φ i)) a 0) ->
  (forall j : int, (φ j) < (φ m) -> (φ (B.[j])) = nth (Z.to_nat (φ j)) b 0) ->
  forall z q T H, (φ q) = z -> (φ q) <= (φ n) * (φ m) ->
  (φ (PArray.length T)) = ((φ n) + 1) * ((φ m) + 1) ->
  (forall i j : Z, 0 <= i <= (φ n) -> 0 <= j <= (φ m) ->
     (i = (φ n) \/ j = (φ m) \/ (φ q) <= i * (φ m) + j) ->
     forall ι : int, (φ ι) = i * ((φ m) + 1) + j -> (φ (T.[ι])) = cellv a b i j) ->
  (φ ((dp K B m w q T H).[0%uint63])) = Z.of_nat (lcs a b).
Proof.
  intros a b K B n m w Hn Hm Hn52 Hm52 Hw HK HB z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q T H Hz Hq LT Hinv.
  pose proof (to_Z_bounded n). pose proof (to_Z_bounded m). pose proof (to_Z_bounded q).
  rewrite dp_eq. destruct (bdec (0 <? q)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'. change ((φ 0)%uint63) with 0 in Hlt'.
    assert (Mpos : 0 < (φ m)).
    { destruct (Z.eq_dec (φ m) 0) as [E | E]; [| lia].
      rewrite E, Z.mul_0_r in Hq. lia. }
    cbv zeta.
    assert (Hq' : (φ (q - 1))%uint63 = (φ q) - 1) by sia.
    set (q' := (q - 1)%uint63) in *.
    set (i0 := (q' / m)%uint63). set (j0 := (q' mod m)%uint63).
    assert (Ei : (φ i0) = (φ q') / (φ m)) by (apply div_spec).
    assert (Ej : (φ j0) = (φ q') mod (φ m)) by (apply mod_spec).
    pose proof (Z.div_mod (φ q') (φ m) ltac:(lia)) as Dm.
    pose proof (Z.mod_pos_bound (φ q') (φ m) Mpos) as Mb.
    assert (Hi0 : 0 <= (φ i0) < (φ n)).
    { rewrite Ei. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; lia. }
    rewrite <- Ei, <- Ej in *.
    set (vi := (φ i0)) in *. set (vj := (φ j0)) in *.
    assert (Eq' : (φ q') = vi * (φ m) + vj) by lia.
    assert (Ei1 : (φ (i0 + 1))%uint63 = vi + 1) by (unfold vi in *; sia).
    assert (Ej1 : (φ (j0 + 1))%uint63 = vj + 1) by (unfold vj in *; sia).
    assert (I1 : (φ ((i0 + 1) * w + (j0 + 1)))%uint63 = (vi + 1) * ((φ m) + 1) + (vj + 1))
      by (rewrite idx_ok; lia).
    assert (I2 : (φ ((i0 + 1) * w + j0))%uint63 = (vi + 1) * ((φ m) + 1) + vj)
      by (rewrite idx_ok; lia).
    assert (I3 : (φ (i0 * w + (j0 + 1)))%uint63 = vi * ((φ m) + 1) + (vj + 1))
      by (rewrite idx_ok; lia).
    assert (I0 : (φ (i0 * w + j0))%uint63 = vi * ((φ m) + 1) + vj)
      by (rewrite idx_ok; lia).
    assert (V1 := Hinv (vi + 1) (vj + 1) ltac:(lia) ltac:(lia) ltac:(right; right; lia) _ I1).
    assert (V2 := Hinv (vi + 1) vj ltac:(lia) ltac:(lia) ltac:(right; right; lia) _ I2).
    assert (V3 := Hinv vi (vj + 1) ltac:(lia) ltac:(lia) ltac:(right; right; lia) _ I3).
    set (c := if (K.[i0] =? B.[j0])%uint63 then (T.[(i0 + 1) * w + (j0 + 1)] + 1)%uint63
              else imax T.[(i0 + 1) * w + j0] T.[i0 * w + (j0 + 1)]).
    assert (Hc : (φ c) = cellv a b vi vj).
    { unfold c, cellv. rewrite eqb_Z, HK, HB by lia.
      unfold cellv in V1, V2, V3.
      replace (Z.to_nat (vi + 1)) with (S (Z.to_nat vi)) in V1, V2 by lia.
      replace (Z.to_nat (vj + 1)) with (S (Z.to_nat vj)) in V1, V3 by lia.
      rewrite (skipn_cons_nth a (Z.to_nat vi)) by lia.
      rewrite (skipn_cons_nth b (Z.to_nat vj)) by lia.
      rewrite lcs_cc.
      rewrite <- (skipn_cons_nth a (Z.to_nat vi)) by lia.
      rewrite <- (skipn_cons_nth b (Z.to_nat vj)) by lia.
      fold vi vj.
      destruct (nth (Z.to_nat vi) a 0 =? nth (Z.to_nat vj) b 0).
      - pose proof (lcs_le (skipn (S (Z.to_nat vi)) a) (skipn (S (Z.to_nat vj)) b)).
        rewrite length_skipn in H3.
        rewrite add_spec, V1. change ((φ 1)%uint63) with 1.
        rewrite Z.mod_small by (rewrite wB_value; lia). lia.
      - rewrite imax_ok, V2, V3. lia. }
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_down. exact Hlt.
    + lia.
    + rewrite alength_set. exact LT.
    + intros i j Hi Hj Hcond ι Hι.
      destruct (Z.eq_dec ((φ (i0 * w + j0))%uint63) (φ ι)) as [E | E].
      * assert (Mi : i * ((φ m) + 1) <= (φ n) * ((φ m) + 1))
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite set_get_same; [| exact E | rewrite LT; lia].
        rewrite I0, Hι in E. destruct (digits ((φ m) + 1) vi vj i j ltac:(lia) ltac:(lia) E)
          as [<- <-]. exact Hc.
      * rewrite set_get_other by exact E. apply Hinv; [lia | lia | | exact Hι].
        destruct Hcond as [C | [C | C]]; [left; exact C | right; left; exact C|].
        destruct (Z.le_gt_cases (φ q) (i * (φ m) + j)) as [C' | C']; [right; right; exact C'|].
        destruct (Z.eq_dec j (φ m)) as [Cj | Cj]; [right; left; exact Cj|].
        exfalso. destruct (digits (φ m) vi vj i j ltac:(lia) ltac:(lia) ltac:(lia)) as [<- <-].
        apply E. rewrite I0, Hι. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge. change ((φ 0)%uint63) with 0 in Hge.
    rewrite (Hinv 0 0 ltac:(lia) ltac:(lia) ltac:(right; right; lia) 0%uint63 eq_refl).
    reflexivity.
Qed.

Lemma bk_length : forall a, (List.length (bk a) <= 52)%nat.
Proof.
  intros a. unfold bk. rewrite <- (zrange_length 52 0) at 2. apply sub_length, sub_filter.
Qed.

Lemma lcs_for_spec : forall h (t : int) (SU RK : array int) (n : int),
  Forall valid_card h -> (φ n) = Z.of_nat (List.length h) -> (φ n) <= 52 ->
  (forall j : int, (φ j) < (φ n) -> (φ (SU.[j])) = sid (hc h j) /\ (φ (RK.[j])) = rk (hc h j)) ->
  (φ (lcs_for t SU RK n)) = Z.of_nat (Lt h (φ t)).
Proof.
  intros h t SU RK n Hv Hn Hn52 Hc. unfold lcs_for.
  set (a := map (key (φ t)) h).
  match goal with |- context [keys ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8] =>
    destruct (keys a1 a2 a3 a4 a5 a6 a7 a8) as [K P] eqn:EK end.
  destruct (keys_spec h t SU RK n Hv Hn Hc _ 0%uint63 (PArray.make n 0%uint63)
              (PArray.make 52 0%uint63) _ eq_refl
              ltac:(change ((φ 0)%uint63) with 0; lia)
              ltac:(apply alength_make; lia)
              ltac:(apply alength_make; change ((φ 52)%uint63) with 52; lia)
              ltac:(intros j Hj; change ((φ 0)%uint63) with 0 in Hj;
                    pose proof (to_Z_bounded j); lia)
              ltac:(intros k Hk; rewrite aget_make;
                    replace (Z.to_nat ((φ 0)%uint63)) with 0%nat by reflexivity;
                    cbn [firstn present existsb ind]; reflexivity)
              K P EK) as (LK & LP & HK & HP).
  fold a in HP.
  match goal with |- context [compact ?a1 ?a2 ?a3 ?a4 ?a5] =>
    destruct (compact a1 a2 a3 a4 a5) as [B m] eqn:EC end.
  destruct (compact_spec a P HP _ 0%uint63 (PArray.make 52 0%uint63) 0%uint63 _ eq_refl
              ltac:(change ((φ 0)%uint63) with 0; lia)
              ltac:(apply alength_make; change ((φ 52)%uint63) with 52; lia)
              eq_refl
              ltac:(intros j Hj; change ((φ 0)%uint63) with 0 in Hj;
                    pose proof (to_Z_bounded j); lia)
              B m EC) as (LB & Hm & HB).
  pose proof (bk_length a) as Lb.
  pose proof (to_Z_bounded n). pose proof (to_Z_bounded m).
  assert (Hw : (φ (m + 1))%uint63 = (φ m) + 1) by sia.
  assert (Hnm : (φ (n * m))%uint63 = (φ n) * (φ m)).
  { rewrite mul_spec. apply Z.mod_small.
    assert ((φ n) * (φ m) <= 52 * 52) by (apply Z.mul_le_mono_nonneg; lia).
    split; [apply Z.mul_nonneg_nonneg; lia | rewrite wB_value; lia]. }
  assert (Hsz : (φ ((n + 1) * (m + 1)))%uint63 = ((φ n) + 1) * ((φ m) + 1)).
  { assert (E1 : (φ (n + 1))%uint63 = (φ n) + 1) by sia.
    pose proof (idx_ok (n + 1) 0 (m + 1) ltac:(lia) ltac:(change ((φ 0)%uint63) with 0; lia) ltac:(lia)) as E.
    rewrite add_spec in E. change ((φ 0)%uint63) with 0 in E. rewrite Z.add_0_r in E.
    rewrite Z.mod_small in E by apply to_Z_bounded. rewrite E, E1, Hw. ring. }
  assert (La : (φ n) = Z.of_nat (List.length a)) by (unfold a; rewrite length_map; exact Hn).
  rewrite (dp_spec a (bk a) K B n m (m + 1) La Hm ltac:(lia) ltac:(lia) Hw
             ltac:(intros i Hi; rewrite HK by exact Hi; unfold a, hc;
                   rewrite (nth_indep _ 0 (key (φ t) EmptyString))
                     by (rewrite length_map; lia);
                   rewrite map_nth; reflexivity)
             HB _ (n * m)%uint63 _ _ eq_refl ltac:(lia)).
  - reflexivity.
  - rewrite alength_make; [exact Hsz|]. rewrite Hsz.
    assert (((φ n) + 1) * ((φ m) + 1) <= 53 * 53) by (apply Z.mul_le_mono_nonneg; lia). lia.
  - intros i j Hi Hj Hcond ι Hι. rewrite aget_make. change ((φ 0)%uint63) with 0.
    unfold cellv.
    destruct (Z.eq_dec i (φ n)) as [Ci | Ci].
    { rewrite skipn_all2 by lia. reflexivity. }
    destruct (Z.eq_dec j (φ m)) as [Cj | Cj].
    { rewrite (skipn_all2 (bk a)) by lia. rewrite lcs_nil_r. reflexivity. }
    exfalso. destruct Hcond as [C | [C | C]]; [lia | lia |]. rewrite Hnm in C.
    assert ((i + 1) * (φ m) <= (φ n) * (φ m)) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia.
Qed.

Lemma bestn_S : forall h T, bestn h (S T) =
  Nat.max (bestn h T) (if injb (Z.of_nat T) then Lt h (Z.of_nat T) else O).
Proof. reflexivity. Qed.

Lemma bestn_le : forall h T, (bestn h T <= List.length h)%nat.
Proof.
  intros h T; induction T as [| T IH]; [simpl; lia|]. rewrite bestn_S.
  destruct (injb (Z.of_nat T)); [| lia].
  pose proof (lcs_le (map (key (Z.of_nat T)) h) (bk (map (key (Z.of_nat T)) h))).
  rewrite length_map in H. unfold Lt. lia.
Qed.

Lemma search_spec : forall h (SU RK : array int) (n : int),
  Forall valid_card h -> (φ n) = Z.of_nat (List.length h) -> (φ n) <= 52 ->
  (forall j : int, (φ j) < (φ n) -> (φ (SU.[j])) = sid (hc h j) /\ (φ (RK.[j])) = rk (hc h j)) ->
  forall z t best H, gap 4096 t = z -> (φ t) <= 4096 ->
  (φ best) = Z.of_nat (bestn h (Z.to_nat (φ t))) ->
  (φ (search SU RK n t best H)) = Z.of_nat (bestn h (Z.to_nat 4096)).
Proof.
  intros h SU RK n Hv Hn Hn52 Hc z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t best H Hz Ht Hb.
  rewrite search_eq. destruct (bdec (t <? 4096)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'. change ((φ 4096)%uint63) with 4096 in Hlt'.
    assert (Ht1 : (φ (t + 1))%uint63 = (φ t) + 1) by sia.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite Ht1, Z2Nat.inj_add, Nat.add_1_r, bestn_S by lia.
      rewrite Z2Nat.id by (pose proof (to_Z_bounded t); lia).
      rewrite inj_m_ok. destruct (injb (φ t)).
      * rewrite imax_ok, Hb, (lcs_for_spec h t SU RK n Hv Hn Hn52 Hc). lia.
      * rewrite Hb. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge. change ((φ 4096)%uint63) with 4096 in Hge.
    rewrite Hb. replace (φ t) with 4096 by lia. reflexivity.
Qed.

Lemma min_moves_impl_correct : forall (h : list String.string) (x : array PrimString.string),
  valid_input h -> repr x h ->
  exists m : N, repr (min_moves_impl x) m /\ min_moves_spec h m.
Proof.
  intros h x Hv Hx.
  exists (N.of_nat (List.length h - bestn h (Z.to_nat 4096))).
  split; [| apply answer_spec; exact Hv].
  pose proof (valid_cards h Hv) as Vh.
  assert (Ln : (φ (PArray.length x)) = Z.of_nat (List.length h))
    by (destruct Hx as [Hl _]; symmetry; exact Hl).
  pose proof (vi_n h Hv) as Hn. unfold len in Hn.
  assert (Hn52 : (φ (PArray.length x)) <= 52) by lia.
  unfold min_moves_impl.
  match goal with |- context [prep ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
    destruct (prep a1 a2 a3 a4 a5 a6) as [SU RK] eqn:EP end.
  destruct (prep_spec x h Hx Vh (PArray.length x) Ln ltac:(lia) _ 0%uint63
              (PArray.make (PArray.length x) 0%uint63) (PArray.make (PArray.length x) 0%uint63) _ eq_refl
              ltac:(change ((φ 0)%uint63) with 0; lia)
              ltac:(apply alength_make; lia) ltac:(apply alength_make; lia)
              ltac:(intros j Hj; change ((φ 0)%uint63) with 0 in Hj;
                    pose proof (to_Z_bounded j); lia)
              SU RK EP) as (LS & LR & Hc).
  pose proof (search_spec h SU RK (PArray.length x) Vh Ln Hn52 Hc _ 0%uint63 0%uint63
                (Zwf_well_founded 0 (gap 4096 0)) eq_refl
                ltac:(change ((φ 0)%uint63) with 0; lia) eq_refl) as Hs.
  pose proof (bestn_le h (Z.to_nat 4096)) as Hle.
  unfold repr, repr_uint. rewrite sub_spec.
  lazymatch goal with |- context [(φ ?L - φ ?S) mod wB] =>
    replace (φ S) with (Z.of_nat (bestn h (Z.to_nat 4096))) by exact (eq_sym Hs);
    replace (φ L) with (Z.of_nat (List.length h)) by exact (eq_sym Ln) end.
  rewrite Z.mod_small by (rewrite wB_value; lia).
  lia.
Qed.

Definition min_moves_correct : forall (h : list String.string) (x : array PrimString.string),
  valid_input h -> repr x h ->
  exists m : N, repr (min_moves x) m /\ min_moves_spec h m
  := min_moves_impl_correct.
