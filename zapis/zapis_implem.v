From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray PrimString ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
Import ListNotations.

(* ================================================================== *)
(* Math side: words as lists of characters                             *)
(* ================================================================== *)

Local Open Scope list_scope.

Definition opener (c : ascii) : bool :=
  ((c =? "(")%char || (c =? "[")%char || (c =? "{")%char)%bool.
Definition closer (c : ascii) : bool :=
  ((c =? ")")%char || (c =? "]")%char || (c =? "}")%char)%bool.
Definition dch (c : ascii) : Z := if opener c then 1%Z else if closer c then (-1)%Z else 0%Z.
Fixpoint dep (t : list ascii) : Z :=
  match t with [] => 0%Z | c :: t' => (dch c + dep t')%Z end.

Lemma dep_app : forall a b, dep (a ++ b) = (dep a + dep b)%Z.
Proof. induction a as [|c a IH]; intros b; simpl; [reflexivity|]. rewrite IH. lia. Qed.

(* Regular words, on lists. *)
Inductive regL : list ascii -> Prop :=
  | rL_nil : regL []
  | rL_wrap : forall o c a, matching o c -> regL a -> regL (o :: a ++ [c])
  | rL_cat : forall a b, regL a -> regL b -> regL (a ++ b).

Lemma matching_oc : forall o c, matching o c ->
  closer c = true /\ dch o = 1%Z /\ dch c = (-1)%Z.
Proof.
  intros o c [[-> ->]|[[-> ->]|[-> ->]]]; repeat split; reflexivity.
Qed.

Lemma closer_dch : forall c, closer c = true -> dch c = (-1)%Z.
Proof.
  intros c H. unfold closer in H. rewrite !Bool.orb_true_iff in H.
  destruct H as [[H|H]|H]; apply Ascii.eqb_eq in H; subst; reflexivity.
Qed.

Lemma regL_dep : forall t, regL t ->
  dep t = 0%Z /\ forall p q, t = p ++ q -> (0 <= dep p)%Z.
Proof.
  induction 1 as [| o c a Hm Ha [IH1 IH2] | a b Ha [IHa1 IHa2] Hb [IHb1 IHb2]].
  - split; [reflexivity|]. intros p q E. symmetry in E. apply app_eq_nil in E.
    destruct E; subst; simpl; lia.
  - destruct (matching_oc _ _ Hm) as (_ & Ho & Hc). split.
    + simpl. rewrite dep_app. simpl. lia.
    + intros p q E. destruct p as [|z p]; [simpl; lia|].
      simpl in E. injection E as Ez E. subst z.
      destruct (app_eq_app a [c] p q E) as [l [[E1 E2]|[E1 E2]]].
      * pose proof (IH2 p l E1). simpl. lia.
      * subst p. simpl. rewrite dep_app.
        destruct l as [|z l]; simpl in *; [lia|].
        injection E2 as E3 E4. symmetry in E4. apply app_eq_nil in E4.
        destruct E4; subst. simpl. lia.
  - split.
    + rewrite dep_app. lia.
    + intros p q E.
      destruct (app_eq_app a b p q E) as [l [[E1 E2]|[E1 E2]]].
      * exact (IHa2 p l E1).
      * subst p. rewrite dep_app. pose proof (IHb2 l q E2). lia.
Qed.

Lemma regL_decomp : forall t, regL t ->
  t = [] \/ exists o c u v, matching o c /\ regL u /\ regL v /\ t = o :: u ++ c :: v.
Proof.
  induction 1 as [| o c a Hm Ha _ | a b Ha IHa Hb IHb].
  - left; reflexivity.
  - right. exists o, c, a, []. repeat split; auto. constructor.
  - destruct IHa as [->|(o & c & u & v & Hm & Hu & Hv & ->)].
    + exact IHb.
    + right. exists o, c, u, (v ++ b). repeat split; auto.
      * apply rL_cat; auto.
      * simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma regL_build : forall o c u v, matching o c -> regL u -> regL v ->
  regL (o :: u ++ c :: v).
Proof.
  intros o c u v Hm Hu Hv.
  replace (o :: u ++ c :: v) with ((o :: u ++ [c]) ++ v)
    by (simpl; rewrite <- app_assoc; reflexivity).
  apply rL_cat; [apply rL_wrap|]; auto.
Qed.

Lemma regL_even : forall t, regL t -> Nat.Even (List.length t).
Proof.
  induction 1 as [| o c a Hm Ha [k Hk] | a b Ha [k Hk] Hb [m Hm]].
  - exists 0%nat; reflexivity.
  - exists (S k). simpl. rewrite List.length_app. simpl. lia.
  - exists (k + m)%nat. rewrite List.length_app. lia.
Qed.

(* The decomposition of a nonempty regular word by its first bracket is
   unique. *)
Lemma decomp_unique : forall o c u v o' c' u' v',
  o :: u ++ c :: v = o' :: u' ++ c' :: v' -> regL u -> regL u' ->
  closer c = true -> closer c' = true ->
  o = o' /\ u = u' /\ c = c' /\ v = v'.
Proof.
  intros o c u v o' c' u' v' E Hu Hu' Hc Hc'.
  injection E as Eo E. subst o'.
  destruct (app_eq_app u (c :: v) u' (c' :: v') E) as [l [[E1 E2]|[E1 E2]]].
  - destruct l as [|z l].
    + rewrite app_nil_r in E1. subst u. simpl in E2. injection E2 as -> ->. auto.
    + simpl in E2. injection E2 as Ez E3. subst z. exfalso.
      destruct (regL_dep _ Hu) as [_ P].
      pose proof (P (u' ++ [c']) l) as P'.
      rewrite E1, <- app_assoc in P'. simpl in P'. specialize (P' eq_refl).
      rewrite dep_app in P'. destruct (regL_dep _ Hu') as [D _]. simpl in P'.
      rewrite closer_dch in P' by exact Hc'. lia.
  - destruct l as [|z l].
    + rewrite app_nil_r in E1. subst u'. simpl in E2. injection E2 as -> ->. auto.
    + simpl in E2. injection E2 as Ez E3. subst z. exfalso.
      destruct (regL_dep _ Hu') as [_ P].
      pose proof (P (u ++ [c]) l) as P'.
      rewrite E1, <- app_assoc in P'. simpl in P'. specialize (P' eq_refl).
      rewrite dep_app in P'. destruct (regL_dep _ Hu) as [D _]. simpl in P'.
      rewrite closer_dch in P' by exact Hc. lia.
Qed.

(* Completions, character by character. *)
Definition cbool (x y : ascii) : bool := ((x =? y)%char || (x =? "?")%char)%bool.
Definition compat (x y : ascii) : Prop := cbool x y = true.

Definition bpairs : list (ascii * ascii) :=
  [("(", ")"); ("[", "]"); ("{", "}")]%char.

Definition opts (x y : ascii) : list (ascii * ascii) :=
  filter (fun p => (cbool x (fst p) && cbool y (snd p))%bool) bpairs.

Lemma in_bpairs : forall o c, In (o, c) bpairs <-> matching o c.
Proof.
  intros o c. unfold bpairs, matching. simpl. split.
  - intros [H|[H|[H|[]]]]; injection H as <- <-; auto.
  - intros [[-> ->]|[[-> ->]|[-> ->]]]; auto.
Qed.

Lemma in_opts : forall x y o c,
  In (o, c) (opts x y) <-> matching o c /\ compat x o /\ compat y c.
Proof.
  intros x y o c. unfold opts, compat. rewrite filter_In, in_bpairs.
  simpl. rewrite Bool.andb_true_iff. tauto.
Qed.

Lemma opts_nodup : forall x y, NoDup (opts x y).
Proof.
  intros x y. apply NoDup_filter. unfold bpairs.
  repeat constructor; simpl; intuition discriminate.
Qed.

Fixpoint splits {A} (r : list A) : list (list A * A * list A) :=
  match r with
  | [] => []
  | y :: b => ([], y, b) :: map (fun p => (y :: fst (fst p), snd (fst p), snd p)) (splits b)
  end.

Lemma in_splits : forall {A} (r a b : list A) y,
  In (a, y, b) (splits r) <-> r = a ++ y :: b.
Proof.
  intros A r. induction r as [|z r IH]; intros a b y.
  - simpl. split; [tauto|]. intro E. destruct a; discriminate.
  - simpl. rewrite in_map_iff. split.
    + intros [E|[[[a' y'] b'] [E Hin]]].
      * injection E as <- <- <-. reflexivity.
      * simpl in E. injection E as <- <- <-. apply IH in Hin. subst. reflexivity.
    + intros E. destruct a as [|a0 a].
      * simpl in E. injection E as <- <-. left; reflexivity.
      * right. simpl in E. injection E as <- E. exists (a, y, b).
        split; [reflexivity| apply IH; exact E].
Qed.

Lemma NoDup_map_inj : forall {A B} (f : A -> B) l,
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l. induction l as [|a l IH]; simpl; intros Hi Hn; constructor.
  - inversion Hn; subst. rewrite in_map_iff. intros [z [Ez Hz]].
    apply Hi in Ez; auto. subst. contradiction.
  - inversion Hn; subst. apply IH; auto.
Qed.

Lemma NoDup_flat_map : forall {A B} (f : A -> list B) l,
  NoDup l -> (forall x, In x l -> NoDup (f x)) ->
  (forall x1 x2 t, In x1 l -> In x2 l -> In t (f x1) -> In t (f x2) -> x1 = x2) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l. induction l as [|a l IH]; simpl; intros Hn Hf Hd; [constructor|].
  inversion Hn as [|? ? Hna Hnl]; subst. apply NoDup_app.
  - apply Hf; auto.
  - apply IH; auto. intros x1 x2 t Hx1 Hx2. apply Hd; auto.
  - intros t Ht Ht'. apply in_flat_map in Ht' as [z [Hz Htz]].
    assert (a = z) by (apply (Hd a z t); auto). subst. contradiction.
Qed.

Lemma splits_nodup : forall {A} (r : list A), NoDup (splits r).
Proof.
  intros A r. induction r as [|y b IH]; simpl; constructor.
  - rewrite in_map_iff. intros [[[a' y'] b'] [E _]]. simpl in E.
    injection E as E1 _ _. discriminate E1.
  - apply NoDup_map_inj; auto.
    intros [[a1 y1] b1] [[a2 y2] b2] _ _ E. simpl in E.
    injection E as E1 E2 E3. subst. reflexivity.
Qed.

Lemma app_len_inj : forall {A} (a a' l l' : list A),
  List.length a = List.length a' -> a ++ l = a' ++ l' -> a = a' /\ l = l'.
Proof.
  intros A a. induction a as [|z a IH]; intros a' l l' Hl E; destruct a' as [|z' a'];
    simpl in *; try discriminate; auto.
  injection Hl as Hl. injection E as -> E. destruct (IH a' l l' Hl E). subst. auto.
Qed.

(* The enumeration of the regular completions of a word. *)
Fixpoint enF (f : nat) (w : list ascii) : list (list ascii) :=
  match f with
  | O => []
  | S f' =>
      match w with
      | [] => [[]]
      | x :: r =>
          flat_map (fun s =>
            flat_map (fun p =>
              flat_map (fun u => map (fun v => fst p :: u ++ snd p :: v) (enF f' (snd s)))
                (enF f' (fst (fst s))))
              (opts x (snd (fst s))))
            (splits r)
      end
  end.

Lemma enF_spec : forall f w, (List.length w < f)%nat ->
  NoDup (enF f w) /\ forall t, In t (enF f w) <-> Forall2 compat w t /\ regL t.
Proof.
  induction f as [|f IH]; intros w Hw; [simpl in Hw; lia|].
  destruct w as [|x r].
  - simpl. split.
    + constructor; [intros []|constructor].
    + intros t. split.
      * intros [<-|[]]. split; constructor.
      * intros [HF _]. inversion HF. left; reflexivity.
  - simpl in Hw.
    assert (Hsub : forall a y b, In (a, y, b) (splits r) ->
              (List.length a < f)%nat /\ (List.length b < f)%nat).
    { intros a y b H. apply in_splits in H. subst r.
      rewrite List.length_app in Hw. simpl in Hw. lia. }
    split.
    + cbn [enF]. apply NoDup_flat_map; [apply splits_nodup| |].
      * intros [[a y] b] Hs. destruct (Hsub _ _ _ Hs) as [Ha Hb].
        destruct (IH a Ha) as [Na Sa]. destruct (IH b Hb) as [Nb Sb]. simpl.
        apply NoDup_flat_map; [apply opts_nodup| |].
        -- intros [o c] Hoc. simpl. apply NoDup_flat_map; [exact Na| |].
           ++ intros u Hu. apply NoDup_map_inj; auto.
              intros v1 v2 _ _ E. injection E as E. apply app_inv_head in E.
              injection E as E. exact E.
           ++ intros u1 u2 t Hu1 Hu2 Ht1 Ht2.
              apply in_map_iff in Ht1 as [v1 [<- _]].
              apply in_map_iff in Ht2 as [v2 [E _]].
              apply Sa in Hu1 as [_ Ru1]. apply Sa in Hu2 as [_ Ru2].
              apply in_opts in Hoc as (Hm & _ & _).
              destruct (matching_oc _ _ Hm) as (Hc & _ & _).
              apply decomp_unique in E; auto. symmetry; apply E.
        -- intros [o1 c1] [o2 c2] t H1 H2 Ht1 Ht2. simpl in Ht1, Ht2.
           apply in_flat_map in Ht1 as [u1 [Hu1 Ht1]].
           apply in_map_iff in Ht1 as [v1 [<- _]].
           apply in_flat_map in Ht2 as [u2 [Hu2 Ht2]].
           apply in_map_iff in Ht2 as [v2 [E _]].
           apply Sa in Hu1 as [_ Ru1]. apply Sa in Hu2 as [_ Ru2].
           apply in_opts in H1 as (Hm1 & _ & _). apply in_opts in H2 as (Hm2 & _ & _).
           destruct (matching_oc _ _ Hm1) as (Hc1 & _ & _).
           destruct (matching_oc _ _ Hm2) as (Hc2 & _ & _).
           apply decomp_unique in E; auto. destruct E as (-> & _ & -> & _). reflexivity.
      * intros [[a1 y1] b1] [[a2 y2] b2] t H1 H2 Ht1 Ht2. simpl in Ht1, Ht2.
        destruct (Hsub _ _ _ H1) as [Ha1 Hb1]. destruct (Hsub _ _ _ H2) as [Ha2 Hb2].
        apply in_flat_map in Ht1 as [[o1 c1] [Hoc1 Ht1]].
        apply in_flat_map in Ht1 as [u1 [Hu1 Ht1]].
        apply in_map_iff in Ht1 as [v1 [<- _]].
        apply in_flat_map in Ht2 as [[o2 c2] [Hoc2 Ht2]].
        apply in_flat_map in Ht2 as [u2 [Hu2 Ht2]].
        apply in_map_iff in Ht2 as [v2 [E _]].
        apply (IH a1 Ha1) in Hu1 as [Fu1 Ru1]. apply (IH a2 Ha2) in Hu2 as [Fu2 Ru2].
        apply in_opts in Hoc1 as (Hm1 & _ & _). apply in_opts in Hoc2 as (Hm2 & _ & _).
        destruct (matching_oc _ _ Hm1) as (Hc1 & _ & _).
        destruct (matching_oc _ _ Hm2) as (Hc2 & _ & _).
        simpl in E. apply decomp_unique in E; auto. destruct E as (_ & Eu & _ & _).
        apply Forall2_length in Fu1. apply Forall2_length in Fu2.
        apply in_splits in H1. apply in_splits in H2. rewrite H1 in H2.
        apply app_len_inj in H2; [|subst; lia]. destruct H2 as [-> H2].
        injection H2 as -> ->. reflexivity.
    + intros t. cbn [enF]. rewrite in_flat_map. split.
      * intros [[[a y] b] [Hs Ht]]. simpl in Ht.
        apply in_flat_map in Ht as [[o c] [Hoc Ht]].
        apply in_flat_map in Ht as [u [Hu Ht]].
        apply in_map_iff in Ht as [v [<- Hv]]. simpl.
        destruct (Hsub _ _ _ Hs) as [Ha Hb].
        apply (IH a Ha) in Hu as [Fu Ru]. apply (IH b Hb) in Hv as [Fv Rv].
        apply in_opts in Hoc as (Hm & Hxo & Hyc). apply in_splits in Hs. subst r.
        split.
        -- constructor; [exact Hxo|]. apply Forall2_app; [exact Fu|].
           constructor; assumption.
        -- apply regL_build; assumption.
      * intros [HF HR].
        destruct (regL_decomp _ HR) as [->|(o & c & u & v & Hm & Hu & Hv & ->)];
          [inversion HF|].
        inversion HF as [|? ? ? ? Hxo HF']; subst.
        apply Forall2_app_inv_r in HF' as (r1 & r2 & F1 & F2 & ->).
        inversion F2 as [|y ? b ? Hyc Fb]; subst.
        rewrite List.length_app in Hw. simpl in Hw.
        exists (r1, y, b). split; [apply in_splits; reflexivity|]. simpl.
        apply in_flat_map. exists (o, c). split; [apply in_opts; auto|]. simpl.
        apply in_flat_map. exists u. split.
        -- apply (IH r1 ltac:(lia)). auto.
        -- apply in_map_iff. exists v. split; [reflexivity|].
           apply (IH b ltac:(lia)). auto.
Qed.

(* ================================================================== *)
(* Counting                                                            *)
(* ================================================================== *)

Definition cnt (w : list ascii) : nat := List.length (enF (S (List.length w)) w).

Lemma enF_len_indep : forall f f' w, (List.length w < f)%nat -> (List.length w < f')%nat ->
  List.length (enF f w) = List.length (enF f' w).
Proof.
  intros f f' w H H'.
  destruct (enF_spec f w H) as [N1 S1]. destruct (enF_spec f' w H') as [N2 S2].
  apply Nat.le_antisymm; apply NoDup_incl_length; auto; intros t Ht.
  - apply S2, S1, Ht.
  - apply S1, S2, Ht.
Qed.

Lemma list_sum_const : forall {A} (l : list A) c,
  list_sum (map (fun _ => c) l) = (List.length l * c)%nat.
Proof. intros A l c. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Definition P (x y : ascii) : nat := List.length (opts x y).

Lemma enF_S_cons : forall f x r, enF (S f) (x :: r) =
  flat_map (fun s =>
    flat_map (fun p =>
      flat_map (fun u => map (fun v => fst p :: u ++ snd p :: v) (enF f (snd s)))
        (enF f (fst (fst s))))
      (opts x (snd (fst s))))
    (splits r).
Proof. reflexivity. Qed.

Lemma cnt_cons : forall x r, cnt (x :: r) =
  list_sum (map (fun s => P x (snd (fst s)) * cnt (fst (fst s)) * cnt (snd s))%nat (splits r)).
Proof.
  intros x r. unfold cnt at 1. change (List.length (x :: r)) with (S (List.length r)).
  rewrite enF_S_cons.
  rewrite length_flat_map. f_equal. apply map_ext_in.
  intros [[a y] b] Hs. cbn [fst snd]. apply in_splits in Hs.
  assert (Ha : List.length (enF (S (List.length r)) a) = cnt a).
  { unfold cnt. apply enF_len_indep; subst r; rewrite ?List.length_app; simpl; lia. }
  assert (Hb : List.length (enF (S (List.length r)) b) = cnt b).
  { unfold cnt. apply enF_len_indep; subst r; rewrite ?List.length_app; simpl; lia. }
  rewrite length_flat_map. erewrite map_ext.
  2:{ intros p. rewrite length_flat_map. erewrite map_ext.
      2:{ intros u. apply length_map. }
      rewrite list_sum_const. reflexivity. }
  rewrite list_sum_const. rewrite Ha, Hb. unfold P. lia.
Qed.

Lemma cnt_nil : cnt [] = 1%nat.
Proof. reflexivity. Qed.

Lemma cnt_odd : forall w, Nat.Odd (List.length w) -> cnt w = 0%nat.
Proof.
  intros w Ho. unfold cnt.
  destruct (enF (S (List.length w)) w) as [|t E] eqn:HE; [reflexivity|]. exfalso.
  destruct (enF_spec (S (List.length w)) w ltac:(lia)) as [_ Hs].
  assert (Ht : In t (enF (S (List.length w)) w)) by (rewrite HE; left; reflexivity).
  apply Hs in Ht as [HF HR]. apply Forall2_length in HF. apply regL_even in HR.
  rewrite <- HF in HR. destruct Ho as [k Hk]. destruct HR as [m Hm]. lia.
Qed.

(* Intervals [i, j) of a word. *)
Definition sub (w : list ascii) (i j : nat) : list ascii := firstn (j - i) (skipn i w).

Lemma sub_len : forall w i j, (j <= List.length w)%nat -> List.length (sub w i j) = (j - i)%nat.
Proof. intros w i j H. unfold sub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma skipn_cons_nth : forall {A} (l : list A) i d, (i < List.length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros A l. induction l as [|a l IH]; intros i d H; destruct i; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma sub_cons : forall w i j, (i < j <= List.length w)%nat ->
  sub w i j = nth i w "?"%char :: sub w (S i) j.
Proof.
  intros w i j H. unfold sub. rewrite (skipn_cons_nth w i "?"%char) by lia.
  replace (j - i)%nat with (S (j - S i)) by lia. reflexivity.
Qed.

Lemma splits_eq : forall {A} (l : list A) d,
  splits l = map (fun q => (firstn q l, nth q l d, skipn (S q) l)) (seq 0 (List.length l)).
Proof.
  intros A l d. induction l as [|a l IH]; simpl; [reflexivity|]. f_equal.
  rewrite IH, <- seq_shift, !map_map. apply map_ext. intros q. reflexivity.
Qed.

Lemma sub_firstn : forall w i j q, (q <= j - i)%nat ->
  firstn q (sub w i j) = sub w i (i + q).
Proof. intros. unfold sub. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma sub_nth : forall w i j q d, (i + q < j)%nat ->
  nth q (sub w i j) d = nth (i + q) w d.
Proof.
  intros. unfold sub. rewrite nth_firstn.
  replace (q <? j - i)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  apply nth_skipn.
Qed.

Lemma sub_skipn : forall w i j q, (q <= j - i)%nat ->
  skipn q (sub w i j) = sub w (i + q) j.
Proof.
  intros. unfold sub. rewrite skipn_firstn_comm, skipn_skipn.
  replace (q + i)%nat with (i + q)%nat by lia. f_equal. lia.
Qed.

Definition term (w : list ascii) (i j q : nat) : nat :=
  (P (nth i w "?"%char) (nth (i + 1 + q) w "?"%char)
   * cnt (sub w (i + 1) (i + 1 + q)) * cnt (sub w (i + 2 + q) j))%nat.

Definition psum (w : list ascii) (i j q : nat) : nat :=
  list_sum (map (term w i j) (seq 0 q)).

Lemma cnt_rec : forall w i j, (i <= j <= List.length w)%nat ->
  cnt (sub w i j) = ((if (j =? i)%nat then 1 else 0) + psum w i j (j - i - 1))%nat.
Proof.
  intros w i j H. unfold psum. destruct (Nat.eq_dec j i) as [->|Hne].
  - rewrite Nat.eqb_refl. unfold sub. rewrite Nat.sub_diag. reflexivity.
  - rewrite (proj2 (Nat.eqb_neq j i) Hne). rewrite sub_cons by lia.
    rewrite cnt_cons, (splits_eq _ "?"%char), sub_len by lia.
    replace (j - S i)%nat with (j - i - 1)%nat by lia.
    rewrite map_map. simpl (0 + _)%nat. f_equal. apply map_ext_in.
    intros q Hq. apply in_seq in Hq. unfold term. cbn [fst snd].
    rewrite sub_firstn by lia. rewrite sub_nth by lia. rewrite sub_skipn by lia.
    replace (S i + q)%nat with (i + 1 + q)%nat by lia.
    replace (S i + S q)%nat with (i + 2 + q)%nat by lia.
    replace (S i) with (i + 1)%nat by lia. reflexivity.
Qed.

Lemma psum_step : forall w i j q, (i + q + 2 <= j <= List.length w)%nat -> Nat.Even q ->
  psum w i j (q + 2) = (psum w i j q + term w i j q)%nat.
Proof.
  intros w i j q H He. unfold psum. rewrite seq_app, map_app, list_sum_app. simpl.
  assert (Hz : term w i j (S q) = 0%nat).
  { unfold term. rewrite (cnt_odd (sub w (i + 1) (i + 1 + S q))); [lia|].
    rewrite sub_len by lia. destruct He as [k Hk]. exists k. lia. }
  rewrite Hz. lia.
Qed.

Lemma psum_final : forall w i j, (i <= j <= List.length w)%nat -> Nat.Even (j - i) ->
  psum w i j (j - i) = psum w i j (j - i - 1).
Proof.
  intros w i j H He. destruct (Nat.eq_dec j i) as [->|Hne].
  - rewrite Nat.sub_diag. reflexivity.
  - unfold psum. replace (j - i)%nat with ((j - i - 1) + 1)%nat at 1 by lia.
    rewrite seq_app, map_app, list_sum_app. simpl.
    assert (Hz : term w i j (j - i - 1) = 0%nat).
    { unfold term. rewrite (cnt_odd (sub w (i + 1) (i + 1 + (j - i - 1)))); [lia|].
      rewrite sub_len by lia. destruct He as [k Hk]. exists (k - 1)%nat. lia. }
    rewrite Hz. lia.
Qed.

(* ================================================================== *)
(* From String.string to lists                                         *)
(* ================================================================== *)

Lemma los_app : forall a b : string,
  list_ascii_of_string (a ++ b)%string = list_ascii_of_string a ++ list_ascii_of_string b.
Proof. induction a as [|c a IH]; intros b; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma sol_app : forall a b : list ascii,
  string_of_list_ascii (a ++ b) = (string_of_list_ascii a ++ string_of_list_ascii b)%string.
Proof. induction a as [|c a IH]; intros b; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma los_length : forall s : string, List.length (list_ascii_of_string s) = String.length s.
Proof. induction s as [|c s IH]; simpl; congruence. Qed.

Lemma los_get : forall (s : string) k, String.get k s = nth_error (list_ascii_of_string s) k.
Proof. induction s as [|c s IH]; intros [|k]; simpl; auto. Qed.

Lemma regular_regL : forall t, regular t -> regL (list_ascii_of_string t).
Proof.
  induction 1 as [| o c a Hm Ha IH | a b Ha IHa Hb IHb].
  - constructor.
  - simpl. rewrite los_app. simpl. apply rL_wrap; auto.
  - rewrite los_app. apply rL_cat; auto.
Qed.

Lemma regL_regular : forall l, regL l -> regular (string_of_list_ascii l).
Proof.
  induction 1 as [| o c a Hm Ha IH | a b Ha IHa Hb IHb].
  - constructor.
  - simpl. rewrite sol_app. simpl. apply regular_wrap; auto.
  - rewrite sol_app. apply regular_cat; auto.
Qed.

Lemma regular_iff : forall t, regular t <-> regL (list_ascii_of_string t).
Proof.
  intros t. split; [apply regular_regL|].
  intros H. apply regL_regular in H. rewrite string_of_list_ascii_of_string in H. exact H.
Qed.

Lemma Forall2_compat_iff : forall L T : list ascii,
  Forall2 compat L T <-> List.length T = List.length L /\
    forall k, (k < List.length L)%nat ->
      nth_error L k = Some "?"%char \/ nth_error T k = nth_error L k.
Proof.
  intros L. induction L as [|a L IH]; intros T; split.
  - intros HF. inversion HF. simpl. split; [reflexivity|]. intros k Hk; lia.
  - intros [Hl _]. destruct T; [constructor|discriminate].
  - intros HF. inversion HF as [|? b ? T' Hab HF']; subst.
    apply IH in HF' as [Hl Hk]. simpl. split; [congruence|].
    intros [|k] Hk'; simpl.
    + unfold compat, cbool in Hab. apply Bool.orb_true_iff in Hab as [E|E];
        apply Ascii.eqb_eq in E; subst; auto.
    + apply Hk. lia.
  - intros [Hl Hk]. destruct T as [|b T]; [discriminate|]. constructor.
    + destruct (Hk 0%nat ltac:(simpl; lia)) as [E|E]; simpl in E; injection E as E;
        unfold compat, cbool; subst; rewrite Ascii.eqb_refl; [apply Bool.orb_true_r|reflexivity].
    + apply IH. simpl in Hl. split; [lia|]. intros k Hk'. apply (Hk (S k)). simpl; lia.
Qed.

Lemma completion_iff : forall s t,
  completion s t <-> Forall2 compat (list_ascii_of_string s) (list_ascii_of_string t).
Proof.
  intros s t. rewrite Forall2_compat_iff, !los_length. unfold completion.
  split; intros [Hl Hk]; split; auto; intros k Hlt.
  - rewrite <- !los_get. auto.
  - rewrite !los_get. auto.
Qed.

(* ================================================================== *)
(* Uint63 / PArray plumbing                                            *)
(* ================================================================== *)

Local Open Scope uint63_scope.
Local Open Scope array_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

Lemma add_small : forall a b : int, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof.
  intros a b H. rewrite add_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia.
Qed.

Lemma mul_small : forall a b : int, ((φ a) * (φ b) < wB)%Z -> (φ (a * b)) = ((φ a) * (φ b))%Z.
Proof.
  intros a b H. rewrite mul_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). nia.
Qed.

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

Lemma dec_down : forall t : int,
  (0 <? t) = true -> Zwf 0 (φ (t - 1)) (φ t).
Proof.
  intros t H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (t - 1)) = ((φ t) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

Definition MOD : int := 100000.

(* min v MOD *)
Definition capm (v : int) : int := if v <? MOD then v else MOD.

(* the character a may be o, and the character b may be c *)
Definition okp (a b o c : int) : bool :=
  ((a =? o) || (a =? 63)) && ((b =? c) || (b =? 63)).

(* the number of bracket kinds (o, c) such that a can be o and b can be c *)
Definition pcode (a b : int) : int :=
  (if okp a b 40 41 then 1 else 0) + (if okp a b 91 93 then 1 else 0)
  + (if okp a b 123 125 then 1 else 0).

(* the residue of the interval [a, b) sits at ixi W a b, its capped count
   at the next cell *)
Definition ixi (W a b : int) : int := 2 * (a * W + b).

(* Sum over k = kk, kk + 2, ... (t terms) of the products, the residue in
   r and the count capped at MOD in c. *)
Fixpoint inner (x : PrimString.string) (tb : array int) (W ci ii j kk t r c : int)
    (H : Acc (Zwf 0) (φ t)) {struct H} : int * int :=
  match bdec (0 <? t) with
  | left Ht =>
      let p := pcode ci (PrimString.get x kk) in
      let ia := ixi W (ii + 1) kk in
      let ib := ixi W (kk + 1) j in
      let ra := tb.[ia] in
      let ca := tb.[ia + 1] in
      let rb := tb.[ib] in
      let cb := tb.[ib + 1] in
      inner x tb W ci ii j (kk + 2) (t - 1)
        ((r + ((p * ra) mod MOD) * rb) mod MOD)
        (capm (c + capm (capm (p * ca) * cb)))
        (Acc_inv H (dec_down t Ht))
  | right _ => (r, c)
  end.

Lemma inner_eq : forall x tb W ci ii j kk t r c H,
  inner x tb W ci ii j kk t r c H =
  match bdec (0 <? t) with
  | left Ht =>
      let p := pcode ci (PrimString.get x kk) in
      let ia := ixi W (ii + 1) kk in
      let ib := ixi W (kk + 1) j in
      let ra := tb.[ia] in
      let ca := tb.[ia + 1] in
      let rb := tb.[ib] in
      let cb := tb.[ib + 1] in
      inner x tb W ci ii j (kk + 2) (t - 1)
        ((r + ((p * ra) mod MOD) * rb) mod MOD)
        (capm (c + capm (capm (p * ca) * cb)))
        (Acc_inv H (dec_down t Ht))
  | right _ => (r, c)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The intervals [ii, ii + L) for ii = ii .. m - 1 (L = 2h). *)
Fixpoint middle (x : PrimString.string) (W h L m ii : int) (tb : array int)
    (H : Acc (Zwf 0) (gap m ii)) {struct H} : array int :=
  match bdec (ii <? m) with
  | left Hi =>
      let j := ii + L in
      let b0 := if h =? 0 then 1 else 0 in
      let rc := inner x tb W (PrimString.get x ii) ii j (ii + 1) h b0 b0
                  (Zwf_well_founded 0 (φ h)) in
      let p := ixi W ii j in
      middle x W h L m (ii + 1) (tb.[p <- fst rc].[p + 1 <- snd rc])
        (Acc_inv H (dec_step m ii Hi))
  | right _ => tb
  end.

Lemma middle_eq : forall x W h L m ii tb H,
  middle x W h L m ii tb H =
  match bdec (ii <? m) with
  | left Hi =>
      let j := ii + L in
      let b0 := if h =? 0 then 1 else 0 in
      let rc := inner x tb W (PrimString.get x ii) ii j (ii + 1) h b0 b0
                  (Zwf_well_founded 0 (φ h)) in
      let p := ixi W ii j in
      middle x W h L m (ii + 1) (tb.[p <- fst rc].[p + 1 <- snd rc])
        (Acc_inv H (dec_step m ii Hi))
  | right _ => tb
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The even interval lengths 2h, 2h + 2, ..., up to n. *)
Fixpoint outer (x : PrimString.string) (n W hm h : int) (tb : array int)
    (H : Acc (Zwf 0) (gap hm h)) {struct H} : array int :=
  match bdec (h <? hm) with
  | left Hh =>
      let L := 2 * h in
      outer x n W hm (h + 1)
        (middle x W h L (n - L + 1) 0 tb (Zwf_well_founded 0 (gap (n - L + 1) 0)))
        (Acc_inv H (dec_step hm h Hh))
  | right _ => tb
  end.

Lemma outer_eq : forall x n W hm h tb H,
  outer x n W hm h tb H =
  match bdec (h <? hm) with
  | left Hh =>
      let L := 2 * h in
      outer x n W hm (h + 1)
        (middle x W h L (n - L + 1) 0 tb (Zwf_well_founded 0 (gap (n - L + 1) 0)))
        (Acc_inv H (dec_step hm h Hh))
  | right _ => tb
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition zapis_impl (x : PrimString.string) : uint * bool :=
  let n := PrimString.length x in
  let W := n + 1 in
  let tb := outer x n W (n / 2 + 1) 0 (PArray.make (2 * (W * W)) 0)
              (Zwf_well_founded 0 (gap (n / 2 + 1) 0)) in
  let p := ixi W 0 n in
  (tb.[p], MOD <=? tb.[p + 1]).

(* ================================================================== *)
(* Arithmetic of one step                                              *)
(* ================================================================== *)

Lemma capm_spec : forall v, (φ (capm v)) = Z.min (φ v) 100000.
Proof.
  intros v. unfold capm. destruct (v <? MOD) eqn:E.
  - rewrite ltb_spec in E. change (φ MOD) with 100000%Z in E. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
    change (φ MOD) with 100000%Z in *. lia.
Qed.

Lemma min_mul_cap : forall a b : Z, (0 <= a)%Z -> (0 <= b)%Z ->
  Z.min (Z.min a 100000 * Z.min b 100000) 100000 = Z.min (a * b) 100000.
Proof.
  intros a b Ha0 Hb0.
  destruct (Z.eq_dec a 0) as [->|Ha]; [simpl; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb]; [rewrite !Z.mul_0_r; simpl; lia|].
  destruct (Z.le_gt_cases 100000 a), (Z.le_gt_cases 100000 b).
  - rewrite (Z.min_r a), (Z.min_r b) by lia. nia.
  - rewrite (Z.min_r a), (Z.min_l b) by lia. nia.
  - rewrite (Z.min_l a), (Z.min_r b) by lia. nia.
  - rewrite (Z.min_l a), (Z.min_l b) by lia. reflexivity.
Qed.

Lemma step_r : forall (r p ra rb : int) (S Pn A B : Z),
  (0 <= S)%Z -> (0 <= Pn <= 3)%Z -> (0 <= A)%Z -> (0 <= B)%Z ->
  (φ r) = (S mod 100000)%Z -> (φ p) = Pn ->
  (φ ra) = (A mod 100000)%Z -> (φ rb) = (B mod 100000)%Z ->
  (φ ((r + ((p * ra) mod MOD) * rb) mod MOD)) = ((S + Pn * A * B) mod 100000)%Z.
Proof.
  intros r p ra rb S Pn A B HS HP HA HB Hr Hp Ha Hb.
  pose proof (Z.mod_pos_bound S 100000 ltac:(lia)).
  pose proof (Z.mod_pos_bound A 100000 ltac:(lia)).
  pose proof (Z.mod_pos_bound B 100000 ltac:(lia)).
  assert (E1 : (φ (p * ra)) = ((φ p) * (φ ra))%Z) by (apply mul_small; rewrite wB_val; nia).
  assert (E2 : (φ ((p * ra) mod MOD)) = (((φ p) * (φ ra)) mod 100000)%Z)
    by (rewrite mod_spec, E1; reflexivity).
  assert (B2 : (0 <= ((φ p) * (φ ra)) mod 100000 < 100000)%Z) by (apply Z.mod_pos_bound; lia).
  assert (E3 : (φ (((p * ra) mod MOD) * rb)) = ((((φ p) * (φ ra)) mod 100000) * (φ rb))%Z)
    by (rewrite mul_small; rewrite E2; [reflexivity|]; rewrite wB_val; nia).
  assert (E4 : (φ (r + ((p * ra) mod MOD) * rb)) = ((φ r) + (((φ p) * (φ ra)) mod 100000) * (φ rb))%Z)
    by (rewrite add_small; rewrite E3; [reflexivity|]; rewrite wB_val; nia).
  rewrite mod_spec, E4. change (φ MOD) with 100000%Z.
  rewrite Hr, Hp, Ha, Hb.
  rewrite Zplus_mod_idemp_l, Zmult_mod_idemp_r.
  rewrite <- (Zplus_mod_idemp_r ((Pn * A) mod 100000 * (B mod 100000))).
  rewrite <- Zmult_mod, Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma step_c : forall (c p ca cb : int) (S Pn A B : Z),
  (0 <= S)%Z -> (0 <= Pn <= 3)%Z -> (0 <= A)%Z -> (0 <= B)%Z ->
  (φ c) = Z.min S 100000 -> (φ p) = Pn ->
  (φ ca) = Z.min A 100000 -> (φ cb) = Z.min B 100000 ->
  (φ (capm (c + capm (capm (p * ca) * cb)))) = Z.min (S + Pn * A * B) 100000.
Proof.
  intros c p ca cb S Pn A B HS HP HA HB Hc Hp Ha Hb.
  assert (E1 : (φ (capm (p * ca))) = Z.min (Pn * A) 100000).
  { rewrite capm_spec, mul_small; [|rewrite wB_val, Hp, Ha; nia].
    rewrite Hp, Ha. rewrite <- (min_mul_cap Pn A) by lia. rewrite (Z.min_l Pn) by lia. lia. }
  assert (E2 : (φ (capm (capm (p * ca) * cb))) = Z.min (Pn * A * B) 100000).
  { rewrite capm_spec, mul_small; [|rewrite wB_val, E1, Hb; nia].
    rewrite E1, Hb. rewrite <- (min_mul_cap (Pn * A) B) by nia. lia. }
  rewrite capm_spec, add_small; [|rewrite wB_val, E2, Hc; lia].
  rewrite E2, Hc. lia.
Qed.

Lemma eqb_lit : forall (a k : int) (u ch : ascii),
  Z.to_N (φ a) = N_of_ascii u -> N_of_ascii ch = Z.to_N (φ k) -> (a =? k) = (u =? ch)%char.
Proof.
  intros a k u ch Ha Hk. apply Bool.eq_iff_eq_true. rewrite Uint63.eqb_spec, Ascii.eqb_eq.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded k). split.
  - intros ->. rewrite <- (ascii_N_embedding u), <- (ascii_N_embedding ch). congruence.
  - intros ->. apply to_Z_inj. lia.
Qed.

Lemma P_le3 : forall u v, (P u v <= 3)%nat.
Proof.
  intros u v. unfold P, opts.
  pose proof (filter_length_le (fun p => (cbool u (fst p) && cbool v (snd p))%bool) bpairs).
  exact H.
Qed.

Lemma pcode_spec : forall (a b : int) (u v : ascii),
  Z.to_N (φ a) = N_of_ascii u -> Z.to_N (φ b) = N_of_ascii v ->
  (φ (pcode a b)) = Z.of_nat (P u v).
Proof.
  intros a b u v Ha Hb.
  assert (Q : forall (k : int) (ch : ascii), N_of_ascii ch = Z.to_N (φ k) ->
            (a =? k) = (u =? ch)%char) by (intros; apply eqb_lit; auto).
  assert (R : forall (k : int) (ch : ascii), N_of_ascii ch = Z.to_N (φ k) ->
            (b =? k) = (v =? ch)%char) by (intros; apply eqb_lit; auto).
  assert (E1 : okp a b 40 41 = (cbool u "(" && cbool v ")")%bool).
  { unfold okp, cbool. rewrite (Q 40 "("%char), (Q 63 "?"%char), (R 41 ")"%char), (R 63 "?"%char)
      by reflexivity. reflexivity. }
  assert (E2 : okp a b 91 93 = (cbool u "[" && cbool v "]")%bool).
  { unfold okp, cbool. rewrite (Q 91 "["%char), (Q 63 "?"%char), (R 93 "]"%char), (R 63 "?"%char)
      by reflexivity. reflexivity. }
  assert (E3 : okp a b 123 125 = (cbool u "{" && cbool v "}")%bool).
  { unfold okp, cbool. rewrite (Q 123 "{"%char), (Q 63 "?"%char), (R 125 "}"%char), (R 63 "?"%char)
      by reflexivity. reflexivity. }
  unfold pcode. rewrite E1, E2, E3. unfold P, opts, bpairs. cbn [filter fst snd].
  destruct (cbool u "(" && cbool v ")")%bool, (cbool u "[" && cbool v "]")%bool,
    (cbool u "{" && cbool v "}")%bool; reflexivity.
Qed.

Lemma int_of : forall (ii : int) (i : nat), (φ ii) = Z.of_nat i -> ii = of_Z (Z.of_nat i).
Proof.
  intros ii i H. apply to_Z_inj. rewrite of_Z_spec, <- H. symmetry. apply Z.mod_small.
  apply to_Z_bounded.
Qed.

Lemma of_nat_val : forall i : nat, (Z.of_nat i < wB)%Z -> (φ (of_Z (Z.of_nat i))) = Z.of_nat i.
Proof. intros i H. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

(* ================================================================== *)
(* The loops                                                           *)
(* ================================================================== *)

Section Loops.

Variable x : PrimString.string.
Variable w : list ascii.
Variable n : int.
Hypothesis Hn : (φ n) = Z.of_nat (List.length w).
Hypothesis Hn200 : (List.length w <= 200)%nat.
Hypothesis Hch : forall k : nat, (k < List.length w)%nat ->
  Z.to_N (φ (PrimString.get x (of_Z (Z.of_nat k)))) = N_of_ascii (nth k w "?"%char).

Definition ix (a b : nat) : int := ixi (n + 1) (of_Z (Z.of_nat a)) (of_Z (Z.of_nat b)).

Definition SZ : int := 2 * ((n + 1) * (n + 1)).

Definition good (tb : array int) (a b : nat) : Prop :=
  (φ (tb.[ix a b])) = (Z.of_nat (cnt (sub w a b)) mod 100000)%Z /\
  (φ (tb.[ix a b + 1])) = Z.min (Z.of_nat (cnt (sub w a b))) 100000.

Definition done (tb : array int) (lim : nat) : Prop :=
  forall a b, (a <= b <= List.length w)%nat -> Nat.Even (b - a) -> (b - a < lim)%nat ->
  good tb a b.

Lemma W_val : (φ (n + 1)) = (Z.of_nat (List.length w) + 1)%Z.
Proof. rewrite add_small; rewrite Hn; [reflexivity|]. rewrite wB_val. change (φ 1) with 1%Z. lia. Qed.

Lemma SZ_val : (φ SZ) = (2 * ((Z.of_nat (List.length w) + 1) * (Z.of_nat (List.length w) + 1)))%Z.
Proof.
  unfold SZ. pose proof W_val as HW.
  assert (E : (φ ((n + 1) * (n + 1))) = ((Z.of_nat (List.length w) + 1) * (Z.of_nat (List.length w) + 1))%Z)
    by (rewrite mul_small; rewrite HW; [reflexivity|]; rewrite wB_val; nia).
  rewrite mul_small; rewrite E; [reflexivity|]. change (φ 2) with 2%Z. rewrite wB_val. nia.
Qed.

Lemma prod_bound : forall a L : Z, (0 <= a <= 200)%Z -> (0 <= L <= 200)%Z ->
  (0 <= a * (L + 1) <= 40200)%Z.
Proof. intros. nia. Qed.

Lemma ix_val : forall a b, (a <= List.length w)%nat -> (b <= List.length w)%nat ->
  (φ (ix a b)) = (2 * (Z.of_nat a * (Z.of_nat (List.length w) + 1) + Z.of_nat b))%Z /\
  (φ (ix a b + 1)) = (2 * (Z.of_nat a * (Z.of_nat (List.length w) + 1) + Z.of_nat b) + 1)%Z.
Proof.
  intros a b Ha Hb. pose proof W_val as HW.
  pose proof (prod_bound (Z.of_nat a) (Z.of_nat (List.length w)) ltac:(lia) ltac:(lia)) as PB.
  set (X := (Z.of_nat a * (Z.of_nat (List.length w) + 1))%Z) in *.
  assert (Ea : (φ (of_Z (Z.of_nat a))) = Z.of_nat a) by (apply of_nat_val; rewrite wB_val; lia).
  assert (Eb : (φ (of_Z (Z.of_nat b))) = Z.of_nat b) by (apply of_nat_val; rewrite wB_val; lia).
  assert (E1 : (φ (of_Z (Z.of_nat a) * (n + 1))) = X).
  { rewrite mul_small; rewrite Ea, HW; [reflexivity|]. fold X. rewrite wB_val; lia. }
  assert (E2 : (φ (of_Z (Z.of_nat a) * (n + 1) + of_Z (Z.of_nat b))) = (X + Z.of_nat b)%Z).
  { rewrite add_small; rewrite E1, Eb; [reflexivity|]. rewrite wB_val; lia. }
  assert (E3 : (φ (ix a b)) = (2 * (X + Z.of_nat b))%Z).
  { unfold ix, ixi. rewrite mul_small; change (φ 2) with 2%Z; rewrite E2; [reflexivity|].
    rewrite wB_val. lia. }
  split; [exact E3|].
  rewrite add_small; rewrite E3; change (φ 1) with 1%Z; [reflexivity|]. rewrite wB_val. lia.
Qed.

Lemma lin_inj : forall a b a' b' Wz : Z, (0 <= a)%Z -> (0 <= a')%Z ->
  (0 <= b < Wz)%Z -> (0 <= b' < Wz)%Z -> (a * Wz + b = a' * Wz + b')%Z -> a = a' /\ b = b'.
Proof.
  intros a b a' b' Wz Ha Ha' Hb Hb' E.
  destruct (Z.lt_trichotomy a a') as [H|[H|H]].
  - exfalso. assert (a * Wz + Wz <= a' * Wz)%Z by nia. lia.
  - subst. lia.
  - exfalso. assert (a' * Wz + Wz <= a * Wz)%Z by nia. lia.
Qed.

Lemma ix_lt : forall a b, (a <= List.length w)%nat -> (b <= List.length w)%nat ->
  (ix a b <? SZ) = true /\ (ix a b + 1 <? SZ) = true.
Proof.
  intros a b Ha Hb. destruct (ix_val a b Ha Hb) as [E1 E2].
  rewrite !ltb_spec, E1, E2, SZ_val.
  assert (Z.of_nat a * (Z.of_nat (List.length w) + 1) + Z.of_nat b + 1 <=
          (Z.of_nat (List.length w) + 1) * (Z.of_nat (List.length w) + 1))%Z.
  { assert (Z.of_nat a * (Z.of_nat (List.length w) + 1) <=
            Z.of_nat (List.length w) * (Z.of_nat (List.length w) + 1))%Z
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  lia.
Qed.

Lemma good_set_other : forall tb a b i j v1 v2,
  (a <= List.length w)%nat -> (b <= List.length w)%nat ->
  (i <= List.length w)%nat -> (j <= List.length w)%nat ->
  (a, b) <> (i, j) -> good tb a b ->
  good (tb.[ix i j <- v1].[ix i j + 1 <- v2]) a b.
Proof.
  intros tb a b i j v1 v2 Ha Hb Hi Hj Hne [G1 G2].
  destruct (ix_val a b Ha Hb) as [Ea Ea']. destruct (ix_val i j Hi Hj) as [Ei Ei'].
  assert (Hd : (Z.of_nat a * (Z.of_nat (List.length w) + 1) + Z.of_nat b)%Z <>
               (Z.of_nat i * (Z.of_nat (List.length w) + 1) + Z.of_nat j)%Z).
  { intros E. apply lin_inj in E; try lia. apply Hne. f_equal; lia. }
  split.
  - rewrite aget_set_other, aget_set_other; [exact G1| |];
      intro F; apply (f_equal to_Z) in F; lia.
  - rewrite aget_set_other, aget_set_other; [exact G2| |];
      intro F; apply (f_equal to_Z) in F; lia.
Qed.

Lemma good_set_same : forall tb i j v1 v2,
  PArray.length tb = SZ ->
  (i <= List.length w)%nat -> (j <= List.length w)%nat ->
  (φ v1) = (Z.of_nat (cnt (sub w i j)) mod 100000)%Z ->
  (φ v2) = Z.min (Z.of_nat (cnt (sub w i j))) 100000 ->
  good (tb.[ix i j <- v1].[ix i j + 1 <- v2]) i j.
Proof.
  intros tb i j v1 v2 Hl Hi Hj H1 H2.
  destruct (ix_val i j Hi Hj) as [Ei Ei']. destruct (ix_lt i j Hi Hj) as [L1 L2].
  split.
  - rewrite aget_set_other by (intro F; apply (f_equal to_Z) in F; lia).
    rewrite aget_set_same by (rewrite Hl; exact L1). exact H1.
  - rewrite aget_set_same by (rewrite alength_set, Hl; exact L2). exact H2.
Qed.

Lemma done_mono : forall tb lim lim', (lim' <= lim)%nat -> done tb lim -> done tb lim'.
Proof. intros tb lim lim' H D a b H1 H2 H3. apply D; auto. lia. Qed.

Definition base (i j : nat) : nat := if (j =? i)%nat then 1%nat else 0%nat.

Lemma inner_spec : forall tb (i j h : nat) (ii jj ci : int),
  PArray.length tb = SZ -> done tb (2 * h) ->
  (φ ii) = Z.of_nat i -> (φ jj) = Z.of_nat j -> j = (i + 2 * h)%nat ->
  (j <= List.length w)%nat ->
  ((i < List.length w)%nat -> Z.to_N (φ ci) = N_of_ascii (nth i w "?"%char)) ->
  forall (z : Z) (q tn : nat) (kk t r c : int) (H : Acc (Zwf 0) (φ t)),
  (φ t) = z -> (φ t) = Z.of_nat tn ->
  (φ kk) = Z.of_nat (i + 1 + q) -> Nat.Even q -> (q + 2 * tn = 2 * h)%nat ->
  (φ r) = (Z.of_nat (base i j + psum w i j q) mod 100000)%Z ->
  (φ c) = Z.min (Z.of_nat (base i j + psum w i j q)) 100000 ->
  (φ (fst (inner x tb (n + 1) ci ii jj kk t r c H))) = (Z.of_nat (cnt (sub w i j)) mod 100000)%Z /\
  (φ (snd (inner x tb (n + 1) ci ii jj kk t r c H))) = Z.min (Z.of_nat (cnt (sub w i j))) 100000.
Proof.
  intros tb i j h ii jj ci Hl D Hii Hjj Hj HjN Hci z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q tn kk t r c H Hz Ht Hkk Hq Hqt Hr Hc.
  rewrite inner_eq. destruct (bdec (0 <? t)) as [Hp | Hp].
  - pose proof Hp as Hp'. rewrite ltb_spec in Hp'. change (φ 0) with 0%Z in Hp'.
    assert (Htn : (1 <= tn)%nat) by lia.
    cbv zeta.
    set (A := cnt (sub w (i + 1) (i + 1 + q))).
    set (B := cnt (sub w (i + 2 + q) j)).
    set (Pn := P (nth i w "?"%char) (nth (i + 1 + q) w "?"%char)).
    assert (Hi1 : ii + 1 = of_Z (Z.of_nat (i + 1))).
    { apply int_of. rewrite add_small; change (φ 1) with 1%Z; rewrite Hii; [lia|].
      rewrite wB_val; lia. }
    assert (Hkk' : kk = of_Z (Z.of_nat (i + 1 + q))) by (apply int_of; exact Hkk).
    assert (Hk1 : kk + 1 = of_Z (Z.of_nat (i + 2 + q))).
    { apply int_of. rewrite add_small; change (φ 1) with 1%Z; rewrite Hkk; [lia|].
      rewrite wB_val; lia. }
    assert (Hjj' : jj = of_Z (Z.of_nat j)) by (apply int_of; exact Hjj).
    destruct (D (i + 1)%nat (i + 1 + q)%nat ltac:(lia)
                ltac:(replace (i + 1 + q - (i + 1))%nat with q by lia; exact Hq)
                ltac:(lia)) as [GA1 GA2].
    destruct (D (i + 2 + q)%nat j ltac:(lia)
                ltac:(destruct Hq as [k Hk]; exists (h - k - 1)%nat; lia)
                ltac:(lia)) as [GB1 GB2].
    unfold ix in GA1, GA2, GB1, GB2.
    rewrite <- Hi1, <- Hkk' in GA1, GA2. rewrite <- Hk1, <- Hjj' in GB1, GB2.
    assert (HP : (φ (pcode ci (PrimString.get x kk))) = Z.of_nat Pn).
    { apply pcode_spec; [apply Hci; lia|]. rewrite Hkk'. apply Hch. lia. }
    pose proof (P_le3 (nth i w "?"%char) (nth (i + 1 + q) w "?"%char)) as HP3. fold Pn in HP3.
    assert (Hsum : (base i j + psum w i j (q + 2))%nat
                   = (base i j + psum w i j q + Pn * A * B)%nat).
    { rewrite psum_step; [| lia | exact Hq]. unfold term. fold Pn A B. lia. }
    assert (Ht1 : (φ (t - 1)) = Z.of_nat (tn - 1)) by sia.
    assert (Hkk2 : (φ (kk + 2)) = Z.of_nat (i + 1 + (q + 2))).
    { rewrite add_small; change (φ 2) with 2%Z; rewrite Hkk; [lia|]. rewrite wB_val; lia. }
    refine (IH (φ (t - 1)) _ (q + 2)%nat (tn - 1)%nat (kk + 2) (t - 1) _ _ _
              eq_refl Ht1 Hkk2 _ _ _ _).
    + rewrite <- Hz. apply dec_down. exact Hp.
    + destruct Hq as [k Hk]. exists (k + 1)%nat. lia.
    + lia.
    + rewrite Hsum, (Nat2Z.inj_add (base i j + psum w i j q)), !Nat2Z.inj_mul.
      apply (step_r _ _ _ _ (Z.of_nat (base i j + psum w i j q)) (Z.of_nat Pn)
               (Z.of_nat A) (Z.of_nat B));
        [lia|lia|lia|lia|exact Hr|exact HP|exact GA1|exact GB1].
    + rewrite Hsum, (Nat2Z.inj_add (base i j + psum w i j q)), !Nat2Z.inj_mul.
      apply (step_c _ _ _ _ (Z.of_nat (base i j + psum w i j q)) (Z.of_nat Pn)
               (Z.of_nat A) (Z.of_nat B));
        [lia|lia|lia|lia|exact Hc|exact HP|exact GA2|exact GB2].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hp. change (φ 0) with 0%Z in Hp.
    assert (tn = 0%nat) by lia. subst tn.
    assert (Hq2 : q = (j - i)%nat) by lia. subst q.
    rewrite psum_final in Hr, Hc by (try lia; exists h; lia).
    rewrite (cnt_rec w i j) by lia. unfold base in Hr, Hc. simpl. split; assumption.
Qed.

Lemma sub_small : forall a b : int, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof.
  intros a b H. rewrite sub_spec. apply Z.mod_small.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia.
Qed.

Lemma middle_spec : forall (h : nat) (hh LL m : int),
  (φ hh) = Z.of_nat h -> (φ LL) = Z.of_nat (2 * h) -> (2 * h <= List.length w)%nat ->
  (φ m) = Z.of_nat (List.length w - 2 * h + 1) ->
  forall (z : Z) (i : nat) (ii : int) (tb : array int) (H : Acc (Zwf 0) (gap m ii)),
  gap m ii = z -> (φ ii) = Z.of_nat i -> (i <= List.length w - 2 * h + 1)%nat ->
  PArray.length tb = SZ -> done tb (2 * h) ->
  (forall a, (a < i)%nat -> good tb a (a + 2 * h)%nat) ->
  PArray.length (middle x (n + 1) hh LL m ii tb H) = SZ /\
  done (middle x (n + 1) hh LL m ii tb H) (2 * h + 1).
Proof.
  intros h hh LL m Hh HL HLN Hm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i ii tb H Hz Hii Hi Hl D Dl.
  rewrite middle_eq. destruct (bdec (ii <? m)) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec, Hm, Hii in Hc'.
    cbv zeta.
    set (j := (i + 2 * h)%nat).
    assert (Hjj : (φ (ii + LL)) = Z.of_nat j).
    { rewrite add_small; rewrite Hii, HL; [unfold j; lia|]. rewrite wB_val; lia. }
    assert (Hii1 : (φ (ii + 1)) = Z.of_nat (i + 1)).
    { rewrite add_small; change (φ 1) with 1%Z; rewrite Hii; [lia|]. rewrite wB_val; lia. }
    set (b0 := if hh =? 0 then 1 else 0).
    assert (Hb0 : (φ b0) = Z.of_nat (base i j) /\ (base i j <= 1)%nat).
    { unfold b0, base, j. destruct (Nat.eq_dec h 0) as [->|Hh0].
      - replace (hh =? 0) with true
          by (symmetry; apply Uint63.eqb_spec; apply to_Z_inj; rewrite Hh; reflexivity).
        rewrite Nat.mul_0_r, Nat.add_0_r, Nat.eqb_refl. split; [reflexivity|lia].
      - replace (hh =? 0) with false
          by (symmetry; rewrite eqb_false_spec; intro E; rewrite E in Hh;
              change (φ 0) with 0%Z in Hh; lia).
        replace (i + 2 * h =? i)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
        split; [reflexivity|lia]. }
    assert (Hps : psum w i j 0 = 0%nat) by reflexivity.
    assert (Hr0 : (φ b0) = (Z.of_nat (base i j + psum w i j 0) mod 100000)%Z).
    { rewrite Hps, Nat.add_0_r. destruct Hb0 as [E1 E2]. rewrite E1.
      rewrite Z.mod_small; lia. }
    assert (Hc0 : (φ b0) = Z.min (Z.of_nat (base i j + psum w i j 0)) 100000).
    { rewrite Hps, Nat.add_0_r. destruct Hb0 as [E1 E2]. rewrite E1. lia. }
    assert (Hci : (i < List.length w)%nat ->
              Z.to_N (φ (PrimString.get x ii)) = N_of_ascii (nth i w "?"%char)).
    { intros Hiw. rewrite (int_of ii i Hii). apply Hch. exact Hiw. }
    destruct (inner_spec tb i j h ii (ii + LL) (PrimString.get x ii) Hl D Hii Hjj eq_refl
                ltac:(unfold j; lia) Hci (φ hh) 0%nat h (ii + 1) hh b0 b0
                (Zwf_well_founded 0 (φ hh)) eq_refl Hh
                ltac:(rewrite Hii1; f_equal; lia) ltac:(exists 0%nat; lia) ltac:(lia)
                Hr0 Hc0) as [R1 R2].
    assert (Hp : ixi (n + 1) ii (ii + LL) = ix i j).
    { unfold ix. rewrite (int_of _ j Hjj), (int_of ii i Hii). reflexivity. }
    refine (IH (gap m (ii + 1)) _ (i + 1)%nat (ii + 1) _ _ eq_refl Hii1 _ _ _ _).
    + rewrite <- Hz. apply dec_step. exact Hc.
    + lia.
    + rewrite !alength_set. exact Hl.
    + intros a b Hab He Hlt. rewrite Hp. apply good_set_other; try lia.
      * intro E. injection E as E1 E2. unfold j in E2. lia.
      * apply D; auto.
    + intros a Ha. rewrite Hp. destruct (Nat.eq_dec a i) as [->|Hai].
      * apply good_set_same; first [exact Hl | exact R1 | exact R2 | lia].
      * apply good_set_other; try lia.
        -- intro E. injection E as E1 E2. lia.
        -- apply Dl. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hm, Hii in Hc.
    split; [exact Hl|].
    intros a b Hab He Hlt.
    destruct (Nat.lt_ge_cases (b - a) (2 * h)) as [Hlt'|Hge].
    + apply D; auto.
    + replace b with (a + 2 * h)%nat by lia. apply Dl. lia.
Qed.

Lemma outer_spec : forall hm : int, (φ hm) = Z.of_nat (List.length w / 2 + 1) ->
  forall (z : Z) (h : nat) (hh : int) (tb : array int) (H : Acc (Zwf 0) (gap hm hh)),
  gap hm hh = z -> (φ hh) = Z.of_nat h -> (h <= List.length w / 2 + 1)%nat ->
  PArray.length tb = SZ -> done tb (2 * h) ->
  done (outer x n (n + 1) hm hh tb H) (List.length w + 1).
Proof.
  intros hm Hhm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h hh tb H Hz Hh Hle Hl D.
  pose proof (Nat.div_mod (List.length w) 2 ltac:(lia)) as Dm.
  pose proof (Nat.mod_upper_bound (List.length w) 2 ltac:(lia)) as Mb.
  rewrite outer_eq. destruct (bdec (hh <? hm)) as [Hc | Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec, Hhm, Hh in Hc'.
    cbv zeta.
    assert (HL : (φ (2 * hh)) = Z.of_nat (2 * h)).
    { rewrite mul_small; change (φ 2) with 2%Z; rewrite Hh; [lia|]. rewrite wB_val; lia. }
    assert (Hm : (φ (n - 2 * hh + 1)) = Z.of_nat (List.length w - 2 * h + 1)).
    { assert (Hs : (φ (n - 2 * hh)) = Z.of_nat (List.length w - 2 * h)).
      { rewrite sub_small by (rewrite HL, Hn; lia). rewrite HL, Hn. lia. }
      rewrite add_small; change (φ 1) with 1%Z; rewrite Hs; [lia|]. rewrite wB_val; lia. }
    destruct (middle_spec h hh (2 * hh) (n - 2 * hh + 1) Hh HL ltac:(lia) Hm _ 0%nat 0 tb
                (Zwf_well_founded 0 (gap (n - 2 * hh + 1) 0)) eq_refl eq_refl ltac:(lia)
                Hl D ltac:(intros a Ha; lia)) as [Hl' D'].
    assert (Hh1 : (φ (hh + 1)) = Z.of_nat (h + 1)).
    { rewrite add_small; change (φ 1) with 1%Z; rewrite Hh; [lia|]. rewrite wB_val; lia. }
    refine (IH (gap hm (hh + 1)) _ (h + 1)%nat (hh + 1) _ _ eq_refl Hh1 _ Hl' _).
    + rewrite <- Hz. apply dec_step. exact Hc.
    + lia.
    + intros a b Hab He Hlt. apply D'; auto. destruct He as [k Hk]. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hhm, Hh in Hc.
    apply (done_mono _ (2 * h)); [lia|exact D].
Qed.

End Loops.

(* ================================================================== *)
(* The contract                                                        *)
(* ================================================================== *)

Lemma zapis_impl_correct : forall (s : string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists o : N * bool, repr (zapis_impl x) o /\ zapis_spec s o.
Proof.
  intros s x Hv [Hlen Hget].
  set (w := list_ascii_of_string s).
  assert (Lw : List.length w = String.length s) by apply los_length.
  destruct Hv as [Hvl Hve _]. unfold slen in Hvl, Hve.
  assert (HN200 : (List.length w <= 200)%nat) by lia.
  assert (HNev : Nat.Even (List.length w)).
  { rewrite Lw. apply N.even_spec in Hve. destruct Hve as [m Hm]. exists (N.to_nat m). lia. }
  set (n := PrimString.length x).
  assert (Hn : (φ n) = Z.of_nat (List.length w)) by (rewrite Lw; symmetry; exact Hlen).
  assert (Hch : forall k : nat, (k < List.length w)%nat ->
            Z.to_N (φ (PrimString.get x (of_Z (Z.of_nat k)))) = N_of_ascii (nth k w "?"%char)).
  { intros k Hk. rewrite Lw in Hk. destruct (Hget k Hk) as [c [Hc Hr]].
    unfold repr, repr_uint in Hr. rewrite Hr. f_equal. symmetry. apply nth_error_nth.
    unfold w. rewrite <- los_get. exact Hc. }
  set (E := enF (S (List.length w)) w).
  set (l := map string_of_list_ascii E).
  assert (Hcnt : cnt w = List.length l) by (unfold l, E, cnt; rewrite length_map; reflexivity).
  exists ((N.of_nat (List.length l) mod 100000)%N, (100000 <=? N.of_nat (List.length l))%N).
  split.
  - unfold zapis_impl. fold n. cbv zeta.
    assert (HSZ : PArray.length (PArray.make (2 * ((n + 1) * (n + 1))) 0) = SZ n).
    { rewrite alength_make. unfold SZ.
      replace (2 * ((n + 1) * (n + 1)) <=? PArray.max_length) with true; [reflexivity|].
      symmetry. rewrite leb_spec, max_length_val. pose proof (SZ_val w n Hn HN200) as ES.
      unfold SZ in ES. rewrite ES.
      assert (Z.of_nat (List.length w) + 1 <= 201)%Z by lia. nia. }
    assert (Hhm : (φ (n / 2 + 1)) = Z.of_nat (List.length w / 2 + 1)).
    { rewrite add_small; rewrite div_spec, Hn; change (φ 2) with 2%Z; change (φ 1) with 1%Z.
      - rewrite Nat2Z.inj_add, Nat2Z.inj_div. reflexivity.
      - rewrite wB_val. zify; Z.to_euclidean_division_equations; lia. }
    pose proof (outer_spec x w n Hn HN200 Hch (n / 2 + 1) Hhm _ 0%nat 0
                  (PArray.make (2 * ((n + 1) * (n + 1))) 0) (Zwf_well_founded 0 _)
                  eq_refl eq_refl ltac:(lia) HSZ ltac:(intros a b _ _ Hlt; lia)) as D.
    destruct (D 0%nat (List.length w) ltac:(lia) ltac:(rewrite Nat.sub_0_r; exact HNev)
                ltac:(lia)) as [G1 G2].
    unfold ix in G1, G2.
    replace (of_Z (Z.of_nat 0)) with 0 in G1, G2 by reflexivity.
    replace (of_Z (Z.of_nat (List.length w))) with n in G1, G2
      by (apply int_of; exact Hn).
    assert (Hsub : sub w 0 (List.length w) = w).
    { unfold sub. rewrite Nat.sub_0_r, skipn_0. apply firstn_all. }
    rewrite Hsub, Hcnt in G1, G2.
    split; simpl.
    + unfold repr, repr_uint. rewrite G1. clear. lia.
    + unfold repr, repr_bool. apply Bool.eq_iff_eq_true. rewrite leb_spec, N.leb_le.
      change (φ MOD) with 100000%Z. rewrite G2. clear. lia.
  - unfold zapis_spec. exists l. split; [|split; [|split; reflexivity]].
    + apply NoDup_map_inj.
      * intros u v _ _ E'. rewrite <- (list_ascii_of_string_of_list_ascii u),
          <- (list_ascii_of_string_of_list_ascii v), E'. reflexivity.
      * apply (enF_spec (S (List.length w)) w ltac:(lia)).
    + intros t. unfold l. rewrite in_map_iff.
      destruct (enF_spec (S (List.length w)) w ltac:(lia)) as [_ Hs]. split.
      * intros [u [<- Hu]]. apply Hs in Hu as [F R]. split.
        -- apply completion_iff. rewrite list_ascii_of_string_of_list_ascii. exact F.
        -- apply regL_regular. exact R.
      * intros [Hc Hreg]. exists (list_ascii_of_string t). split.
        -- apply string_of_list_ascii_of_string.
        -- apply Hs. split; [apply completion_iff; exact Hc|apply regular_iff; exact Hreg].
Qed.

(* ================================================================== *)
(* The spec's items, at top level                                      *)
(* ================================================================== *)

Definition zapis : PrimString.string -> uint * bool := zapis_impl.

Definition zapis_correct : forall (s : string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists o : N * bool, repr (zapis x) o /\ zapis_spec s o
  := zapis_impl_correct.
