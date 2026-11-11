(* Implementation of gcpc (gcpc.spec): an order-statistic AVL tree.

   Code.  Every team k (1 <= k <= n) has a key, one 63-bit word that
   encodes its score and its number,
       key = (C - solved) * 2^44 + penalty * 2^17 + k,     C = 2^17 - 1,
   so that the keys are pairwise distinct and a smaller key is a better
   score (more solved problems, or as many and a smaller penalty; the team
   number only breaks ties).  The current key of every team lives in one
   flat array [keys] indexed by team; all n keys live in an AVL tree
   (an inductive, updated functionally, every node carrying its subtree
   size and height; the balancing function is the one of OCaml's Set).
   An event (a, q) deletes team a's old key from the tree, inserts the new
   one, old - 2^44 + q * 2^17, and the rank of team 1 is one plus the
   number of keys below key(1) - 1 (the keys whose score is better),
   counted with the subtree sizes along one root-to-leaf path.
   The bounds of the contract (solved <= 10^5 < 2^17, penalty <=
   10^8 < 2^27, k <= 10^5 < 2^17) keep the key below 2^62.

   Termination: the two loops (initialisation over the teams, the events)
   recurse structurally on an erased [Acc (Zwf 0) (gap m i)] proof as in
   template/polymul1; the tree functions recurse structurally on the
   tree.  No nat, no Z, no list in the code.

   Proof.  The tree is read through its in-order list [elements]: [ok]
   says the size fields are right, [sorted] that the list is strictly
   increasing.  The balancing function does not change the in-order list,
   so insert / delete are the list functions [ins_list] / [del_list] and
   their effect on the multiset of keys is a [Permutation].  The loop
   invariant says that the keys of the tree are, up to permutation, the
   keys of the teams 1..n after the first j events, and the rank query
   then counts, through the encoding, the teams with a better score. *)

From Gcpc.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation.
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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma ltb_true : forall x y : int, (x <? y) = true <-> ((φ x) < (φ y))%Z.
Proof. intros. apply ltb_spec. Qed.

Lemma ltb_false : forall x y : int, (x <? y) = false <-> ((φ y) <= (φ x))%Z.
Proof.
  intros. rewrite <- Bool.not_true_iff_false, ltb_spec. lia.
Qed.

Lemma eqb_true : forall x y : int, (x =? y) = true <-> x = y.
Proof. intros. apply eqb_spec. Qed.

Lemma phi_inj : forall x y : int, (φ x) = (φ y) -> x = y.
Proof. intros. apply to_Z_inj. assumption. Qed.

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

(* ------------------------------------------------------------------ *)
(* The AVL tree with subtree sizes                                     *)
(* ------------------------------------------------------------------ *)

(* Node l k r size height *)
Inductive tree : Set :=
| Leaf : tree
| Node : tree -> int -> tree -> int -> int -> tree.

Definition height (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ _ h => h end.

Definition size (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ s _ => s end.

Definition mk (l : tree) (k : int) (r : tree) : tree :=
  Node l k r (size l + size r + 1)
    (if height l <? height r then height r + 1 else height l + 1).

(* The rebalancing of OCaml's Set.bal: l and r differ in height by at most
   3 on entry. *)
Definition bal (l : tree) (k : int) (r : tree) : tree :=
  let hl := height l in
  let hr := height r in
  if hr + 2 <? hl then
    match l with
    | Leaf => mk l k r
    | Node ll lk lr _ _ =>
        if height lr <=? height ll then mk ll lk (mk lr k r)
        else match lr with
             | Leaf => mk l k r
             | Node lrl lrk lrr _ _ => mk (mk ll lk lrl) lrk (mk lrr k r)
             end
    end
  else if hl + 2 <? hr then
    match r with
    | Leaf => mk l k r
    | Node rl rk rr _ _ =>
        if height rl <=? height rr then mk (mk l k rl) rk rr
        else match rl with
             | Leaf => mk l k r
             | Node rll rlk rlr _ _ => mk (mk l k rll) rlk (mk rlr rk rr)
             end
    end
  else mk l k r.

Fixpoint insert (x : int) (t : tree) : tree :=
  match t with
  | Leaf => mk Leaf x Leaf
  | Node l k r _ _ =>
      if x <? k then bal (insert x l) k r
      else if k <? x then bal l k (insert x r)
      else t
  end.

(* The minimum of Node l k r, and the tree without it. *)
Fixpoint remove_min (l : tree) (k : int) (r : tree) : int * tree :=
  match l with
  | Leaf => (k, r)
  | Node ll lk lr _ _ =>
      let (m, l') := remove_min ll lk lr in (m, bal l' k r)
  end.

Definition merge (l r : tree) : tree :=
  match l, r with
  | Leaf, _ => r
  | _, Leaf => l
  | _, Node rl rk rr _ _ => let (m, r') := remove_min rl rk rr in bal l m r'
  end.

Fixpoint delete (x : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l k r _ _ =>
      if x <? k then bal (delete x l) k r
      else if k <? x then bal l k (delete x r)
      else merge l r
  end.

(* The number of keys below q (OS-RANK). *)
Fixpoint count_lt (q : int) (t : tree) : int :=
  match t with
  | Leaf => 0
  | Node l k r _ _ =>
      if k <? q then size l + 1 + count_lt q r else count_lt q l
  end.

(* ------------------------------------------------------------------ *)
(* The tree through its in-order list                                  *)
(* ------------------------------------------------------------------ *)

Fixpoint elements (t : tree) : list int :=
  match t with
  | Leaf => []
  | Node l k r _ _ => elements l ++ k :: elements r
  end.

Fixpoint ok (t : tree) : Prop :=
  match t with
  | Leaf => True
  | Node l k r s _ =>
      ok l /\ ok r /\
      (φ s) = Z.of_nat (List.length (elements l) + List.length (elements r) + 1)
  end.

Definition nel (t : tree) : Z := Z.of_nat (List.length (elements t)).

Lemma nel_node : forall l k r s h,
  nel (Node l k r s h) = (nel l + nel r + 1)%Z.
Proof. intros. unfold nel. simpl. rewrite length_app. simpl. lia. Qed.

Lemma nel_nonneg : forall t, (0 <= nel t)%Z.
Proof. intros. unfold nel. lia. Qed.

Lemma size_ok : forall t, ok t -> (φ (size t)) = nel t.
Proof.
  intros [| l k r s h] H; [reflexivity|].
  simpl in H. destruct H as (_ & _ & Hs). simpl. rewrite Hs.
  unfold nel. simpl. rewrite length_app. simpl. lia.
Qed.

Lemma ok_bound : forall t, ok t -> (nel t < wB)%Z.
Proof.
  intros t H. rewrite <- size_ok by exact H. apply to_Z_bounded.
Qed.

Lemma ok_mk : forall l k r, ok l -> ok r -> (nel l + nel r + 1 < wB)%Z ->
  ok (mk l k r).
Proof.
  intros l k r Hl Hr Hb. simpl. split; [exact Hl|]. split; [exact Hr|].
  pose proof (size_ok l Hl). pose proof (size_ok r Hr).
  pose proof (nel_nonneg l). pose proof (nel_nonneg r).
  unfold nel in *.
  rewrite add_spec, add_spec, H, H0. change (φ 1) with 1%Z.
  rewrite (Z.mod_small (_ + _)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma elements_mk : forall l k r,
  elements (mk l k r) = elements l ++ k :: elements r.
Proof. reflexivity. Qed.

Lemma ok_node : forall l k r s h, ok (Node l k r s h) -> ok l /\ ok r.
Proof. intros l k r s h (H1 & H2 & _). split; assumption. Qed.

Ltac nel_simpl := repeat rewrite ?nel_node in *.

Lemma bal_spec : forall l k r, ok l -> ok r -> (nel l + nel r + 1 < wB)%Z ->
  ok (bal l k r) /\ elements (bal l k r) = elements l ++ k :: elements r.
Proof.
  intros l k r Hl Hr Hb.
  pose proof (nel_nonneg l). pose proof (nel_nonneg r).
  unfold bal.
  destruct (height r + 2 <? height l).
  - destruct l as [| ll lk lr ls lh].
    + split; [apply ok_mk; auto | reflexivity].
    + destruct (ok_node _ _ _ _ _ Hl) as [Hll Hlr].
      rewrite nel_node in *.
      pose proof (nel_nonneg ll). pose proof (nel_nonneg lr).
      destruct (height lr <=? height ll).
      * split.
        -- apply ok_mk; auto; [apply ok_mk; auto; lia|]. unfold mk; rewrite nel_node. lia.
        -- simpl. rewrite <- app_assoc. reflexivity.
      * destruct lr as [| lrl lrk lrr lrs lrh].
        -- split; [apply ok_mk; auto; rewrite ?nel_node; lia | reflexivity].
        -- destruct (ok_node _ _ _ _ _ Hlr) as [Hlrl Hlrr].
           rewrite nel_node in *.
           pose proof (nel_nonneg lrl). pose proof (nel_nonneg lrr).
           split.
           ++ apply ok_mk; [apply ok_mk; auto; lia | apply ok_mk; auto; lia |].
              unfold mk; rewrite !nel_node. lia.
           ++ simpl. rewrite <- ?app_assoc. simpl. rewrite <- ?app_assoc.
              reflexivity.
  - destruct (height l + 2 <? height r).
    + destruct r as [| rl rk rr rs rh].
      * split; [apply ok_mk; auto | reflexivity].
      * destruct (ok_node _ _ _ _ _ Hr) as [Hrl Hrr].
        rewrite nel_node in *.
        pose proof (nel_nonneg rl). pose proof (nel_nonneg rr).
        destruct (height rl <=? height rr).
        -- split.
           ++ apply ok_mk; auto; [apply ok_mk; auto; lia|]. unfold mk; rewrite nel_node. lia.
           ++ simpl. rewrite <- app_assoc. reflexivity.
        -- destruct rl as [| rll rlk rlr rls rlh].
           ++ split; [apply ok_mk; auto; rewrite ?nel_node; lia | reflexivity].
           ++ destruct (ok_node _ _ _ _ _ Hrl) as [Hrll Hrlr].
              rewrite nel_node in *.
              pose proof (nel_nonneg rll). pose proof (nel_nonneg rlr).
              split.
              ** apply ok_mk; [apply ok_mk; auto; lia | apply ok_mk; auto; lia |].
                 unfold mk; rewrite !nel_node. lia.
              ** simpl. rewrite <- ?app_assoc. simpl. rewrite <- ?app_assoc.
                 reflexivity.
    + split; [apply ok_mk; auto | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Sorted lists, insertion and deletion on lists                       *)
(* ------------------------------------------------------------------ *)

Fixpoint sorted (l : list int) : Prop :=
  match l with
  | [] => True
  | x :: l' => (forall y, In y l' -> ((φ x) < (φ y))%Z) /\ sorted l'
  end.

Lemma sorted_app : forall l1 l2, sorted (l1 ++ l2) ->
  sorted l1 /\ sorted l2 /\
  (forall x y, In x l1 -> In y l2 -> ((φ x) < (φ y))%Z).
Proof.
  induction l1 as [| a l1 IH]; intros l2 H; simpl in *.
  - split; [exact I|]. split; [exact H|]. intros x y [].
  - destruct H as [Ha H]. destruct (IH l2 H) as (H1 & H2 & H3).
    split; [split; [intros y Hy; apply Ha; apply in_or_app; left; exact Hy | exact H1]|].
    split; [exact H2|].
    intros x y [<- | Hx] Hy.
    + apply Ha. apply in_or_app. right. exact Hy.
    + apply H3; assumption.
Qed.

Lemma sorted_node : forall l k r, sorted (l ++ k :: r) ->
  sorted l /\ sorted r /\ (forall y, In y l -> ((φ y) < (φ k))%Z) /\
  (forall y, In y r -> ((φ k) < (φ y))%Z).
Proof.
  intros l k r H. destruct (sorted_app l (k :: r) H) as (H1 & [H2 H4] & H3).
  split; [exact H1|]. split; [exact H4|]. split; [|exact H2].
  intros y Hy. apply H3; [exact Hy | left; reflexivity].
Qed.

Fixpoint ins_list (x : int) (l : list int) : list int :=
  match l with
  | [] => [x]
  | y :: l' => if x <? y then x :: l else if x =? y then l else y :: ins_list x l'
  end.

Fixpoint del_list (x : int) (l : list int) : list int :=
  match l with
  | [] => []
  | y :: l' => if x <? y then l else if x =? y then l' else y :: del_list x l'
  end.

Lemma ins_app_lt : forall x k l1 l2, ((φ x) < (φ k))%Z ->
  ins_list x (l1 ++ k :: l2) = ins_list x l1 ++ k :: l2.
Proof.
  intros x k l1 l2 Hk. induction l1 as [| y l1 IH]; simpl.
  - replace (x <? k) with true by (symmetry; apply ltb_true; exact Hk). reflexivity.
  - destruct (x <? y); [reflexivity|]. destruct (x =? y); [reflexivity|].
    rewrite IH. reflexivity.
Qed.

Lemma ins_app_gt : forall x l1 l2, (forall y, In y l1 -> ((φ y) < (φ x))%Z) ->
  ins_list x (l1 ++ l2) = l1 ++ ins_list x l2.
Proof.
  intros x l1 l2 H. induction l1 as [| y l1 IH]; simpl; [reflexivity|].
  assert (Hy : ((φ y) < (φ x))%Z) by (apply H; left; reflexivity).
  replace (x <? y) with false by (symmetry; apply ltb_false; lia).
  replace (x =? y) with false
    by (symmetry; apply Bool.not_true_iff_false; rewrite eqb_true; intros ->; lia).
  rewrite IH by (intros z Hz; apply H; right; exact Hz). reflexivity.
Qed.

Lemma ins_same : forall k l, ins_list k (k :: l) = k :: l.
Proof.
  intros k l. simpl.
  replace (k <? k) with false by (symmetry; apply ltb_false; lia).
  replace (k =? k) with true by (symmetry; apply eqb_true; reflexivity).
  reflexivity.
Qed.

Lemma del_app_lt : forall x k l1 l2, ((φ x) < (φ k))%Z ->
  del_list x (l1 ++ k :: l2) = del_list x l1 ++ k :: l2.
Proof.
  intros x k l1 l2 Hk. induction l1 as [| y l1 IH]; simpl.
  - replace (x <? k) with true by (symmetry; apply ltb_true; exact Hk). reflexivity.
  - destruct (x <? y); [reflexivity|]. destruct (x =? y); [reflexivity|].
    rewrite IH. reflexivity.
Qed.

Lemma del_app_gt : forall x l1 l2, (forall y, In y l1 -> ((φ y) < (φ x))%Z) ->
  del_list x (l1 ++ l2) = l1 ++ del_list x l2.
Proof.
  intros x l1 l2 H. induction l1 as [| y l1 IH]; simpl; [reflexivity|].
  assert (Hy : ((φ y) < (φ x))%Z) by (apply H; left; reflexivity).
  replace (x <? y) with false by (symmetry; apply ltb_false; lia).
  replace (x =? y) with false
    by (symmetry; apply Bool.not_true_iff_false; rewrite eqb_true; intros ->; lia).
  rewrite IH by (intros z Hz; apply H; right; exact Hz). reflexivity.
Qed.

Lemma del_same : forall k l, del_list k (k :: l) = l.
Proof.
  intros k l. simpl.
  replace (k <? k) with false by (symmetry; apply ltb_false; lia).
  replace (k =? k) with true by (symmetry; apply eqb_true; reflexivity).
  reflexivity.
Qed.

Lemma ins_length : forall x l,
  (List.length (ins_list x l) <= S (List.length l))%nat.
Proof.
  intros x l. induction l as [| y l IH]; simpl; [lia|].
  destruct (x <? y); simpl; [lia|]. destruct (x =? y); simpl; lia.
Qed.

Lemma del_length : forall x l,
  (List.length (del_list x l) <= List.length l)%nat.
Proof.
  intros x l. induction l as [| y l IH]; simpl; [lia|].
  destruct (x <? y); simpl; [lia|]. destruct (x =? y); simpl; lia.
Qed.

Lemma in_ins : forall x l z, In z (ins_list x l) -> z = x \/ In z l.
Proof.
  intros x l z. induction l as [| y l IH]; simpl.
  - intros [-> | []]. left; reflexivity.
  - destruct (x <? y).
    + intros [-> | H]; [left; reflexivity | right; exact H].
    + destruct (x =? y); [intros H; right; exact H|].
      intros [-> | H]; [right; left; reflexivity|].
      destruct (IH H) as [-> | H']; [left; reflexivity | right; right; exact H'].
Qed.

Lemma in_del : forall x l z, In z (del_list x l) -> In z l.
Proof.
  intros x l z. induction l as [| y l IH]; simpl; [tauto|].
  destruct (x <? y); [tauto|]. destruct (x =? y); [tauto|].
  intros [-> | H]; [left; reflexivity | right; apply IH; exact H].
Qed.

Lemma ins_sorted : forall x l, sorted l -> sorted (ins_list x l).
Proof.
  intros x l. induction l as [| y l IH]; simpl; intros Hs.
  - split; [intros z []| exact I].
  - destruct Hs as [Hy Hs].
    destruct (x <? y) eqn:E1.
    + rewrite ltb_true in E1. simpl. split; [|split; assumption].
      intros z [<- | Hz]; [exact E1|]. specialize (Hy z Hz). lia.
    + destruct (x =? y) eqn:E2; [simpl; split; assumption|].
      rewrite ltb_false in E1.
      assert (Hne : (φ y) <> (φ x))
        by (intro F; apply phi_inj in F; subst y;
            rewrite (proj2 (eqb_true x x) eq_refl) in E2; discriminate).
      simpl. split; [| apply IH; exact Hs].
      intros z Hz. destruct (in_ins x l z Hz) as [-> | Hz']; [lia | apply Hy; exact Hz'].
Qed.

Lemma del_sorted : forall x l, sorted l -> sorted (del_list x l).
Proof.
  intros x l. induction l as [| y l IH]; simpl; intros Hs; [exact I|].
  destruct Hs as [Hy Hs].
  destruct (x <? y); [simpl; split; assumption|].
  destruct (x =? y); [exact Hs|].
  simpl. split; [| apply IH; exact Hs].
  intros z Hz. apply Hy. apply (in_del x). exact Hz.
Qed.

Lemma ins_perm : forall x l, ~ In x l -> Permutation (ins_list x l) (x :: l).
Proof.
  intros x l. induction l as [| y l IH]; simpl; intros Hn; [reflexivity|].
  destruct (x <? y); [reflexivity|].
  destruct (x =? y) eqn:E.
  - rewrite eqb_true in E. subst y. exfalso. apply Hn. left. reflexivity.
  - eapply perm_trans; [apply perm_skip; apply IH; tauto|]. apply perm_swap.
Qed.

Lemma del_perm : forall x l, sorted l -> In x l ->
  Permutation (x :: del_list x l) l.
Proof.
  intros x l. induction l as [| y l IH]; simpl; intros Hs Hin; [destruct Hin|].
  destruct Hs as [Hy Hs].
  destruct (x <? y) eqn:E1.
  - rewrite ltb_true in E1. exfalso.
    destruct Hin as [-> | Hin]; [lia|]. specialize (Hy x Hin). lia.
  - destruct (x =? y) eqn:E2.
    + rewrite eqb_true in E2. subst y. reflexivity.
    + assert (Hin' : In x l).
      { destruct Hin as [-> | Hin]; [|exact Hin].
        rewrite (proj2 (eqb_true x x) eq_refl) in E2. discriminate. }
      eapply perm_trans; [apply perm_swap|]. apply perm_skip. apply IH; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The tree operations, on the in-order list                           *)
(* ------------------------------------------------------------------ *)

Lemma insert_spec : forall x t, ok t -> sorted (elements t) -> (nel t + 1 < wB)%Z ->
  ok (insert x t) /\ elements (insert x t) = ins_list x (elements t).
Proof.
  intros x t. induction t as [| l IHl k r IHr s h]; intros Hok Hs Hb.
  - split; [apply ok_mk; [exact I | exact I | unfold nel; simpl; rewrite wB_val; lia] | reflexivity].
  - destruct (ok_node _ _ _ _ _ Hok) as [Hl Hr].
    simpl in Hs. destruct (sorted_node _ _ _ Hs) as (Hsl & Hsr & Hlk & Hkr).
    rewrite nel_node in Hb.
    pose proof (nel_nonneg l). pose proof (nel_nonneg r).
    simpl insert. destruct (x <? k) eqn:E1.
    + rewrite ltb_true in E1.
      destruct (IHl Hl Hsl ltac:(lia)) as [Hok' He'].
      assert (Hn : (nel (insert x l) <= nel l + 1)%Z).
      { unfold nel. rewrite He'. pose proof (ins_length x (elements l)). lia. }
      destruct (bal_spec (insert x l) k r Hok' Hr ltac:(lia)) as [Hb1 Hb2].
      split; [exact Hb1|]. rewrite Hb2, He'. simpl. rewrite ins_app_lt by exact E1.
      reflexivity.
    + destruct (k <? x) eqn:E2.
      * rewrite ltb_true in E2.
        destruct (IHr Hr Hsr ltac:(lia)) as [Hok' He'].
        assert (Hn : (nel (insert x r) <= nel r + 1)%Z).
        { unfold nel. rewrite He'. pose proof (ins_length x (elements r)). lia. }
        destruct (bal_spec l k (insert x r) Hl Hok' ltac:(lia)) as [Hb1 Hb2].
        split; [exact Hb1|]. rewrite Hb2, He'. simpl.
        replace (elements l ++ k :: elements r) with ((elements l ++ [k]) ++ elements r)
          by (rewrite <- app_assoc; reflexivity).
        rewrite ins_app_gt.
        -- rewrite <- app_assoc. reflexivity.
        -- intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy | [<- | []]];
             [specialize (Hlk y Hy); lia | exact E2].
      * rewrite ltb_false in E1, E2.
        assert (x = k) by (apply phi_inj; lia). subst x.
        split; [exact Hok|]. simpl.
        rewrite ins_app_gt by exact Hlk. rewrite ins_same. reflexivity.
Qed.

Lemma remove_min_spec : forall l k r, ok l -> ok r -> (nel l + nel r + 1 < wB)%Z ->
  ok (snd (remove_min l k r)) /\
  fst (remove_min l k r) :: elements (snd (remove_min l k r))
  = elements l ++ k :: elements r.
Proof.
  intros l. induction l as [| ll IH lk lr _ ls lh]; intros k r Hl Hr Hb.
  - simpl. split; [exact Hr | reflexivity].
  - destruct (ok_node _ _ _ _ _ Hl) as [Hll Hlr].
    rewrite nel_node in Hb.
    pose proof (nel_nonneg ll). pose proof (nel_nonneg lr). pose proof (nel_nonneg r).
    destruct (IH lk lr Hll Hlr ltac:(lia)) as [Hok He].
    simpl. destruct (remove_min ll lk lr) as [m l'] eqn:Er. simpl in Hok, He |- *.
    assert (Hn : (nel l' + 1 = nel ll + nel lr + 1)%Z).
    { unfold nel. pose proof (f_equal (@List.length int) He) as HL.
      simpl in HL. rewrite length_app in HL. simpl in HL. lia. }
    destruct (bal_spec l' k r Hok Hr ltac:(lia)) as [Hb1 Hb2].
    split; [exact Hb1|]. rewrite Hb2.
    change (m :: elements l' ++ k :: elements r) with ((m :: elements l') ++ k :: elements r).
    rewrite He. rewrite <- app_assoc. reflexivity.
Qed.

Lemma merge_spec : forall l r, ok l -> ok r -> (nel l + nel r < wB)%Z ->
  ok (merge l r) /\ elements (merge l r) = elements l ++ elements r.
Proof.
  intros l r Hl Hr Hb.
  destruct l as [| ll lk lr ls lh]; [split; [exact Hr | reflexivity]|].
  destruct r as [| rl rk rr rs rh]; [split; [exact Hl | simpl; rewrite app_nil_r; reflexivity]|].
  destruct (ok_node _ _ _ _ _ Hr) as [Hrl Hrr].
  rewrite (nel_node rl) in Hb.
  pose proof (nel_nonneg rl). pose proof (nel_nonneg rr). pose proof (nel_nonneg (Node ll lk lr ls lh)).
  destruct (remove_min_spec rl rk rr Hrl Hrr ltac:(lia)) as [Hok He].
  unfold merge. destruct (remove_min rl rk rr) as [m r'] eqn:Er. simpl in Hok, He.
  assert (Hn : (nel r' + 1 = nel rl + nel rr + 1)%Z).
  { unfold nel. pose proof (f_equal (@List.length int) He) as HL.
      simpl in HL. rewrite length_app in HL. simpl in HL. lia. }
  destruct (bal_spec (Node ll lk lr ls lh) m r' Hl Hok ltac:(lia)) as [Hb1 Hb2].
  split; [exact Hb1|]. rewrite Hb2, He. reflexivity.
Qed.

Lemma delete_spec : forall x t, ok t -> sorted (elements t) ->
  ok (delete x t) /\ elements (delete x t) = del_list x (elements t).
Proof.
  intros x t. induction t as [| l IHl k r IHr s h]; intros Hok Hs.
  - simpl. split; [exact I | reflexivity].
  - destruct (ok_node _ _ _ _ _ Hok) as [Hl Hr].
    pose proof (ok_bound _ Hok) as Hb. rewrite nel_node in Hb.
    simpl in Hs. destruct (sorted_node _ _ _ Hs) as (Hsl & Hsr & Hlk & Hkr).
    pose proof (nel_nonneg l). pose proof (nel_nonneg r).
    simpl delete. destruct (x <? k) eqn:E1.
    + rewrite ltb_true in E1.
      destruct (IHl Hl Hsl) as [Hok' He'].
      assert (Hn : (nel (delete x l) <= nel l)%Z).
      { unfold nel. rewrite He'. pose proof (del_length x (elements l)). lia. }
      pose proof (nel_nonneg (delete x l)).
      destruct (bal_spec (delete x l) k r Hok' Hr ltac:(lia)) as [Hb1 Hb2].
      split; [exact Hb1|]. rewrite Hb2, He'. simpl. rewrite del_app_lt by exact E1.
      reflexivity.
    + destruct (k <? x) eqn:E2.
      * rewrite ltb_true in E2.
        destruct (IHr Hr Hsr) as [Hok' He'].
        assert (Hn : (nel (delete x r) <= nel r)%Z).
        { unfold nel. rewrite He'. pose proof (del_length x (elements r)). lia. }
        pose proof (nel_nonneg (delete x r)).
        destruct (bal_spec l k (delete x r) Hl Hok' ltac:(lia)) as [Hb1 Hb2].
        split; [exact Hb1|]. rewrite Hb2, He'. simpl.
        replace (elements l ++ k :: elements r) with ((elements l ++ [k]) ++ elements r)
          by (rewrite <- app_assoc; reflexivity).
        rewrite del_app_gt.
        -- rewrite <- app_assoc. reflexivity.
        -- intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy | [<- | []]];
             [specialize (Hlk y Hy); lia | exact E2].
      * rewrite ltb_false in E1, E2.
        assert (x = k) by (apply phi_inj; lia). subst x.
        destruct (merge_spec l r Hl Hr ltac:(lia)) as [Hm1 Hm2].
        split; [exact Hm1|]. rewrite Hm2. simpl.
        rewrite del_app_gt by exact Hlk. rewrite del_same. reflexivity.
Qed.

Lemma filter_all : forall (f : int -> bool) l, (forall y, In y l -> f y = true) ->
  filter f l = l.
Proof.
  intros f l H. induction l as [| y l IH]; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros z Hz; apply H; right; exact Hz).
  reflexivity.
Qed.

Lemma filter_none : forall (f : int -> bool) l, (forall y, In y l -> f y = false) ->
  filter f l = [].
Proof.
  intros f l H. induction l as [| y l IH]; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). apply IH. intros z Hz; apply H; right; exact Hz.
Qed.

Lemma count_lt_spec : forall q t, ok t -> sorted (elements t) ->
  (φ (count_lt q t)) = Z.of_nat (List.length (filter (fun y => y <? q) (elements t))).
Proof.
  intros q t. induction t as [| l IHl k r IHr s h]; intros Hok Hs; [reflexivity|].
  destruct (ok_node _ _ _ _ _ Hok) as [Hl Hr].
  pose proof (ok_bound _ Hok) as Hb. rewrite nel_node in Hb.
  simpl in Hs. destruct (sorted_node _ _ _ Hs) as (Hsl & Hsr & Hlk & Hkr).
  simpl count_lt. simpl elements. rewrite filter_app. simpl filter.
  destruct (k <? q) eqn:E.
  - rewrite ltb_true in E.
    rewrite (filter_all _ (elements l))
      by (intros y Hy; apply ltb_true; specialize (Hlk y Hy); lia).
    pose proof (IHr Hr Hsr) as Hc. pose proof (size_ok l Hl) as Hsz.
    assert (Hcr : (Z.of_nat (List.length (filter (fun y => (y <? q)%uint63) (elements r))) <= nel r)%Z).
    { unfold nel. pose proof (filter_length_le (fun y => (y <? q)%uint63) (elements r)). lia. }
    rewrite length_app. simpl length.
    pose proof (nel_nonneg l). unfold nel in *.
    rewrite add_spec, add_spec, Hsz, Hc. change (φ 1) with 1%Z.
    rewrite (Z.mod_small (_ + 1)) by lia. rewrite Z.mod_small by lia.
    cbn [List.length]. lia.
  - rewrite ltb_false in E.
    rewrite (filter_none _ (elements r))
      by (intros y Hy; apply ltb_false; specialize (Hkr y Hy); lia).
    rewrite app_nil_r. apply IHl; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition KD : int := 17592186044416.        (* 2^44 *)
Definition KE : int := 131072.                (* 2^17 *)
Definition K0 : int := 2305825417027649536.   (* (2^17 - 1) * 2^44 *)

(* Teams k .. n1 - 1 receive their initial key K0 + k (score (0, 0)),
   in [keys] and in the tree. *)
Fixpoint init_loop (n1 k : int) (keys : array int) (T : tree)
    (H : Acc (Zwf 0) (gap n1 k)) {struct H} : array int * tree :=
  match bdec (k <? n1) with
  | left Hk =>
      let key := K0 + k in
      init_loop n1 (k + 1) keys.[k <- key] (insert key T)
        (Acc_inv H (dec_step n1 k Hk))
  | right _ => (keys, T)
  end.

Lemma init_loop_eq : forall n1 k keys T H,
  init_loop n1 k keys T H =
  match bdec (k <? n1) with
  | left Hk =>
      let key := K0 + k in
      init_loop n1 (k + 1) keys.[k <- key] (insert key T)
        (Acc_inv H (dec_step n1 k Hk))
  | right _ => (keys, T)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Events j .. m - 1: team a = xt.[j] solves a problem with penalty
   xp.[j]; out.[j] receives the rank of team 1 after it. *)
Fixpoint ev_loop (xt xp : array int) (m j : int) (keys : array int) (T : tree)
    (out : array int) (H : Acc (Zwf 0) (gap m j)) {struct H} : array int :=
  match bdec (j <? m) with
  | left Hj =>
      let a := xt.[j] in
      let old := keys.[a] in
      let new := old - KD + xp.[j] * KE in
      let keys' := keys.[a <- new] in
      let T' := insert new (delete old T) in
      let ans := count_lt (keys'.[1] - 1) T' + 1 in
      ev_loop xt xp m (j + 1) keys' T' out.[j <- ans]
        (Acc_inv H (dec_step m j Hj))
  | right _ => out
  end.

Lemma ev_loop_eq : forall xt xp m j keys T out H,
  ev_loop xt xp m j keys T out H =
  match bdec (j <? m) with
  | left Hj =>
      let a := xt.[j] in
      let old := keys.[a] in
      let new := old - KD + xp.[j] * KE in
      let keys' := keys.[a <- new] in
      let T' := insert new (delete old T) in
      let ans := count_lt (keys'.[1] - 1) T' + 1 in
      ev_loop xt xp m (j + 1) keys' T' out.[j <- ans]
        (Acc_inv H (dec_step m j Hj))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition gcpc_impl (n : uint) (xt xp : array uint) : array uint :=
  let m := PArray.length xt in
  let n1 := n + 1 in
  let (keys, T) :=
    init_loop n1 1 (PArray.make n1 0) Leaf (Zwf_well_founded 0 (gap n1 1)) in
  ev_loop xt xp m 0 keys T (PArray.make m 0) (Zwf_well_founded 0 (gap m 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: the encoding of a score                                  *)
(* ------------------------------------------------------------------ *)

Definition enc (s pe a : Z) : Z := ((131071 - s) * 17592186044416 + pe * 131072 + a)%Z.

Lemma enc_better : forall (s pe s1 pe1 a : N),
  (s <= 100000)%N -> (pe <= 100000000)%N -> (s1 <= 100000)%N -> (pe1 <= 100000000)%N ->
  (1 <= a <= 100000)%N ->
  (enc (Z.of_N s) (Z.of_N pe) (Z.of_N a) <? enc (Z.of_N s1) (Z.of_N pe1) 1 - 1)%Z
  = better (s, pe) (s1, pe1).
Proof.
  intros s pe s1 pe1 a Hs Hp Hs1 Hp1 Ha.
  set (A := ((131071 - Z.of_N s) * 134217728 + Z.of_N pe)%Z).
  set (A1 := ((131071 - Z.of_N s1) * 134217728 + Z.of_N pe1)%Z).
  assert (E1 : enc (Z.of_N s) (Z.of_N pe) (Z.of_N a) = (A * 131072 + Z.of_N a)%Z)
    by (unfold enc, A; ring).
  assert (E2 : (enc (Z.of_N s1) (Z.of_N pe1) 1 - 1 = A1 * 131072)%Z)
    by (unfold enc, A1; ring).
  rewrite E1, E2.
  assert (Hlex : (A < A1)%Z <-> (s1 < s)%N \/ (s = s1 /\ pe < pe1)%N).
  { unfold A, A1. split; intros H.
    - destruct (N.lt_trichotomy s1 s) as [H1 | [H1 | H1]]; [left; exact H1| |];
        [subst; right; split; [reflexivity | lia] | exfalso; lia].
    - destruct H as [H | [-> H]]; lia. }
  unfold better.
  destruct (Z.ltb_spec (A * 131072 + Z.of_N a) (A1 * 131072)) as [H | H].
  - assert (HA : (A < A1)%Z) by lia. apply Hlex in HA.
    symmetry. apply Bool.orb_true_iff.
    destruct HA as [HA | [-> HA]]; [left; apply N.ltb_lt; exact HA|].
    right. rewrite N.eqb_refl. apply N.ltb_lt. exact HA.
  - assert (HA : ~ (A < A1)%Z) by lia. rewrite Hlex in HA.
    symmetry. apply Bool.orb_false_iff. split.
    + apply N.ltb_ge. lia.
    + apply Bool.andb_false_iff. destruct (N.eqb_spec s s1) as [-> | Hne]; [|left; reflexivity].
      right. apply N.ltb_ge. lia.
Qed.

Lemma enc_team : forall s pe a s' pe' a' : Z,
  (0 <= s <= 100000)%Z -> (0 <= pe <= 100000000)%Z ->
  (0 <= s' <= 100000)%Z -> (0 <= pe' <= 100000000)%Z ->
  (0 <= a < 131072)%Z -> (0 <= a' < 131072)%Z ->
  enc s pe a = enc s' pe' a' -> a = a'.
Proof.
  intros s pe a s' pe' a' Hs Hp Hs' Hp' Ha Ha' H. unfold enc in H.
  assert (Hm : (((131071 - s) * 134217728 + pe - ((131071 - s') * 134217728 + pe')) * 131072
               = a' - a)%Z) by lia.
  set (X := ((131071 - s) * 134217728 + pe - ((131071 - s') * 134217728 + pe'))%Z) in Hm.
  destruct (Z.lt_trichotomy X 0) as [HX | [HX | HX]]; lia.
Qed.

Lemma Z_ltb_int : forall x y : int, (x <? y)%uint63 = ((φ x) <? (φ y))%Z.
Proof.
  intros x y. destruct (x <? y)%uint63 eqn:E.
  - rewrite ltb_true in E. symmetry. apply Z.ltb_lt. exact E.
  - rewrite ltb_false in E. symmetry. apply Z.ltb_ge. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: lists                                                    *)
(* ------------------------------------------------------------------ *)

Lemma firstn_S_app : forall (l : list N) j, (j < List.length l)%nat ->
  firstn (S j) l = firstn j l ++ [nth j l 0%N].
Proof.
  induction l as [| x l IH]; intros [| j] H; simpl in *; try lia; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma combine_app_eq : forall (l1 l2 l1' l2' : list N),
  List.length l1 = List.length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1 as [| x l1 IH]; intros l2 [| y l1'] l2' H; simpl in *; try lia;
    [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma fold_add : forall (x : N) l, fold_right N.add x l = (fold_right N.add 0 l + x)%N.
Proof. intros x l. induction l as [| y l IH]; simpl; lia. Qed.

Lemma perm_filter_length : forall (A : Type) (f : A -> bool) (l l' : list A),
  Permutation l l' -> List.length (filter f l) = List.length (filter f l').
Proof.
  intros A f l l' H. induction H; simpl.
  - reflexivity.
  - destruct (f x); simpl; lia.
  - destruct (f x), (f y); simpl; lia.
  - lia.
Qed.

Lemma filter_length_map : forall (A B : Type) (f : B -> bool) (h : A -> B) l,
  List.length (filter f (map h l)) = List.length (filter (fun x => f (h x)) l).
Proof.
  intros A B f h l. induction l as [| x l IH]; simpl; [reflexivity|].
  destruct (f (h x)); simpl; lia.
Qed.

Lemma NoDup_map_inj : forall (A B : Type) (f : A -> B) l,
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hf Hl. induction Hl as [| x l Hx Hl IH]; simpl; constructor; auto.
  intro Hin. apply in_map_iff in Hin. destruct Hin as (y & Hy & Hin).
  apply Hf in Hy. subst y. contradiction.
Qed.

Lemma in_teams : forall n a, In a (teams n) <-> (1 <= a <= n)%N.
Proof.
  intros n a. unfold teams. rewrite in_map_iff. split.
  - intros (i & <- & Hi). apply in_seq in Hi. lia.
  - intros H. exists (N.to_nat a). split; [lia|]. apply in_seq. lia.
Qed.

Lemma teams_NoDup : forall n, NoDup (teams n).
Proof.
  intros n. unfold teams. apply NoDup_map_inj; [intros; lia|]. apply seq_NoDup.
Qed.

Lemma teams_length : forall n, List.length (teams n) = N.to_nat n.
Proof. intros n. unfold teams. rewrite length_map, length_seq. reflexivity. Qed.

(* Reading an in-bounds cell of an array representing l. *)
Lemma repr_get : forall (x : array uint) (l : list N), repr x l ->
  forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  (φ (PArray.get@{Set} x i)) = Z.of_N (nth (Z.to_nat (φ i)) l 0%N).
Proof.
  intros x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite (nth_error_nth _ _ _ Hv).
  rewrite <- Hr. rewrite Z2N.id by (apply to_Z_bounded). reflexivity.
Qed.

Lemma repr_length : forall (x : array uint) (l : list N), repr x l ->
  (φ (PArray.length@{Set} x)) = Z.of_nat (List.length l).
Proof. intros x l [Hl _]. symmetry. exact Hl. Qed.

(* ------------------------------------------------------------------ *)
(* The initialisation loop                                             *)
(* ------------------------------------------------------------------ *)

Lemma init_loop_spec : forall (nz : Z) (n1 : int),
  (φ n1) = (nz + 1)%Z -> (0 <= nz <= 100000)%Z ->
  forall z (k : int) (keys : array int) (T : tree) (H : Acc (Zwf 0) (gap n1 k)),
  gap n1 k = z -> (1 <= (φ k) <= (φ n1))%Z ->
  (φ (PArray.length keys)) = (φ n1) ->
  (forall i : int, (1 <= (φ i) < (φ k))%Z -> (φ (keys.[i])) = ((φ K0) + (φ i))%Z) ->
  ok T -> sorted (elements T) ->
  Permutation (map to_Z (elements T))
              (map (fun i => (φ K0) + Z.of_nat i)%Z (seq 1 (Z.to_nat (φ k) - 1))) ->
  (φ (PArray.length (fst (init_loop n1 k keys T H)))) = (φ n1) /\
  (forall i : int, (1 <= (φ i) <= nz)%Z ->
     (φ ((fst (init_loop n1 k keys T H)).[i])) = ((φ K0) + (φ i))%Z) /\
  ok (snd (init_loop n1 k keys T H)) /\
  sorted (elements (snd (init_loop n1 k keys T H))) /\
  Permutation (map to_Z (elements (snd (init_loop n1 k keys T H))))
              (map (fun i => (φ K0) + Z.of_nat i)%Z (seq 1 (Z.to_nat nz))).
Proof.
  intros nz n1 Hn1 Hnz z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k keys T H Hz Hk Hkl Hkeys Hok Hs Hperm.
  rewrite init_loop_eq.
  destruct (bdec (k <? n1)) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_true in Hlt'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z)
      by (rewrite add_spec; change (φ 1) with 1%Z; apply Z.mod_small; rewrite wB_val; lia).
    assert (Hkey : (φ (K0 + k)) = ((φ K0) + (φ k))%Z)
      by (rewrite add_spec; apply Z.mod_small;
          change (φ K0) with 2305825417027649536%Z; rewrite wB_val; lia).
    assert (Hnin : ~ In (K0 + k) (elements T)).
    { intros Hi. apply (in_map to_Z) in Hi. apply (Permutation_in _ Hperm) in Hi.
      apply in_map_iff in Hi. destruct Hi as (i & Hi & Hiin). apply in_seq in Hiin. lia. }
    assert (Hb : (nel T + 1 < wB)%Z).
    { unfold nel. pose proof (Permutation_length Hperm) as HL.
      rewrite !length_map, length_seq in HL. rewrite wB_val. lia. }
    destruct (insert_spec (K0 + k) T Hok Hs Hb) as [Hok' He'].
    cbv zeta. eapply IH; [ | reflexivity | lia | | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite alength_set. exact Hkl.
    + intros i Hi. rewrite Hk1 in Hi. destruct (Z.eq_dec (φ i) (φ k)) as [E | E].
      * assert (i = k) by (apply phi_inj; exact E). subst i.
        rewrite aget_set_same by (apply ltb_true; lia). exact Hkey.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hkeys. lia.
    + exact Hok'.
    + rewrite He'. apply ins_sorted. exact Hs.
    + rewrite He'. eapply perm_trans; [apply Permutation_map; apply ins_perm; exact Hnin|].
      cbn [map]. rewrite Hkey.
      replace (Z.to_nat (φ (k + 1)) - 1)%nat with (S (Z.to_nat (φ k) - 1)) by lia.
      rewrite seq_S, map_app. cbn [map].
      replace ((φ K0) + Z.of_nat (1 + (Z.to_nat (φ k) - 1)))%Z with ((φ K0) + (φ k))%Z by lia.
      eapply perm_trans; [apply perm_skip; exact Hperm|]. apply Permutation_cons_append.
  - rewrite ltb_false in Hge. cbn [fst snd].
    split; [exact Hkl|]. split; [intros i Hi; apply Hkeys; lia|].
    split; [exact Hok|]. split; [exact Hs|].
    replace (Z.to_nat nz) with (Z.to_nat (φ k) - 1)%nat by lia. exact Hperm.
Qed.

(* ------------------------------------------------------------------ *)
(* The events                                                          *)
(* ------------------------------------------------------------------ *)

Section Events.

Variables (n : N) (t p : list N).
Hypothesis Hv : valid_input n t p.

Lemma vi_facts : (1 <= n <= 100000)%N /\ ((1 <= List.length t)%nat /\ (N.of_nat (List.length t) <= 100000)%N) /\
  List.length p = List.length t /\
  (forall j, (j < List.length t)%nat ->
     (1 <= nth j t 0 <= n)%N /\ (1 <= nth j p 0 <= 1000)%N).
Proof.
  destruct Hv as [Hn Hm Hpl Ht Hp]. unfold len in *.
  change (10 ^ 5)%N with 100000%N in *.
  split; [exact Hn|]. split; [lia|]. split; [lia|].
  intros j Hj. rewrite Forall_forall in Ht, Hp. split.
  - apply Ht. apply nth_In. exact Hj.
  - apply Hp. apply nth_In. lia.
Qed.

Lemma solved_step : forall j a, (j < List.length t)%nat ->
  solved a (firstn (S j) t)
  = (solved a (firstn j t) + if (nth j t 0 =? a)%N then 1 else 0)%N.
Proof.
  intros j a Hj. unfold solved, len. rewrite firstn_S_app by exact Hj.
  rewrite filter_app, length_app. simpl. destruct (nth j t 0 =? a)%N; simpl; lia.
Qed.

Lemma penalty_step : forall j a, (j < List.length t)%nat ->
  penalty a (firstn (S j) t) (firstn (S j) p)
  = (penalty a (firstn j t) (firstn j p) + if (nth j t 0 =? a)%N then nth j p 0 else 0)%N.
Proof.
  intros j a Hj. destruct vi_facts as (_ & _ & Hpl & _).
  unfold penalty. rewrite (firstn_S_app t j), (firstn_S_app p j) by lia.
  rewrite combine_app_eq by (rewrite !length_firstn; lia).
  rewrite map_app, fold_right_app. cbn [combine map fold_right].
  rewrite (fold_add (_ + 0)%N). lia.
Qed.

Lemma solved_bound : forall j a, (j <= List.length t)%nat ->
  (solved a (firstn j t) <= N.of_nat j)%N.
Proof.
  induction j as [| j IH]; intros a Hj.
  - unfold solved, len. simpl. lia.
  - rewrite solved_step by lia. specialize (IH a ltac:(lia)).
    destruct (_ =? _)%N; lia.
Qed.

Lemma penalty_bound : forall j a, (j <= List.length t)%nat ->
  (penalty a (firstn j t) (firstn j p) <= 1000 * N.of_nat j)%N.
Proof.
  induction j as [| j IH]; intros a Hj.
  - unfold penalty. simpl. lia.
  - rewrite penalty_step by lia. specialize (IH a ltac:(lia)).
    destruct vi_facts as (_ & _ & _ & Hev). destruct (Hev j ltac:(lia)) as [_ Hpj].
    destruct (_ =? _)%N; lia.
Qed.

(* The key of team a after the first j events. *)
Definition keyf (j : nat) (a : N) : Z :=
  enc (Z.of_N (solved a (firstn j t))) (Z.of_N (penalty a (firstn j t) (firstn j p)))
      (Z.of_N a).

Lemma keyf_step : forall j a, (j < List.length t)%nat ->
  keyf (S j) a = if (nth j t 0 =? a)%N
                 then (keyf j a - 17592186044416 + Z.of_N (nth j p 0%N) * 131072)%Z
                 else keyf j a.
Proof.
  intros j a Hj. unfold keyf. rewrite solved_step, penalty_step by exact Hj.
  destruct (_ =? _)%N; unfold enc; lia.
Qed.

Lemma keyf_0 : forall a, keyf 0 a = (2305825417027649536 + Z.of_N a)%Z.
Proof.
  intros a. unfold keyf. rewrite !firstn_0. unfold solved, penalty, len.
  cbn [filter combine map fold_right List.length]. unfold enc. lia.
Qed.

(* The rank query. *)
Lemma rank_count : forall j (T : tree) (q : int), (1 <= j <= List.length t)%nat ->
  ok T -> sorted (elements T) ->
  Permutation (map to_Z (elements T)) (map (keyf j) (teams n)) ->
  (φ q) = (keyf j 1 - 1)%Z ->
  (φ (count_lt q T + 1)) = Z.of_N (rank n (firstn j t) (firstn j p)).
Proof.
  intros j T q Hj Hok Hs Hperm Hq.
  destruct vi_facts as (Hn & Hm & _ & _).
  rewrite add_spec. rewrite (count_lt_spec q T Hok Hs).
  assert (Hc : List.length (filter (fun y => (y <? q)%uint63) (elements T))
     = List.length (filter (fun a => better (score a (firstn j t) (firstn j p))
                                          (score 1 (firstn j t) (firstn j p))) (teams n))).
  { transitivity (List.length (filter (fun z => (z <? (φ q))%Z) (map to_Z (elements T)))).
    - rewrite filter_length_map. f_equal. apply filter_ext. intros y. apply Z_ltb_int.
    - rewrite (perm_filter_length _ _ _ _ Hperm). rewrite filter_length_map. f_equal.
      apply filter_ext_in. intros a Ha. apply in_teams in Ha.
      rewrite Hq. unfold keyf, score.
      pose proof (solved_bound j a ltac:(lia)). pose proof (penalty_bound j a ltac:(lia)).
      pose proof (solved_bound j 1 ltac:(lia)). pose proof (penalty_bound j 1 ltac:(lia)).
      apply enc_better; lia. }
  rewrite Hc. unfold rank, len. change (φ 1) with 1%Z.
  match goal with |- context [List.length (filter ?f (teams n))] =>
    pose proof (filter_length_le f (teams n)) as Hle end.
  rewrite teams_length in Hle.
  rewrite Z.mod_small by (rewrite wB_val; lia). lia.
Qed.

Variables (xt xp : array uint).
Hypothesis Ht : repr xt t.
Hypothesis Hp : repr xp p.

Definition Inv (j : int) (keys : array int) (T : tree) (out : array int) : Prop :=
  (φ (PArray.length keys)) = (Z.of_N n + 1)%Z /\
  (forall i : int, (1 <= (φ i) <= Z.of_N n)%Z ->
     (φ (keys.[i])) = keyf (Z.to_nat (φ j)) (Z.to_N (φ i))) /\
  ok T /\ sorted (elements T) /\
  Permutation (map to_Z (elements T)) (map (keyf (Z.to_nat (φ j))) (teams n)) /\
  PArray.length out = PArray.length xt /\
  (forall i : int, ((φ i) < (φ j))%Z ->
     (φ (out.[i])) = Z.of_N (rank n (firstn (S (Z.to_nat (φ i))) t)
                                  (firstn (S (Z.to_nat (φ i))) p))).

Lemma step_inv : forall (j : int) keys T out,
  ((φ j) < (φ (PArray.length xt)))%Z -> Inv j keys T out ->
  Inv (j + 1) keys.[xt.[j] <- keys.[xt.[j]] - KD + xp.[j] * KE]
    (insert (keys.[xt.[j]] - KD + xp.[j] * KE) (delete (keys.[xt.[j]]) T))
    out.[j <- count_lt (keys.[xt.[j] <- keys.[xt.[j]] - KD + xp.[j] * KE].[1] - 1)
                 (insert (keys.[xt.[j]] - KD + xp.[j] * KE) (delete (keys.[xt.[j]]) T)) + 1].
Proof.
  intros j keys T out Hj (Hkl & Hk & Hok & Hs & Hperm & Hol & Ho).
  destruct vi_facts as (Hn & Hm & Hpl & Hev).
  pose proof (repr_length _ _ Ht) as Lt. pose proof (repr_length _ _ Hp) as Lp.
  pose proof (to_Z_bounded j) as Bj.
  assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z)
    by (rewrite add_spec; change (φ 1) with 1%Z; apply Z.mod_small; rewrite wB_val; lia).
  assert (Hjn : (Z.to_nat (φ j) < List.length t)%nat) by lia.
  assert (Hta : (φ (xt.[j])) = Z.of_N (nth (Z.to_nat (φ j)) t 0%N))
    by (apply repr_get; [exact Ht | lia]).
  assert (Hpa : (φ (xp.[j])) = Z.of_N (nth (Z.to_nat (φ j)) p 0%N))
    by (apply repr_get; [exact Hp | lia]).
  assert (Hjn1 : Z.to_nat (φ (j + 1)) = S (Z.to_nat (φ j))) by lia.
  unfold Inv. rewrite Hjn1.
  set (jn := Z.to_nat (φ j)) in *.
  destruct (Hev jn Hjn) as [Hta' Hpa'].
  set (ta := nth jn t 0%N) in *. set (pa := nth jn p 0%N) in *.
  set (a := xt.[j]) in *.
  set (old := keys.[a]).
  assert (Hold : (φ old) = keyf jn ta)
    by (unfold old; rewrite Hk by lia; rewrite Hta, N2Z.id; reflexivity).
  pose proof (solved_bound jn ta ltac:(lia)) as Bs.
  pose proof (penalty_bound jn ta ltac:(lia)) as Bp.
  set (new := old - KD + xp.[j] * KE).
  assert (BK : (17592186044416 <= keyf jn ta <= 2305843009213693952)%Z)
    by (unfold keyf, enc; lia).
  assert (Hnew : (φ new) = keyf (S jn) ta).
  { rewrite keyf_step by exact Hjn. fold ta pa. rewrite N.eqb_refl.
    unfold new. rewrite add_spec, sub_spec, mul_spec, Hold, Hpa.
    change (φ KD) with 17592186044416%Z. change (φ KE) with 131072%Z.
    rewrite (Z.mod_small (keyf jn ta - _)) by (rewrite wB_val; lia).
    rewrite (Z.mod_small (Z.of_N pa * _)) by (rewrite wB_val; lia).
    rewrite Z.mod_small by (rewrite wB_val; unfold keyf, enc; lia). reflexivity. }
  assert (Hlta : (a <? PArray.length keys) = true) by (apply ltb_true; rewrite Hkl; lia).
  set (keys' := keys.[a <- new]).
  assert (Hk' : forall i : int, (1 <= (φ i) <= Z.of_N n)%Z ->
                (φ (keys'.[i])) = keyf (S jn) (Z.to_N (φ i))).
  { intros i Hi. unfold keys'. destruct (Z.eq_dec (φ i) (φ a)) as [E | E].
    - assert (i = a) by (apply phi_inj; exact E). subst i.
      rewrite aget_set_same by exact Hlta. rewrite Hnew, Hta, N2Z.id. reflexivity.
    - rewrite aget_set_other by (intros F; apply E; rewrite F; reflexivity).
      rewrite Hk by exact Hi. rewrite keyf_step by exact Hjn. fold ta.
      destruct (N.eqb_spec ta (Z.to_N (φ i))); [exfalso; lia | reflexivity]. }
  (* the tree *)
  set (E := elements T) in *.
  assert (Hin_old : In old E).
  { assert (Hi : In (keyf jn ta) (map to_Z E)).
    { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_map. apply in_teams. lia. }
    apply in_map_iff in Hi. destruct Hi as (x & Hx & Hxin).
    assert (x = old) by (apply phi_inj; lia). subst x. exact Hxin. }
  destruct (delete_spec old T Hok Hs) as [Hok1 He1].
  fold E in He1.
  set (D := del_list old E) in *.
  pose proof (del_perm old E Hs Hin_old) as HpD.
  destruct (in_split ta (teams n)) as (A & B & HAB); [apply in_teams; lia|].
  pose proof (teams_NoDup n) as Hnd. rewrite HAB in Hnd.
  pose proof (NoDup_remove_2 _ _ _ Hnd) as HnAB.
  assert (HgA : map (keyf (S jn)) A = map (keyf jn) A).
  { apply map_ext_in. intros b Hb. rewrite keyf_step by exact Hjn. fold ta.
    destruct (N.eqb_spec ta b); [|reflexivity].
    subst b. exfalso. apply HnAB. apply in_or_app. left. exact Hb. }
  assert (HgB : map (keyf (S jn)) B = map (keyf jn) B).
  { apply map_ext_in. intros b Hb. rewrite keyf_step by exact Hjn. fold ta.
    destruct (N.eqb_spec ta b); [|reflexivity].
    subst b. exfalso. apply HnAB. apply in_or_app. right. exact Hb. }
  assert (HD : Permutation (map to_Z D) (map (keyf jn) A ++ map (keyf jn) B)).
  { apply (Permutation_cons_inv (a := (φ old))).
    change ((φ old) :: map to_Z D) with (map to_Z (old :: D)).
    eapply perm_trans; [apply Permutation_map; exact HpD|].
    eapply perm_trans; [exact Hperm|]. rewrite HAB, map_app. cbn [map].
    rewrite Hold. apply Permutation_sym. apply Permutation_middle. }
  assert (Hnin : ~ In new D).
  { intros Hi. apply (in_map to_Z) in Hi. apply (Permutation_in _ HD) in Hi.
    rewrite <- map_app in Hi. apply in_map_iff in Hi. destruct Hi as (b & Hb & Hbin).
    assert (Hbt : In b (teams n)).
    { rewrite HAB. apply in_app_or in Hbin. apply in_or_app.
      destruct Hbin as [Hbin | Hbin]; [left; exact Hbin | right; right; exact Hbin]. }
    apply in_teams in Hbt.
    rewrite Hnew in Hb. unfold keyf in Hb.
    pose proof (solved_bound jn b ltac:(lia)). pose proof (penalty_bound jn b ltac:(lia)).
    pose proof (solved_bound (S jn) ta ltac:(lia)).
    pose proof (penalty_bound (S jn) ta ltac:(lia)).
    apply enc_team in Hb; try lia.
    assert (b = ta) by lia. subst b. apply HnAB. exact Hbin. }
  assert (Hlen_D : (nel (delete old T) + 1 < wB)%Z).
  { unfold nel. rewrite He1. pose proof (Permutation_length HD) as HL.
    rewrite length_map, length_app, !length_map in HL.
    pose proof (teams_length n) as TL. rewrite HAB, length_app in TL. cbn [List.length] in TL.
    rewrite wB_val. lia. }
  assert (Hs1 : sorted (elements (delete old T))) by (rewrite He1; apply del_sorted; exact Hs).
  destruct (insert_spec new _ Hok1 Hs1 Hlen_D) as [Hok2 He2].
  set (T' := insert new (delete old T)) in *.
  assert (Hs2 : sorted (elements T')) by (rewrite He2; apply ins_sorted; exact Hs1).
  assert (Hperm2 : Permutation (map to_Z (elements T')) (map (keyf (S jn)) (teams n))).
  { rewrite He2, He1. eapply perm_trans; [apply Permutation_map; apply ins_perm; exact Hnin|].
    cbn [map]. rewrite HAB, map_app. cbn [map]. rewrite HgA, HgB, Hnew.
    eapply perm_trans; [apply perm_skip; exact HD|]. apply Permutation_middle. }
  split; [unfold keys'; rewrite alength_set; exact Hkl|].
  split; [exact Hk'|].
  split; [exact Hok2|]. split; [exact Hs2|]. split; [exact Hperm2|].
  split; [rewrite alength_set; exact Hol|].
  intros i Hi. rewrite Hj1 in Hi.
  destruct (Z.eq_dec (φ i) (φ j)) as [Eij | Nij].
  - assert (i = j) by (apply phi_inj; exact Eij). subst i.
    rewrite aget_set_same by (apply ltb_true; rewrite Hol; lia).
    fold jn. apply rank_count; [lia | exact Hok2 | exact Hs2 | exact Hperm2 |].
    assert (H1 : (φ (keys'.[1])) = keyf (S jn) 1) by (rewrite Hk'; [reflexivity | change (φ 1) with 1%Z; lia]).
    assert (B1 : (1 <= keyf (S jn) 1)%Z).
    { unfold keyf, enc.
      pose proof (solved_bound (S jn) 1 ltac:(lia)). pose proof (penalty_bound (S jn) 1 ltac:(lia)).
      lia. }
    rewrite sub_spec, H1. change (φ 1) with 1%Z. apply Z.mod_small.
    pose proof (to_Z_bounded (keys'.[1])). lia.
  - rewrite aget_set_other by (intro F; apply Nij; rewrite F; reflexivity).
    apply Ho. lia.
Qed.

Lemma ev_loop_spec : forall z (j : int) keys T out
  (H : Acc (Zwf 0) (gap (PArray.length xt) j)),
  gap (PArray.length xt) j = z -> ((φ j) <= (φ (PArray.length xt)))%Z -> Inv j keys T out ->
  PArray.length (ev_loop xt xp (PArray.length xt) j keys T out H) = PArray.length xt /\
  forall i : int, ((φ i) < (φ (PArray.length xt)))%Z ->
    (φ ((ev_loop xt xp (PArray.length xt) j keys T out H).[i]))
    = Z.of_N (rank n (firstn (S (Z.to_nat (φ i))) t) (firstn (S (Z.to_nat (φ i))) p)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j keys T out H Hz Hjm HI. rewrite ev_loop_eq.
  destruct (bdec (j <? PArray.length xt)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_true in Hj'.
    pose proof (alength_bound xt).
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z)
      by (rewrite add_spec; change (φ 1) with 1%Z; apply Z.mod_small; rewrite wB_val;
          pose proof (to_Z_bounded j); lia).
    cbv zeta. eapply IH; [ | reflexivity | lia | apply step_inv; assumption ].
    rewrite <- Hz. apply dec_step. exact Hj.
  - rewrite ltb_false in Hj. destruct HI as (_ & _ & _ & _ & _ & Hol & Ho).
    split; [exact Hol|]. intros i Hi. apply Ho. lia.
Qed.

End Events.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

(* The output list: the rank of team 1 after each prefix of events. *)
Definition out_list (n : N) (t p : list N) : list N :=
  map (fun i => rank n (firstn (S i) t) (firstn (S i) p)) (seq 0 (List.length t)).

Lemma out_correct : forall (n : N) (t p : list N) (r : array@{Set} uint),
  Z.of_nat (List.length t) = (φ (PArray.length@{Set} r)) ->
  (forall i : int, ((φ i) < Z.of_nat (List.length t))%Z ->
     (φ (PArray.get@{Set} r i))
     = Z.of_N (rank n (firstn (S (Z.to_nat (φ i))) t) (firstn (S (Z.to_nat (φ i))) p))) ->
  repr r (out_list n t p) /\ gcpc_spec n t p (out_list n t p).
Proof.
  intros n t p r Hrl0 Hrc0.
  assert (Hrl : Z.of_nat (List.length t) = (φ (PArray.length@{repr_array.u0} r))) by exact Hrl0.
  assert (Hrc : forall i : int, ((φ i) < Z.of_nat (List.length t))%Z ->
     (φ (PArray.get@{repr_array.u0} r i))
     = Z.of_N (rank n (firstn (S (Z.to_nat (φ i))) t) (firstn (S (Z.to_nat (φ i))) p)))
    by exact Hrc0.
  clear Hrl0 Hrc0.
  assert (Hlen : List.length (out_list n t p) = List.length t).
  { unfold out_list. rewrite length_map, length_seq. reflexivity. }
  assert (Hnth : forall i, (i < List.length t)%nat ->
            nth_error (out_list n t p) i = Some (rank n (firstn (S i) t) (firstn (S i) p))).
  { intros i Hi. unfold out_list. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec i (List.length t)); [reflexivity | lia]. }
  pose proof (to_Z_bounded (PArray.length@{repr_array.u0} r)) as Bl.
  split.
  - split.
    + rewrite Hlen. exact Hrl.
    + intros i Hi. rewrite Hlen in Hi.
      exists (rank n (firstn (S i) t) (firstn (S i) p)). split; [apply Hnth; exact Hi|].
      unfold repr, repr_uint.
      assert (Hi' : (φ (of_Z (Z.of_nat i))) = Z.of_nat i).
      { rewrite of_Z_spec. apply Z.mod_small. lia. }
      change (Uint63.of_nat i) with (of_Z (Z.of_nat i)).
      rewrite Hrc by lia. rewrite Hi', Nat2Z.id, N2Z.id. reflexivity.
  - split.
    + unfold len. rewrite Hlen. reflexivity.
    + intros i Hi. erewrite nth_error_nth; [reflexivity|]. apply Hnth. exact Hi.
Qed.

Lemma gcpc_impl_correct : forall (n : N) (t p : list N) (xn : uint) (xt xp : array uint),
  valid_input n t p -> repr xn n -> repr xt t -> repr xp p ->
  exists o : list N, repr (gcpc_impl xn xt xp) o /\ gcpc_spec n t p o.
Proof.
  intros n t p xn xt xp Hv Hn Ht Hp.
  destruct (vi_facts n t p Hv) as (Hnb & Hm & Hpl & _).
  assert (Hxn : (φ xn) = Z.of_N n).
  { unfold repr, repr_uint in Hn. pose proof (to_Z_bounded xn). lia. }
  assert (Hn1 : (φ (xn + 1)) = (Z.of_N n + 1)%Z)
    by (rewrite add_spec, Hxn; change (φ 1) with 1%Z; apply Z.mod_small; rewrite wB_val; lia).
  pose proof (repr_length _ _ Ht) as Lt.
  exists (out_list n t p).
  unfold gcpc_impl.
  set (n1 := xn + 1) in *.
  assert (Hmk : (φ (PArray.length (PArray.make n1 0))) = (φ n1)).
  { rewrite alength_make.
    replace (n1 <=? PArray.max_length) with true; [reflexivity|].
    symmetry. apply leb_spec. rewrite max_length_val. lia. }
  destruct (init_loop_spec (Z.of_N n) n1 Hn1 ltac:(lia) _ 1 (PArray.make n1 0) Leaf
              (Zwf_well_founded 0 (gap n1 1)) eq_refl
              ltac:(change (φ 1) with 1%Z; lia) Hmk
              ltac:(intros i Hi; change (φ 1) with 1%Z in Hi; lia) I I
              ltac:(change (φ 1) with 1%Z; apply perm_nil))
    as (Hkl & Hk & Hok & Hs & Hperm).
  destruct (init_loop n1 1 (PArray.make n1 0) Leaf (Zwf_well_founded 0 (gap n1 1)))
    as [keys T].
  cbn [fst snd] in Hkl, Hk, Hok, Hs, Hperm.
  set (m := PArray.length xt).
  assert (HmL : PArray.length (PArray.make m 0) = m).
  { rewrite alength_make.
    replace (m <=? PArray.max_length) with true; [reflexivity|].
    symmetry. apply leb_spec. apply alength_bound. }
  assert (HI : Inv n t p xt 0 keys T (PArray.make m 0)).
  { unfold Inv. change (φ 0) with 0%Z. cbn [Z.to_nat].
    split; [rewrite Hkl; exact Hn1|].
    split.
    { intros i Hi. rewrite Hk by exact Hi. rewrite keyf_0.
      change (φ K0) with 2305825417027649536%Z. lia. }
    split; [exact Hok|]. split; [exact Hs|].
    split.
    { replace (Z.to_nat (Z.of_N n)) with (N.to_nat n) in Hperm by lia. eapply perm_trans; [exact Hperm|]. unfold teams. rewrite map_map.
      apply Permutation_refl'. apply map_ext. intros i. rewrite keyf_0.
      change (φ K0) with 2305825417027649536%Z. lia. }
    split; [exact HmL|].
    intros i Hi. pose proof (to_Z_bounded i). lia. }
  destruct (ev_loop_spec n t p Hv xt xp Ht Hp _ 0 keys T (PArray.make m 0)
              (Zwf_well_founded 0 (gap m 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded m); lia) HI)
    as [Hrl Hrc].
  unfold m in *.
  apply out_correct.
  - pose proof (f_equal to_Z Hrl) as H'. rewrite Lt in H'. exact (eq_sym H').
  - intros i Hi. exact (Hrc i ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition gcpc : uint -> array uint -> array uint -> array uint := gcpc_impl.

Definition gcpc_correct :
  forall (n : N) (t p : list N) (xn : uint) (xt xp : array uint),
  valid_input n t p -> repr xn n -> repr xt t -> repr xp p ->
  exists o : list N, repr (gcpc xn xt xp) o /\ gcpc_spec n t p o
  := gcpc_impl_correct.
