(* Implementation of intersectingrectangles (intersectingrectangles.spec):
   a plane sweep over the rectangles' edges, CLRS 33.2 specialised to
   axis-parallel segments.

   Code.  One AVL tree type [tree] (key, value, height: three ints; keys
   compared as signed integers) serves twice.
   - The event queue.  Rectangle i gives two events: its left side at
     x = x1.[i] (value i) and its right side at x = x2.[i] (value n + i).
     The 2n events are inserted into an AVL tree keyed by x, and the sweep
     is an in-order traversal of that tree: a tree sort, O(n log n) in the
     worst case (all x values are distinct, so no key collides).
   - The sweep-line status: the y values of the horizontal edges crossed
     by the sweep line, an AVL tree keyed by y (value unused).
   At a left event of rectangle i, the status is queried for a key
   strictly between y1.[i] and y2.[i] (the left side of i crosses a
   horizontal edge), then y1.[i], y2.[i] are inserted; at a right event
   they are removed, then the status is queried the same way.  The sweep
   stops at the first crossing.  All operations are O(log n).

   Why this decides the contract: all x values are distinct and all y
   values are distinct, so two boundaries meet iff a vertical side of one
   rectangle strictly crosses a horizontal side of the other
   ([geometry]).

   Termination: the tree functions recurse structurally on the tree; the
   insertion loop recurses on an erased [Acc (Zwf 0) (gap n i)] proof, the
   template's device.  No nat, no Z in the code. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Reals Sorted.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

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
(* AVL trees over int keys (signed order), with an int payload          *)
(* ------------------------------------------------------------------ *)

Inductive tree : Set :=
| Leaf : tree
| Node : tree -> int -> int -> tree -> int -> tree.

Definition height (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ _ h => h end.

Definition hmax (a b : int) : int := if a <? b then b else a.

Definition node (l : tree) (k v : int) (r : tree) : tree :=
  Node l k v r (hmax (height l) (height r) + 1).

Definition bal (l : tree) (k v : int) (r : tree) : tree :=
  let hl := height l in
  let hr := height r in
  if hr + 2 <? hl then
    match l with
    | Leaf => node l k v r
    | Node ll lk lv lr _ =>
        if height lr <=? height ll then node ll lk lv (node lr k v r)
        else match lr with
             | Leaf => node l k v r
             | Node lrl lrk lrv lrr _ =>
                 node (node ll lk lv lrl) lrk lrv (node lrr k v r)
             end
    end
  else if hl + 2 <? hr then
    match r with
    | Leaf => node l k v r
    | Node rl rk rv rr _ =>
        if height rl <=? height rr then node (node l k v rl) rk rv rr
        else match rl with
             | Leaf => node l k v r
             | Node rll rlk rlv rlr _ =>
                 node (node l k v rll) rlk rlv (node rlr rk rv rr)
             end
    end
  else node l k v r.

Fixpoint insert (k v : int) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf k v Leaf 1
  | Node l k' v' r h =>
      if Sint63.ltb k k' then bal (insert k v l) k' v' r
      else if Sint63.ltb k' k then bal l k' v' (insert k v r)
      else Node l k v r h
  end.

Fixpoint remove_min (l : tree) (k v : int) (r : tree) : int * int * tree :=
  match l with
  | Leaf => (k, v, r)
  | Node ll lk lv lr _ =>
      let '(mk, mv, l') := remove_min ll lk lv lr in (mk, mv, bal l' k v r)
  end.

Definition merge (l r : tree) : tree :=
  match l with
  | Leaf => r
  | Node _ _ _ _ _ =>
      match r with
      | Leaf => l
      | Node rl rk rv rr _ =>
          let '(mk, mv, r') := remove_min rl rk rv rr in bal l mk mv r'
      end
  end.

Fixpoint remove (k : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l k' v' r _ =>
      if Sint63.ltb k k' then bal (remove k l) k' v' r
      else if Sint63.ltb k' k then bal l k' v' (remove k r)
      else merge l r
  end.

(* Is there a key strictly between lo and hi? *)
Fixpoint between (lo hi : int) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node l k _ r _ =>
      if Sint63.leb k lo then between lo hi r
      else if Sint63.leb hi k then between lo hi l
      else true
  end.

(* ------------------------------------------------------------------ *)
(* The sweep                                                           *)
(* ------------------------------------------------------------------ *)

(* Events of rectangles i, i+1, ..., n-1 into the event tree. *)
Fixpoint build (x1 x2 : array sint) (n i : int) (t : tree)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : tree :=
  match bdec (i <? n) with
  | left Hi =>
      build x1 x2 n (i + 1) (insert x2.[i] (n + i) (insert x1.[i] i t))
        (Acc_inv H (dec_step n i Hi))
  | right _ => t
  end.

Lemma build_eq : forall x1 x2 n i t H,
  build x1 x2 n i t H =
  match bdec (i <? n) with
  | left Hi =>
      build x1 x2 n (i + 1) (insert x2.[i] (n + i) (insert x1.[i] i t))
        (Acc_inv H (dec_step n i Hi))
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* One event: v < n is the left side of rectangle v, v >= n the right
   side of rectangle v - n.  None: a crossing was found. *)
Definition step (n : int) (y1 y2 : array sint) (v : int) (s : tree)
    : option tree :=
  if v <? n then
    let lo := y1.[v] in
    let hi := y2.[v] in
    if between lo hi s then None else Some (insert hi 0 (insert lo 0 s))
  else
    let i := v - n in
    let lo := y1.[i] in
    let hi := y2.[i] in
    let s' := remove hi (remove lo s) in
    if between lo hi s' then None else Some s'.

(* In-order traversal of the event tree, threading the status. *)
Fixpoint sweep (n : int) (y1 y2 : array sint) (t s : tree) : option tree :=
  match t with
  | Leaf => Some s
  | Node l _ v r _ =>
      match sweep n y1 y2 l s with
      | None => None
      | Some s1 =>
          match step n y1 y2 v s1 with
          | None => None
          | Some s2 => sweep n y1 y2 r s2
          end
      end
  end.

Definition intersecting_rectangles_impl (x1 y1 x2 y2 : array sint) : bool :=
  let n := PArray.length x1 in
  let ev := build x1 x2 n 0 Leaf (Zwf_well_founded 0 (gap n 0)) in
  match sweep n y1 y2 ev Leaf with
  | None => true
  | Some _ => false
  end.

(* ------------------------------------------------------------------ *)
(* Prop side: the trees                                                *)
(* ------------------------------------------------------------------ *)

Fixpoint elems (t : tree) : list (int * int) :=
  match t with
  | Leaf => []
  | Node l k v r _ => elems l ++ (k, v) :: elems r
  end.

Definition kz (p : int * int) : Z := Sint63.to_Z (fst p).

Definition ltk (a b : int * int) : Prop := (kz a < kz b)%Z.

Definition sorted (t : tree) : Prop := StronglySorted ltk (elems t).

Lemma ss_app : forall A B : list (int * int),
  StronglySorted ltk (A ++ B) <->
  StronglySorted ltk A /\ StronglySorted ltk B /\
  (forall a b, In a A -> In b B -> ltk a b).
Proof.
  induction A as [| x A IH]; intros B; simpl.
  - split; [intros H; repeat split; auto; [constructor | tauto]
           | intros (_ & H & _); exact H].
  - split.
    + intros H. apply StronglySorted_inv in H as [H1 H2].
      apply IH in H1 as (HA & HB & HAB).
      rewrite Forall_forall in H2.
      repeat split; auto.
      * constructor; auto. rewrite Forall_forall. intros y Hy.
        apply H2. apply in_or_app. left. exact Hy.
      * intros a b [Ea | Ea] Hb; [subst a; apply H2; apply in_or_app; right; exact Hb|].
        apply HAB; auto.
    + intros (HA & HB & HAB). apply StronglySorted_inv in HA as [HA1 HA2].
      constructor.
      * apply IH. repeat split; auto.
      * rewrite Forall_forall in *. intros y Hy. apply in_app_or in Hy as [Hy | Hy].
        -- apply HA2. exact Hy.
        -- apply HAB; [left; reflexivity | exact Hy].
Qed.

Lemma ss_node : forall (A B : list (int * int)) x,
  StronglySorted ltk (A ++ x :: B) <->
  StronglySorted ltk A /\ StronglySorted ltk B /\
  (forall a, In a A -> ltk a x) /\ (forall b, In b B -> ltk x b).
Proof.
  intros A B x. rewrite ss_app. split.
  - intros (HA & HB & HAB). apply StronglySorted_inv in HB as [HB1 HB2].
    rewrite Forall_forall in HB2.
    repeat split; auto. intros a Ha. apply HAB; [exact Ha | left; reflexivity].
  - intros (HA & HB & Hx1 & Hx2). repeat split; auto.
    + constructor; [exact HB | rewrite Forall_forall; exact Hx2].
    + intros a b Ha [Eb | Hb]; [subst b; apply Hx1; exact Ha|].
      pose proof (Hx1 a Ha). pose proof (Hx2 b Hb). unfold ltk in *. lia.
Qed.

Lemma bal_elems : forall l k v r,
  elems (bal l k v r) = elems l ++ (k, v) :: elems r.
Proof.
  intros l k v r. unfold bal, node.
  destruct (height r + 2 <? height l).
  - destruct l as [| ll lk lv lr lh]; [reflexivity|].
    destruct (height lr <=? height ll).
    + simpl. rewrite <- app_assoc. reflexivity.
    + destruct lr as [| lrl lrk lrv lrr lrh]; [reflexivity|].
      simpl. rewrite <- !app_assoc. simpl. rewrite <- !app_assoc. reflexivity.
  - destruct (height l + 2 <? height r); [|reflexivity].
    destruct r as [| rl rk rv rr rh]; [reflexivity|].
    destruct (height rl <=? height rr).
    + simpl. rewrite <- app_assoc. reflexivity.
    + destruct rl as [| rll rlk rlv rlr rlh]; [reflexivity|].
      simpl. rewrite <- !app_assoc. simpl. reflexivity.
Qed.

Lemma ltb_false_ge : forall a b : int,
  Sint63.ltb a b = false -> (Sint63.to_Z b <= Sint63.to_Z a)%Z.
Proof.
  intros a b H. destruct (Z.lt_ge_cases (Sint63.to_Z a) (Sint63.to_Z b)) as [E|E];
    [|exact E].
  apply Sint63.ltb_spec in E. rewrite E in H. discriminate.
Qed.

Lemma ltb_true_lt : forall a b : int,
  Sint63.ltb a b = true -> (Sint63.to_Z a < Sint63.to_Z b)%Z.
Proof. intros a b H. apply Sint63.ltb_spec. exact H. Qed.

Lemma leb_true_le : forall a b : int,
  Sint63.leb a b = true -> (Sint63.to_Z a <= Sint63.to_Z b)%Z.
Proof. intros a b H. apply Sint63.leb_spec. exact H. Qed.

Lemma leb_false_gt : forall a b : int,
  Sint63.leb a b = false -> (Sint63.to_Z b < Sint63.to_Z a)%Z.
Proof.
  intros a b H. destruct (Z.lt_ge_cases (Sint63.to_Z b) (Sint63.to_Z a)) as [E|E];
    [exact E|].
  apply Sint63.leb_spec in E. rewrite E in H. discriminate.
Qed.

Lemma insert_in : forall k v t,
  (forall p, In p (elems t) -> kz p <> Sint63.to_Z k) ->
  forall p, In p (elems (insert k v t)) <-> p = (k, v) \/ In p (elems t).
Proof.
  intros k v t. induction t as [| l IHl k' v' r IHr h]; intros Hk p.
  - simpl. split; (intros [E | []]; left; symmetry; exact E).
  - simpl. destruct (Sint63.ltb k k') eqn:E1.
    + rewrite bal_elems, !in_app_iff, IHl.
      * simpl. tauto.
      * intros q Hq. apply Hk. simpl. apply in_or_app. left. exact Hq.
    + destruct (Sint63.ltb k' k) eqn:E2.
      * rewrite bal_elems, !in_app_iff. simpl. rewrite IHr.
        -- tauto.
        -- intros q Hq. apply Hk. simpl. apply in_or_app. right. right. exact Hq.
      * exfalso. apply ltb_false_ge in E1, E2.
        apply (Hk (k', v')); [simpl; apply in_or_app; right; left; reflexivity|].
        unfold kz. simpl. lia.
Qed.

Lemma insert_sorted : forall k v t,
  sorted t -> (forall p, In p (elems t) -> kz p <> Sint63.to_Z k) ->
  sorted (insert k v t).
Proof.
  intros k v t. induction t as [| l IHl k' v' r IHr h]; intros Hs Hk.
  - unfold sorted. simpl. constructor; constructor.
  - unfold sorted in *. simpl in *. apply ss_node in Hs as (Hl & Hr & Hlx & Hxr).
    destruct (Sint63.ltb k k') eqn:E1.
    + apply ltb_true_lt in E1.
      assert (Hk' : forall p, In p (elems l) -> kz p <> Sint63.to_Z k)
        by (intros q Hq; apply Hk; apply in_or_app; left; exact Hq).
      rewrite bal_elems. apply ss_node. repeat split; auto.
      intros a Ha. apply insert_in in Ha; [|exact Hk'].
      destruct Ha as [Ea | Ha]; [subst a; unfold ltk, kz; simpl; lia | auto].
    + destruct (Sint63.ltb k' k) eqn:E2.
      * apply ltb_true_lt in E2.
        assert (Hk' : forall p, In p (elems r) -> kz p <> Sint63.to_Z k)
          by (intros q Hq; apply Hk; apply in_or_app; right; right; exact Hq).
        rewrite bal_elems. apply ss_node. repeat split; auto.
        intros a Ha. apply insert_in in Ha; [|exact Hk'].
        destruct Ha as [Ea | Ha]; [subst a; unfold ltk, kz; simpl; lia | auto].
      * exfalso. apply ltb_false_ge in E1, E2.
        apply (Hk (k', v')); [apply in_or_app; right; left; reflexivity|].
        unfold kz. simpl. lia.
Qed.

Lemma remove_min_elems : forall l k v r mk mv t',
  remove_min l k v r = (mk, mv, t') ->
  elems l ++ (k, v) :: elems r = (mk, mv) :: elems t'.
Proof.
  induction l as [| ll IHll lk lv lr _ lh]; intros k v r mk mv t' H.
  - simpl in H. injection H as <- <- <-. reflexivity.
  - simpl in H. destruct (remove_min ll lk lv lr) as [[a b] c] eqn:E.
    injection H as <- <- <-. rewrite bal_elems. simpl.
    rewrite (app_comm_cons (elems c) _ (a, b)), <- (IHll _ _ _ _ _ _ E).
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma merge_elems : forall l r, elems (merge l r) = elems l ++ elems r.
Proof.
  intros l r. unfold merge. destruct l as [| ll lk lv lr lh]; [reflexivity|].
  destruct r as [| rl rk rv rr rh]; [rewrite app_nil_r; reflexivity|].
  destruct (remove_min rl rk rv rr) as [[a b] c] eqn:E.
  rewrite bal_elems. rewrite <- (remove_min_elems _ _ _ _ _ _ _ E). reflexivity.
Qed.

Lemma remove_spec : forall k t, sorted t ->
  sorted (remove k t) /\
  forall p, In p (elems (remove k t)) <->
            In p (elems t) /\ kz p <> Sint63.to_Z k.
Proof.
  intros k t. induction t as [| l IHl k' v' r IHr h]; intros Hs.
  - simpl. split; [exact Hs | tauto].
  - unfold sorted in *. simpl in *.
    pose proof Hs as Hs'. apply ss_node in Hs' as (Hl & Hr & Hlx & Hxr).
    destruct (IHl Hl) as [Sl Il]. destruct (IHr Hr) as [Sr Ir].
    destruct (Sint63.ltb k k') eqn:E1.
    + apply ltb_true_lt in E1. rewrite bal_elems. split.
      * apply ss_node. repeat split; auto.
        intros a Ha. apply Il in Ha as [Ha _]. auto.
      * intros p. rewrite !in_app_iff, Il. simpl. split.
        -- intros [[H1 H2] | [H1 | H1]]; [tauto| |].
           ++ subst p. unfold kz. simpl. split; [tauto | lia].
           ++ pose proof (Hxr p H1). unfold ltk, kz in *. simpl in *.
              split; [tauto | lia].
        -- tauto.
    + destruct (Sint63.ltb k' k) eqn:E2.
      * apply ltb_true_lt in E2. rewrite bal_elems. split.
        -- apply ss_node. repeat split; auto.
           intros a Ha. apply Ir in Ha as [Ha _]. auto.
        -- intros p. rewrite !in_app_iff. simpl. rewrite Ir. split.
           ++ intros [H1 | [H1 | [H1 H2]]]; [| |tauto].
              ** pose proof (Hlx p H1). unfold ltk, kz in *. simpl in *.
                 split; [tauto | lia].
              ** subst p. unfold kz. simpl. split; [tauto | lia].
           ++ tauto.
      * apply ltb_false_ge in E1, E2. rewrite merge_elems. split.
        -- apply ss_app. repeat split; auto.
           intros a b Ha Hb. pose proof (Hlx a Ha). pose proof (Hxr b Hb).
           unfold ltk in *. lia.
        -- intros p. rewrite !in_app_iff. simpl. split.
           ++ intros [H1 | H1].
              ** pose proof (Hlx p H1). unfold ltk, kz in *. simpl in *.
                 split; [tauto | lia].
              ** pose proof (Hxr p H1). unfold ltk, kz in *. simpl in *.
                 split; [tauto | lia].
           ++ intros [[H1 | [H1 | H1]] H2]; [tauto | | tauto].
              subst p. unfold kz in H2. simpl in H2. lia.
Qed.

Lemma between_spec : forall lo hi t, sorted t ->
  between lo hi t = true <->
  exists p, In p (elems t) /\
            (Sint63.to_Z lo < kz p < Sint63.to_Z hi)%Z.
Proof.
  intros lo hi t. induction t as [| l IHl k v r IHr h]; intros Hs.
  - simpl. split; [discriminate | intros (p & [] & _)].
  - unfold sorted in *. simpl in *.
    pose proof Hs as Hs'. apply ss_node in Hs' as (Hl & Hr & Hlx & Hxr).
    destruct (Sint63.leb k lo) eqn:E1.
    + apply leb_true_le in E1. rewrite (IHr Hr). split.
      * intros (p & Hp & Hb). exists p. split; [|exact Hb].
        apply in_or_app. right. right. exact Hp.
      * intros (p & Hp & Hb). exists p. split; [|exact Hb].
        apply in_app_or in Hp as [Hp | [Hp | Hp]]; [| |exact Hp].
        -- pose proof (Hlx p Hp). unfold ltk, kz in *. simpl in *. lia.
        -- subst p. unfold kz in Hb. simpl in Hb. lia.
    + apply leb_false_gt in E1. destruct (Sint63.leb hi k) eqn:E2.
      * apply leb_true_le in E2. rewrite (IHl Hl). split.
        -- intros (p & Hp & Hb). exists p. split; [|exact Hb].
           apply in_or_app. left. exact Hp.
        -- intros (p & Hp & Hb). exists p. split; [|exact Hb].
           apply in_app_or in Hp as [Hp | [Hp | Hp]]; [exact Hp| |].
           ++ subst p. unfold kz in Hb. simpl in Hb. lia.
           ++ pose proof (Hxr p Hp). unfold ltk, kz in *. simpl in *. lia.
      * apply leb_false_gt in E2. split; [intros _|reflexivity].
        exists (k, v). split; [apply in_or_app; right; left; reflexivity|].
        unfold kz. simpl. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the sweep as a list traversal                            *)
(* ------------------------------------------------------------------ *)

Fixpoint sweepL (n : int) (y1 y2 : array sint) (E : list (int * int)) (s : tree)
    : option tree :=
  match E with
  | [] => Some s
  | (_, v) :: E' =>
      match step n y1 y2 v s with
      | None => None
      | Some s' => sweepL n y1 y2 E' s'
      end
  end.

Lemma sweepL_app : forall n y1 y2 A B s,
  sweepL n y1 y2 (A ++ B) s =
  match sweepL n y1 y2 A s with
  | None => None
  | Some s' => sweepL n y1 y2 B s'
  end.
Proof.
  intros n y1 y2 A. induction A as [| [k v] A IH]; intros B s; [reflexivity|].
  simpl. destruct (step n y1 y2 v s); [apply IH | reflexivity].
Qed.

Lemma sweep_elems : forall n y1 y2 t s,
  sweep n y1 y2 t s = sweepL n y1 y2 (elems t) s.
Proof.
  intros n y1 y2 t. induction t as [| l IHl k v r IHr h]; intros s; [reflexivity|].
  simpl. rewrite sweepL_app, <- IHl. destruct (sweep n y1 y2 l s); [|reflexivity].
  simpl. destruct (step n y1 y2 v t); [apply IHr | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* The sweep invariant, on machine arrays                              *)
(* ------------------------------------------------------------------ *)

Section Sweep.

Variables (n : int) (ax1 ay1 ax2 ay2 : array sint).

Definition X1 (j : int) : Z := Sint63.to_Z ax1.[j].
Definition X2 (j : int) : Z := Sint63.to_Z ax2.[j].
Definition Y1 (j : int) : Z := Sint63.to_Z ay1.[j].
Definition Y2 (j : int) : Z := Sint63.to_Z ay2.[j].

Hypothesis Hn : ((φ n) <= 100000)%Z.
Hypothesis Hxo : forall j, ((φ j) < (φ n))%Z -> (X1 j < X2 j)%Z.
Hypothesis Hyo : forall j, ((φ j) < (φ n))%Z -> (Y1 j < Y2 j)%Z.
Hypothesis Hxd : forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z -> i <> j ->
  X1 i <> X1 j /\ X2 i <> X2 j.
Hypothesis Hxd12 : forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z -> X1 i <> X2 j.
Hypothesis Hyd : forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z -> i <> j ->
  Y1 i <> Y1 j /\ Y2 i <> Y2 j.
Hypothesis Hyd12 : forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z -> Y1 i <> Y2 j.

Definition ev1 (j : int) : int * int := (ax1.[j], j).
Definition ev2 (j : int) : int * int := (ax2.[j], n + j).

Definition is_event (p : int * int) : Prop :=
  exists j, ((φ j) < (φ n))%Z /\ (p = ev1 j \/ p = ev2 j).

Lemma int_eq_dec : forall a b : int, {a = b} + {a <> b}.
Proof.
  intros a b. destruct (Uint63.eqb a b) eqn:E;
    [left; apply eqb_spec; exact E | right; apply eqb_false_spec; exact E].
Defined.

Lemma add_n : forall j, ((φ j) < (φ n))%Z -> (φ (n + j)) = ((φ n) + (φ j))%Z.
Proof. intros j Hj. pose proof (to_Z_bounded j). sia. Qed.

Lemma ev_neq12 : forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z -> ev1 i <> ev2 j.
Proof.
  intros i j Hi Hj E. injection E as _ E.
  pose proof (add_n j Hj). pose proof (to_Z_bounded j).
  apply (f_equal to_Z) in E. lia.
Qed.

Lemma ev1_inj : forall i j, ev1 i = ev1 j -> i = j.
Proof. intros i j E. injection E as _ E. exact E. Qed.

Lemma ev2_inj : forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z -> ev2 i = ev2 j -> i = j.
Proof.
  intros i j Hi Hj E. injection E as _ E.
  apply to_Z_inj. pose proof (add_n i Hi). pose proof (add_n j Hj).
  apply (f_equal to_Z) in E. lia.
Qed.

Definition rect (v : int) : int := if v <? n then v else v - n.

(* The event p reveals a crossing: its vertical side crosses a horizontal
   side of rectangle j. *)
Definition cond (p : int * int) : Prop :=
  exists j, ((φ j) < (φ n))%Z /\ (X1 j < kz p < X2 j)%Z /\
    ((Y1 (rect (snd p)) < Y1 j < Y2 (rect (snd p)))%Z \/
     (Y1 (rect (snd p)) < Y2 j < Y2 (rect (snd p)))%Z).

(* y is a key of the status after the events of P. *)
Definition active (P : list (int * int)) (y : Z) : Prop :=
  exists j, ((φ j) < (φ n))%Z /\ In (ev1 j) P /\ ~ In (ev2 j) P /\
            (y = Y1 j \/ y = Y2 j).

Definition keys_of (s : tree) (y : Z) : Prop :=
  exists p, In p (elems s) /\ kz p = y.

Definition status_ok (P : list (int * int)) (s : tree) : Prop :=
  sorted s /\ forall y, keys_of s y <-> active P y.

Lemma rect_left : forall i, ((φ i) < (φ n))%Z -> rect i = i.
Proof.
  intros i Hi. unfold rect. replace (i <? n) with true; [reflexivity|].
  symmetry. apply ltb_spec. exact Hi.
Qed.

Lemma rect_right : forall i, ((φ i) < (φ n))%Z -> rect (n + i) = i.
Proof.
  intros i Hi. pose proof (add_n i Hi). pose proof (to_Z_bounded i).
  unfold rect. replace (n + i <? n) with false.
  - apply to_Z_inj. sia.
  - symmetry. apply Bool.not_true_iff_false. rewrite ltb_spec. lia.
Qed.

Lemma kz_ev1 : forall j, kz (ev1 j) = X1 j.
Proof. reflexivity. Qed.
Lemma kz_ev2 : forall j, kz (ev2 j) = X2 j.
Proof. reflexivity. Qed.

Lemma sweepL_correct : forall E,
  StronglySorted ltk E -> (forall p, In p E <-> is_event p) ->
  forall R P s, E = P ++ R -> status_ok P s ->
  (sweepL n ay1 ay2 R s = None <-> exists p, In p R /\ cond p).
Proof.
  intros E HE Hev R. induction R as [| p R IH]; intros P s HPR [Hs Hk].
  - simpl. split; [discriminate | intros (p & [] & _)].
  - assert (Hp : is_event p) by (apply Hev; rewrite HPR; apply in_or_app; right; left; reflexivity).
    pose proof HE as HE'. rewrite HPR in HE'. apply ss_node in HE' as (_ & _ & HPp & HpR).
    (* the events of P are exactly those left of p *)
    assert (Hdone : forall q, is_event q -> In q P <-> (kz q < kz p)%Z).
    { intros q Hq. split; [intros Hin; apply HPp; exact Hin|].
      intros Hlt. apply Hev in Hq. rewrite HPR in Hq.
      apply in_app_or in Hq as [Hq | [Hq | Hq]]; [exact Hq| |].
      - subst q. lia.
      - pose proof (HpR q Hq). unfold ltk in *. lia. }
    assert (Hd1 : forall j, ((φ j) < (φ n))%Z -> In (ev1 j) P <-> (X1 j < kz p)%Z).
    { intros j Hj. apply Hdone. exists j. auto. }
    assert (Hd2 : forall j, ((φ j) < (φ n))%Z -> In (ev2 j) P <-> (X2 j < kz p)%Z).
    { intros j Hj. apply Hdone. exists j. auto. }
    assert (HPR' : E = (P ++ [p]) ++ R) by (rewrite <- app_assoc; exact HPR).
    destruct Hp as (i & Hi & [Ep | Ep]); subst p.
    + (* left side of rectangle i *)
      rewrite kz_ev1 in Hd1, Hd2.
      simpl. unfold step.
      replace (i <? n) with true by (symmetry; apply ltb_spec; exact Hi).
      pose proof (Hxo i Hi). pose proof (Hyo i Hi).
      assert (Hq : between ay1.[i] ay2.[i] s = true <-> cond (ev1 i)).
      { rewrite between_spec by exact Hs. unfold cond. simpl snd.
        rewrite rect_left by exact Hi. rewrite kz_ev1. split.
        - intros (q & Hq & Hb). assert (Ka : active P (kz q)) by (apply Hk; exists q; auto).
          destruct Ka as (j & Hj & H1 & H2 & H3).
          rewrite Hd1 in H1 by exact Hj. rewrite Hd2 in H2 by exact Hj.
          pose proof (Hxd12 i j Hi Hj).
          exists j. unfold Y1, Y2 in *. split; [exact Hj|]. split; [lia|].
          destruct H3 as [H3 | H3]; rewrite H3 in Hb; [left | right]; exact Hb.
        - intros (j & Hj & Hx & Hy). pose proof (Hyo j Hj).
          assert (Ka : active P (if Z_lt_dec (Y1 i) (Y1 j) then Y1 j else Y2 j)).
          { exists j. split; [exact Hj|]. rewrite Hd1, Hd2 by exact Hj.
            split; [lia|]. split; [lia|].
            destruct (Z_lt_dec (Y1 i) (Y1 j)); [left | right]; reflexivity. }
          apply Hk in Ka. destruct Ka as (q & Hq & Eq). exists q. split; [exact Hq|].
          rewrite Eq. unfold Y1, Y2 in *.
          destruct (Z_lt_dec (Sint63.to_Z ay1.[i]) (Sint63.to_Z ay1.[j])); lia. }
      destruct (between ay1.[i] ay2.[i] s) eqn:Eb.
      * split; [intros _|reflexivity]. exists (ev1 i). split; [left; reflexivity|].
        apply Hq. reflexivity.
      * assert (Hnc : ~ cond (ev1 i)) by (rewrite <- Hq; discriminate).
        assert (Hlo : forall q, In q (elems s) -> kz q <> Sint63.to_Z ay1.[i]).
        { intros q Hin Eq. assert (Ka : active P (kz q)) by (apply Hk; exists q; auto).
          destruct Ka as (j & Hj & H1 & _ & H3). rewrite Hd1 in H1 by exact Hj.
          destruct (int_eq_dec i j) as [<- | Nij]; [lia|].
          pose proof (Hyd i j Hi Hj Nij). pose proof (Hyd12 i j Hi Hj).
          unfold Y1, Y2 in *. lia. }
        assert (Hhi : forall q, In q (elems (insert ay1.[i] 0 s)) ->
                      kz q <> Sint63.to_Z ay2.[i]).
        { intros q Hin. apply insert_in in Hin; [|exact Hlo].
          destruct Hin as [-> | Hin]; [unfold kz, Y1, Y2 in *; simpl; lia|].
          intros Eq. assert (Ka : active P (kz q)) by (apply Hk; exists q; auto).
          destruct Ka as (j & Hj & H1 & _ & H3). rewrite Hd1 in H1 by exact Hj.
          destruct (int_eq_dec i j) as [<- | Nij]; [lia|].
          pose proof (Hyd i j Hi Hj Nij). pose proof (Hyd12 j i Hj Hi).
          unfold Y1, Y2 in *. lia. }
        rewrite (IH (P ++ [ev1 i])).
        -- split.
           ++ intros (q & Hin & Hc). exists q. split; [right; exact Hin | exact Hc].
           ++ intros (q & [<- | Hin] & Hc); [contradiction|]. exists q. auto.
        -- exact HPR'.
        -- split; [apply insert_sorted; [apply insert_sorted; [exact Hs | exact Hlo] | exact Hhi]|].
           intros y. unfold keys_of. split.
           ++ intros (q & Hin & Eq). apply insert_in in Hin; [|exact Hhi].
              rewrite insert_in in Hin by exact Hlo.
              destruct Hin as [-> | [-> | Hin]].
              ** exists i. rewrite !in_app_iff. simpl. split; [exact Hi|].
                 split; [right; left; reflexivity|].
                 split; [|right; exact (eq_sym Eq)].
                 intros [H1 | [H1 | []]].
                 --- rewrite Hd2 in H1 by exact Hi. lia.
                 --- exact (ev_neq12 i i Hi Hi H1).
              ** exists i. rewrite !in_app_iff. simpl. split; [exact Hi|].
                 split; [right; left; reflexivity|].
                 split; [|left; exact (eq_sym Eq)].
                 intros [H1 | [H1 | []]].
                 --- rewrite Hd2 in H1 by exact Hi. lia.
                 --- exact (ev_neq12 i i Hi Hi H1).
              ** assert (Ka : active P y) by (apply Hk; exists q; auto).
                 destruct Ka as (j & Hj & H1 & H2 & H3).
                 exists j. rewrite !in_app_iff. simpl. split; [exact Hj|].
                 split; [left; exact H1|]. split; [|exact H3].
                 intros [H4 | [H4 | []]]; [contradiction|].
                 exact (ev_neq12 i j Hi Hj H4).
           ++ intros (j & Hj & H1 & H2 & H3). rewrite !in_app_iff in H1, H2.
              simpl in H1, H2.
              destruct H1 as [H1 | [H1 | []]].
              ** assert (Ka : keys_of s y).
                 { apply Hk. exists j. repeat split; auto. }
                 destruct Ka as (q & Hin & Eq). exists q. split; [|exact Eq].
                 apply insert_in; [exact Hhi|]. right.
                 apply insert_in; [exact Hlo|]. right. exact Hin.
              ** apply ev1_inj in H1. subst j.
                 destruct H3 as [-> | ->].
                 --- exists (ay1.[i], 0). split; [|reflexivity].
                     apply insert_in; [exact Hhi|]. right.
                     apply insert_in; [exact Hlo|]. left. reflexivity.
                 --- exists (ay2.[i], 0). split; [|reflexivity].
                     apply insert_in; [exact Hhi|]. left. reflexivity.
    + (* right side of rectangle i *)
      rewrite kz_ev2 in Hd1, Hd2.
      simpl. unfold step.
      pose proof (add_n i Hi) as Ani. pose proof (to_Z_bounded i) as Bi.
      replace (n + i <? n) with false
        by (symmetry; apply Bool.not_true_iff_false; rewrite ltb_spec; lia).
      replace (n + i - n) with i by (apply to_Z_inj; sia).
      pose proof (Hxo i Hi) as Oxi. pose proof (Hyo i Hi) as Oyi.
      destruct (remove_spec ay1.[i] s Hs) as [S1 I1].
      destruct (remove_spec ay2.[i] _ S1) as [S2 I2].
      set (s' := remove ay2.[i] (remove ay1.[i] s)) in *.
      assert (Hk' : forall y, keys_of s' y <->
                    active P y /\ y <> Y1 i /\ y <> Y2 i).
      { intros y. rewrite <- Hk. unfold keys_of. split.
        - intros (q & Hin & Eq). apply I2 in Hin as [Hin N2].
          apply I1 in Hin as [Hin N1]. subst y. unfold Y1, Y2.
          split; [exists q; auto | split; assumption].
        - intros ((q & Hin & Eq) & N1 & N2). exists q. split; [|exact Eq].
          apply I2. split; [apply I1; split; [exact Hin|]|]; unfold Y1, Y2 in *; lia. }
      assert (Hq : between ay1.[i] ay2.[i] s' = true <-> cond (ev2 i)).
      { rewrite between_spec by exact S2. unfold cond. simpl snd.
        rewrite rect_right by exact Hi. rewrite kz_ev2. split.
        - intros (q & Hq & Hb). assert (Ka : keys_of s' (kz q)) by (exists q; auto).
          apply Hk' in Ka as ((j & Hj & H1 & H2 & H3) & _ & _).
          rewrite Hd1 in H1 by exact Hj. rewrite Hd2 in H2 by exact Hj.
          destruct (int_eq_dec i j) as [<- | Nij].
          + unfold Y1, Y2 in *. lia.
          + pose proof (Hxd i j Hi Hj Nij).
            exists j. unfold Y1, Y2 in *. split; [exact Hj|]. split; [lia|].
            destruct H3 as [H3 | H3]; rewrite H3 in Hb; [left | right]; exact Hb.
        - intros (j & Hj & Hx & Hy). pose proof (Hyo j Hj).
          set (y := if Z_lt_dec (Y1 i) (Y1 j) then Y1 j else Y2 j).
          assert (Hyb : (Y1 i < y < Y2 i)%Z)
            by (unfold y; destruct (Z_lt_dec (Y1 i) (Y1 j)); lia).
          assert (Ka : keys_of s' y).
          { apply Hk'. split; [|lia].
            exists j. split; [exact Hj|]. rewrite Hd1, Hd2 by exact Hj.
            split; [lia|]. split; [lia|].
            unfold y. destruct (Z_lt_dec (Y1 i) (Y1 j)); [left | right]; reflexivity. }
          destruct Ka as (q & Hq & Eq). exists q. split; [exact Hq|].
          rewrite Eq. exact Hyb. }
      destruct (between ay1.[i] ay2.[i] s') eqn:Eb.
      * split; [intros _|reflexivity]. exists (ev2 i). split; [left; reflexivity|].
        apply Hq. reflexivity.
      * assert (Hnc : ~ cond (ev2 i)) by (rewrite <- Hq; discriminate).
        rewrite (IH (P ++ [ev2 i])).
        -- split.
           ++ intros (q & Hin & Hc). exists q. split; [right; exact Hin | exact Hc].
           ++ intros (q & [<- | Hin] & Hc); [contradiction|]. exists q. auto.
        -- exact HPR'.
        -- split; [exact S2|]. intros y. rewrite Hk'. split.
           ++ intros ((j & Hj & H1 & H2 & H3) & N1 & N2).
              exists j. rewrite !in_app_iff. simpl. split; [exact Hj|].
              split; [left; exact H1|]. split; [|exact H3].
              intros [H4 | [H4 | []]]; [contradiction|].
              apply ev2_inj in H4; [|exact Hi|exact Hj]. subst j. lia.
           ++ intros (j & Hj & H1 & H2 & H3). rewrite !in_app_iff in H1, H2.
              simpl in H1, H2.
              destruct H1 as [H1 | [H1 | []]];
                [| exfalso; exact (ev_neq12 j i Hj Hi (eq_sym H1))].
              assert (Nij : i <> j) by (intros <-; apply H2; right; left; reflexivity).
              pose proof (Hyd i j Hi Hj Nij). pose proof (Hyd12 i j Hi Hj).
              pose proof (Hyd12 j i Hj Hi).
              split; [|unfold Y1, Y2 in *; lia].
              exists j. repeat split; auto.
Qed.

Definition crossM (i j : int) : Prop :=
  ((X1 j < X1 i < X2 j) \/ (X1 j < X2 i < X2 j))%Z /\
  ((Y1 i < Y1 j < Y2 i) \/ (Y1 i < Y2 j < Y2 i))%Z.

Lemma sweep_result : forall t,
  sorted t -> (forall p, In p (elems t) <-> is_event p) ->
  sweep n ay1 ay2 t Leaf = None <->
  exists i j, ((φ i) < (φ n))%Z /\ ((φ j) < (φ n))%Z /\ crossM i j.
Proof.
  intros t Ht Hev. rewrite sweep_elems.
  rewrite (sweepL_correct (elems t) Ht Hev (elems t) [] Leaf eq_refl).
  - split.
    + intros (p & Hin & (j & Hj & Hx & Hy)). apply Hev in Hin.
      destruct Hin as (i & Hi & [-> | ->]).
      * simpl snd in Hy. rewrite rect_left in Hy by exact Hi.
        exists i, j. repeat split; auto.
      * simpl snd in Hy. rewrite rect_right in Hy by exact Hi.
        exists i, j. repeat split; auto.
    + intros (i & j & Hi & Hj & [[Hx | Hx] Hy]).
      * exists (ev1 i). split; [apply Hev; exists i; auto|].
        exists j. simpl snd. rewrite rect_left by exact Hi. auto.
      * exists (ev2 i). split; [apply Hev; exists i; auto|].
        exists j. simpl snd. rewrite rect_right by exact Hi. auto.
  - split; [constructor|]. intros y. unfold keys_of, active. simpl. split.
    + intros (p & [] & _).
    + intros (j & _ & [] & _).
Qed.

Lemma build_spec : forall z i t H,
  gap n i = z -> ((φ i) <= (φ n))%Z -> sorted t ->
  (forall p, In p (elems t) <->
     exists j, ((φ j) < (φ i))%Z /\ (p = ev1 j \/ p = ev2 j)) ->
  sorted (build ax1 ax2 n i t H) /\
  forall p, In p (elems (build ax1 ax2 n i t H)) <-> is_event p.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i t H Hz Hin Hs Ht. rewrite build_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    pose proof (Hxo i Hi').
    assert (H1 : forall p, In p (elems t) -> kz p <> Sint63.to_Z ax1.[i]).
    { intros p Hp. apply Ht in Hp as (j & Hj & [-> | ->]).
      - rewrite kz_ev1. assert (Nij : j <> i) by (intros ->; lia).
        apply (Hxd j i ltac:(lia) Hi' Nij).
      - rewrite kz_ev2. intros E. apply (Hxd12 i j Hi' ltac:(lia)). symmetry. exact E. }
    assert (H2 : forall p, In p (elems (insert ax1.[i] i t)) ->
                 kz p <> Sint63.to_Z ax2.[i]).
    { intros p Hp. apply insert_in in Hp; [|exact H1].
      destruct Hp as [-> | Hp]; [unfold kz, X1, X2 in *; simpl; lia|].
      apply Ht in Hp as (j & Hj & [-> | ->]).
      - rewrite kz_ev1. apply (Hxd12 j i ltac:(lia) Hi').
      - rewrite kz_ev2. assert (Nij : j <> i) by (intros ->; lia).
        apply (Hxd j i ltac:(lia) Hi' Nij). }
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + apply insert_sorted; [apply insert_sorted; assumption | exact H2].
    + intros p. rewrite insert_in by exact H2. rewrite insert_in by exact H1.
      rewrite Ht. split.
      * intros [-> | [-> | (j & Hj & Hp)]].
        -- exists i. split; [lia | right; reflexivity].
        -- exists i. split; [lia | left; reflexivity].
        -- exists j. split; [lia | exact Hp].
      * intros (j & Hj & Hp).
        destruct (Z.eq_dec (φ j) (φ i)) as [E | E].
        -- apply to_Z_inj in E. subst j.
           destruct Hp as [-> | ->]; [right; left | left]; reflexivity.
        -- right. right. exists j. split; [lia | exact Hp].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    split; [exact Hs|]. intros p. rewrite Ht. unfold is_event. split.
    + intros (j & Hj & Hp). exists j. split; [lia | exact Hp].
    + intros (j & Hj & Hp). exists j. split; [lia | exact Hp].
Qed.

Lemma impl_iff :
  match sweep n ay1 ay2
          (build ax1 ax2 n 0 Leaf (Zwf_well_founded 0 (gap n 0))) Leaf with
  | None => true
  | Some _ => false
  end = true <->
  exists i j, ((φ i) < (φ n))%Z /\ ((φ j) < (φ n))%Z /\ crossM i j.
Proof.
  destruct (build_spec _ 0 Leaf (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded n); lia)
              ltac:(constructor)
              ltac:(intros p; simpl; split; [intros [] |
                    intros (j & Hj & _); change (φ 0) with 0%Z in Hj;
                    pose proof (to_Z_bounded j); lia]))
    as [Hs Hev].
  rewrite <- (sweep_result _ Hs Hev).
  destruct (sweep n ay1 ay2 _ Leaf); split; congruence.
Qed.

End Sweep.

(* ------------------------------------------------------------------ *)
(* Geometry: two boundaries meet iff a side crosses a side             *)
(* ------------------------------------------------------------------ *)

Section Geometry.

Variables x1 y1 x2 y2 : list Z.

Definition crossN (i j : N) : Prop :=
  ((entry x1 j < entry x1 i < entry x2 j) \/
   (entry x1 j < entry x2 i < entry x2 j))%Z /\
  ((entry y1 i < entry y1 j < entry y2 i) \/
   (entry y1 i < entry y2 j < entry y2 i))%Z.

Hypothesis Hxo : forall i, (i < len x1)%N -> (entry x1 i < entry x2 i)%Z.
Hypothesis Hyo : forall i, (i < len x1)%N -> (entry y1 i < entry y2 i)%Z.
Hypothesis Hxd : forall i j, (i < len x1)%N -> (j < len x1)%N -> i <> j ->
  entry x1 i <> entry x1 j /\ entry x2 i <> entry x2 j.
Hypothesis Hxd12 : forall i j, (i < len x1)%N -> (j < len x1)%N ->
  entry x1 i <> entry x2 j.
Hypothesis Hyd : forall i j, (i < len x1)%N -> (j < len x1)%N -> i <> j ->
  entry y1 i <> entry y1 j /\ entry y2 i <> entry y2 j.
Hypothesis Hyd12 : forall i j, (i < len x1)%N -> (j < len x1)%N ->
  entry y1 i <> entry y2 j.

Lemma intersect_sym : forall i j,
  intersect x1 y1 x2 y2 i j -> intersect x1 y1 x2 y2 j i.
Proof. intros i j (p & q & H1 & H2). exists p, q. split; assumption. Qed.

Lemma cross_intersect : forall i j, (i < len x1)%N -> (j < len x1)%N ->
  crossN i j -> intersect x1 y1 x2 y2 i j.
Proof.
  intros i j Hi Hj [Hx Hy]. pose proof (Hxo i Hi). pose proof (Hyo j Hj).
  pose (c := if Z_lt_dec (entry x1 j) (entry x1 i) then
               if Z_lt_dec (entry x1 i) (entry x2 j) then entry x1 i else entry x2 i
             else entry x2 i).
  pose (d := if Z_lt_dec (entry y1 i) (entry y1 j) then
               if Z_lt_dec (entry y1 j) (entry y2 i) then entry y1 j else entry y2 j
             else entry y2 j).
  assert (Hc : ((c = entry x1 i \/ c = entry x2 i) /\ (entry x1 j < c < entry x2 j))%Z).
  { unfold c. destruct (Z_lt_dec (entry x1 j) (entry x1 i));
      [destruct (Z_lt_dec (entry x1 i) (entry x2 j))|]; lia. }
  assert (Hd : ((d = entry y1 j \/ d = entry y2 j) /\ (entry y1 i < d < entry y2 i))%Z).
  { unfold d. destruct (Z_lt_dec (entry y1 i) (entry y1 j));
      [destruct (Z_lt_dec (entry y1 j) (entry y2 i))|]; lia. }
  assert (Hxi : (entry x1 i <= entry x2 i)%Z) by lia.
  assert (Hyj : (entry y1 j <= entry y2 j)%Z) by lia.
  exists (IZR c), (IZR d). unfold on_boundary, coord.
  destruct Hc as [Hc1 Hc2]. destruct Hd as [Hd1 Hd2].
  split; split; [| split | | split].
  - split; apply IZR_le; lia.
  - split; apply IZR_le; lia.
  - destruct Hc1 as [-> | ->]; [left | right; left]; reflexivity.
  - split; apply IZR_le; lia.
  - split; apply IZR_le; lia.
  - destruct Hd1 as [-> | ->]; [right; right; left | right; right; right]; reflexivity.
Qed.

Lemma intersect_cross : forall i j, (i < len x1)%N -> (j < len x1)%N -> i <> j ->
  intersect x1 y1 x2 y2 i j -> crossN i j \/ crossN j i.
Proof.
  intros i j Hi Hj Nij (p & q & (Hpi & Hqi & Si) & (Hpj & Hqj & Sj)).
  pose proof (Hxo i Hi). pose proof (Hxo j Hj).
  pose proof (Hyo i Hi). pose proof (Hyo j Hj).
  pose proof (Hxd i j Hi Hj Nij). pose proof (Hyd i j Hi Hj Nij).
  pose proof (Hxd12 i j Hi Hj). pose proof (Hxd12 j i Hj Hi).
  pose proof (Hyd12 i j Hi Hj). pose proof (Hyd12 j i Hj Hi).
  unfold coord in *. unfold crossN.
  destruct Hpi as [Hpi1 Hpi2]. destruct Hqi as [Hqi1 Hqi2].
  destruct Hpj as [Hpj1 Hpj2]. destruct Hqj as [Hqj1 Hqj2].
  destruct Si as [Si | [Si | [Si | Si]]]; subst;
  destruct Sj as [Sj | [Sj | [Sj | Sj]]]; subst;
  repeat match goal with
         | H : (IZR _ <= IZR _)%R |- _ => apply le_IZR in H
         | H : IZR _ = IZR _ |- _ => apply eq_IZR in H
         end;
  lia.
Qed.

Lemma geometry :
  some_pair_intersects x1 y1 x2 y2 <->
  exists i j, (i < len x1)%N /\ (j < len x1)%N /\ crossN i j.
Proof.
  split.
  - intros (i & j & [Hij Hj] & Hint).
    assert (Nij : i <> j) by (intros ->; lia).
    destruct (intersect_cross i j ltac:(lia) Hj Nij Hint) as [C | C].
    + exists i, j. split; [lia|]. split; [exact Hj | exact C].
    + exists j, i. split; [exact Hj|]. split; [lia | exact C].
  - intros (i & j & Hi & Hj & C).
    assert (Nij : i <> j).
    { intros ->. destruct C as [[C | C] _]; lia. }
    pose proof (cross_intersect i j Hi Hj C) as Hint.
    destruct (N.lt_ge_cases i j) as [L | L].
    + exists i, j. split; [lia | exact Hint].
    + exists j, i. split; [lia | apply intersect_sym; exact Hint].
Qed.

End Geometry.

(* ------------------------------------------------------------------ *)
(* From the machine arrays to the math lists                           *)
(* ------------------------------------------------------------------ *)

Lemma repr_get : forall (x : array sint) (a : list Z), repr x a ->
  forall i : int, ((φ i) < Z.of_nat (List.length a))%Z ->
  Sint63.to_Z x.[i] = entry a (Z.to_N (φ i)).
Proof.
  intros x a [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hr.
  unfold entry. rewrite Z_N_nat. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array sint) (a : list Z), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma nodup_parts : forall l1 l2 : list Z,
  NoDup (l1 ++ l2) -> List.length l2 = List.length l1 ->
  (forall a b : N, (a < len l1)%N -> (b < len l1)%N -> a <> b ->
     entry l1 a <> entry l1 b /\ entry l2 a <> entry l2 b) /\
  (forall a b : N, (a < len l1)%N -> (b < len l1)%N -> entry l1 a <> entry l2 b).
Proof.
  intros l1 l2 H Hl. rewrite (NoDup_nth _ 0%Z) in H. rewrite length_app in H.
  unfold len, entry. split.
  - intros a b Ha Hb Nab. split; intros E.
    + apply Nab. apply N2Nat.inj. apply H; [lia | lia |].
      rewrite !app_nth1 by lia. exact E.
    + apply Nab. apply N2Nat.inj.
      assert (E' : (List.length l1 + N.to_nat a = List.length l1 + N.to_nat b)%nat).
      { apply H; [lia | lia |]. rewrite !app_nth2_plus. exact E. }
      lia.
  - intros a b Ha Hb E.
    assert (E' : (N.to_nat a = List.length l1 + N.to_nat b)%nat).
    { apply H; [lia | lia |]. rewrite app_nth1 by lia. rewrite app_nth2_plus. exact E. }
    lia.
Qed.

(* Bridge from the iff form to the spec's match on the bool. *)
Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P H; [exact (proj1 H eq_refl)|].
  intro p. discriminate (proj2 H p).
Qed.

Lemma intersecting_rectangles_impl_correct :
  forall (x1 y1 x2 y2 : list Z) (ax1 ay1 ax2 ay2 : array sint),
  valid_input x1 y1 x2 y2 ->
  repr ax1 x1 -> repr ay1 y1 -> repr ax2 x2 -> repr ay2 y2 ->
  exists b : bool,
    repr (intersecting_rectangles_impl ax1 ay1 ax2 ay2) b /\
    intersecting_rectangles_spec x1 y1 x2 y2 b.
Proof.
  intros x1 y1 x2 y2 ax1 ay1 ax2 ay2 Hv Rx1 Ry1 Rx2 Ry2.
  destruct Hv as [Hn Ly1 Lx2 Ly2 _ _ _ _ Hxo Hyo Hxd Hyd].
  unfold len in Hn, Ly1, Lx2, Ly2.
  pose proof (repr_length _ _ Rx1) as Ln.
  set (n := PArray.length ax1) in *.
  assert (Lx2' : List.length x2 = List.length x1) by lia.
  assert (Ly1' : List.length y1 = List.length x1) by lia.
  assert (Ly2' : List.length y2 = List.length x1) by lia.
  destruct (nodup_parts x1 x2 Hxd Lx2') as [Dx Dx12].
  destruct (nodup_parts y1 y2 Hyd ltac:(lia)) as [Dy Dy12].
  unfold len in Dy, Dy12. rewrite Ly1' in Dy, Dy12.
  (* reading the four arrays *)
  assert (G : forall j : int, ((φ j) < (φ n))%Z ->
     X1 ax1 j = entry x1 (Z.to_N (φ j)) /\ X2 ax2 j = entry x2 (Z.to_N (φ j)) /\
     Y1 ay1 j = entry y1 (Z.to_N (φ j)) /\ Y2 ay2 j = entry y2 (Z.to_N (φ j))).
  { intros j Hj. unfold X1, X2, Y1, Y2.
    split; [|split; [|split]];
      [exact (repr_get _ _ Rx1 j ltac:(lia)) | exact (repr_get _ _ Rx2 j ltac:(lia))
      |exact (repr_get _ _ Ry1 j ltac:(lia)) | exact (repr_get _ _ Ry2 j ltac:(lia))]. }
  assert (Bj : forall j : int, ((φ j) < (φ n))%Z -> (Z.to_N (φ j) < len x1)%N).
  { intros j Hj. unfold len. lia. }
  assert (Inj : forall i j : int, i <> j -> Z.to_N (φ i) <> Z.to_N (φ j)).
  { intros i j Nij E. apply Nij. apply to_Z_inj.
    pose proof (to_Z_bounded i). pose proof (to_Z_bounded j). lia. }
  exists (intersecting_rectangles_impl ax1 ay1 ax2 ay2).
  split; [reflexivity|].
  unfold intersecting_rectangles_spec, intersecting_rectangles_impl.
  apply bool_match_of_iff.
  fold n.
  unshelve refine (iff_trans (impl_iff n ax1 ay1 ax2 ay2 _ _ _ _ _ _ _) _).
  - lia.
  - intros j Hj. destruct (G j Hj) as (A1 & A2 & _ & _). rewrite A1, A2.
    apply Hxo. auto.
  - intros j Hj. destruct (G j Hj) as (_ & _ & A3 & A4). rewrite A3, A4.
    apply Hyo. auto.
  - intros i j Hi Hj Nij.
    destruct (G i Hi) as (A1 & A2 & _ & _). destruct (G j Hj) as (B1 & B2 & _ & _).
    rewrite A1, A2, B1, B2. apply Dx; auto.
  - intros i j Hi Hj.
    destruct (G i Hi) as (A1 & _ & _ & _). destruct (G j Hj) as (_ & B2 & _ & _).
    rewrite A1, B2. apply Dx12; auto.
  - intros i j Hi Hj Nij.
    destruct (G i Hi) as (_ & _ & A3 & A4). destruct (G j Hj) as (_ & _ & B3 & B4).
    rewrite A3, A4, B3, B4. apply Dy; auto.
  - intros i j Hi Hj.
    destruct (G i Hi) as (_ & _ & A3 & _). destruct (G j Hj) as (_ & _ & _ & B4).
    rewrite A3, B4. apply Dy12; auto.
  - rewrite (geometry x1 y1 x2 y2).
    + split.
      * intros (i & j & Hi & Hj & [Cx Cy]).
        destruct (G i Hi) as (A1 & A2 & A3 & A4).
        destruct (G j Hj) as (B1 & B2 & B3 & B4).
        exists (Z.to_N (φ i)), (Z.to_N (φ j)). split; [auto|]. split; [auto|].
        unfold crossN. rewrite <- A1, <- A2, <- A3, <- A4, <- B1, <- B2, <- B3, <- B4.
        split; assumption.
      * intros (i & j & Hi & Hj & [Cx Cy]).
        unfold len in Hi, Hj.
        set (ii := of_Z (Z.of_N i)). set (jj := of_Z (Z.of_N j)).
        assert (Ei : (φ ii) = Z.of_N i)
          by (unfold ii; rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
        assert (Ej : (φ jj) = Z.of_N j)
          by (unfold jj; rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
        destruct (G ii ltac:(lia)) as (A1 & A2 & A3 & A4).
        destruct (G jj ltac:(lia)) as (B1 & B2 & B3 & B4).
        rewrite Ei, N2Z.id in A1, A2, A3, A4. rewrite Ej, N2Z.id in B1, B2, B3, B4.
        exists ii, jj. split; [lia|]. split; [lia|].
        unfold crossM. rewrite A1, A2, A3, A4, B1, B2, B3, B4.
        split; assumption.
    + intros i Hi. apply Hxo. exact Hi.
    + intros i Hi. apply Hyo. exact Hi.
    + exact Dx.
    + exact Dx12.
    + exact Dy.
    + exact Dy12.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition intersecting_rectangles :
  array sint -> array sint -> array sint -> array sint -> bool :=
  intersecting_rectangles_impl.

Definition intersecting_rectangles_correct :
  forall (x1 y1 x2 y2 : list Z) (ax1 ay1 ax2 ay2 : array sint),
  valid_input x1 y1 x2 y2 ->
  repr ax1 x1 -> repr ay1 y1 -> repr ax2 x2 -> repr ay2 y2 ->
  exists b : bool,
    repr (intersecting_rectangles ax1 ay1 ax2 ay2) b /\
    intersecting_rectangles_spec x1 y1 x2 y2 b
  := intersecting_rectangles_impl_correct.
