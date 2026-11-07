(* Implementation of selfbalancingbst (selfbalancingbst.spec): an
   order-statistic red-black tree, persistent, one per instance.

   Code.  [tree] is a red-black tree whose nodes carry the colour, the key,
   the value and the subtree size (CLRS 13 and 14.1).  Every node is built
   by [node], which recomputes the size from the two children, so rank,
   k-th and size read the sizes and never walk the tree.  Insertion is
   Okasaki's balance on the way up ([lbal]/[rbal]); deletion is Kahrs'
   functional red-black delete ([del], [append], [lbalS]/[rbalS]), the
   algorithm of Stdlib's MSetRBT, here with values and sizes.  The trees
   are purely functional, so the copy command shares the source tree in
   O(1).  The 1001 instances (index 0 unused) live in two flat PArrays,
   the trees and the cursors (an option key, re-searched from the root
   when used); the commands are read in one left-to-right pass, the arrays
   and the output array threaded linearly.  A first pass counts the output
   lines (r, g, z) to allocate the output.

   Termination: structural recursion on the tree for the tree operations;
   the two command loops recurse on an erased [Acc (Zwf 0) (gap q j)]
   proof, as in template/polymul1.  No nat, no Z in the code.

   Proof.  [elements t] is the in-order list of (key, value) pairs read
   through Sint63.to_Z; every tree operation is proven against the spec's
   list operation on [elements] (given that the list is sorted by key, an
   invariant all operations preserve as a consequence), and [wf] says that
   every stored size is the sum of its children's plus one, which makes
   the size field the length of [elements] modulo 2^63.  The colours are
   not part of any invariant: the balance is the algorithm's business, the
   contract only needs the contents. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The trees                                                           *)
(* ------------------------------------------------------------------ *)

Inductive color := Red | Black.

(* Node colour left key value size right. *)
Inductive tree :=
| Leaf
| Node (c : color) (l : tree) (k v s : int) (r : tree).

Definition size (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ _ s _ => s end.

Definition node (c : color) (l : tree) (k v : int) (r : tree) : tree :=
  Node c l k v (size l + size r + 1) r.

Definition key_lt (a b : int) : bool := Sint63.ltb a b.

Definition makeBlack (t : tree) : tree :=
  match t with Leaf => Leaf | Node _ l k v s r => Node Black l k v s r end.

Definition makeRed (t : tree) : tree :=
  match t with Leaf => Leaf | Node _ l k v s r => Node Red l k v s r end.

Definition lbal (l : tree) (k v : int) (r : tree) : tree :=
  match l with
  | Node Red (Node Red a x vx _ b) y vy _ c =>
      node Red (node Black a x vx b) y vy (node Black c k v r)
  | Node Red a x vx _ (Node Red b y vy _ c) =>
      node Red (node Black a x vx b) y vy (node Black c k v r)
  | _ => node Black l k v r
  end.

Definition rbal (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red (Node Red b y vy _ c) z vz _ d =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | Node Red b y vy _ (Node Red c z vz _ d) =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | _ => node Black l k v r
  end.

Definition rbal' (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red b y vy _ (Node Red c z vz _ d) =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | Node Red (Node Red b y vy _ c) z vz _ d =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | _ => node Black l k v r
  end.

(* Insertion below the root (the root is blackened by [insert]). *)
Fixpoint ins (x vx : int) (t : tree) : tree :=
  match t with
  | Leaf => node Red Leaf x vx Leaf
  | Node c l y vy _ r =>
      if key_lt x y then
        match c with
        | Red => node Red (ins x vx l) y vy r
        | Black => lbal (ins x vx l) y vy r
        end
      else if x =? y then t
      else
        match c with
        | Red => node Red l y vy (ins x vx r)
        | Black => rbal l y vy (ins x vx r)
        end
  end.

Definition insert_t (x vx : int) (t : tree) : tree := makeBlack (ins x vx t).

(* Kahrs' deletion. *)
Definition lbalS (l : tree) (k v : int) (r : tree) : tree :=
  match l with
  | Node Red a x vx _ b => node Red (node Black a x vx b) k v r
  | _ =>
      match r with
      | Node Black a y vy _ b => rbal' l k v (node Red a y vy b)
      | Node Red (Node Black a y vy _ b) z vz _ c =>
          node Red (node Black l k v a) y vy (rbal' b z vz (makeRed c))
      | _ => node Red l k v r
      end
  end.

Definition rbalS (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red b y vy _ c => node Red l k v (node Black b y vy c)
  | _ =>
      match l with
      | Node Black a x vx _ b => lbal (node Red a x vx b) k v r
      | Node Red a x vx _ (Node Black b y vy _ c) =>
          node Red (lbal (makeRed a) x vx b) y vy (node Black c k v r)
      | _ => node Red l k v r
      end
  end.

Fixpoint append (l : tree) : tree -> tree :=
  match l with
  | Leaf => fun r => r
  | Node lc ll lx lv _ lr =>
      fix append_l (r : tree) : tree :=
        match r with
        | Leaf => l
        | Node rc rl rx rv _ rr =>
            match lc, rc with
            | Red, Red =>
                let lrl := append lr rl in
                match lrl with
                | Node Red lr' x vx _ rl' =>
                    node Red (node Red ll lx lv lr') x vx (node Red rl' rx rv rr)
                | _ => node Red ll lx lv (node Red lrl rx rv rr)
                end
            | Black, Black =>
                let lrl := append lr rl in
                match lrl with
                | Node Red lr' x vx _ rl' =>
                    node Red (node Black ll lx lv lr') x vx (node Black rl' rx rv rr)
                | _ => lbalS ll lx lv (node Black lrl rx rv rr)
                end
            | Black, Red => node Red (append_l rl) rx rv rr
            | Red, Black => node Red ll lx lv (append lr r)
            end
        end
  end.

Fixpoint del (x : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node _ a y vy _ b =>
      if key_lt x y then
        match a with
        | Node Black _ _ _ _ _ => lbalS (del x a) y vy b
        | _ => node Red (del x a) y vy b
        end
      else if x =? y then append a b
      else
        match b with
        | Node Black _ _ _ _ _ => rbalS a y vy (del x b)
        | _ => node Red a y vy (del x b)
        end
  end.

Definition delete_t (x : int) (t : tree) : tree := makeBlack (del x t).

(* The queries: each returns a key (or nothing). *)
Fixpoint find_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt x k then find_t x l
      else if x =? k then Some k
      else find_t x r
  end.

(* the first key >= x *)
Fixpoint lower_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt k x then lower_t x r
      else match lower_t x l with Some z => Some z | None => Some k end
  end.

(* the first key > x *)
Fixpoint upper_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt x k then
        match upper_t x l with Some z => Some z | None => Some k end
      else upper_t x r
  end.

(* the last key < x *)
Fixpoint pred_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt k x then
        match pred_t x r with Some z => Some z | None => Some k end
      else pred_t x l
  end.

Fixpoint front_t (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ _ =>
      match front_t l with Some z => Some z | None => Some k end
  end.

Fixpoint back_t (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ _ k _ _ r =>
      match back_t r with Some z => Some z | None => Some k end
  end.

(* the key at 0-based position n, through the sizes *)
Fixpoint kth_t (n : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      let sl := size l in
      if n <? sl then kth_t n l
      else if n =? sl then Some k
      else kth_t (n - sl - 1) r
  end.

(* the number of keys < x, through the sizes *)
Fixpoint rank_t (x : int) (t : tree) : int :=
  match t with
  | Leaf => 0
  | Node _ l k _ _ r =>
      if key_lt x k then rank_t x l
      else if x =? k then size l
      else size l + 1 + rank_t x r
  end.

Fixpoint lookup_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k v _ r =>
      if key_lt x k then lookup_t x l
      else if x =? k then Some v
      else lookup_t x r
  end.

(* the value of key x becomes w (same shape, same sizes) *)
Fixpoint setv_t (x w : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node c l k v s r =>
      if key_lt x k then Node c (setv_t x w l) k v s r
      else if x =? k then Node c l k w s r
      else Node c l k v s (setv_t x w r)
  end.

(* ------------------------------------------------------------------ *)
(* The command loop                                                    *)
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

Definition is_out (op : int) : bool := (op =? 114) || (op =? 103) || (op =? 122).

(* acc + the number of output commands among j .. q-1 *)
Fixpoint count_loop (ops : array int) (q j acc : int)
    (H : Acc (Zwf 0) (gap q j)) {struct H} : int :=
  match bdec (j <? q) with
  | left Hj =>
      count_loop ops q (j + 1) (if is_out ops.[j] then acc + 1 else acc)
        (Acc_inv H (dec_step q j Hj))
  | right _ => acc
  end.

Definition on_cur (cur : option int) (f : int -> option int) : option int :=
  match cur with None => None | Some c => f c end.

(* One command on the instance array T, the cursor array C and the output
   array O, whose next free cell is p. *)
Definition exec (T : array tree) (C : array (option int))
    (O : array (option int)) (p id op x y : int)
    : array tree * array (option int) * array (option int) * int :=
  let t := T.[id] in
  let cur := C.[id] in
  if op =? 97 then (T.[id <- T.[x]], C.[id <- None], O, p)
  else if op =? 63 then (T, C.[id <- find_t x t], O, p)
  else if op =? 108 then (T, C.[id <- lower_t x t], O, p)
  else if op =? 117 then (T, C.[id <- upper_t x t], O, p)
  else if op =? 105 then (T.[id <- insert_t x y t], C.[id <- Some x], O, p)
  else if op =? 101 then
    (T.[id <- match cur with None => t | Some c => delete_t c t end],
     C.[id <- None], O, p)
  else if op =? 102 then (T, C.[id <- front_t t], O, p)
  else if op =? 98 then (T, C.[id <- back_t t], O, p)
  else if op =? 62 then (T, C.[id <- on_cur cur (fun c => upper_t c t)], O, p)
  else if op =? 60 then (T, C.[id <- on_cur cur (fun c => pred_t c t)], O, p)
  else if op =? 107 then
    (T, C.[id <- if Sint63.ltb x 0 then None else kth_t x t], O, p)
  else if op =? 114 then
    (T, C, O.[p <- on_cur cur (fun c => Some (rank_t c t))], p + 1)
  else if op =? 103 then
    (T, C, O.[p <- on_cur cur (fun c => lookup_t c t)], p + 1)
  else if op =? 115 then
    (T.[id <- match cur with None => t | Some c => setv_t c x t end], C, O, p)
  else if op =? 122 then (T, C, O.[p <- Some (size t)], p + 1)
  else (T, C, O, p).

Fixpoint run_loop (ids ops xs ys : array int) (q j : int)
    (T : array tree) (C : array (option int)) (O : array (option int)) (p : int)
    (H : Acc (Zwf 0) (gap q j)) {struct H} : array (option int) :=
  match bdec (j <? q)%uint63 with
  | left Hj =>
      let '(T', C', O', p') := exec T C O p ids.[j] ops.[j] xs.[j] ys.[j] in
      run_loop ids ops xs ys q (j + 1)%uint63 T' C' O' p'
        (Acc_inv H (dec_step q j Hj))
  | right _ => O
  end.

Definition run_impl (ids ops : array uint) (xs ys : array sint)
    : array (option sint) :=
  let q := PArray.length ids in
  let n := count_loop ops q 0 0 (Zwf_well_founded 0 (gap q 0)) in
  run_loop ids ops xs ys q 0 (PArray.make 1001 Leaf) (PArray.make 1001 None)
    (PArray.make n None) 0 (Zwf_well_founded 0 (gap q 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: the tree layer                                           *)
(* ------------------------------------------------------------------ *)

Local Notation zs := Sint63.to_Z.

Fixpoint elements (t : tree) : entries :=
  match t with
  | Leaf => []
  | Node _ l k v _ r => elements l ++ (zs k, zs v) :: elements r
  end.

Fixpoint wf (t : tree) : Prop :=
  match t with
  | Leaf => True
  | Node _ l _ _ s r => wf l /\ wf r /\ s = size l + size r + 1
  end.

Ltac lnorm := repeat progress (simpl; rewrite <- ?app_assoc); reflexivity.
Ltac des := repeat match goal with
  | |- context [match ?t with _ => _ end] => destruct t
  end.
Ltac wfsolve := unfold node, makeRed, makeBlack in *; simpl in *; intuition.

Lemma elements_node : forall c l k v r,
  elements (node c l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. reflexivity. Qed.

Lemma wf_node : forall c l k v r, wf l -> wf r -> wf (node c l k v r).
Proof. intros; simpl; auto. Qed.

Lemma elements_makeBlack : forall t, elements (makeBlack t) = elements t.
Proof. destruct t; reflexivity. Qed.
Lemma elements_makeRed : forall t, elements (makeRed t) = elements t.
Proof. destruct t; reflexivity. Qed.
Lemma wf_makeBlack : forall t, wf t -> wf (makeBlack t).
Proof. destruct t; simpl; auto. Qed.
Lemma wf_makeRed : forall t, wf t -> wf (makeRed t).
Proof. destruct t; simpl; auto. Qed.

Lemma elements_lbal : forall l k v r,
  elements (lbal l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. intros; unfold lbal; des; lnorm. Qed.
Lemma elements_rbal : forall l k v r,
  elements (rbal l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. intros; unfold rbal; des; lnorm. Qed.
Lemma elements_rbal' : forall l k v r,
  elements (rbal' l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. intros; unfold rbal'; des; lnorm. Qed.

Lemma wf_lbal : forall l k v r, wf l -> wf r -> wf (lbal l k v r).
Proof. intros; unfold lbal; des; wfsolve. Qed.
Lemma wf_rbal : forall l k v r, wf l -> wf r -> wf (rbal l k v r).
Proof. intros; unfold rbal; des; wfsolve. Qed.
Lemma wf_rbal' : forall l k v r, wf l -> wf r -> wf (rbal' l k v r).
Proof. intros; unfold rbal'; des; wfsolve. Qed.

Arguments lbal : simpl never.
Arguments rbal : simpl never.
Arguments rbal' : simpl never.
Arguments makeRed : simpl never.

Ltac lnorm2 := repeat progress (simpl; rewrite ?elements_lbal, ?elements_rbal',
  ?elements_node, ?elements_makeRed, <- ?app_assoc); reflexivity.

Lemma elements_lbalS : forall l k v r,
  elements (lbalS l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof.
  intros; unfold lbalS; des;
    lnorm2.
Qed.
Lemma elements_rbalS : forall l k v r,
  elements (rbalS l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof.
  intros; unfold rbalS; des;
    lnorm2.
Qed.
Lemma wf_lbalS : forall l k v r, wf l -> wf r -> wf (lbalS l k v r).
Proof.
  intros; unfold lbalS; des; try apply wf_rbal'; try apply wf_node;
    try apply wf_rbal'; try apply wf_makeRed; wfsolve.
Qed.
Lemma wf_rbalS : forall l k v r, wf l -> wf r -> wf (rbalS l k v r).
Proof.
  intros; unfold rbalS; des; try apply wf_lbal; try apply wf_node;
    try apply wf_lbal; try apply wf_makeRed; wfsolve.
Qed.

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Sorted lists of entries                                             *)
(* ------------------------------------------------------------------ *)

Definition keys_lt (c : Z) (l : entries) : Prop := Forall (fun e => fst e < c) l.
Definition keys_gt (c : Z) (l : entries) : Prop := Forall (fun e => c < fst e) l.

Fixpoint srt (l : entries) : Prop :=
  match l with
  | [] => True
  | e :: l' => keys_gt (fst e) l' /\ srt l'
  end.

Lemma keys_gt_weaken : forall a b l, a <= b -> keys_gt b l -> keys_gt a l.
Proof.
  intros a b l H1 H2. unfold keys_gt in *. eapply Forall_impl; [|exact H2].
  intros e He; simpl in He; lia.
Qed.

Lemma keys_lt_weaken : forall a b l, b <= a -> keys_lt b l -> keys_lt a l.
Proof.
  intros a b l H1 H2. unfold keys_lt in *. eapply Forall_impl; [|exact H2].
  intros e He; simpl in He; lia.
Qed.

Lemma srt_app : forall a e b,
  srt (a ++ e :: b) <->
  srt a /\ srt b /\ keys_lt (fst e) a /\ keys_gt (fst e) b.
Proof.
  induction a as [|x a IH]; intros e b; simpl.
  - unfold keys_lt. intuition.
  - rewrite IH. unfold keys_gt, keys_lt. rewrite Forall_app, !Forall_cons_iff.
    split.
    + intros [[H1 [H2 H3]] [H4 [H5 [H6 H7]]]]. intuition.
    + intros [[H1 H2] [H3 [H4 H5]]].
      destruct H4 as [H4 H4'].
      repeat split; auto.
      eapply Forall_impl; [|exact H5]. intros e' He'. simpl in *. lia.
Qed.

Lemma srt_node : forall l k v r,
  srt (elements l ++ (k, v) :: elements r) ->
  srt (elements l) /\ srt (elements r) /\
  keys_lt k (elements l) /\ keys_gt k (elements r).
Proof. intros l k v r H. apply srt_app in H. exact H. Qed.

Lemma Forall_insert : forall (P : Z * Z -> Prop) k v l,
  P (k, v) -> Forall P l -> Forall P (insert k v l).
Proof.
  intros P k v l Hk. induction l as [|[k' v'] l IH]; intros Hl; simpl.
  - constructor; auto.
  - inversion Hl; subst.
    destruct (k <? k') eqn:E1; [constructor; auto|].
    destruct (k =? k') eqn:E2; [constructor; auto|]. constructor; auto.
Qed.

Lemma srt_insert : forall k v l, srt l -> srt (insert k v l).
Proof.
  intros k v l. induction l as [|[k' v'] l IH]; intros Hl; simpl.
  - split; [constructor | exact I].
  - destruct Hl as [Hg Hs].
    destruct (k <? k') eqn:E1.
    + apply Z.ltb_lt in E1. simpl. split; [|split; auto].
      constructor; [simpl; lia|]. eapply keys_gt_weaken; [|exact Hg]. simpl; lia.
    + destruct (k =? k') eqn:E2; [simpl; split; auto|].
      apply Z.ltb_ge in E1. apply Z.eqb_neq in E2. simpl. split; [|auto].
      apply Forall_insert; [simpl; lia | exact Hg].
Qed.

Lemma length_insert : forall k v l, (List.length (insert k v l) <= S (List.length l))%nat.
Proof.
  intros k v l. induction l as [|[k' v'] l IH]; simpl; [lia|].
  destruct (k <? k'); [simpl; lia|]. destruct (k =? k'); simpl; lia.
Qed.

Lemma insert_app_lt : forall k v a x b, k < fst x ->
  insert k v (a ++ x :: b) = insert k v a ++ x :: b.
Proof.
  intros k v a x b H. induction a as [|[k' v'] a IH]; simpl.
  - destruct x as [kx vx]; simpl in H.
    replace (k <? kx) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct (k <? k'); [reflexivity|]. destruct (k =? k'); [reflexivity|].
    rewrite IH. reflexivity.
Qed.

Lemma insert_app_gt : forall k v a b, keys_lt k a ->
  insert k v (a ++ b) = a ++ insert k v b.
Proof.
  intros k v a b H. induction a as [|[k' v'] a IH]; simpl; [reflexivity|].
  inversion H; subst. simpl in *.
  replace (k <? k') with false by (symmetry; apply Z.ltb_ge; lia).
  replace (k =? k') with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite IH by auto. reflexivity.
Qed.

Lemma erase_app : forall c a b, erase c (a ++ b) = erase c a ++ erase c b.
Proof. intros. unfold erase. apply filter_app. Qed.

Lemma erase_none : forall c a, Forall (fun e => fst e <> c) a -> erase c a = a.
Proof.
  intros c a H. unfold erase. induction H as [|e a He Ha IH]; simpl; [reflexivity|].
  replace (fst e =? c) with false by (symmetry; apply Z.eqb_neq; exact He).
  simpl. rewrite IH. reflexivity.
Qed.

Lemma keys_lt_ne : forall c a, keys_lt c a -> Forall (fun e => fst e <> c) a.
Proof. intros c a H. eapply Forall_impl; [|exact H]. intros e He; simpl in He; lia. Qed.
Lemma keys_gt_ne : forall c a, keys_gt c a -> Forall (fun e => fst e <> c) a.
Proof. intros c a H. eapply Forall_impl; [|exact H]. intros e He; simpl in He; lia. Qed.

Lemma Forall_filter' : forall (P : Z * Z -> Prop) f l,
  Forall P l -> Forall P (filter f l).
Proof.
  intros P f l H. induction H as [|e l He Hl IH]; simpl; [constructor|].
  destruct (f e); [constructor|]; auto.
Qed.

Lemma srt_filter : forall f l, srt l -> srt (filter f l).
Proof.
  intros f l. induction l as [|e l IH]; intros Hl; simpl; [exact I|].
  destruct Hl as [Hg Hs]. destruct (f e); simpl; auto.
  split; auto. apply Forall_filter'. exact Hg.
Qed.

Lemma length_erase : forall c l, (List.length (erase c l) <= List.length l)%nat.
Proof. intros. unfold erase. apply filter_length_le. Qed.

Lemma first_key_app : forall p a b,
  first_key p (a ++ b) =
  match first_key p a with Some z => Some z | None => first_key p b end.
Proof.
  intros p a b. induction a as [|[k v] a IH]; simpl; [reflexivity|].
  destruct (p k); [reflexivity | exact IH].
Qed.

Lemma first_key_none : forall (p : Z -> bool) a,
  Forall (fun e => p (fst e) = false) a -> first_key p a = None.
Proof.
  intros p a H. induction H as [|[k v] a He Ha IH]; simpl in *; [reflexivity|].
  rewrite He. exact IH.
Qed.

(* ------------------------------------------------------------------ *)
(* Keys                                                                *)
(* ------------------------------------------------------------------ *)

Lemma key_trichotomy : forall x y : int,
  (key_lt x y = true /\ zs x < zs y) \/
  (key_lt x y = false /\ (x =? y)%uint63 = true /\ zs x = zs y) \/
  (key_lt x y = false /\ (x =? y)%uint63 = false /\ zs y < zs x).
Proof.
  intros x y. unfold key_lt.
  destruct (Sint63.ltb x y) eqn:E1.
  - left. split; [reflexivity|]. apply Sint63.ltb_spec. exact E1.
  - right. assert (H1 : ~ zs x < zs y)
      by (intro H; apply Sint63.ltb_spec in H; congruence).
    destruct (x =? y)%uint63 eqn:E2.
    + left. apply eqb_spec in E2. subst. auto.
    + right. repeat split; auto.
      assert (zs x <> zs y); [|lia].
      intro H. apply Sint63.to_Z_inj in H. subst.
      rewrite eqb_refl in E2. discriminate.
Qed.

Ltac kcase x y :=
  destruct (key_trichotomy x y) as [[E1 Hxy]|[[E1 [E2 Hxy]]|[E1 [E2 Hxy]]]];
  rewrite ?E1, ?E2.

(* ------------------------------------------------------------------ *)
(* Insertion                                                           *)
(* ------------------------------------------------------------------ *)

Lemma elements_ins : forall x vx t, srt (elements t) ->
  elements (ins x vx t) = insert (zs x) (zs vx) (elements t).
Proof.
  intros x vx t. induction t as [|c l IHl y vy s r IHr]; intros Hs;
    [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [ins elements]. kcase x y.
  - assert (H : elements (match c with
                          | Red => node Red (ins x vx l) y vy r
                          | Black => lbal (ins x vx l) y vy r end)
                = elements (ins x vx l) ++ (zs y, zs vy) :: elements r)
      by (destruct c; [apply elements_node | apply elements_lbal]).
    rewrite H, IHl by exact Hl.
    rewrite insert_app_lt by (simpl; lia). reflexivity.
  - rewrite insert_app_gt by (rewrite Hxy; exact Hlt).
    cbn [insert]. rewrite Hxy, Z.ltb_irrefl, Z.eqb_refl. reflexivity.
  - assert (H : elements (match c with
                          | Red => node Red l y vy (ins x vx r)
                          | Black => rbal l y vy (ins x vx r) end)
                = elements l ++ (zs y, zs vy) :: elements (ins x vx r))
      by (destruct c; [apply elements_node | apply elements_rbal]).
    rewrite H, IHr by exact Hr.
    rewrite insert_app_gt by (eapply keys_lt_weaken; [|exact Hlt]; lia).
    cbn [insert].
    replace (zs x <? zs y) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (zs x =? zs y) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
Qed.

Lemma wf_ins : forall x vx t, wf t -> wf (ins x vx t).
Proof.
  intros x vx t. induction t as [|c l IHl y vy s r IHr]; intros Hw;
    [simpl; auto|].
  pose proof Hw as Hw'. cbn [wf] in Hw'. destruct Hw' as [Hl [Hr _]].
  cbn [ins]. destruct (key_lt x y); [|destruct (x =? y)%uint63; [exact Hw|]];
    destruct c; auto using wf_node, wf_lbal, wf_rbal.
Qed.

Lemma elements_insert_t : forall x vx t, srt (elements t) ->
  elements (insert_t x vx t) = insert (zs x) (zs vx) (elements t).
Proof. intros. unfold insert_t. rewrite elements_makeBlack. apply elements_ins; auto. Qed.

Lemma wf_insert_t : forall x vx t, wf t -> wf (insert_t x vx t).
Proof. intros. unfold insert_t. apply wf_makeBlack, wf_ins; auto. Qed.

(* ------------------------------------------------------------------ *)
(* Deletion                                                            *)
(* ------------------------------------------------------------------ *)

Lemma append_NN : forall lc ll lx lv ls lr rc rl rx rv rs rr,
  append (Node lc ll lx lv ls lr) (Node rc rl rx rv rs rr) =
  match lc, rc with
  | Red, Red =>
      match append lr rl with
      | Node Red lr' x vx _ rl' =>
          node Red (node Red ll lx lv lr') x vx (node Red rl' rx rv rr)
      | lrl => node Red ll lx lv (node Red lrl rx rv rr)
      end
  | Black, Black =>
      match append lr rl with
      | Node Red lr' x vx _ rl' =>
          node Red (node Black ll lx lv lr') x vx (node Black rl' rx rv rr)
      | lrl => lbalS ll lx lv (node Black lrl rx rv rr)
      end
  | Black, Red => node Red (append (Node lc ll lx lv ls lr) rl) rx rv rr
  | Red, Black => node Red ll lx lv (append lr (Node rc rl rx rv rs rr))
  end.
Proof.
  intros. destruct lc, rc; try reflexivity;
    simpl; destruct (append lr rl) as [|[] ? ? ? ? ?]; reflexivity.
Qed.

Ltac red_case :=
  match goal with
  | IHm : elements (Node Red ?a (?x) (?vx) _ ?b) = elements ?lr ++ elements ?rl |- _ =>
      cbn [elements] in IHm;
      assert (K : forall T, elements a ++ (zs x, zs vx) :: elements b ++ T
                            = elements lr ++ elements rl ++ T)
        by (intro T; rewrite app_comm_cons, app_assoc, IHm, <- app_assoc; reflexivity);
      rewrite !elements_node; cbn [elements];
      repeat progress (simpl; rewrite <- ?app_assoc); rewrite K; reflexivity
  end.

Lemma elements_append : forall l r,
  elements (append l r) = elements l ++ elements r.
Proof.
  induction l as [|lc ll IHll lx lv ls lr IHlr]; intros r; [reflexivity|].
  induction r as [|rc rl IHrl rx rv rs rr IHrr].
  - simpl. rewrite app_nil_r. reflexivity.
  - rewrite append_NN. pose proof (IHlr rl) as IHm.
    remember (append lr rl) as m eqn:Em. clear Em.
    destruct lc, rc.
    + destruct m as [|[] a x vx s b];
        [rewrite !elements_node, IHm; lnorm | red_case | rewrite !elements_node, IHm; lnorm].
    + rewrite !elements_node, IHlr. lnorm.
    + rewrite !elements_node, IHrl. lnorm.
    + destruct m as [|[] a x vx s b];
        [rewrite elements_lbalS, !elements_node, IHm; lnorm | red_case
        | rewrite elements_lbalS, !elements_node, IHm; lnorm].
Qed.

Lemma wf_append : forall l r, wf l -> wf r -> wf (append l r).
Proof.
  induction l as [|lc ll IHll lx lv ls lr IHlr]; intros r Hl Hr; [exact Hr|].
  revert Hr. induction r as [|rc rl IHrl rx rv rs rr IHrr]; intros Hr; [exact Hl|].
  rewrite append_NN.
  pose proof Hl as Hl'. pose proof Hr as Hr'. cbn [wf] in Hl', Hr'.
  destruct Hl' as [Hll [Hlr _]]. destruct Hr' as [Hrl [Hrr _]].
  pose proof (IHlr rl Hlr Hrl) as Wm.
  remember (append lr rl) as m eqn:Em. clear Em.
  destruct lc, rc.
  - destruct m as [|[] a x vx s b]; wfsolve.
  - apply wf_node; [exact Hll|]. apply IHlr; auto.
  - apply wf_node; [apply IHrl; exact Hrl | exact Hrr].
  - destruct m as [|[] a x vx s b]; try (apply wf_lbalS); wfsolve.
Qed.

Lemma erase_cons : forall c e l,
  erase c (e :: l) = if fst e =? c then erase c l else e :: erase c l.
Proof. intros. unfold erase. simpl. destruct (fst e =? c); reflexivity. Qed.

Lemma elements_del : forall x t, srt (elements t) ->
  elements (del x t) = erase (zs x) (elements t).
Proof.
  intros x t. induction t as [|c a IHa y vy s b IHb]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Ha [Hb [Hlt Hgt]]].
  cbn [del elements]. rewrite erase_app, erase_cons. cbn [fst]. kcase x y.
  - assert (H : elements (match a with
                          | Node Black _ _ _ _ _ => lbalS (del x a) y vy b
                          | _ => node Red (del x a) y vy b end)
                = elements (del x a) ++ (zs y, zs vy) :: elements b)
      by (destruct a as [|[] ? ? ? ? ?];
          [apply elements_node | apply elements_node | apply elements_lbalS]).
    rewrite H, IHa by exact Ha.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (erase_none _ (elements b)); [reflexivity|].
    apply keys_gt_ne. eapply keys_gt_weaken; [|exact Hgt]. lia.
  - rewrite elements_append, Hxy, Z.eqb_refl.
    rewrite (erase_none _ (elements a)) by (apply keys_lt_ne; exact Hlt).
    rewrite (erase_none _ (elements b)) by (apply keys_gt_ne; exact Hgt).
    reflexivity.
  - assert (H : elements (match b with
                          | Node Black _ _ _ _ _ => rbalS a y vy (del x b)
                          | _ => node Red a y vy (del x b) end)
                = elements a ++ (zs y, zs vy) :: elements (del x b))
      by (destruct b as [|[] ? ? ? ? ?];
          [apply elements_node | apply elements_node | apply elements_rbalS]).
    rewrite H, IHb by exact Hb.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (erase_none _ (elements a)); [reflexivity|].
    apply keys_lt_ne. eapply keys_lt_weaken; [|exact Hlt]. lia.
Qed.

Lemma wf_del : forall x t, wf t -> wf (del x t).
Proof.
  intros x t. induction t as [|c a IHa y vy s b IHb]; intros Hw; [exact I|].
  pose proof Hw as Hw'. cbn [wf] in Hw'. destruct Hw' as [Ha [Hb _]].
  cbn [del]. destruct (key_lt x y).
  - destruct a as [|[] ? ? ? ? ?]; auto using wf_node, wf_lbalS.
  - destruct (x =? y)%uint63; [apply wf_append; auto|].
    destruct b as [|[] ? ? ? ? ?]; auto using wf_node, wf_rbalS.
Qed.

Lemma elements_delete_t : forall x t, srt (elements t) ->
  elements (delete_t x t) = erase (zs x) (elements t).
Proof. intros. unfold delete_t. rewrite elements_makeBlack. apply elements_del; auto. Qed.

Lemma wf_delete_t : forall x t, wf t -> wf (delete_t x t).
Proof. intros. unfold delete_t. apply wf_makeBlack, wf_del; auto. Qed.

(* ------------------------------------------------------------------ *)
(* Setting a value                                                     *)
(* ------------------------------------------------------------------ *)

Lemma set_value_none : forall c v l, Forall (fun e => fst e <> c) l ->
  set_value c v l = l.
Proof.
  intros c v l H. unfold set_value. induction H as [|e l He Hl IH]; simpl;
    [reflexivity|].
  replace (fst e =? c) with false by (symmetry; apply Z.eqb_neq; exact He).
  rewrite IH. reflexivity.
Qed.

Lemma set_value_app : forall c v a b,
  set_value c v (a ++ b) = set_value c v a ++ set_value c v b.
Proof. intros. unfold set_value. apply map_app. Qed.

Lemma elements_setv : forall x w t, srt (elements t) ->
  elements (setv_t x w t) = set_value (zs x) (zs w) (elements t).
Proof.
  intros x w t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [setv_t elements]. rewrite set_value_app. unfold set_value at 2.
  cbn [map fst]. fold (set_value (zs x) (zs w) (elements r)). kcase x y.
  - cbn [elements]. rewrite IHl by exact Hl.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (set_value_none _ _ (elements r)); [reflexivity|].
    apply keys_gt_ne. eapply keys_gt_weaken; [|exact Hgt]. lia.
  - cbn [elements]. rewrite Hxy, Z.eqb_refl.
    rewrite (set_value_none _ _ (elements l)) by (apply keys_lt_ne; exact Hlt).
    rewrite (set_value_none _ _ (elements r)) by (apply keys_gt_ne; exact Hgt).
    reflexivity.
  - cbn [elements]. rewrite IHr by exact Hr.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (set_value_none _ _ (elements l)); [reflexivity|].
    apply keys_lt_ne. eapply keys_lt_weaken; [|exact Hlt]. lia.
Qed.

Lemma size_setv : forall x w t, size (setv_t x w t) = size t.
Proof.
  intros x w [|c l k v s r]; [reflexivity|]. cbn [setv_t].
  destruct (key_lt x k); [reflexivity|]. destruct (x =? k)%uint63; reflexivity.
Qed.

Lemma wf_setv : forall x w t, wf t -> wf (setv_t x w t).
Proof.
  intros x w t. induction t as [|c l IHl y vy s r IHr]; intros Hw; [exact I|].
  cbn [wf] in Hw. destruct Hw as [Hl [Hr Hs]].
  cbn [setv_t]. destruct (key_lt x y); [|destruct (x =? y)%uint63];
    cbn [wf]; rewrite ?size_setv; auto.
Qed.

Lemma length_set_value : forall c v l, List.length (set_value c v l) = List.length l.
Proof. intros. unfold set_value. apply length_map. Qed.

Lemma srt_set_value : forall c v l, srt l -> srt (set_value c v l).
Proof.
  intros c v l. unfold set_value.
  assert (Hk : forall e, fst (if fst e =? c then (c, v) else e) = fst e).
  { intros e. destruct (fst e =? c) eqn:E; [apply Z.eqb_eq in E; simpl; lia|reflexivity]. }
  induction l as [|e l IH]; intros Hs; simpl; [exact I|].
  destruct Hs as [Hg Hs]. split; auto.
  rewrite Hk. unfold keys_gt in *. apply Forall_map.
  eapply Forall_impl; [|exact Hg]. intros e' He'. rewrite Hk. exact He'.
Qed.

(* ------------------------------------------------------------------ *)
(* The queries                                                         *)
(* ------------------------------------------------------------------ *)

Lemma key_lt_true : forall a b, key_lt a b = true -> zs a < zs b.
Proof. intros a b H. apply Sint63.ltb_spec. exact H. Qed.

Lemma key_lt_false : forall a b, key_lt a b = false -> zs b <= zs a.
Proof.
  intros a b H. destruct (Z.le_gt_cases (zs b) (zs a)) as [L|L]; [exact L|].
  apply Sint63.ltb_spec in L. unfold key_lt in H. congruence.
Qed.

Ltac kcase2 a b :=
  let E := fresh "E" in
  destruct (key_lt a b) eqn:E;
  [apply key_lt_true in E | apply key_lt_false in E].

Ltac fkn H :=
  apply first_key_none; eapply Forall_impl; [|exact H];
  let kk := fresh "kk" in let vv := fresh "vv" in let Hk := fresh "Hk" in
  intros [kk vv] Hk; simpl in *;
  first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; lia.

Lemma Forall_rev' : forall (P : Z * Z -> Prop) l, Forall P l -> Forall P (rev l).
Proof. intros. apply Forall_rev. exact H. Qed.

Lemma rev_node : forall (l : entries) e r,
  rev (l ++ e :: r) = rev r ++ e :: rev l.
Proof. intros. rewrite rev_app_distr. simpl. rewrite <- app_assoc. reflexivity. Qed.

Lemma find_t_spec : forall x t, srt (elements t) ->
  option_map zs (find_t x t) = first_key (fun k => k =? zs x) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [find_t elements]. rewrite first_key_app. cbn [first_key]. kcase x y.
  - rewrite IHl by exact Hl. destruct (first_key _ (elements l)); [reflexivity|].
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    symmetry. fkn Hgt.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    rewrite Hxy, Z.eqb_refl. reflexivity.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    apply IHr. exact Hr.
Qed.

Lemma lower_t_spec : forall x t, srt (elements t) ->
  option_map zs (lower_t x t) = first_key (fun k => zs x <=? k) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [lower_t elements]. rewrite first_key_app. cbn [first_key]. kcase2 y x.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    replace (zs x <=? zs y) with false by (symmetry; apply Z.leb_gt; lia).
    apply IHr. exact Hr.
  - rewrite <- IHl by exact Hl. destruct (lower_t x l); [reflexivity|].
    replace (zs x <=? zs y) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.

Lemma upper_t_spec : forall x t, srt (elements t) ->
  option_map zs (upper_t x t) = first_key (fun k => zs x <? k) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [upper_t elements]. rewrite first_key_app. cbn [first_key]. kcase2 x y.
  - rewrite <- IHl by exact Hl. destruct (upper_t x l); [reflexivity|].
    replace (zs x <? zs y) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    replace (zs x <? zs y) with false by (symmetry; apply Z.ltb_ge; lia).
    apply IHr. exact Hr.
Qed.

Lemma pred_t_spec : forall x t, srt (elements t) ->
  option_map zs (pred_t x t) = first_key (fun k => k <? zs x) (rev (elements t)).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  apply Forall_rev' in Hlt. apply Forall_rev' in Hgt.
  cbn [pred_t elements]. rewrite rev_node, first_key_app. cbn [first_key]. kcase2 y x.
  - rewrite <- IHr by exact Hr. destruct (pred_t x r); [reflexivity|].
    replace (zs y <? zs x) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - replace (first_key _ (rev (elements r))) with (@None Z) by (symmetry; fkn Hgt).
    replace (zs y <? zs x) with false by (symmetry; apply Z.ltb_ge; lia).
    apply IHl. exact Hl.
Qed.

Lemma front_t_spec : forall t,
  option_map zs (front_t t) = first_key (fun _ => true) (elements t).
Proof.
  induction t as [|c l IHl y vy s r IHr]; [reflexivity|].
  cbn [front_t elements]. rewrite first_key_app, <- IHl.
  destruct (front_t l); reflexivity.
Qed.

Lemma back_t_spec : forall t,
  option_map zs (back_t t) = first_key (fun _ => true) (rev (elements t)).
Proof.
  induction t as [|c l IHl y vy s r IHr]; [reflexivity|].
  cbn [back_t elements]. rewrite rev_node, first_key_app, <- IHr.
  destruct (back_t r); reflexivity.
Qed.

Lemma find_app' : forall (f : Z * Z -> bool) a b,
  find f (a ++ b) = match find f a with Some e => Some e | None => find f b end.
Proof.
  intros f a b. induction a as [|e a IH]; simpl; [reflexivity|].
  destruct (f e); [reflexivity | exact IH].
Qed.

Lemma find_none : forall (f : Z * Z -> bool) a,
  Forall (fun e => f e = false) a -> find f a = None.
Proof.
  intros f a H. induction H as [|e a He Ha IH]; simpl; [reflexivity|].
  rewrite He. exact IH.
Qed.

Ltac fdn H :=
  apply find_none; eapply Forall_impl; [|exact H];
  let kk := fresh "kk" in let vv := fresh "vv" in let Hk := fresh "Hk" in
  intros [kk vv] Hk; simpl in *; apply Z.eqb_neq; lia.

Lemma lookup_t_spec : forall x t, srt (elements t) ->
  option_map zs (lookup_t x t) = lookup (zs x) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  unfold lookup in *. cbn [lookup_t elements]. rewrite find_app'. cbn [find fst].
  kcase x y.
  - rewrite IHl by exact Hl. destruct (find _ (elements l)); [reflexivity|].
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (find _ (elements r)) with (@None (Z * Z)) by (symmetry; fdn Hgt).
    reflexivity.
  - replace (find _ (elements l)) with (@None (Z * Z)) by (symmetry; fdn Hlt).
    rewrite Hxy, Z.eqb_refl. reflexivity.
  - replace (find _ (elements l)) with (@None (Z * Z)) by (symmetry; fdn Hlt).
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    apply IHr. exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* Sizes, k-th and rank                                                *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma size_wf : forall t, wf t ->
  (φ (size t)) = Z.of_nat (List.length (elements t)) mod wB.
Proof.
  induction t as [|c l IHl y vy s r IHr]; intros Hw; [reflexivity|].
  cbn [wf] in Hw. destruct Hw as [Hl [Hr Hs]].
  cbn [size elements]. rewrite Hs, !add_spec, IHl, IHr by assumption.
  change (φ 1)%uint63 with 1. rewrite length_app. cbn [List.length].
  rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
  generalize (Z.of_nat (List.length (elements l))) (Z.of_nat (List.length (elements r))).
  intros A B. rewrite wB_val. Z.to_euclidean_division_equations. lia.
Qed.

Lemma size_len : forall t, wf t ->
  Z.of_nat (List.length (elements t)) < wB ->
  (φ (size t)) = Z.of_nat (List.length (elements t)).
Proof. intros t Hw Hl. rewrite size_wf by exact Hw. apply Z.mod_small. lia. Qed.

Lemma kth_t_spec : forall t n, wf t ->
  Z.of_nat (List.length (elements t)) < wB ->
  option_map zs (kth_t n t) = option_map fst (nth_error (elements t) (Z.to_nat (φ n))).
Proof.
  induction t as [|c l IHl y vy s r IHr]; intros n Hw Hb.
  - simpl. destruct (Z.to_nat (φ n)); reflexivity.
  - cbn [wf] in Hw. destruct Hw as [Hl [Hr _]].
    cbn [elements] in Hb |- *. rewrite length_app in Hb. cbn [List.length] in Hb.
    assert (Hsl : (φ (size l)) = Z.of_nat (List.length (elements l)))
      by (apply size_len; [exact Hl | lia]).
    pose proof (to_Z_bounded n) as Bn.
    cbn [kth_t].
    destruct (n <? size l)%uint63 eqn:E1.
    + rewrite ltb_spec in E1. rewrite nth_error_app1 by lia. apply IHl; [exact Hl | lia].
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
      destruct (n =? size l)%uint63 eqn:E2.
      * apply eqb_spec in E2. subst n.
        rewrite nth_error_app2 by lia.
        replace (Z.to_nat (φ (size l)) - List.length (elements l))%nat with 0%nat by lia.
        reflexivity.
      * assert (Hne : (φ n) <> (φ (size l)))
          by (intro E; apply to_Z_inj in E; rewrite E, eqb_refl in E2; discriminate).
        assert (Hsub : (φ (n - size l - 1)) = (φ n) - Z.of_nat (List.length (elements l)) - 1)
          by (rewrite <- Hsl; sia).
        rewrite IHr by (first [exact Hr | lia]).
        rewrite nth_error_app2 by lia.
        replace (Z.to_nat (φ n) - List.length (elements l))%nat
          with (S (Z.to_nat (φ (n - size l - 1)))) by lia.
        reflexivity.
Qed.

Lemma filter_none' : forall (f : Z * Z -> bool) l,
  Forall (fun e => f e = false) l -> filter f l = [].
Proof.
  intros f l H. induction H as [|e l He Hl IH]; simpl; [reflexivity|].
  rewrite He. exact IH.
Qed.

Lemma filter_all' : forall (f : Z * Z -> bool) l,
  Forall (fun e => f e = true) l -> filter f l = l.
Proof.
  intros f l H. induction H as [|e l He Hl IH]; simpl; [reflexivity|].
  rewrite He, IH. reflexivity.
Qed.

Lemma rank_t_spec : forall x t, wf t -> srt (elements t) ->
  Z.of_nat (List.length (elements t)) < wB ->
  (φ (rank_t x t)) = rank (zs x) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hw Hs Hb;
    [reflexivity|].
  cbn [wf] in Hw. destruct Hw as [Hl [Hr _]].
  cbn [elements] in Hs, Hb |- *. rewrite length_app in Hb. cbn [List.length] in Hb.
  apply srt_node in Hs. destruct Hs as [Sl [Sr [Hlt Hgt]]].
  assert (Hsl : (φ (size l)) = Z.of_nat (List.length (elements l)))
    by (apply size_len; [exact Hl | lia]).
  unfold rank. rewrite filter_app. cbn [filter fst]. rewrite length_app.
  cbn [rank_t]. kcase x y.
  - replace (zs y <? zs x) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (filter_none' _ (elements r)).
    + rewrite IHl by (first [assumption | lia]). unfold rank. simpl. lia.
    + eapply Forall_impl; [|exact Hgt]. intros [kk vv] Hk; simpl in *.
      apply Z.ltb_ge; lia.
  - replace (zs y <? zs x) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (filter_none' _ (elements r)).
    + rewrite (filter_all' _ (elements l)).
      * rewrite Hsl. simpl. lia.
      * eapply Forall_impl; [|exact Hlt]. intros [kk vv] Hk; simpl in *.
        apply Z.ltb_lt; lia.
    + eapply Forall_impl; [|exact Hgt]. intros [kk vv] Hk; simpl in *.
      apply Z.ltb_ge; lia.
  - replace (zs y <? zs x) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (filter_all' _ (elements l)).
    + rewrite !add_spec, Hsl, IHr by (first [assumption | lia]).
      unfold rank. change (φ 1)%uint63 with 1.
      pose proof (filter_length_le (fun e => fst e <? zs x) (elements r)).
      cbn [List.length].
      rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
    + eapply Forall_impl; [|exact Hlt]. intros [kk vv] Hk; simpl in *.
      apply Z.ltb_lt; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The instances                                                       *)
(* ------------------------------------------------------------------ *)

Lemma slength_set : forall (A : Set) (t : array A) i (a : A),
  PArray.length t.[i <- a] = PArray.length t.
Proof. intros. exact (PArray.length_set A t i a). Qed.
Lemma sget_set_same : forall (A : Set) (t : array A) i (a : A),
  (i <? PArray.length t)%uint63 = true -> t.[i <- a].[i] = a.
Proof. intros A t i a H. exact (PArray.get_set_same A t i a H). Qed.
Lemma sget_set_other : forall (A : Set) (t : array A) i j (a : A),
  i <> j -> t.[i <- a].[j] = t.[j].
Proof. intros A t i j a H. exact (PArray.get_set_other A t i j a H). Qed.
Lemma sget_make : forall (A : Set) (a : A) n i, (PArray.make n a).[i] = a.
Proof. intros. exact (PArray.get_make A a n i). Qed.
Lemma slength_make : forall (A : Set) n (a : A),
  PArray.length (PArray.make n a)
  = if (n <=? PArray.max_length)%uint63 then n else PArray.max_length.
Proof. intros. exact (PArray.length_make A n a). Qed.

(* Instance i is represented by tree t and cursor c, with at most b keys. *)
Definition inst_ok (i : inst) (t : tree) (c : option int) (b : Z) : Prop :=
  wf t /\ srt (elements t) /\ Z.of_nat (List.length (elements t)) <= b /\
  fst i = elements t /\ snd i = option_map zs c.

Record rel (s : state) (T : array tree) (C : array (option int)) (b : Z) : Prop := {
  rel_T : PArray.length T = 1001%uint63;
  rel_C : PArray.length C = 1001%uint63;
  rel_i : forall id : N, (id <= 1000)%N ->
            inst_ok (s id) T.[of_Z (Z.of_N id)] C.[of_Z (Z.of_N id)] b
}.

Definition upd (s : state) (id : N) (i : inst) : state :=
  fun j => if N.eqb j id then i else s j.

Lemma inst_ok_weaken : forall i t c b b', b <= b' -> inst_ok i t c b -> inst_ok i t c b'.
Proof. unfold inst_ok. intuition lia. Qed.

Lemma rel_weaken : forall s T C b b', b <= b' -> rel s T C b -> rel s T C b'.
Proof.
  intros s T C b b' Hb [H1 H2 H3]. constructor; auto.
  intros id Hid. eapply inst_ok_weaken; [exact Hb | auto].
Qed.

Lemma idx_eq : forall (idm : int) (id : N), (φ idm) = Z.of_N id -> of_Z (Z.of_N id) = idm.
Proof. intros idm id H. rewrite <- H. apply of_to_Z. Qed.

Lemma idx_ne : forall (idm : int) (id id' : N), (φ idm) = Z.of_N id ->
  (id' <= 1000)%N -> id' <> id -> idm <> of_Z (Z.of_N id').
Proof.
  intros idm id id' H Hb Hne E. apply Hne.
  assert ((φ idm) = (φ (of_Z (Z.of_N id')))) by (rewrite E; reflexivity).
  rewrite of_Z_spec, Z.mod_small in H0 by (rewrite wB_val; lia). lia.
Qed.

Lemma rel_set : forall s T C b b' (idm : int) (id : N) i t c,
  rel s T C b -> b <= b' -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok i t c b' ->
  rel (fun j => if N.eqb j id then i else s j) T.[idm <- t] C.[idm <- c] b'.
Proof.
  intros s T C b b' idm id i t c [HT HC Hi] Hb Hid Hidb Hok.
  assert (Hlt : (idm <? 1001)%uint63 = true) by (rewrite ltb_spec; change (φ 1001)%uint63 with 1001; lia).
  constructor.
  - rewrite slength_set. exact HT.
  - rewrite slength_set. exact HC.
  - intros id' Hid'. destruct (N.eqb_spec id' id) as [E|E].
    + subst id'. rewrite (idx_eq idm id Hid).
      rewrite !sget_set_same by (rewrite ?HT, ?HC; exact Hlt). exact Hok.
    + rewrite !sget_set_other by (apply (idx_ne idm id id'); auto).
      eapply inst_ok_weaken; [exact Hb | apply Hi; exact Hid'].
Qed.

Lemma rel_setC : forall s T C b b' (idm : int) (id : N) i c,
  rel s T C b -> b <= b' -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok i T.[idm] c b' ->
  rel (fun j => if N.eqb j id then i else s j) T C.[idm <- c] b'.
Proof.
  intros s T C b b' idm id i c [HT HC Hi] Hb Hid Hidb Hok.
  assert (Hlt : (idm <? 1001)%uint63 = true) by (rewrite ltb_spec; change (φ 1001)%uint63 with 1001; lia).
  constructor.
  - exact HT.
  - rewrite slength_set. exact HC.
  - intros id' Hid'. destruct (N.eqb_spec id' id) as [E|E].
    + subst id'. rewrite (idx_eq idm id Hid).
      rewrite !sget_set_same by (rewrite ?HT, ?HC; exact Hlt). exact Hok.
    + rewrite !sget_set_other by (apply (idx_ne idm id id'); auto).
      eapply inst_ok_weaken; [exact Hb | apply Hi; exact Hid'].
Qed.

Lemma rel_setT : forall s T C b b' (idm : int) (id : N) i t,
  rel s T C b -> b <= b' -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok i t C.[idm] b' ->
  rel (fun j => if N.eqb j id then i else s j) T.[idm <- t] C b'.
Proof.
  intros s T C b b' idm id i t [HT HC Hi] Hb Hid Hidb Hok.
  assert (Hlt : (idm <? 1001)%uint63 = true) by (rewrite ltb_spec; change (φ 1001)%uint63 with 1001; lia).
  constructor.
  - rewrite slength_set. exact HT.
  - exact HC.
  - intros id' Hid'. destruct (N.eqb_spec id' id) as [E|E].
    + subst id'. rewrite (idx_eq idm id Hid).
      rewrite !sget_set_same by (rewrite ?HT, ?HC; exact Hlt). exact Hok.
    + rewrite !sget_set_other by (apply (idx_ne idm id id'); auto).
      eapply inst_ok_weaken; [exact Hb | apply Hi; exact Hid'].
Qed.

Lemma rel_get : forall s T C b (idm : int) (id : N),
  rel s T C b -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok (s id) T.[idm] C.[idm] b.
Proof.
  intros s T C b idm id [_ _ Hi] Hid Hb. rewrite <- (idx_eq idm id Hid). auto.
Qed.

Lemma rel_init : rel init (PArray.make 1001 Leaf) (PArray.make 1001 None) 0.
Proof.
  constructor; [reflexivity | reflexivity |].
  intros id Hid. rewrite !sget_make. unfold inst_ok, init. simpl. intuition lia.
Qed.

(* ------------------------------------------------------------------ *)
(* One command                                                         *)
(* ------------------------------------------------------------------ *)

Lemma zs_small : forall a : int, 0 <= (φ a) < 2 ^ 62 -> zs a = (φ a).
Proof.
  intros a H. rewrite Sint63.to_Z_cmodwB. apply Sint63.cmod_small.
  rewrite wB_val. lia.
Qed.

Lemma phi_nonneg : forall a : int, 0 <= zs a -> (φ a) = zs a.
Proof.
  intros a H. rewrite <- Sint63.to_Z_mod_Uint63to_Z. apply Z.mod_small.
  pose proof (Sint63.to_Z_bounded a) as B.
  change (Sint63Axioms.to_Z Sint63.max_int) with 4611686018427387903 in B.
  rewrite wB_val. lia.
Qed.

Lemma repr_opt : forall (v : option int) (m : option Z),
  option_map zs v = m -> repr (v : option sint) m.
Proof.
  intros [a|] [m|] H; cbv [repr repr_option repr_sint]; simpl in *;
    try discriminate; try injection H; auto.
Qed.

Definition out_ok (o : list (option Z)) (O O' : array (option int)) (p p' : int) : Prop :=
  (o = [] /\ O' = O /\ p' = p) \/
  (exists (m : option Z) (v : option int),
     o = [m] /\ repr (v : option sint) m /\ O' = O.[p <- v] /\ p' = (p + 1)%uint63).

Definition valid_ops : list N :=
  [97; 63; 108; 117; 105; 101; 102; 98; 62; 60; 114; 107; 103; 115; 122]%N.

Ltac mv :=
  split; [|left; auto];
  eapply rel_setC; [eassumption | lia | eassumption | lia |];
  match goal with tt := ?v : tree |- _ => change v with tt end;
  unfold inst_ok; simpl; repeat split; auto; try lia; symmetry.

Lemma exec_correct : forall s T C O p b (idm opm xm ym : int) (id op : N) (x y : Z)
    s' o T' C' O' p',
  rel s T C b -> b < 4194304 ->
  (φ idm) = Z.of_N id -> (1 <= id <= 1000)%N ->
  (φ opm) = Z.of_N op -> In op valid_ops ->
  zs xm = x -> zs ym = y -> args_ok op x y ->
  step s (id, op, x, y) = (s', o) ->
  exec T C O p idm opm xm ym = (T', C', O', p') ->
  rel s' T' C' (b + 1) /\ out_ok o O O' p p'.
Proof.
  intros s T C O p b idm opm xm ym id op x y s' o T' C' O' p'
    Hr Hb Hid Hidb Hop Hin Hx Hy Ha Hs He.
  pose proof (rel_get s T C b idm id Hr Hid ltac:(lia)) as Hi.
  destruct Hi as (Wt & St & Lt & Ft & Ct).
  set (t := T.[idm]) in *. set (cur := C.[idm]) in *.
  assert (Lt' : Z.of_nat (List.length (elements t)) < wB) by (rewrite wB_val; lia).
  unfold step in Hs. destruct (s id) as [tm cm] eqn:Es. simpl in Ft, Ct. subst tm cm.
  unfold valid_ops in Hin.
  repeat destruct Hin as [Hin|Hin]; [| | | | | | | | | | | | | | | destruct Hin];
    subst op; unfold args_ok in Ha;
    (assert (Eop : opm = of_Z (Z.of_N _)) by (rewrite <- Hop; symmetry; apply of_to_Z));
    simpl in Eop; subst opm;
    unfold exec in He; simpl in He; fold t cur in He;
    injection He as <- <- <- <-; injection Hs as <- <-; subst x y;
    assert (Ecur : C.[idm] = cur) by reflexivity; clearbody cur.
  - (* a *)
    assert (Hxm : (φ xm) = zs xm) by (apply phi_nonneg; lia).
    pose proof (rel_get s T C b xm (Z.to_N (zs xm)) Hr ltac:(lia) ltac:(lia))
      as (W2 & S2 & L2 & F2 & C2).
    split; [|left; auto].
    eapply rel_set; [exact Hr | lia | exact Hid | lia |].
    unfold inst_ok; simpl; repeat split; auto; lia.
  - (* ? *) mv. apply find_t_spec. exact St.
  - (* l *) mv. apply lower_t_spec. exact St.
  - (* u *) mv. apply upper_t_spec. exact St.
  - (* i *)
    split; [|left; auto].
    eapply rel_set; [exact Hr | lia | exact Hid | lia |].
    pose proof (length_insert (zs xm) (zs ym) (elements t)).
    unfold inst_ok; simpl; rewrite elements_insert_t by exact St;
      repeat split; auto using wf_insert_t, srt_insert; lia.
  - (* e *)
    split; [|left; auto].
    eapply rel_set; [exact Hr | lia | exact Hid | lia |].
    destruct cur as [c|]; simpl.
    + pose proof (length_erase (zs c) (elements t)).
      unfold inst_ok; simpl; rewrite elements_delete_t by exact St;
        repeat split; auto using wf_delete_t; [apply srt_filter; exact St | lia].
    + unfold inst_ok; simpl; repeat split; auto; lia.
  - (* f *) mv. apply front_t_spec.
  - (* b *) mv. apply back_t_spec.
  - (* > *) mv. destruct cur as [c|]; [apply upper_t_spec; exact St | reflexivity].
  - (* < *) mv. destruct cur as [c|]; [apply pred_t_spec; exact St | reflexivity].
  - (* r *)
    split; [apply (rel_weaken s T C b); [lia | exact Hr]|].
    right. eexists; eexists; split; [reflexivity|]. split; [|split; reflexivity].
    apply repr_opt. destruct cur as [c|]; [|reflexivity]. simpl. f_equal.
    pose proof (rank_t_spec c t Wt St Lt') as Hk.
    pose proof (filter_length_le (fun e => fst e <? zs c) (elements t)).
    unfold rank in Hk. rewrite zs_small; [exact Hk | lia].
  - (* k *) mv. unfold kth.
    destruct (Sint63.ltb xm 0) eqn:E.
    + apply Sint63.ltb_spec in E. rewrite Sint63.to_Z_0 in E. change (zs xm < 0) in E.
      replace (0 <=? zs xm) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + assert (E' : 0 <= zs xm).
      { destruct (Z.le_gt_cases 0 (zs xm)) as [L|L]; [exact L|].
        rewrite <- Sint63.to_Z_0 in L. apply Sint63.ltb_spec in L. congruence. }
      replace (0 <=? zs xm) with true by (symmetry; apply Z.leb_le; lia).
      rewrite <- (phi_nonneg xm E'). apply kth_t_spec; assumption.
  - (* g *)
    split; [apply (rel_weaken s T C b); [lia | exact Hr]|].
    right. eexists; eexists; split; [reflexivity|]. split; [|split; reflexivity].
    apply repr_opt. destruct cur as [c|]; [|reflexivity]. simpl.
    apply lookup_t_spec. exact St.
  - (* s *)
    split; [|left; auto].
    eapply rel_setT; [exact Hr | lia | exact Hid | lia |].
    destruct cur as [c|]; simpl.
    + unfold inst_ok; simpl; rewrite elements_setv by exact St;
        repeat split; auto using wf_setv, srt_set_value;
        rewrite ?length_set_value, ?Ecur; [lia | reflexivity].
    + unfold inst_ok; simpl; rewrite Ecur; repeat split; auto; lia.
  - (* z *)
    split; [apply (rel_weaken s T C b); [lia | exact Hr]|].
    right. eexists; eexists; split; [reflexivity|]. split; [|split; reflexivity].
    apply repr_opt. simpl. f_equal.
    rewrite zs_small; rewrite size_len by assumption; [reflexivity | lia].
Qed.

Lemma step_len : forall s id op x y (opm : int),
  (φ opm) = Z.of_N op -> In op valid_ops ->
  List.length (snd (step s (id, op, x, y))) = if is_out opm then 1%nat else 0%nat.
Proof.
  intros s id op x y opm Hop Hin.
  unfold step. destruct (s id) as [t cur].
  unfold valid_ops in Hin.
  repeat destruct Hin as [Hin|Hin]; [| | | | | | | | | | | | | | | destruct Hin];
    subst op;
    (assert (Eop : opm = of_Z (Z.of_N _)) by (rewrite <- Hop; symmetry; apply of_to_Z));
    simpl in Eop; subst opm; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The loops                                                           *)
(* ------------------------------------------------------------------ *)

Lemma of_nat_phi : forall j : int, Uint63.of_nat (Z.to_nat (φ j)) = j.
Proof.
  intros j. rewrite Z2Nat.id by (pose proof (to_Z_bounded j); lia). apply of_to_Z.
Qed.

Lemma repr_get_u : forall (x : array uint) (l : list N) k, repr x l ->
  (k < List.length l)%nat -> (φ (x.[Uint63.of_nat k])) = Z.of_N (nth k l 0%N).
Proof.
  intros x l k [Hl Hc] Hk. destruct (Hc k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth _ _ _ Hm). unfold repr, repr_uint in Hr.
  rewrite <- Hr. rewrite Z2N.id by (apply to_Z_bounded). reflexivity.
Qed.

Lemma repr_get_s : forall (x : array sint) (l : list Z) k, repr x l ->
  (k < List.length l)%nat -> zs (x.[Uint63.of_nat k]) = nth k l 0.
Proof.
  intros x l k [Hl Hc] Hk. destruct (Hc k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth _ _ _ Hm). unfold repr, repr_sint in Hr.
  rewrite <- Hr. reflexivity.
Qed.

Lemma repr_len : forall {A M} `{Repr A M} (x : array A) (l : list M), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros A M R x l [Hl _]. symmetry. exact Hl. Qed.

Lemma alength_bound : forall (A : Set) (t : array A), (φ (PArray.length t)) <= 4194303.
Proof.
  intros A t. pose proof (PArray.leb_length A t) as H.
  rewrite leb_spec in H. exact H.
Qed.

Lemma count_loop_eq : forall ops q j acc H,
  count_loop ops q j acc H =
  match bdec (j <? q)%uint63 with
  | left Hj =>
      count_loop ops q (j + 1)%uint63 (if is_out ops.[j] then (acc + 1)%uint63 else acc)
        (Acc_inv H (dec_step q j Hj))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma run_loop_eq : forall ids ops xs ys q j T C O p H,
  run_loop ids ops xs ys q j T C O p H =
  match bdec (j <? q)%uint63 with
  | left Hj =>
      let '(T', C', O', p') := exec T C O p ids.[j] ops.[j] xs.[j] ys.[j] in
      run_loop ids ops xs ys q (j + 1)%uint63 T' C' O' p'
        (Acc_inv H (dec_step q j Hj))
  | right _ => O
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Loops.

Variables (idsl opsl : list N) (xsl ysl : list Z).
Variables (ia oa : array uint) (xa ya : array sint).
Hypothesis Hv : valid_input idsl opsl xsl ysl.
Hypothesis Hia : repr ia idsl.
Hypothesis Hoa : repr oa opsl.
Hypothesis Hxa : repr xa xsl.
Hypothesis Hya : repr ya ysl.

Let n := List.length idsl.

Definition cmdf (k : nat) : command :=
  (nth k idsl 0%N, nth k opsl 0%N, nth k xsl 0, nth k ysl 0).

Definition cmds_from (j : nat) : list command := map cmdf (seq j (n - j)).

Lemma cmds_from_S : forall j, (j < n)%nat -> cmds_from j = cmdf j :: cmds_from (S j).
Proof.
  intros j Hj. unfold cmds_from. replace (n - j)%nat with (S (n - S j)) by lia.
  reflexivity.
Qed.

Lemma cmds_from_n : forall j, (n <= j)%nat -> cmds_from j = [].
Proof. intros j Hj. unfold cmds_from. replace (n - j)%nat with 0%nat by lia. reflexivity. Qed.

Lemma lengths : List.length opsl = n /\ List.length xsl = n /\ List.length ysl = n.
Proof. destruct Hv as [[H1 [H2 H3]] _ _ _]. auto. Qed.

Lemma op_at : forall k, (k < n)%nat ->
  (φ (oa.[Uint63.of_nat k])) = Z.of_N (nth k opsl 0%N) /\ In (nth k opsl 0%N) valid_ops.
Proof.
  intros k Hk. destruct lengths as [L1 _].
  split; [exact (repr_get_u oa opsl k Hoa ltac:(lia))|].
  destruct Hv as [_ _ Hops _]. apply (proj1 (Forall_nth _ _) Hops). lia.
Qed.

Lemma replay_len : forall j s,
  (List.length (replay s (cmds_from j)) <= n - j)%nat.
Proof.
  intros j. remember (n - j)%nat as m eqn:Em. revert j Em.
  induction m as [|m IH]; intros j Em s.
  - rewrite cmds_from_n by lia. simpl. lia.
  - rewrite cmds_from_S by lia. cbn [replay].
    destruct (step s (cmdf j)) as [s' o] eqn:Es.
    destruct (op_at j ltac:(lia)) as [Hop Hin].
    pose proof (step_len s (nth j idsl 0%N) _ (nth j xsl 0) (nth j ysl 0) _ Hop Hin) as Hl.
    unfold cmdf in Es. rewrite Es in Hl. simpl in Hl.
    pose proof (IH (S j) ltac:(lia) s') as IH'.
    rewrite length_app. destruct (is_out _); lia.
Qed.

Lemma count_loop_spec : forall (q : int), (φ q) = Z.of_nat n ->
  forall z j acc H s, gap q j = z -> (φ j) <= (φ q) -> (φ acc) <= (φ j) ->
  (φ (count_loop oa q j acc H))
  = (φ acc) + Z.of_nat (List.length (replay s (cmds_from (Z.to_nat (φ j))))).
Proof.
  intros q Hq z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j acc H s Hz Hjq Hacc.
  pose proof (to_Z_bounded j) as Bj.
  pose proof (replay_len (Z.to_nat (φ j)) s) as Hle.
  rewrite count_loop_eq.
  destruct (bdec (j <? q)%uint63) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    rewrite cmds_from_S by lia. cbn [replay].
    destruct (step s (cmdf (Z.to_nat (φ j)))) as [s' o] eqn:Es.
    destruct (op_at (Z.to_nat (φ j)) ltac:(lia)) as [Hop Hin].
    rewrite of_nat_phi in Hop.
    pose proof (step_len s (nth (Z.to_nat (φ j)) idsl 0%N) _ (nth (Z.to_nat (φ j)) xsl 0)
                  (nth (Z.to_nat (φ j)) ysl 0) _ Hop Hin) as Hl.
    unfold cmdf in Es. rewrite Es in Hl. simpl in Hl.
    pose proof (replay_len (S (Z.to_nat (φ j))) s') as Hle'.
    rewrite (IH (gap q (j + 1)%uint63)) with (s := s');
      [| rewrite <- Hz; apply dec_step; exact Hj | reflexivity | lia |].
    + replace (Z.to_nat (φ (j + 1))%uint63) with (S (Z.to_nat (φ j))) by lia.
      rewrite length_app.
      match goal with |- context [is_out ?g] =>
        match type of Hl with context [is_out ?h] => change h with g in Hl end end.
      rewrite Hl.
      destruct (is_out _).
      * assert ((φ (acc + 1))%uint63 = (φ acc) + 1) by sia. lia.
      * lia.
    + pose proof (to_Z_bounded q). destruct (is_out _); [sia | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    rewrite cmds_from_n by lia. simpl. lia.
Qed.


Lemma n_bound : Z.of_nat n <= 4194303.
Proof.
  assert (H0 : (φ (PArray.length ia)) <= 4194303) by exact (alength_bound uint ia).
  assert (H : Z.of_nat (List.length idsl) = (φ (PArray.length@{Set} ia)))
    by (destruct Hia as [Hl _]; exact Hl).
  unfold n. lia.
Qed.

Lemma run_loop_spec : forall (q : int), (φ q) = Z.of_nat n ->
  forall z j T C O p H s, gap q j = z -> (φ j) <= (φ q) -> rel s T C (φ j) ->
  (φ p) + Z.of_nat (List.length (replay s (cmds_from (Z.to_nat (φ j)))))
    = (φ (PArray.length O)) ->
  PArray.length (run_loop ia oa xa ya q j T C O p H) = PArray.length O /\
  (forall i, (φ i) < (φ p) -> (run_loop ia oa xa ya q j T C O p H).[i] = O.[i]) /\
  (forall k, (k < List.length (replay s (cmds_from (Z.to_nat (φ j)))))%nat ->
     exists m, nth_error (replay s (cmds_from (Z.to_nat (φ j)))) k = Some m /\
       repr ((run_loop ia oa xa ya q j T C O p H).[of_Z ((φ p) + Z.of_nat k)]
               : option sint) m).
Proof.
  intros q Hq z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j T C O p H s Hz Hjq Hrel Hlen.
  pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded p) as Bp.
  pose proof n_bound as Hnb. pose proof (alength_bound (option int) O) as BO.
  rewrite run_loop_eq.
  destruct (bdec (j <? q)%uint63) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    remember (Z.to_nat (φ j)) as k eqn:Ek.
    assert (Hk : (k < n)%nat) by lia.
    assert (Ej : Uint63.of_nat k = j) by (subst k; apply of_nat_phi).
    destruct lengths as [L1 [L2 L3]].
    assert (Hid : (φ (ia.[j])) = Z.of_N (nth k idsl 0%N))
      by (rewrite <- Ej; exact (repr_get_u ia idsl k Hia Hk)).
    assert (Hop : (φ (oa.[j])) = Z.of_N (nth k opsl 0%N))
      by (rewrite <- Ej; exact (repr_get_u oa opsl k Hoa ltac:(lia))).
    assert (Hx : zs (xa.[j]) = nth k xsl 0)
      by (rewrite <- Ej; exact (repr_get_s xa xsl k Hxa ltac:(lia))).
    assert (Hy : zs (ya.[j]) = nth k ysl 0)
      by (rewrite <- Ej; exact (repr_get_s ya ysl k Hya ltac:(lia))).
    destruct (op_at k Hk) as [_ Hin].
    destruct Hv as [_ Hids _ Hargs].
    assert (Hidb : (1 <= nth k idsl 0%N <= 1000)%N)
      by (apply (proj1 (Forall_nth _ _) Hids); exact Hk).
    pose proof (Hargs k Hk) as Ha.
    rewrite cmds_from_S in Hlen |- * by exact Hk. cbn [replay] in Hlen |- *.
    destruct (step s (cmdf k)) as [s' o] eqn:Hs.
    match goal with |- context [exec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8] =>
      destruct (exec a1 a2 a3 a4 a5 a6 a7 a8) as [[[T' C'] O'] p'] eqn:He end.
    destruct (exec_correct s T C O p (φ j) _ _ _ _
                (nth k idsl 0%N) (nth k opsl 0%N) (nth k xsl 0) (nth k ysl 0)
                s' o T' C' O' p' Hrel ltac:(lia) Hid Hidb Hop Hin Hx Hy Ha Hs He)
      as [Hrel' Hout].
    rewrite <- Hj1 in Hrel'.
    assert (Ek1 : Z.to_nat (φ (j + 1))%uint63 = S k) by lia.
    rewrite length_app in Hlen.
    assert (Hlen' : (φ p') + Z.of_nat (List.length (replay s' (cmds_from (S k))))
                    = (φ (PArray.length O'))).
    { destruct Hout as [[-> [-> ->]] | (m & v & -> & Hr & -> & ->)].
      - simpl in Hlen. lia.
      - rewrite slength_set. simpl in Hlen.
        assert ((φ (p + 1))%uint63 = (φ p) + 1) by sia. lia. }
    rewrite <- Ek1 in Hlen'.
    destruct (IH (gap q (j + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; exact Hj)
                (j + 1)%uint63 T' C' O' p' (Acc_inv H (dec_step q j Hj)) s'
                eq_refl ltac:(lia) Hrel' Hlen') as [IH1 [IH2 IH3]].
    rewrite Ek1 in IH3.
    destruct Hout as [[-> [-> ->]] | (m & v & -> & Hr & -> & ->)].
    + split; [exact IH1|]. split; [exact IH2|]. exact IH3.
    + assert (Hp1 : (φ (p + 1))%uint63 = (φ p) + 1).
      { simpl in Hlen. sia. }
      assert (Hpl : (p <? PArray.length O)%uint63 = true)
        by (rewrite ltb_spec; simpl in Hlen; lia).
      split; [rewrite IH1; apply slength_set|].
      split.
      * intros i Hi. rewrite IH2 by lia. apply sget_set_other.
        intro E. subst i. lia.
      * intros [|k'] Hk'.
        -- exists m. split; [reflexivity|].
           rewrite Z.add_0_r, of_to_Z, IH2 by lia.
           rewrite sget_set_same by exact Hpl. exact Hr.
        -- simpl in Hk'. destruct (IH3 k' ltac:(lia)) as (m' & Hm' & Hr').
           exists m'. split; [exact Hm'|].
           replace ((φ p) + Z.of_nat (S k')) with ((φ (p + 1))%uint63 + Z.of_nat k') by lia.
           exact Hr'.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    rewrite cmds_from_n by lia. simpl.
    split; [reflexivity|]. split; [reflexivity|]. intros k Hk. lia.
Qed.

Lemma run_impl_correct :
  exists out : list (option Z),
    repr (run_impl ia oa xa ya) out /\ run_commands_spec idsl opsl xsl ysl out.
Proof.
  exists (replay init (commands idsl opsl xsl ysl)). split; [|reflexivity].
  assert (Ec : commands idsl opsl xsl ysl = cmds_from 0).
  { unfold commands, cmds_from. rewrite Nat.sub_0_r. reflexivity. }
  rewrite Ec.
  pose proof n_bound as Hnb.
  set (q := PArray.length ia).
  assert (Hq : (φ q) = Z.of_nat n) by exact (repr_len ia idsl Hia).
  set (cnt := count_loop oa q 0 0 (Zwf_well_founded 0 (gap q 0))).
  assert (Hcnt : (φ cnt) = Z.of_nat (List.length (replay init (cmds_from 0)))).
  { unfold cnt. rewrite (count_loop_spec q Hq _ 0%uint63 0%uint63 _ init eq_refl)
      by (change (φ 0)%uint63 with 0; lia).
    reflexivity. }
  pose proof (replay_len 0 init) as Hrl.
  assert (HO : PArray.length (PArray.make cnt (@None int)) = cnt).
  { rewrite slength_make.
    replace (cnt <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303. lia. }
  destruct (run_loop_spec q Hq _ 0%uint63 (PArray.make 1001 Leaf) (PArray.make 1001 None)
              (PArray.make cnt None) 0%uint63 (Zwf_well_founded 0 (gap q 0)) init
              eq_refl ltac:(change (φ 0)%uint63 with 0; lia) rel_init
              ltac:(rewrite HO, Hcnt; reflexivity))
    as [R1 [_ R3]].
  change (run_impl ia oa xa ya) with
    (run_loop ia oa xa ya q 0 (PArray.make 1001 Leaf) (PArray.make 1001 None)
       (PArray.make cnt None) 0 (Zwf_well_founded 0 (gap q 0))).
  split.
  - assert (HL : Z.of_nat (List.length (replay init (cmds_from 0)))
                 = (φ (PArray.length (run_loop ia oa xa ya q 0 (PArray.make 1001 Leaf)
                       (PArray.make 1001 None) (PArray.make cnt None) 0
                       (Zwf_well_founded 0 (gap q 0))))))
      by (rewrite R1, HO; symmetry; exact Hcnt).
    exact HL.
  - intros k Hk. destruct (R3 k Hk) as (m & Hm & Hr).
    exists m. split; [exact Hm | exact Hr].
Qed.

End Loops.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition run_commands :
  array uint -> array uint -> array sint -> array sint -> array (option sint)
  := run_impl.

Definition run_commands_correct :
  forall (ids ops : list N) (xs ys : list Z)
         (a b : array uint) (c d : array sint),
  valid_input ids ops xs ys ->
  repr a ids -> repr b ops -> repr c xs -> repr d ys ->
  exists out : list (option Z),
    repr (run_commands a b c d) out /\ run_commands_spec ids ops xs ys out
  := fun ids ops xs ys a b c d Hv Ha Hb Hc Hd =>
       run_impl_correct ids ops xs ys a b c d Hv Ha Hb Hc Hd.
