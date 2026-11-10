(* Implementation of joinstrings (joinstrings.spec): linked-list
   splicing, then one balanced concatenation.

   Code.  The strings are the nodes 0 .. n-1 (node u is S_(u+1)).  Two flat
   int tables: [nx] (the successor of a node in its list) and [tl] (the
   last node of the list headed by a node).  Operation "a b" with
   x = a - 1, y = b - 1 sets nx[tl[x]] := y and tl[x] := tl[y]: the list of
   y is spliced after the list of x in O(1), no character is touched.  The
   remaining string is the list of r = a_(N-1) - 1 (node 0 when N = 1): it
   is walked once into a flat table [ord] of its nodes, and the output is
   the balanced concatenation [build lo hi] = cat (build lo mid)
   (build mid hi) of the strings of ord[0 .. c), O(L log N).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof, as in template/polymul1.  Every table is
   threaded linearly (each [set] on the latest version); xs, xa, xb are
   only read. *)

From Joinstrings.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString PString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

Definition split_ok (lo hi : int) : bool := (lo <? hi) && (1 <? hi - lo).

Definition mid_of (lo hi : int) : int := lo + (hi - lo) / 2.

Lemma dec_left : forall lo hi : int,
  split_ok lo hi = true -> Zwf 0 (gap (mid_of lo hi) lo) (gap hi lo).
Proof.
  intros lo hi H. unfold split_ok in H.
  apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, gap, mid_of.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. change (φ 1) with 1%Z in H2. sia.
Qed.

Lemma dec_right : forall lo hi : int,
  split_ok lo hi = true -> Zwf 0 (gap hi (mid_of lo hi)) (gap hi lo).
Proof.
  intros lo hi H. unfold split_ok in H.
  apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, gap, mid_of.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. change (φ 1) with 1%Z in H2. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* tl[i] := i for i = k .. n-1: every node is a one-node list. *)
Fixpoint init_loop (n k : int) (tl : array int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array int :=
  match bdec (k <? n) with
  | left Hk => init_loop n (k + 1) tl.[k <- k] (Acc_inv H (dec_step n k Hk))
  | right _ => tl
  end.

Lemma init_loop_eq : forall n k tl H,
  init_loop n k tl H =
  match bdec (k <? n) with
  | left Hk => init_loop n (k + 1) tl.[k <- k] (Acc_inv H (dec_step n k Hk))
  | right _ => tl
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Operations k .. m-1: splice the list of y = b-1 after the list of
   x = a-1. *)
Fixpoint ops_loop (xa xb : array int) (m k : int) (nx tl : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int * array int :=
  match bdec (k <? m) with
  | left Hk =>
      let x := xa.[k] - 1 in
      let y := xb.[k] - 1 in
      let ty := tl.[y] in
      let tx := tl.[x] in
      ops_loop xa xb m (k + 1) nx.[tx <- y] tl.[x <- ty]
        (Acc_inv H (dec_step m k Hk))
  | right _ => (nx, tl)
  end.

Lemma ops_loop_eq : forall xa xb m k nx tl H,
  ops_loop xa xb m k nx tl H =
  match bdec (k <? m) with
  | left Hk =>
      let x := xa.[k] - 1 in
      let y := xb.[k] - 1 in
      let ty := tl.[y] in
      let tx := tl.[x] in
      ops_loop xa xb m (k + 1) nx.[tx <- y] tl.[x <- ty]
        (Acc_inv H (dec_step m k Hk))
  | right _ => (nx, tl)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Walk the list from cur to its last node t, writing the nodes into
   ord[i ..]; returns ord and the number of nodes. *)
Fixpoint walk (nx : array int) (t n cur i : int) (ord : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * int :=
  match bdec (i <? n) with
  | left Hi =>
      if cur =? t then (ord.[i <- cur], i + 1)
      else walk nx t n nx.[cur] (i + 1) ord.[i <- cur]
             (Acc_inv H (dec_step n i Hi))
  | right _ => (ord, i)
  end.

Lemma walk_eq : forall nx t n cur i ord H,
  walk nx t n cur i ord H =
  match bdec (i <? n) with
  | left Hi =>
      if cur =? t then (ord.[i <- cur], i + 1)
      else walk nx t n nx.[cur] (i + 1) ord.[i <- cur]
             (Acc_inv H (dec_step n i Hi))
  | right _ => (ord, i)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The concatenation of the strings of the nodes ord[lo .. hi), balanced. *)
Fixpoint build (xs : array PrimString.string) (ord : array int) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : PrimString.string :=
  match bdec (split_ok lo hi) with
  | left Hlt =>
      PrimString.cat
        (build xs ord lo (mid_of lo hi) (Acc_inv H (dec_left lo hi Hlt)))
        (build xs ord (mid_of lo hi) hi (Acc_inv H (dec_right lo hi Hlt)))
  | right _ => xs.[ord.[lo]]
  end.

Lemma build_eq : forall xs ord lo hi H,
  build xs ord lo hi H =
  match bdec (split_ok lo hi) with
  | left Hlt =>
      PrimString.cat
        (build xs ord lo (mid_of lo hi) (Acc_inv H (dec_left lo hi Hlt)))
        (build xs ord (mid_of lo hi) hi (Acc_inv H (dec_right lo hi Hlt)))
  | right _ => xs.[ord.[lo]]
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition root_of (xa : array int) (m : int) : int :=
  if m =? 0 then 0 else xa.[m - 1] - 1.

Definition joinstrings_impl (xs : array PrimString.string) (xa xb : array uint)
    : PrimString.string :=
  let n := PArray.length xs in
  let m := PArray.length xa in
  let tl0 := init_loop n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  let nt := ops_loop xa xb m 0 (PArray.make n 0) tl0
              (Zwf_well_founded 0 (gap m 0)) in
  let nx := fst nt in
  let tl := snd nt in
  let r := root_of xa m in
  let oc := walk nx tl.[r] n r 0 (PArray.make n 0)
              (Zwf_well_founded 0 (gap n 0)) in
  build xs (fst oc) 0 (snd oc) (Zwf_well_founded 0 (gap (snd oc) 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: generic list facts                                       *)
(* ------------------------------------------------------------------ *)

Lemma firstn_S_snoc : forall {A} (l : list A) k d, (k < List.length l)%nat ->
  firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  intros A l. induction l as [| x l IH]; intros [| k] d Hk; simpl in *; try lia.
  - reflexivity.
  - f_equal. apply IH. lia.
Qed.

Lemma skipn_nth_cons : forall {A} (l : list A) i d, (i < List.length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros A l. induction l as [| x l IH]; intros [| i] d Hi; simpl in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma firstn_add : forall {A} p q (l : list A),
  firstn (p + q) l = firstn p l ++ firstn q (skipn p l).
Proof.
  intros A p. induction p as [| p IH]; intros q l; [reflexivity|].
  destruct l as [| x l]; simpl.
  - destruct q; reflexivity.
  - f_equal. apply IH.
Qed.

Lemma In_firstn_nth : forall (l : list N) k v, In v (firstn k l) ->
  exists i, (i < k)%nat /\ (i < List.length l)%nat /\ nth i l 0%N = v.
Proof.
  intros l k v Hv.
  destruct (In_nth _ _ 0%N Hv) as (i & Hi & Hn).
  rewrite length_firstn in Hi.
  exists i. split; [lia|]. split; [lia|].
  rewrite nth_firstn in Hn. destruct (Nat.ltb_spec i k); [exact Hn | lia].
Qed.

Lemma nodup_bound : forall (l : list nat) n, NoDup l ->
  (forall v, In v l -> (v < n)%nat) -> (List.length l <= n)%nat.
Proof.
  intros l n Hd Hb.
  rewrite <- (length_seq n 0).
  apply NoDup_incl_length; [exact Hd|].
  intros v Hv. apply in_seq. specialize (Hb v Hv). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: linked lists                                             *)
(* ------------------------------------------------------------------ *)

Definition disj (l1 l2 : list nat) : Prop := forall w, In w l1 -> ~ In w l2.

(* l is the list of nodes met by following nx from u until the node t. *)
Fixpoint chain (nx : nat -> nat) (u t : nat) (l : list nat) {struct l} : Prop :=
  match l with
  | [] => False
  | v :: l' => v = u /\
      match l' with
      | [] => u = t
      | w :: _ => u <> t /\ nx u = w /\ chain nx w t l'
      end
  end.

Lemma chain_head : forall nx l u t, chain nx u t l -> exists l', l = u :: l'.
Proof.
  intros nx [| v l] u t H; simpl in H; [tauto|].
  destruct H as [-> _]. eauto.
Qed.

Lemma chain_last_in : forall nx l u t, chain nx u t l -> In t l.
Proof.
  intros nx l. induction l as [| v l IH]; intros u t H; simpl in H; [tauto|].
  destruct H as [-> H]. destruct l as [| w l'].
  - subst. left. reflexivity.
  - destruct H as (_ & _ & Hc). right. eapply IH. exact Hc.
Qed.

Lemma chain_frame : forall nx nx' l u t, chain nx u t l ->
  (forall v, In v l -> v <> t -> nx' v = nx v) -> chain nx' u t l.
Proof.
  intros nx nx' l. induction l as [| v l IH]; intros u t H Hf; simpl in *; [tauto|].
  destruct H as [-> H]. split; [reflexivity|].
  destruct l as [| w l']; [exact H|].
  destruct H as (Hne & Hnx & Hc). split; [exact Hne|]. split.
  - rewrite (Hf u (or_introl eq_refl) Hne). exact Hnx.
  - apply IH; [exact Hc|]. intros v Hv Hvt. apply Hf; [right; exact Hv | exact Hvt].
Qed.

Lemma chain_app : forall nx nx' l1 u t1 v t2 l2,
  chain nx u t1 l1 -> chain nx v t2 l2 -> disj l1 l2 -> nx' t1 = v ->
  (forall w, In w l1 -> w <> t1 -> nx' w = nx w) ->
  (forall w, In w l2 -> w <> t2 -> nx' w = nx w) ->
  chain nx' u t2 (l1 ++ l2).
Proof.
  intros nx nx' l1. induction l1 as [| w0 l1 IH];
    intros u t1 v t2 l2 H1 H2 Hd Ht Hf1 Hf2; simpl in H1; [tauto|].
  destruct H1 as [-> H1].
  assert (Hu2 : u <> t2).
  { intro E. apply (Hd u (or_introl eq_refl)). rewrite E.
    eapply chain_last_in. exact H2. }
  destruct l1 as [| w l1'].
  - subst t1. destruct (chain_head _ _ _ _ H2) as [l2' E2].
    simpl. rewrite E2. split; [reflexivity|]. split; [exact Hu2|]. split; [exact Ht|].
    rewrite <- E2. apply chain_frame with nx; [exact H2 | exact Hf2].
  - destruct H1 as (Hne & Hnx & Hc).
    change ((u :: w :: l1') ++ l2) with (u :: (w :: l1') ++ l2).
    simpl. split; [reflexivity|]. split; [exact Hu2|]. split.
    + rewrite (Hf1 u (or_introl eq_refl) Hne). exact Hnx.
    + change (w :: l1' ++ l2) with ((w :: l1') ++ l2).
      apply IH with t1 v; auto.
      * intros x Hx. apply Hd. right. exact Hx.
      * intros x Hx Hxt. apply Hf1; [right; exact Hx | exact Hxt].
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: math strings and the statement's operations              *)
(* ------------------------------------------------------------------ *)

Definition sconcat (l : list string) : string :=
  fold_right String.append ""%string l.

Lemma sappend_nil_r : forall t : string, (t ++ "")%string = t.
Proof. induction t as [| c t IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma sappend_assoc : forall t1 t2 t3 : string,
  (t1 ++ (t2 ++ t3))%string = ((t1 ++ t2) ++ t3)%string.
Proof. induction t1 as [| c t IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma slength_append : forall t1 t2 : string,
  String.length (t1 ++ t2) = (String.length t1 + String.length t2)%nat.
Proof. induction t1 as [| c t IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma sconcat_app : forall l1 l2,
  sconcat (l1 ++ l2) = (sconcat l1 ++ sconcat l2)%string.
Proof.
  induction l1 as [| t l IH]; intros l2; simpl; [reflexivity|].
  rewrite IH. apply sappend_assoc.
Qed.

(* The piece firstn d (skipn p l) is no longer than the whole. *)
Lemma sub_len : forall (f : nat -> string) (l : list nat) d p,
  (String.length (sconcat (map f (firstn d (skipn p l))))
   <= String.length (sconcat (map f l)))%nat.
Proof.
  intros f l d p.
  rewrite <- (firstn_skipn p l) at 2.
  rewrite <- (firstn_skipn d (skipn p l)) at 2.
  rewrite !map_app, !sconcat_app, !slength_append. lia.
Qed.

(* S_v of the input, 0-based. *)
Definition S0 (s : list string) (v : nat) : string := nth v s ""%string.

Fixpoint tot (st : list string) : nat :=
  match st with
  | [] => 0%nat
  | t :: st' => (String.length t + tot st')%nat
  end.

Lemma tot_app : forall l1 l2, tot (l1 ++ l2) = (tot l1 + tot l2)%nat.
Proof. induction l1 as [| t l IH]; intros; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma total_tot : forall st, total st = N.of_nat (tot st).
Proof.
  induction st as [| t st IH]; [reflexivity|].
  unfold total in *. simpl. rewrite IH. unfold slen. lia.
Qed.

Lemma nth_le_tot : forall st p, (String.length (nth p st ""%string) <= tot st)%nat.
Proof.
  induction st as [| t st IH]; intros [| p]; simpl; try lia.
  specialize (IH p). lia.
Qed.

Definition setn (st : list string) (p : nat) (t : string) : list string :=
  firstn p st ++ t :: skipn (S p) st.

Lemma split_at : forall (st : list string) p d, (p < List.length st)%nat ->
  st = firstn p st ++ nth p st d :: skipn (S p) st.
Proof.
  induction st as [| x st IH]; intros [| p] d Hp; simpl in *; try lia.
  - reflexivity.
  - f_equal. apply IH. lia.
Qed.

Lemma setn_length : forall st p t, (p < List.length st)%nat ->
  List.length (setn st p t) = List.length st.
Proof.
  intros st p t Hp. unfold setn.
  assert (E : List.length st
              = List.length (firstn p st ++ nth p st ""%string :: skipn (S p) st))
    by (f_equal; apply split_at; exact Hp).
  rewrite E, !length_app. reflexivity.
Qed.

Lemma setn_same : forall st p t, (p < List.length st)%nat ->
  nth p (setn st p t) ""%string = t.
Proof.
  intros st p t Hp. unfold setn.
  rewrite app_nth2; rewrite length_firstn; [| lia].
  replace (p - Nat.min p (List.length st))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma setn_other : forall st p q t, (p < List.length st)%nat -> q <> p ->
  nth q (setn st p t) ""%string = nth q st ""%string.
Proof.
  intros st p q t Hp Hq.
  rewrite (split_at st p ""%string Hp) at 2. unfold setn.
  destruct (Nat.ltb_spec q p).
  - rewrite !app_nth1 by (rewrite length_firstn; lia). reflexivity.
  - rewrite !app_nth2 by (rewrite length_firstn; lia).
    rewrite length_firstn.
    destruct (q - Nat.min p (List.length st))%nat as [| e] eqn:E; [lia|].
    reflexivity.
Qed.

Lemma setn_tot : forall st p t, (p < List.length st)%nat ->
  (tot (setn st p t) + String.length (nth p st ""%string)
   = tot st + String.length t)%nat.
Proof.
  intros st p t Hp. unfold setn.
  assert (E : tot st = tot (firstn p st ++ nth p st ""%string :: skipn (S p) st))
    by (f_equal; apply split_at; exact Hp).
  rewrite E, !tot_app. simpl. lia.
Qed.

Lemma str_node : forall st u, str st (N.of_nat u + 1) = nth u st ""%string.
Proof.
  intros st u. unfold str. f_equal. lia.
Qed.

Lemma join_eq : forall st x y,
  join st (N.of_nat x + 1) (N.of_nat y + 1)
  = setn (setn st x (nth x st "" ++ nth y st "")%string) y ""%string.
Proof.
  intros st x y. unfold join, set_str. rewrite !str_node.
  replace (N.to_nat (N.of_nat x + 1 - 1)) with x by lia.
  replace (N.to_nat (N.of_nat y + 1 - 1)) with y by lia.
  replace (N.to_nat (N.of_nat x + 1)) with (S x) by lia.
  replace (N.to_nat (N.of_nat y + 1)) with (S y) by lia.
  reflexivity.
Qed.

Lemma join_props : forall st x y,
  (x < List.length st)%nat -> (y < List.length st)%nat -> x <> y ->
  let st' := join st (N.of_nat x + 1) (N.of_nat y + 1) in
  List.length st' = List.length st /\
  nth x st' ""%string = (nth x st "" ++ nth y st "")%string /\
  (forall z, z <> x -> z <> y -> nth z st' ""%string = nth z st ""%string) /\
  tot st' = tot st.
Proof.
  intros st x y Hx Hy Hxy st'. unfold st'. rewrite join_eq.
  set (st1 := setn st x (nth x st "" ++ nth y st "")%string).
  assert (L1 : List.length st1 = List.length st) by (apply setn_length; exact Hx).
  split; [rewrite setn_length; [exact L1 | lia] |].
  split.
  - rewrite setn_other by lia. apply setn_same. exact Hx.
  - split.
    + intros z Hzx Hzy. rewrite setn_other by lia. apply setn_other; assumption.
    + pose proof (setn_tot st x (nth x st "" ++ nth y st "")%string Hx) as T1.
      pose proof (setn_tot st1 y ""%string ltac:(lia)) as T2.
      fold st1 in T1.
      assert (E : nth y st1 ""%string = nth y st ""%string)
        by (apply setn_other; [exact Hx | lia]).
      rewrite E in T2. rewrite slength_append in T1. simpl in T2. lia.
Qed.

(* The state after the first k operations. *)
Definition run_k (s : list string) (a b : list N) (k : nat) : list string :=
  fold_left (fun st op => join st (fst op) (snd op)) (firstn k (combine a b)) s.

Lemma run_k_succ : forall s a b k,
  (k < List.length a)%nat -> List.length a = List.length b ->
  run_k s a b (S k) = join (run_k s a b k) (nth k a 0%N) (nth k b 0%N).
Proof.
  intros s a b k Hk Hab. unfold run_k.
  rewrite (firstn_S_snoc _ k (0%N, 0%N))
    by (rewrite length_combine; lia).
  rewrite fold_left_app. simpl.
  rewrite combine_nth by exact Hab. reflexivity.
Qed.

Lemma run_k_all : forall s a b,
  List.length a = List.length b -> run_k s a b (List.length a) = run s a b.
Proof.
  intros s a b Hab. unfold run_k, run.
  rewrite firstn_all2; [reflexivity|]. rewrite length_combine. lia.
Qed.

(* The node of the 1-based index a_k / b_k. *)
Lemma valid_node : forall (s : list string) (l : list N) k,
  Forall (fun x => (1 <= x <= len s)%N) l -> (k < List.length l)%nat ->
  exists u, (u < List.length s)%nat /\ nth k l 0%N = (N.of_nat u + 1)%N.
Proof.
  intros s l k Hf Hk.
  rewrite Forall_forall in Hf.
  pose proof (Hf _ (nth_In l 0%N Hk)) as H. unfold len in H.
  exists (N.to_nat (nth k l 0%N) - 1)%nat. split; lia.
Qed.

(* Neither index of operation k has been emptied by an earlier one. *)
Lemma alive_ops : forall s a b k, valid_input s a b ->
  (k < List.length a)%nat ->
  ~ In (nth k a 0%N) (firstn k b) /\ ~ In (nth k b 0%N) (firstn k b).
Proof.
  intros s a b k Hv Hk.
  destruct Hv as [_ _ _ _ Hla Hlb _ _ _ Hfut].
  assert (Lab : List.length a = List.length b) by (unfold len in *; lia).
  split; intro H; destruct (In_firstn_nth _ _ _ H) as (i & Hik & Hil & Hn);
    destruct (Hfut i k Hik Hk) as [H1 H2]; congruence.
Qed.

Lemma run_k_len_tot : forall s a b, valid_input s a b ->
  forall k, (k <= List.length a)%nat ->
  List.length (run_k s a b k) = List.length s /\ tot (run_k s a b k) = tot s.
Proof.
  intros s a b Hv k. induction k as [| k IH]; intros Hk; [split; reflexivity|].
  pose proof Hv as Hv'.
  destruct Hv' as [_ _ _ _ Hla Hlb Hva Hvb Hneq _].
  assert (Lab : List.length a = List.length b) by (unfold len in *; lia).
  destruct (IH ltac:(lia)) as [IL IT].
  rewrite run_k_succ by (exact Hk || exact Lab).
  destruct (valid_node s a k Hva ltac:(lia)) as (x & Hx & Ex).
  destruct (valid_node s b k Hvb ltac:(lia)) as (y & Hy & Ey).
  assert (Hxy : x <> y).
  { intro E. apply (Hneq k ltac:(lia)). rewrite Ex, Ey, E. reflexivity. }
  rewrite Ex, Ey.
  destruct (join_props (run_k s a b k) x y ltac:(lia) ltac:(lia) Hxy)
    as (L & _ & _ & T).
  split; [rewrite L; exact IL | rewrite T; exact IT].
Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: the invariant of the splicing loop                        *)
(* ------------------------------------------------------------------ *)

(* Node u is alive after k operations: S_(u+1) has not been emptied. *)
Definition alive (b : list N) (k u : nat) : Prop :=
  ~ In (N.of_nat u + 1)%N (firstn k b).

(* After k operations, with successor nxf and last node tlf: every alive
   node u heads a list L u, from u to tlf u, of distinct nodes whose
   strings concatenate to S_(u+1); the lists of two alive nodes are
   disjoint. *)
Definition inv (n : nat) (s : list string) (b : list N) (k : nat)
    (st : list string) (nxf tlf : nat -> nat) : Prop :=
  exists L : nat -> list nat,
    (forall u, (u < n)%nat -> alive b k u ->
       chain nxf u (tlf u) (L u) /\ NoDup (L u) /\
       (forall v, In v (L u) -> (v < n)%nat) /\
       nth u st ""%string = sconcat (map (S0 s) (L u))) /\
    (forall u v, (u < n)%nat -> (v < n)%nat -> alive b k u -> alive b k v ->
       u <> v -> disj (L u) (L v)).

Lemma inv_init : forall n s b nxf tlf, List.length s = n ->
  (forall u, (u < n)%nat -> tlf u = u) -> inv n s b 0 s nxf tlf.
Proof.
  intros n s b nxf tlf Hn Ht. exists (fun u => [u]). split.
  - intros u Hu _. rewrite Ht by exact Hu. split; [simpl; auto|].
    split; [constructor; [simpl; tauto | constructor]|].
    split; [intros v [<- | []]; exact Hu|].
    simpl. rewrite sappend_nil_r. reflexivity.
  - intros u v _ _ _ _ Huv w [<- | []] [E | []]. auto.
Qed.

Lemma alive_succ : forall b k u y,
  firstn (S k) b = firstn k b ++ [(N.of_nat y + 1)%N] ->
  alive b (S k) u -> alive b k u /\ u <> y.
Proof.
  intros b k u y E H. unfold alive in *. rewrite E in H. split.
  - intro F. apply H. apply in_or_app. left. exact F.
  - intro F. apply H. apply in_or_app. right. left. subst. reflexivity.
Qed.

Lemma inv_step : forall n s b k st nxf tlf nxf' tlf' x y,
  inv n s b k st nxf tlf -> List.length st = n ->
  (x < n)%nat -> (y < n)%nat -> x <> y -> alive b k x -> alive b k y ->
  firstn (S k) b = firstn k b ++ [(N.of_nat y + 1)%N] ->
  nxf' (tlf x) = y -> (forall v, (v < n)%nat -> v <> tlf x -> nxf' v = nxf v) ->
  tlf' x = tlf y -> (forall u, (u < n)%nat -> u <> x -> tlf' u = tlf u) ->
  inv n s b (S k) (join st (N.of_nat x + 1) (N.of_nat y + 1)) nxf' tlf'.
Proof.
  intros n s b k st nxf tlf nxf' tlf' x y [L [HL Hd]] Hst Hx Hy Hxy Ax Ay Eb
    Hn1 Hn2 Ht1 Ht2.
  destruct (join_props st x y ltac:(lia) ltac:(lia) Hxy) as (_ & J1 & J2 & _).
  destruct (HL x Hx Ax) as (Cx & Dx & Bx & Sx).
  destruct (HL y Hy Ay) as (Cy & Dy & By & Sy).
  pose proof (Hd x y Hx Hy Ax Ay Hxy) as Dxy.
  pose proof (chain_last_in _ _ _ _ Cx) as Tx.
  exists (fun z => if Nat.eqb z x then L x ++ L y else L z). split.
  - intros u Hu Au. destruct (alive_succ b k u y Eb Au) as [Au' Huy].
    destruct (Nat.eqb_spec u x) as [-> | Hux].
    + rewrite Ht1. split; [| split; [| split]].
      * apply chain_app with nxf (tlf x) y; [exact Cx | exact Cy | exact Dxy | exact Hn1 | |].
        -- intros w Hw Hwt. apply Hn2; [apply Bx; exact Hw | exact Hwt].
        -- intros w Hw Hwt. apply Hn2; [apply By; exact Hw|].
           intro E. apply (Dxy (tlf x) Tx). rewrite <- E. exact Hw.
      * apply NoDup_app; auto.
      * intros v Hv. apply in_app_or in Hv. destruct Hv; auto.
      * rewrite J1, Sx, Sy, map_app, sconcat_app. reflexivity.
    + destruct (HL u Hu Au') as (Cu & Du & Bu & Su).
      rewrite Ht2 by assumption. split; [| split; [| split]]; auto.
      * apply chain_frame with nxf; [exact Cu|].
        intros w Hw Hwt. apply Hn2; [apply Bu; exact Hw|].
        intro E. apply (Hd x u Hx Hu Ax Au' (fun F => Hux (eq_sym F)) (tlf x) Tx).
        rewrite <- E. exact Hw.
      * rewrite J2 by assumption. exact Su.
  - intros u v Hu Hv Au Av Huv.
    destruct (alive_succ b k u y Eb Au) as [Au' Huy].
    destruct (alive_succ b k v y Eb Av) as [Av' Hvy].
    destruct (Nat.eqb_spec u x) as [-> | Hux]; destruct (Nat.eqb_spec v x) as [-> | Hvx].
    + congruence.
    + intros w Hw. apply in_app_or in Hw. destruct Hw as [Hw | Hw].
      * apply (Hd x v); auto.
      * apply (Hd y v); auto.
    + intros w Hw Hw'. apply in_app_or in Hw'. destruct Hw' as [Hw' | Hw'].
      * apply (Hd u x Hu Hx Au' Ax Hux w Hw Hw').
      * apply (Hd u y Hu Hy Au' Ay Huy w Hw Hw').
    + apply Hd; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Machine side: Uint63 / PArray plumbing                              *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
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

Lemma ofn_spec : forall u : nat, (Z.of_nat u < 9223372036854775808)%Z ->
  (φ (of_Z (Z.of_nat u))) = Z.of_nat u.
Proof.
  intros u Hu. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia.
Qed.

Lemma int_ofn : forall (i : int) (u : nat), (φ i) = Z.of_nat u -> i = of_Z (Z.of_nat u).
Proof. intros i u H. rewrite <- H. symmetry. apply of_to_Z. Qed.

(* A table read as nodes. *)
Definition rd (t : array int) (u : nat) : nat := Z.to_nat (φ (t.[of_Z (Z.of_nat u)])).

Lemma rd_phi : forall t u, (φ (t.[of_Z (Z.of_nat u)])) = Z.of_nat (rd t u).
Proof. intros t u. unfold rd. pose proof (to_Z_bounded (t.[of_Z (Z.of_nat u)])). lia. Qed.

Lemma rd_set_same : forall (t : array int) (p : nat) (w : int),
  (Z.of_nat p < (φ (PArray.length t)))%Z ->
  rd (t.[of_Z (Z.of_nat p) <- w]) p = Z.to_nat (φ w).
Proof.
  intros t p w Hp. unfold rd.
  pose proof (to_Z_bounded (PArray.length t)).
  rewrite aget_set_same; [reflexivity|].
  rewrite ltb_spec, ofn_spec by lia. lia.
Qed.

Lemma rd_set_other : forall (t : array int) (p v : nat) (w : int),
  (Z.of_nat p < 9223372036854775808)%Z -> (Z.of_nat v < 9223372036854775808)%Z ->
  v <> p -> rd (t.[of_Z (Z.of_nat p) <- w]) v = rd t v.
Proof.
  intros t p v w Hp Hv Hpv. unfold rd.
  rewrite aget_set_other; [reflexivity|].
  intro E. apply Hpv. apply (f_equal to_Z) in E.
  rewrite !ofn_spec in E by lia. lia.
Qed.

Lemma get_uint : forall (xa : array uint) (a : list N), repr xa a ->
  forall k, (k < List.length a)%nat ->
  (φ (xa.[of_Z (Z.of_nat k)])) = Z.of_N (nth k a 0%N).
Proof.
  intros xa a [Hl Hc] k Hk.
  destruct (Hc k Hk) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  erewrite nth_error_nth by exact Hm. rewrite <- Hr.
  rewrite Z2N.id by (pose proof (to_Z_bounded (xa.[of_Z (Z.of_nat k)])); lia).
  reflexivity.
Qed.

Lemma repr_len : forall {A M} `{Repr A M} (x : array A) (l : list M), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros A M R x l [Hl _]. symmetry. exact Hl. Qed.

(* ------------------------------------------------------------------ *)
(* Machine side: the loops                                             *)
(* ------------------------------------------------------------------ *)

Lemma init_loop_spec : forall (n : int) (z : Z) (k : int) (tl : array int)
    (H : Acc (Zwf 0) (gap n k)),
  gap n k = z -> PArray.length tl = n -> ((φ k) <= (φ n))%Z ->
  (forall j : int, ((φ j) < (φ k))%Z -> tl.[j] = j) ->
  PArray.length (init_loop n k tl H) = n /\
  forall j : int, ((φ j) < (φ n))%Z -> (init_loop n k tl H).[j] = j.
Proof.
  intros n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k tl H Hz Hlen Hkn Hinv.
  rewrite init_loop_eq. destruct (bdec (k <? n)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + rewrite alength_set. exact Hlen.
    + lia.
    + intros j Hj. rewrite Hk1 in Hj.
      destruct (Z.eq_dec (φ j) (φ k)) as [E | E].
      * assert (j = k) by (apply to_Z_inj; exact E). subst j.
        apply aget_set_same. rewrite Hlen. exact Hk.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    split; [exact Hlen|]. intros j Hj. apply Hinv. lia.
Qed.

Lemma ops_loop_spec : forall s a b (xa xb : array uint) (NN M : int),
  valid_input s a b -> repr xa a -> repr xb b ->
  (φ NN) = Z.of_nat (List.length s) -> (φ M) = Z.of_nat (List.length a) ->
  forall z k nx tl H, gap M k = z -> ((φ k) <= (φ M))%Z ->
  PArray.length nx = NN -> PArray.length tl = NN ->
  inv (List.length s) s b (Z.to_nat (φ k)) (run_k s a b (Z.to_nat (φ k))) (rd nx) (rd tl) ->
  let R := ops_loop xa xb M k nx tl H in
  PArray.length (fst R) = NN /\ PArray.length (snd R) = NN /\
  inv (List.length s) s b (List.length a) (run_k s a b (List.length a))
    (rd (fst R)) (rd (snd R)).
Proof.
  intros s a b xa xb NN M Hv Ha Hb HN HM z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k nx tl H Hz Hkm Hnx Htl Hinv R. unfold R. clear R.
  rewrite ops_loop_eq. destruct (bdec (k <? M)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    pose proof (to_Z_bounded k) as Bk.
    pose proof Hv as Hv'.
    destruct Hv' as [Hvn _ _ _ Hla Hlb Hva Hvb Hneq _].
    unfold len in Hvn, Hla, Hlb.
    assert (Lab : List.length a = List.length b) by lia.
    set (kn := Z.to_nat (φ k)) in *.
    assert (Ekn : (φ k) = Z.of_nat kn) by (unfold kn; lia).
    assert (Hkn : (kn < List.length a)%nat) by lia.
    destruct (valid_node s a kn Hva Hkn) as (x & Hx & Ex).
    destruct (valid_node s b kn Hvb ltac:(lia)) as (y & Hy & Ey).
    assert (Ek : k = of_Z (Z.of_nat kn)) by (apply int_ofn; exact Ekn).
    assert (Hxa : (φ (xa.[k])) = (Z.of_nat x + 1)%Z)
      by (rewrite Ek, (get_uint xa a Ha kn Hkn), Ex; lia).
    assert (Hyb : (φ (xb.[k])) = (Z.of_nat y + 1)%Z)
      by (rewrite Ek, (get_uint xb b Hb kn ltac:(lia)), Ey; lia).
    assert (Exi : xa.[k] - 1 = of_Z (Z.of_nat x))
      by (apply int_ofn; sia).
    assert (Eyi : xb.[k] - 1 = of_Z (Z.of_nat y))
      by (apply int_ofn; sia).
    cbv zeta.
    lazymatch goal with
    |- context [ops_loop _ _ _ _ (?nx0.[?tl0.[?X] <- ?Y]) (?tl1.[?X' <- ?tl2.[?Y']]) _] =>
      assert (Exi' : X = of_Z (Z.of_nat x)) by exact Exi;
      assert (Eyi' : Y = of_Z (Z.of_nat y)) by exact Eyi;
      assert (Exi'' : X' = of_Z (Z.of_nat x)) by exact Exi;
      assert (Eyi'' : Y' = of_Z (Z.of_nat y)) by exact Eyi;
      rewrite ?Exi', ?Eyi', ?Exi'', ?Eyi''
    end.
    destruct (alive_ops s a b kn Hv Hkn) as [Ax Ay].
    rewrite Ex in Ax. rewrite Ey in Ay.
    assert (Hxy : x <> y).
    { intro E. apply (Hneq kn Hkn). rewrite Ex, Ey, E. reflexivity. }
    pose proof Hinv as Hinv'.
    destruct Hinv' as [L [HL _]].
    destruct (HL x Hx Ax) as (Cx & _ & Bx & _).
    pose proof (Bx _ (chain_last_in _ _ _ _ Cx)) as Tx.
    assert (Etx : tl.[of_Z (Z.of_nat x)] = of_Z (Z.of_nat (rd tl x)))
      by (apply int_ofn; apply rd_phi).
    rewrite Etx.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | | | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + rewrite alength_set. exact Hnx.
    + rewrite alength_set. exact Htl.
    + replace (Z.to_nat (φ (k + 1))) with (S kn) by lia.
      rewrite run_k_succ by (exact Hkn || exact Lab).
      rewrite Ex, Ey.
      destruct (run_k_len_tot s a b Hv kn ltac:(lia)) as [Lst _].
      apply inv_step with (rd nx) (rd tl); auto.
      * rewrite (firstn_S_snoc b kn 0%N) by lia. rewrite Ey. reflexivity.
      * rewrite rd_set_same by lia.
        rewrite ofn_spec by lia. lia.
      * intros v Hv1 Hv2. apply rd_set_other; lia.
      * rewrite rd_set_same by lia. reflexivity.
      * intros u Hu1 Hu2. apply rd_set_other; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    replace (Z.to_nat (φ k)) with (List.length a) in Hinv by lia.
    split; [exact Hnx|]. split; [exact Htl | exact Hinv].
Qed.

Lemma walk_spec : forall (nx : array int) (t NN : int) (l : list nat) (tn : nat),
  (φ t) = Z.of_nat tn -> (List.length l <= Z.to_nat (φ NN))%nat ->
  forall z (i cur : int) (ord : array int) (H : Acc (Zwf 0) (gap NN i)),
  gap NN i = z ->
  (Z.to_nat (φ i) < List.length l)%nat ->
  chain (rd nx) (nth (Z.to_nat (φ i)) l 0%nat) tn (skipn (Z.to_nat (φ i)) l) ->
  (φ cur) = Z.of_nat (nth (Z.to_nat (φ i)) l 0%nat) ->
  PArray.length ord = NN ->
  (forall j, (j < Z.to_nat (φ i))%nat ->
     (φ (ord.[of_Z (Z.of_nat j)])) = Z.of_nat (nth j l 0%nat)) ->
  let W := walk nx t NN cur i ord H in
  PArray.length (fst W) = NN /\ (φ (snd W)) = Z.of_nat (List.length l) /\
  forall j, (j < List.length l)%nat ->
    (φ ((fst W).[of_Z (Z.of_nat j)])) = Z.of_nat (nth j l 0%nat).
Proof.
  intros nx t NN l tn Ht Hln z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i cur ord H Hz Hil Hc Hcur Hord Hcells W. unfold W. clear W.
  pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded NN) as BN.
  set (iN := Z.to_nat (φ i)) in *.
  assert (Ei : (φ i) = Z.of_nat iN) by (unfold iN; lia).
  rewrite walk_eq. destruct (bdec (i <? NN)) as [Hi | Hi].
  2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. lia. }
  pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
  rewrite (skipn_nth_cons l iN 0%nat) in Hc by lia. cbn [chain] in Hc. destruct Hc as [_ Hc].
  set (u := nth iN l 0%nat) in *.
  assert (Eiu : i = of_Z (Z.of_nat iN)) by (apply int_ofn; exact Ei).
  assert (Hcells' : forall j, (j < S iN)%nat ->
     (φ (ord.[i <- cur].[of_Z (Z.of_nat j)])) = Z.of_nat (nth j l 0%nat)).
  { intros j Hj. destruct (Nat.eq_dec j iN) as [-> | Hne].
    - rewrite <- Eiu, aget_set_same; [exact Hcur|]. rewrite Hord. exact Hi.
    - rewrite aget_set_other; [apply Hcells; lia|].
      intro E. apply Hne. apply (f_equal to_Z) in E.
      rewrite ofn_spec in E by lia. lia. }
  assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  pose proof (length_skipn (S iN) l) as Ls.
  destruct (cur =? t) eqn:Ect.
  - rewrite Uint63.eqb_spec in Ect.
    destruct (skipn (S iN) l) as [| w r'] eqn:Es.
    + simpl in Ls. simpl.
      split; [rewrite alength_set; exact Hord|].
      split; [lia|].
      intros j Hj. apply Hcells'. lia.
    + exfalso. destruct Hc as [Hne _]. apply Hne.
      apply (f_equal to_Z) in Ect. lia.
  - destruct (skipn (S iN) l) as [| w r'] eqn:Es.
    + exfalso. rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in Ect.
      apply Ect. apply to_Z_inj. lia.
    + destruct Hc as (_ & Hnx & Hc').
      simpl in Ls.
      assert (Ew : w = nth (S iN) l 0%nat).
      { pose proof (skipn_nth_cons l (S iN) 0%nat ltac:(lia)) as E.
        rewrite Es in E. congruence. }
      assert (Hti : Z.to_nat (φ (i + 1)) = S iN) by lia.
      eapply IH; [ | reflexivity | | | | | ].
      * rewrite <- Hz. apply dec_step. exact Hi.
      * rewrite Hti. lia.
      * rewrite Hti, Es, <- Ew. exact Hc'.
      * rewrite Hti, <- Ew, <- Hnx.
        assert (Ec : cur = of_Z (Z.of_nat u)) by (apply int_ofn; exact Hcur).
        rewrite Ec. apply rd_phi.
      * rewrite alength_set. exact Hord.
      * rewrite Hti. exact Hcells'.
Qed.

(* ------------------------------------------------------------------ *)
(* Machine side: strings                                               *)
(* ------------------------------------------------------------------ *)

Lemma max_length_val : (φ PrimString.max_length) = 16777211%Z.
Proof. reflexivity. Qed.

Lemma repr_cat : forall (x1 x2 : PrimString.string) (i1 i2 : string),
  repr x1 i1 -> repr x2 i2 ->
  (Z.of_nat (String.length i1) + Z.of_nat (String.length i2) <= 16777211)%Z ->
  repr (PrimString.cat x1 x2) (i1 ++ i2)%string.
Proof.
  intros x1 x2 i1 i2 [L1 C1] [L2 C2] Hb.
  pose proof (to_Z_bounded (PrimString.length x1)).
  pose proof (to_Z_bounded (PrimString.length x2)).
  assert (HL : (φ (PrimString.length (PrimString.cat x1 x2)))
               = ((φ (PrimString.length x1)) + (φ (PrimString.length x2)))%Z).
  { rewrite PString.cat_length_spec_no_overflow by (rewrite max_length_val; lia).
    rewrite add_spec, Z.mod_small; [reflexivity|]. rewrite wB_val. lia. }
  split.
  - rewrite slength_append, HL. lia.
  - intros k Hk. rewrite slength_append in Hk.
    destruct (Nat.ltb_spec k (String.length i1)) as [Hk1 | Hk1].
    + destruct (C1 k Hk1) as (c & Hc & Hr). exists c. split.
      * rewrite <- append_correct1 by exact Hk1. exact Hc.
      * unfold repr, repr_uint in *.
        rewrite PString.cat_get_spec_l; [exact Hr|].
        rewrite ofn_spec by lia. lia.
    + set (k' := (k - String.length i1)%nat).
      destruct (C2 k' ltac:(unfold k'; lia)) as (c & Hc & Hr). exists c. split.
      * replace k with (k' + String.length i1)%nat by (unfold k'; lia).
        rewrite <- append_correct2. exact Hc.
      * unfold repr, repr_uint in *.
        rewrite PString.cat_get_spec_r;
          [| rewrite ofn_spec by lia; lia | rewrite ofn_spec, max_length_val by lia; lia].
        replace (of_Z (Z.of_nat k) - PrimString.length x1) with (of_Z (Z.of_nat k'));
          [exact Hr|].
        apply to_Z_inj. rewrite sub_spec, !ofn_spec by (unfold k'; lia).
        rewrite Z.mod_small; unfold k'; lia.
Qed.

Lemma build_spec : forall (s : list string) (xs : array PrimString.string)
    (l : list nat) (ord : array int),
  repr xs s -> (forall v, In v l -> (v < List.length s)%nat) ->
  (forall j, (j < List.length l)%nat ->
     (φ (ord.[of_Z (Z.of_nat j)])) = Z.of_nat (nth j l 0%nat)) ->
  (Z.of_nat (String.length (sconcat (map (S0 s) l))) <= 16777211)%Z ->
  (Z.of_nat (List.length l) <= 4194303)%Z ->
  forall z (lo hi : int) (H : Acc (Zwf 0) (gap hi lo)),
  gap hi lo = z -> ((φ lo) < (φ hi))%Z -> ((φ hi) <= Z.of_nat (List.length l))%Z ->
  repr (build xs ord lo hi H)
    (sconcat (map (S0 s) (firstn (Z.to_nat ((φ hi) - (φ lo))) (skipn (Z.to_nat (φ lo)) l)))).
Proof.
  intros s xs l ord Hxs Hl Hord Hlen Hll z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi H Hz Hlh Hhl.
  pose proof (to_Z_bounded lo) as Blo. pose proof (to_Z_bounded hi) as Bhi.
  rewrite build_eq. destruct (bdec (split_ok lo hi)) as [Hs | Hs].
  - pose proof Hs as Hs'. unfold split_ok in Hs'.
    apply andb_prop in Hs'. destruct Hs' as [_ H2]. rewrite ltb_spec in H2.
    assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z)
      by (rewrite sub_spec, Z.mod_small; [reflexivity | rewrite wB_val; lia]).
    rewrite E in H2. change (φ 1) with 1%Z in H2.
    pose proof (Z.div_pos ((φ hi) - (φ lo)) 2 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_lt ((φ hi) - (φ lo)) 2 ltac:(lia) ltac:(lia)) as D1.
    assert (Em : (φ (mid_of lo hi)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z).
    { unfold mid_of. rewrite add_spec, div_spec, E. change (φ 2) with 2%Z.
      rewrite Z.mod_small; [reflexivity | rewrite wB_val; lia]. }
    assert (D2 : (1 <= ((φ hi) - (φ lo)) / 2)%Z)
      by (apply (Z.div_le_mono 2 ((φ hi) - (φ lo)) 2); lia).
    pose proof (IH _ ltac:(rewrite <- Hz; exact (dec_left lo hi Hs)) lo (mid_of lo hi)
                  (Acc_inv H (dec_left lo hi Hs)) eq_refl ltac:(lia) ltac:(lia)) as R1.
    pose proof (IH _ ltac:(rewrite <- Hz; exact (dec_right lo hi Hs)) (mid_of lo hi) hi
                  (Acc_inv H (dec_right lo hi Hs)) eq_refl ltac:(lia) ltac:(lia)) as R2.
    set (d1 := Z.to_nat ((φ (mid_of lo hi)) - (φ lo))) in *.
    set (d2 := Z.to_nat ((φ hi) - (φ (mid_of lo hi)))) in *.
    replace (Z.to_nat (φ (mid_of lo hi))) with (d1 + Z.to_nat (φ lo))%nat in R2
      by (unfold d1; lia).
    rewrite <- skipn_skipn in R2.
    replace (Z.to_nat ((φ hi) - (φ lo))) with (d1 + d2)%nat by (unfold d1, d2; lia).
    pose proof (sub_len (S0 s) l (d1 + d2) (Z.to_nat (φ lo))) as B.
    rewrite firstn_add, map_app, sconcat_app in B |- *.
    rewrite slength_append in B.
    apply repr_cat; [exact R1 | exact R2 | lia].
  - assert (E1 : (φ hi) = ((φ lo) + 1)%Z).
    { unfold split_ok in Hs. apply Bool.andb_false_iff in Hs.
      destruct Hs as [Hs | Hs];
        rewrite <- Bool.not_true_iff_false, ltb_spec in Hs; [lia|].
      assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z)
      by (rewrite sub_spec, Z.mod_small; [reflexivity | rewrite wB_val; lia]).
      rewrite E in Hs. change (φ 1) with 1%Z in Hs. lia. }
    replace (Z.to_nat ((φ hi) - (φ lo))) with 1%nat by lia.
    set (lon := Z.to_nat (φ lo)).
    rewrite (skipn_nth_cons l lon 0%nat) by (unfold lon; lia).
    simpl. rewrite sappend_nil_r.
    assert (Elo : lo = of_Z (Z.of_nat lon)) by (apply int_ofn; unfold lon; lia).
    assert (Ev : ord.[lo] = of_Z (Z.of_nat (nth lon l 0%nat)))
      by (apply int_ofn; rewrite Elo; apply Hord; unfold lon; lia).
    rewrite Ev.
    set (v := nth lon l 0%nat).
    assert (Hv : (v < List.length s)%nat)
      by (apply Hl; apply nth_In; unfold lon; lia).
    destruct Hxs as [_ Hc].
    destruct (Hc v Hv) as (m & Hm & Hr).
    unfold S0. erewrite nth_error_nth by exact Hm.
    exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

(* The remaining node: r = a_(N-1) - 1, or 0 when N = 1. *)
Lemma root_spec : forall s a b (xa : array uint), valid_input s a b -> repr xa a ->
  exists rn, (φ (root_of xa (PArray.length xa))) = Z.of_nat rn /\
             (rn < List.length s)%nat /\ alive b (List.length a) rn.
Proof.
  intros s a b xa Hv Ha. pose proof Hv as Hv'.
  destruct Hv' as [Hvn _ _ _ Hla Hlb Hva _ Hneq Hfut]. unfold len in *.
  pose proof (repr_len xa a Ha) as HM.
  unfold root_of. destruct (PArray.length xa =? 0) eqn:E0.
  - rewrite Uint63.eqb_spec in E0. rewrite E0 in HM. change (φ 0) with 0%Z in HM.
    exists 0%nat. split; [reflexivity|]. split; [lia|].
    unfold alive. replace (List.length a) with 0%nat by lia. simpl. tauto.
  - rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in E0.
    assert (Hm : (0 < List.length a)%nat).
    { destruct (List.length a) eqn:El; [| lia]. exfalso. apply E0. apply to_Z_inj.
      rewrite HM. reflexivity. }
    set (m1 := (List.length a - 1)%nat).
    destruct (valid_node s a m1 Hva ltac:(unfold m1; lia)) as (x & Hx & Ex).
    assert (EM : PArray.length xa - 1 = of_Z (Z.of_nat m1)).
    { apply int_ofn. rewrite sub_spec, HM. change (φ 1) with 1%Z.
      rewrite Z.mod_small; [unfold m1; lia | rewrite wB_val; lia]. }
    assert (Hxa : (φ (xa.[PArray.length xa - 1])) = (Z.of_nat x + 1)%Z).
    { rewrite EM, (get_uint xa a Ha m1 ltac:(unfold m1; lia)), Ex. lia. }
    exists x.
    lazymatch goal with
    |- ((φ (?X - 1)) = _) /\ _ => assert (HX : (φ X) = (Z.of_nat x + 1)%Z) by exact Hxa
    end.
    split; [rewrite sub_spec, HX; change (φ 1) with 1%Z;
            rewrite Z.mod_small; [lia | rewrite wB_val; lia] |].
    split; [exact Hx|].
    unfold alive. rewrite <- Ex. intro H.
    destruct (In_firstn_nth _ _ _ H) as (i & Hi & Hib & Hn).
    destruct (Nat.eq_dec i m1) as [-> | Hne].
    + apply (Hneq m1 ltac:(unfold m1; lia)). symmetry. exact Hn.
    + destruct (Hfut i m1 ltac:(unfold m1 in *; lia) ltac:(unfold m1; lia)) as [F _].
      apply F. symmetry. exact Hn.
Qed.

Lemma joinstrings_impl_correct :
  forall (s : list string) (a b : list N)
         (xs : array PrimString.string) (xa xb : array uint),
  valid_input s a b -> repr xs s -> repr xa a -> repr xb b ->
  exists o : string, repr (joinstrings_impl xs xa xb) o /\
                     joinstrings_spec s a b o.
Proof.
  intros s a b xs xa xb Hv Hs Ha Hb.
  pose proof Hv as Hv'.
  destruct Hv' as [Hvn _ _ Hvt Hla Hlb _ _ _ _]. unfold len in *.
  assert (Lab : List.length a = List.length b) by lia.
  pose proof (repr_len xs s Hs) as HN.
  pose proof (repr_len xa a Ha) as HM.
  unfold joinstrings_impl.
  set (NN := PArray.length xs) in *.
  set (M := PArray.length xa) in *.
  assert (Hmk : PArray.length (PArray.make NN 0) = NN).
  { rewrite alength_make.
    replace (NN <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia. }
  (* the tail table: tl[u] = u *)
  destruct (init_loop_spec NN _ 0 (PArray.make NN 0) (Zwf_well_founded 0 (gap NN 0))
              eq_refl Hmk ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j Hj; change (φ 0) with 0%Z in Hj;
                    pose proof (to_Z_bounded j); lia)) as [Ltl0 Ctl0].
  set (tl0 := init_loop NN 0 (PArray.make NN 0) (Zwf_well_founded 0 (gap NN 0))) in *.
  assert (Hinv0 : inv (List.length s) s b 0 s (rd (PArray.make NN 0)) (rd tl0)).
  { apply inv_init; [reflexivity|]. intros u Hu. unfold rd.
    rewrite Ctl0 by (rewrite ofn_spec by lia; lia).
    rewrite ofn_spec by lia. lia. }
  (* the splices *)
  pose proof (ops_loop_spec s a b xa xb NN M Hv Ha Hb HN HM _ 0
                (PArray.make NN 0) tl0 (Zwf_well_founded 0 (gap M 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) Hmk Ltl0 Hinv0) as Hops.
  cbv zeta in Hops.
  set (nt := ops_loop xa xb M 0 (PArray.make NN 0) tl0 (Zwf_well_founded 0 (gap M 0)))
    in *.
  destruct Hops as (Lnx & Ltl & Hinv).
  rewrite run_k_all in Hinv by exact Lab.
  (* the remaining list *)
  destruct (root_spec s a b xa Hv Ha) as (rn & Hr & Hrn & Ar).
  fold M in Hr.
  set (r := root_of xa M) in *.
  destruct Hinv as [L [HL _]].
  destruct (HL rn Hrn Ar) as (Cr & Dr & Br & Sr).
  destruct (chain_head _ _ _ _ Cr) as [l' El].
  assert (Hlr : (List.length (L rn) <= List.length s)%nat)
    by (apply nodup_bound; assumption).
  assert (Er : r = of_Z (Z.of_nat rn)) by (apply int_ofn; exact Hr).
  pose proof (walk_spec (fst nt) ((snd nt).[r]) NN (L rn) (rd (snd nt) rn)
                ltac:(rewrite Er; apply rd_phi) ltac:(lia)
                _ 0 r (PArray.make NN 0) (Zwf_well_founded 0 (gap NN 0)) eq_refl
                ltac:(rewrite El; simpl; lia)
                ltac:(change (Z.to_nat (φ 0)) with 0%nat; rewrite skipn_O;
                      replace (nth 0 (L rn) 0%nat) with rn by (rewrite El; reflexivity);
                      exact Cr)
                ltac:(change (Z.to_nat (φ 0)) with 0%nat; rewrite El; exact Hr)
                Hmk
                ltac:(intros j Hj; change (Z.to_nat (φ 0)) with 0%nat in Hj; lia))
    as Hw.
  cbv zeta in Hw.
  set (oc := walk (fst nt) (snd nt).[r] NN r 0 (PArray.make NN 0)
               (Zwf_well_founded 0 (gap NN 0))) in *.
  destruct Hw as (Lord & Hc & Cord).
  (* the output *)
  destruct (run_k_len_tot s a b Hv (List.length a) ltac:(lia)) as [_ Tot].
  rewrite run_k_all in Tot by exact Lab.
  pose proof (nth_le_tot (run s a b) rn) as Tr.
  rewrite total_tot in Hvt.
  pose proof (build_spec s xs (L rn) (fst oc) Hs Br Cord
                ltac:(rewrite <- Sr; lia) ltac:(lia)
                _ 0 (snd oc) (Zwf_well_founded 0 (gap (snd oc) 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; rewrite Hc, El; simpl; lia)
                ltac:(lia)) as Hbuild.
  change (φ 0) with 0%Z in Hbuild. change (Z.to_nat 0) with 0%nat in Hbuild.
  rewrite Hc, Z.sub_0_r, Nat2Z.id, skipn_O, firstn_all in Hbuild.
  exists (str (run s a b) (N.of_nat rn + 1)).
  split.
  - rewrite str_node, Sr. exact Hbuild.
  - exists (N.of_nat rn + 1)%N. split; [unfold len; lia|]. split; [|reflexivity].
    unfold alive in Ar. rewrite firstn_all2 in Ar by lia. exact Ar.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition joinstrings :
  array PrimString.string -> array uint -> array uint -> PrimString.string
  := joinstrings_impl.

Definition joinstrings_correct :
  forall (s : list string) (a b : list N)
         (xs : array PrimString.string) (xa xb : array uint),
  valid_input s a b -> repr xs s -> repr xa a -> repr xb b ->
  exists o : string, repr (joinstrings xs xa xb) o /\
                     joinstrings_spec s a b o
  := joinstrings_impl_correct.
