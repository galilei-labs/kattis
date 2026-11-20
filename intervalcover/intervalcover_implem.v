(* Implementation of intervalcover.spec: greedy interval cover.

   Code.  An index array [0..n) is merge-sorted by left endpoint
   ([msort_rec], top-down, one scratch array, as in the closestpair2
   template); [sweep] then runs the greedy rounds: from the current
   position q, [scan] takes the intervals whose left end is <= cur and
   keeps the largest right end; the round chooses that interval if it
   contains cur (first round) or goes beyond cur (later rounds), writes it
   to the scratch W[cnt], and stops when the reach is >= b.  The position
   only moves forward.  The answer is copied into an array of exactly cnt
   cells.  Only PrimFloat.leb / ltb on the floats; every loop is the
   combinator [loop] (erased Acc on hi - i), the sort and the rounds
   recurse on an erased Acc on n - q; no nat, no Z, no list in the code.

   Proof.  [lb]: if a selection S covers [a, y] and c_0 = a, c_{j+1} is at
   least c_j and every right end of an interval starting <= c_j, then
   |S| <= m implies y <= c_m.  The greedy's reaches are such a chain, all
   below b before the last, which gives minimality; a round that fails
   gives a fixpoint of the chain below b (or a = point uncovered), hence
   no covering at all. *)

From Intervalcover.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf Sorting.Sorted Sorting.Permutation.
From StdGalilei Require Import repr repr_float.
From Flocq Require Core.Core.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.
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
Elpi complexity sumbool.
Elpi complexity bdec.
Arguments bdec_cost : simpl never.
Elpi complexity andb.
Arguments andb_cost : simpl never.
Elpi complexity orb.
Arguments orb_cost : simpl never.

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

(* Guard of the two recursions: lo < hi and hi - lo > c. *)
Definition guard (c lo hi : int) : bool := (lo <? hi) && (c <? hi - lo).
Elpi complexity guard.
Arguments guard_cost : simpl never.

Lemma dec_left : forall c lo hi : int, guard c lo hi = true ->
  Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof.
  intros c lo hi H. unfold guard in H. apply andb_prop in H as [H1 H2].
  rewrite Uint63.ltb_spec in H1, H2. pose proof (to_Z_bounded c).
  assert (Hs : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
  rewrite Hs in H2. unfold Zwf, gap. sia.
Qed.

Lemma dec_right : forall c lo hi : int, guard c lo hi = true -> (1 <= to_Z c)%Z ->
  Zwf 0 (gap hi (lo + (hi - lo) / 2)) (gap hi lo).
Proof.
  intros c lo hi H Hc. unfold guard in H. apply andb_prop in H as [H1 H2].
  rewrite Uint63.ltb_spec in H1, H2.
  assert (Hs : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
  rewrite Hs in H2. unfold Zwf, gap. sia.
Qed.

Lemma one_ge_1 : (1 <= to_Z 1)%Z. Proof. reflexivity. Qed.

(* The one loop combinator: for i = lo, lo+1, ... while i < hi and
   [cont i s], s := f i s. *)
Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.

Definition loop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) : St :=
  wloop hi cont f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.
Elpi complexity wloop.
Arguments wloop_cost : simpl never.
Elpi complexity loop.
Arguments loop_cost : simpl never.
(* One step of the merge of A[lo, mid) and A[mid, hi) into T, by key. *)
Definition merge_step (key : array float) (A : array int) (mid hi : int)
    (k : int) (st : int * int * array int) : int * int * array int :=
  let '(i, j, T) := st in
  if i <? mid then
    if hi <=? j then (i + 1, j, T.[k <- A.[i]])
    else
      let a := A.[i] in
      let b := A.[j] in
      if (key.[a] <=? key.[b])%float then (i + 1, j, T.[k <- a])
      else (i, j + 1, T.[k <- b])
  else (i, j + 1, T.[k <- A.[j]]).
Elpi complexity merge_step.
Arguments merge_step_cost : simpl never.

Definition merge (key : array float) (lo mid hi : int) (A T : array int) : array int :=
  let '(_, _, T) := loop hi (fun _ _ => true) (merge_step key A mid hi) lo (lo, mid, T) in T.
Elpi complexity merge.
Arguments merge_cost : simpl never.

Definition copy_step (k : int) (st : array int * array int) : array int * array int :=
  let '(A, T) := st in (A.[k <- T.[k]], T).
Elpi complexity copy_step.
Arguments copy_step_cost : simpl never.

Definition merge_copy (key : array float) (lo mid hi : int) (A T : array int)
    : array int * array int :=
  let T := merge key lo mid hi A T in
  loop hi (fun _ _ => true) copy_step lo (A, T).
Elpi complexity merge_copy.
Arguments merge_copy_cost : simpl never.

(* Merge sort of the index segment A[lo, hi) by key, T a scratch array. *)
Fixpoint msort_rec (key : array float) (lo hi : int) (A T : array int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int * array int :=
  match bdec (guard 1 lo hi) with
  | left Hg =>
      let m := lo + (hi - lo) / 2 in
      let '(A, T) := msort_rec key lo m A T (Acc_inv H (dec_left 1 lo hi Hg)) in
      let '(A, T) := msort_rec key m hi A T (Acc_inv H (dec_right 1 lo hi Hg one_ge_1)) in
      merge_copy key lo m hi A T
  | right _ => (A, T)
  end.
Elpi complexity msort_rec.
Arguments msort_rec_cost : simpl never.

Definition iota_step (k : int) (P : array int) : array int := P.[k <- k].
Elpi complexity iota_step.
Arguments iota_step_cost : simpl never.

(* The sweep, one round: from position q of the sorted index array P,
   scan the intervals whose left end is at most cur, keeping the largest
   right end (found, best, its index); the state carries the position
   reached. *)
Definition scan_cont (ls : array float) (P : array int) (cur : float)
    (p : int) (st : int * bool * float * int) : bool :=
  (ls.[P.[p]] <=? cur)%float.
Elpi complexity scan_cont.
Arguments scan_cont_cost : simpl never.

Definition scan_step (rs : array float) (P : array int)
    (p : int) (st : int * bool * float * int) : int * bool * float * int :=
  let '(_, f, best, bi) := st in
  let i := P.[p] in
  let r := rs.[i] in
  if (best <=? r)%float then (p + 1, true, r, i) else (p + 1, f, best, bi).
Elpi complexity scan_step.
Arguments scan_step_cost : simpl never.

Definition adv (n q q' : int) : bool := (q <? q') && (q' <=? n).
Elpi complexity adv.
Arguments adv_cost : simpl never.

Lemma dec_adv : forall n q q', adv n q q' = true -> Zwf 0 (gap n q') (gap n q).
Proof.
  intros n q q' H. unfold adv in H. apply andb_prop in H as [H1 H2].
  rewrite Uint63.ltb_spec in H1. rewrite Uint63.leb_spec in H2.
  unfold Zwf, gap. lia.
Qed.

(* The greedy rounds: cur is the reach so far, W[0, cnt) the intervals
   chosen; each round chooses the interval of largest reach among those
   starting at or before cur (the first round needs it to contain cur =
   a, the later ones to go beyond cur), until the reach is at least b. *)
Fixpoint sweep (ls rs : array float) (b : float) (P : array int) (n : int)
    (q cnt : int) (cur : float) (W : array int)
    (H : Acc (Zwf 0) (gap n q)) {struct H} : option (array int * int) :=
  match loop n (scan_cont ls P cur) (scan_step rs P) q (q, false, cur, 0) with
  | (q', found, best, bi) =>
    if andb found (orb (cnt =? 0)%uint63 (cur <? best)%float) then
      let W := W.[cnt <- bi] in
      if (b <=? best)%float then Some (W, cnt + 1)
      else match bdec (adv n q q') with
           | left Ha => sweep ls rs b P n q' (cnt + 1) best W (Acc_inv H (dec_adv n q q' Ha))
           | right _ => None
           end
    else None
  end.
Elpi complexity sweep.
Arguments sweep_cost : simpl never.

Definition copy_out (W : array int) (k : int) (O : array int) : array int := O.[k <- W.[k]].
Elpi complexity copy_out.
Arguments copy_out_cost : simpl never.

Definition cover (x y : float) (ls rs : array float) : option (array uint) :=
  let n := PArray.length ls in
  let P := loop n (fun _ _ => true) iota_step 0 (PArray.make n 0) in
  let '(P, _) := msort_rec ls 0 n P (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  match sweep ls rs y P n 0 0 x (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) with
  | Some (W, k) => Some (loop k (fun _ _ => true) (copy_out W) 0 (PArray.make k 0))
  | None => None
  end.
Elpi complexity cover.

(* ================================================================== *)
(* Proofs                                                              *)
(* ================================================================== *)

Section LoopProof.
Context {St : Type}.

Lemma wloop_eq : forall (hi : int) cont (f : int -> St -> St) i s H,
  wloop hi cont f i s H =
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma loop_inv : forall (P : int -> St -> Prop) (hi lo : int) cont f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> cont j t = true ->
     P (j + 1) (f j t)) ->
  exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (loop hi cont f lo s) /\
    (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (loop hi cont f lo s) = false)).
Proof.
  intros P hi lo cont f s Hle Hp Hstep. unfold loop.
  assert (G : forall n i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = n ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t ->
     exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (wloop hi cont f i t H) /\
       (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (wloop hi cont f i t H) = false))).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H En Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      destruct (cont i t) eqn:Ec.
      + apply (IH (gap hi (i + 1))).
        * rewrite <- En. apply dec_step; exact Hlt.
        * reflexivity.
        * pose proof (to_Z_bounded hi).
          assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
        * apply Hstep; auto; lia.
      + exists i. split; [lia |]. split; [exact Pt | right; split; [lia | exact Ec]].
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      exists i. split; [lia |]. split; [exact Pt | left; lia]. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi (fun _ _ => true) f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep.
  destruct (loop_inv P hi lo (fun _ _ => true) f s Hle Hp) as (j & _ & Pj & [E | [_ E]]).
  - intros j t Hj Pt _. apply Hstep; auto.
  - apply to_Z_inj in E. subst j. exact Pj.
  - discriminate.
Qed.

End LoopProof.

(* ------------------------------------------------------------------ *)
(* PArray plumbing, restated at [array int] (universe instances)       *)
(* ------------------------------------------------------------------ *)

Lemma iget_set_same : forall (t : array int) (i v : int),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same int t i v H). Qed.

Lemma iget_set_other : forall (t : array int) (i j v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.

Lemma ilength_set : forall (t : array int) (i v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.

Lemma ilength_make : forall (n v : int),
  PArray.length (PArray.make n v) = if n <=? max_length then n else max_length.
Proof. intros n v. exact (length_make int n v). Qed.

Lemma ilength_bound : forall (t : array int), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H. rewrite Uint63.leb_spec in H.
  exact H.
Qed.

Lemma flength_bound : forall (t : array float), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length float t) as H. rewrite Uint63.leb_spec in H.
  exact H.
Qed.

Lemma to_Z_of_Z_small : forall z, (0 <= z < wB)%Z -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small; exact Hz. Qed.

Lemma wB_big : (4194304 < wB)%Z.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Segments of an index array, as lists                                *)
(* ------------------------------------------------------------------ *)

Fixpoint seg (A : array int) (lo : Z) (len : nat) : list int :=
  match len with
  | O => []
  | S k => A.[of_Z lo] :: seg A (lo + 1) k
  end.

Lemma seg_length : forall A len lo, List.length (seg A lo len) = len.
Proof. intros A len; induction len; intros lo; simpl; auto. Qed.

Lemma seg_snoc : forall A k lo,
  seg A lo (S k) = seg A lo k ++ [A.[of_Z (lo + Z.of_nat k)]].
Proof.
  intros A k; induction k; intros lo.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - change (seg A lo (S (S k))) with (A.[of_Z lo] :: seg A (lo + 1) (S k)).
    rewrite IHk. simpl. do 3 f_equal. rewrite Zpos_P_of_succ_nat.
    replace (lo + Z.succ (Z.of_nat k))%Z with (lo + 1 + Z.of_nat k)%Z by lia. reflexivity.
Qed.

Lemma seg_app : forall A k1 k2 lo,
  seg A lo (k1 + k2) = seg A lo k1 ++ seg A (lo + Z.of_nat k1) k2.
Proof.
  intros A k1; induction k1; intros k2 lo.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - simpl. rewrite IHk1. do 3 f_equal. lia.
Qed.

Lemma seg_ext : forall A B len lo,
  (forall z, (lo <= z < lo + Z.of_nat len)%Z -> A.[of_Z z] = B.[of_Z z]) ->
  seg A lo len = seg B lo len.
Proof.
  intros A B len; induction len; intros lo H; simpl; auto.
  f_equal; [apply H; lia | apply IHlen; intros z Hz; apply H; lia].
Qed.

Lemma seg_nth : forall A len lo k d, (k < len)%nat ->
  nth k (seg A lo len) d = A.[of_Z (lo + Z.of_nat k)].
Proof.
  intros A len; induction len; intros lo k d Hk; [lia |].
  destruct k; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IHlen by lia. f_equal. f_equal. lia.
Qed.

Lemma seg_In : forall A len lo a,
  In a (seg A lo len) <-> exists z, (lo <= z < lo + Z.of_nat len)%Z /\ A.[of_Z z] = a.
Proof.
  intros A len; induction len; intros lo a; simpl.
  - split; [tauto | intros (z & Hz & _); lia].
  - rewrite IHlen. split.
    + intros [E | (z & Hz & E)]; [exists lo | exists z]; split; auto; lia.
    + intros (z & Hz & E). destruct (Z.eq_dec z lo) as [-> | Hne]; [left; exact E |].
      right. exists z. split; auto; lia.
Qed.

(* a write outside the segment does not change it *)
Lemma seg_set_out : forall A (i v : int) len lo,
  (0 <= lo)%Z -> (lo + Z.of_nat len <= wB)%Z ->
  (to_Z i < lo \/ lo + Z.of_nat len <= to_Z i)%Z ->
  seg (A.[i <- v]) lo len = seg A lo len.
Proof.
  intros A i v len lo H0 H1 H2. apply seg_ext. intros z Hz.
  apply iget_set_other. intros E.
  subst i. rewrite to_Z_of_Z_small in H2; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Lists: sortedness, the merge model                                  *)
(* ------------------------------------------------------------------ *)

Section SortedLemmas.
Context {A : Type} (Rl : A -> A -> Prop).

Lemma SS_app : forall l1 l2, StronglySorted Rl (l1 ++ l2) ->
  StronglySorted Rl l1 /\ StronglySorted Rl l2 /\
  (forall a b, In a l1 -> In b l2 -> Rl a b).
Proof.
  intros l1; induction l1 as [| c l1 IH]; intros l2 H; simpl in *.
  - split; [constructor | split; [exact H | tauto]].
  - apply StronglySorted_inv in H as [H1 H2]. destruct (IH l2 H1) as (S1 & S2 & X).
    rewrite Forall_forall in H2. split; [| split; [exact S2 |]].
    + constructor; [exact S1 | rewrite Forall_forall; intros z Hz; apply H2, in_or_app; auto].
    + intros a b [<- | Ha] Hb; [apply H2, in_or_app; auto | auto].
Qed.

Lemma SS_filter : forall (f : A -> bool) l, StronglySorted Rl l -> StronglySorted Rl (filter f l).
Proof.
  intros f l; induction l as [| c l IH]; intros H; simpl; [constructor |].
  apply StronglySorted_inv in H as [H1 H2].
  destruct (f c); [| auto]. constructor; [auto |].
  rewrite Forall_forall in *. intros z Hz. apply filter_In in Hz. apply H2; tauto.
Qed.

Lemma SS_nth : forall l i j d, StronglySorted Rl l -> (i < j < List.length l)%nat ->
  Rl (nth i l d) (nth j l d).
Proof.
  intros l; induction l as [| c l IH]; intros i j d H Hij; simpl in *; [lia |].
  apply StronglySorted_inv in H as [H1 H2]. destruct i, j; try lia.
  - rewrite Forall_forall in H2. apply H2, nth_In. lia.
  - apply IH; auto; lia.
Qed.

End SortedLemmas.

Section Merge.
Variable le : int -> int -> bool.

Fixpoint lmerge (l1 : list int) : list int -> list int :=
  match l1 with
  | [] => fun l2 => l2
  | a :: l1' =>
      fix aux (l2 : list int) : list int :=
        match l2 with
        | [] => a :: l1'
        | b :: l2' => if le a b then a :: lmerge l1' l2 else b :: aux l2'
        end
  end.

Lemma lmerge_nil_r : forall l, lmerge l [] = l.
Proof. intros [| a l]; reflexivity. Qed.

Lemma lmerge_cons : forall a l1 b l2, lmerge (a :: l1) (b :: l2) =
  if le a b then a :: lmerge l1 (b :: l2) else b :: lmerge (a :: l1) l2.
Proof. reflexivity. Qed.

Lemma lmerge_perm : forall l1 l2, Permutation (lmerge l1 l2) (l1 ++ l2).
Proof.
  intros l1; induction l1 as [| a l1 IH1]; intros l2; [simpl; reflexivity |].
  induction l2 as [| b l2 IH2].
  - rewrite lmerge_nil_r, app_nil_r. reflexivity.
  - rewrite lmerge_cons. destruct (le a b).
    + simpl. constructor. apply IH1.
    + eapply perm_trans; [constructor; exact IH2 |].
      simpl. eapply perm_trans; [apply perm_swap |]. constructor.
      apply Permutation_middle.
Qed.

Variable K : int -> R.
Variable Pd : int -> Prop.
Hypothesis le_spec : forall a b, Pd a -> Pd b -> (le a b = true <-> (K a <= K b)%R).

Definition Rk (a b : int) : Prop := (K a <= K b)%R.

Lemma lmerge_sorted : forall l1 l2, Forall Pd l1 -> Forall Pd l2 ->
  StronglySorted Rk l1 -> StronglySorted Rk l2 -> StronglySorted Rk (lmerge l1 l2).
Proof.
  intros l1; induction l1 as [| a l1 IH1]; intros l2 P1 P2 S1 S2; [exact S2 |].
  induction l2 as [| b l2 IH2]; [rewrite lmerge_nil_r; exact S1 |].
  pose proof S1 as S1'. pose proof S2 as S2'.
  apply StronglySorted_inv in S1' as [T1 F1]. apply StronglySorted_inv in S2' as [T2 F2].
  pose proof P1 as P1'. pose proof P2 as P2'.
  apply Forall_inv_tail in P1' as Q1. apply Forall_inv in P1'.
  apply Forall_inv_tail in P2' as Q2. apply Forall_inv in P2'.
  rewrite lmerge_cons. destruct (le a b) eqn:E.
  - apply le_spec in E; auto.
    constructor; [apply IH1; auto |].
    apply (Permutation_Forall (Permutation_sym (lmerge_perm l1 (b :: l2)))).
    apply Forall_app. split; [exact F1 |]. constructor; [exact E |].
    rewrite Forall_forall in *. intros z Hz. unfold Rk in *. specialize (F2 z Hz). lra.
  - assert (E' : (K b < K a)%R).
    { destruct (Rlt_le_dec (K b) (K a)) as [Hlt | Hge]; [exact Hlt |].
      apply le_spec in Hge; auto. congruence. }
    constructor; [apply IH2; auto |].
    apply (Permutation_Forall (Permutation_sym (lmerge_perm (a :: l1) l2))).
    apply Forall_app. split; [| exact F2]. constructor; [unfold Rk; lra |].
    rewrite Forall_forall in *. intros z Hz. unfold Rk in *. specialize (F1 z Hz). lra.
Qed.

End Merge.

(* ------------------------------------------------------------------ *)
(* Segments between machine indices                                    *)
(* ------------------------------------------------------------------ *)

Definition sg (A : array int) (lo hi : int) : list int :=
  seg A (to_Z lo) (Z.to_nat (to_Z hi - to_Z lo)).

Lemma sg_length : forall A lo hi, List.length (sg A lo hi) = Z.to_nat (to_Z hi - to_Z lo).
Proof. intros. apply seg_length. Qed.

Lemma sg_nil : forall A lo hi, (to_Z hi <= to_Z lo)%Z -> sg A lo hi = [].
Proof. intros A lo hi H. unfold sg. replace (Z.to_nat (to_Z hi - to_Z lo)) with O by lia. reflexivity. Qed.

Lemma sg_cons : forall A lo hi, (to_Z lo < to_Z hi)%Z ->
  sg A lo hi = A.[lo] :: sg A (lo + 1) hi.
Proof.
  intros A lo hi H. pose proof (to_Z_bounded hi).
  assert (E : to_Z (lo + 1) = (to_Z lo + 1)%Z) by sia.
  unfold sg. rewrite E. replace (Z.to_nat (to_Z hi - to_Z lo)) with (S (Z.to_nat (to_Z hi - (to_Z lo + 1)))) by lia.
  simpl. rewrite of_to_Z. reflexivity.
Qed.

Lemma sg_app : forall A lo mid hi, (to_Z lo <= to_Z mid <= to_Z hi)%Z ->
  sg A lo hi = sg A lo mid ++ sg A mid hi.
Proof.
  intros A lo mid hi H. unfold sg.
  replace (Z.to_nat (to_Z hi - to_Z lo)) with (Z.to_nat (to_Z mid - to_Z lo) + Z.to_nat (to_Z hi - to_Z mid))%nat by lia.
  rewrite seg_app. f_equal. f_equal. lia.
Qed.

Lemma sg_ext : forall A B lo hi,
  (forall p : int, (to_Z lo <= to_Z p < to_Z hi)%Z -> A.[p] = B.[p]) ->
  sg A lo hi = sg B lo hi.
Proof.
  intros A B lo hi H. unfold sg. apply seg_ext. intros z Hz.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  apply H. rewrite to_Z_of_Z_small; lia.
Qed.

Lemma sg_In : forall A lo hi a,
  In a (sg A lo hi) <-> exists p : int, (to_Z lo <= to_Z p < to_Z hi)%Z /\ A.[p] = a.
Proof.
  intros A lo hi a. unfold sg. rewrite seg_In.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  split.
  - intros (z & Hz & E). exists (of_Z z). rewrite to_Z_of_Z_small by lia. split; [lia | exact E].
  - intros (p & Hp & E). exists (to_Z p). rewrite of_to_Z. split; [lia | exact E].
Qed.

Lemma sg_nth : forall A lo hi k d, (k < Z.to_nat (to_Z hi - to_Z lo))%nat ->
  nth k (sg A lo hi) d = A.[of_Z (to_Z lo + Z.of_nat k)].
Proof. intros. unfold sg. apply seg_nth. exact H. Qed.

Lemma sg_snoc_set : forall (T : array int) lo k v, (to_Z lo <= to_Z k)%Z ->
  (to_Z k < to_Z (PArray.length T))%Z ->
  sg (T.[k <- v]) lo (k + 1) = sg T lo k ++ [v].
Proof.
  intros T lo k v H1 H2. pose proof (ilength_bound T).
  assert (E : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
  unfold sg. rewrite E.
  replace (Z.to_nat (to_Z k + 1 - to_Z lo)) with (S (Z.to_nat (to_Z k - to_Z lo))) by lia.
  rewrite seg_snoc. pose proof (to_Z_bounded lo). f_equal.
  - apply seg_set_out; lia.
  - replace (to_Z lo + Z.of_nat (Z.to_nat (to_Z k - to_Z lo)))%Z with (to_Z k) by lia.
    rewrite of_to_Z. rewrite iget_set_same; [reflexivity |]. rewrite Uint63.ltb_spec. exact H2.
Qed.

(* a write outside the segment *)
Lemma sg_set_out : forall (A : array int) i v lo hi,
  (to_Z i < to_Z lo \/ to_Z hi <= to_Z i)%Z -> sg (A.[i <- v]) lo hi = sg A lo hi.
Proof.
  intros A i v lo hi H. apply sg_ext. intros p Hp. apply iget_set_other.
  intros ->. lia.
Qed.

(* agreement outside [lo, hi) *)
Definition agree (A B : array int) (lo hi : int) : Prop :=
  forall p : int, (to_Z p < to_Z lo \/ to_Z hi <= to_Z p)%Z -> B.[p] = A.[p].

Lemma agree_refl : forall A lo hi, agree A A lo hi.
Proof. intros A lo hi p _. reflexivity. Qed.

Lemma agree_trans : forall A B C lo hi lo' hi',
  (to_Z lo <= to_Z lo')%Z -> (to_Z hi' <= to_Z hi)%Z ->
  agree A B lo' hi' -> agree B C lo hi -> agree A C lo hi.
Proof.
  intros A B C lo hi lo' hi' H1 H2 HAB HBC p Hp. rewrite HBC by exact Hp. apply HAB. lia.
Qed.

Lemma agree_widen : forall A B lo hi lo' hi', agree A B lo' hi' ->
  (to_Z lo <= to_Z lo')%Z -> (to_Z hi' <= to_Z hi)%Z -> agree A B lo hi.
Proof. intros A B lo hi lo' hi' H H1 H2 p Hp. apply H. lia. Qed.

Lemma agree_tr : forall A B C lo hi, agree A B lo hi -> agree B C lo hi -> agree A C lo hi.
Proof. intros A B C lo hi H1 H2 p Hp. rewrite H2 by exact Hp. apply H1, Hp. Qed.

Lemma agree_sg : forall A B lo hi a b,
  agree A B lo hi -> (to_Z b <= to_Z lo \/ to_Z hi <= to_Z a)%Z ->
  sg B a b = sg A a b.
Proof. intros A B lo hi a b H Hab. apply sg_ext. intros p Hp. apply H. lia. Qed.

Lemma sg_snoc : forall (T : array int) lo k, (to_Z lo <= to_Z k < 4194303)%Z ->
  sg T lo (k + 1) = sg T lo k ++ [T.[k]].
Proof.
  intros T lo k H. assert (E : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
  rewrite (sg_app T lo k (k + 1)) by lia. f_equal.
  rewrite sg_cons by lia. rewrite sg_nil by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Merge, copy back                                                    *)
(* ------------------------------------------------------------------ *)

Definition lek (key : array float) (a b : int) : bool := (key.[a] <=? key.[b])%float.

Lemma merge_spec : forall key (A T : array int) lo mid hi,
  (to_Z lo <= to_Z mid <= to_Z hi)%Z -> (to_Z hi <= to_Z (PArray.length T))%Z ->
  PArray.length (merge key lo mid hi A T) = PArray.length T /\
  sg (merge key lo mid hi A T) lo hi = lmerge (lek key) (sg A lo mid) (sg A mid hi).
Proof.
  intros key A T lo mid hi Hb HT. pose proof (ilength_bound T).
  unfold merge.
  pose proof (for_inv (fun (k : int) (st : int * int * array int) =>
     let '(i, j, T0) := st in
     (to_Z lo <= to_Z i <= to_Z mid)%Z /\ (to_Z mid <= to_Z j <= to_Z hi)%Z /\
     (to_Z i - to_Z lo + (to_Z j - to_Z mid) = to_Z k - to_Z lo)%Z /\
     PArray.length T0 = PArray.length T /\
     sg T0 lo k ++ lmerge (lek key) (sg A i mid) (sg A j hi)
       = lmerge (lek key) (sg A lo mid) (sg A mid hi))
     hi lo (merge_step key A mid hi) (lo, mid, T)) as Hf.
  destruct (loop hi (fun _ _ => true) (merge_step key A mid hi) lo (lo, mid, T))
    as [[iF jF] T'].
  destruct Hf as (HiF & HjF & HcF & HLF & HIF).
  - lia.
  - split; [lia |]. split; [lia |]. split; [lia |]. split; [reflexivity |].
    rewrite sg_nil by lia. reflexivity.
  - intros k [[i j] T0] Hk (Hi & Hj & Hc & HL & HI).
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
    assert (HkT : (to_Z k < to_Z (PArray.length T0))%Z) by (rewrite HL; lia).
    unfold merge_step.
    destruct (i <? mid) eqn:Eim.
    + rewrite Uint63.ltb_spec in Eim.
      assert (Ei : to_Z (i + 1) = (to_Z i + 1)%Z) by sia.
      rewrite (sg_cons A i mid Eim) in HI.
      destruct (hi <=? j) eqn:Ejh.
      * rewrite Uint63.leb_spec in Ejh. rewrite (sg_nil A j hi) in HI by lia.
        rewrite lmerge_nil_r in HI.
        split; [lia |]. split; [lia |]. split; [lia |]. split; [rewrite ilength_set; exact HL |].
        rewrite sg_snoc_set by lia. rewrite (sg_nil A j hi) by lia. rewrite lmerge_nil_r.
        rewrite <- app_assoc. exact HI.
      * assert (Ejh' : (to_Z j < to_Z hi)%Z)
          by (assert (~ (to_Z hi <= to_Z j))%Z by (rewrite <- Uint63.leb_spec; congruence); lia).
        rewrite (sg_cons A j hi Ejh') in HI. rewrite lmerge_cons in HI.
        unfold lek in HI at 1.
        destruct (key.[A.[i]] <=? key.[A.[j]])%float eqn:Ec.
        -- split; [lia |]. split; [lia |]. split; [lia |]. split; [rewrite ilength_set; exact HL |].
           rewrite sg_snoc_set by lia. rewrite (sg_cons A j hi Ejh').
           rewrite <- app_assoc. exact HI.
        -- assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
           split; [lia |]. split; [lia |]. split; [lia |]. split; [rewrite ilength_set; exact HL |].
           rewrite sg_snoc_set by lia. rewrite (sg_cons A i mid Eim).
           rewrite <- app_assoc. exact HI.
    + assert (Eim' : ~ (to_Z i < to_Z mid)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      assert (Ejh : (to_Z j < to_Z hi)%Z) by lia.
      assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
      rewrite (sg_nil A i mid) in HI by lia. rewrite (sg_cons A j hi Ejh) in HI.
      split; [lia |]. split; [lia |]. split; [lia |]. split; [rewrite ilength_set; exact HL |].
      rewrite sg_snoc_set by lia. rewrite (sg_nil A i mid) by lia.
      rewrite <- app_assoc. exact HI.
  - split; [exact HLF |].
    rewrite (sg_nil A iF mid), (sg_nil A jF hi) in HIF by lia.
    simpl in HIF. rewrite app_nil_r in HIF. exact HIF.
Qed.

Lemma copy_spec : forall (A T : array int) lo hi,
  (to_Z lo <= to_Z hi)%Z -> (to_Z hi <= to_Z (PArray.length A))%Z ->
  let r := loop hi (fun _ _ => true) copy_step lo (A, T) in
  snd r = T /\ PArray.length (fst r) = PArray.length A /\
  sg (fst r) lo hi = sg T lo hi /\ agree A (fst r) lo hi.
Proof.
  intros A T lo hi Hb HA. pose proof (ilength_bound A). cbv zeta.
  apply (for_inv (fun (k : int) (st : array int * array int) =>
     snd st = T /\ PArray.length (fst st) = PArray.length A /\
     sg (fst st) lo k = sg T lo k /\ agree A (fst st) lo k)).
  - lia.
  - simpl. split; [reflexivity |]. split; [reflexivity |].
    split; [rewrite !sg_nil by lia; reflexivity | apply agree_refl].
  - intros k [A0 T0] Hk (E & HL & HS & HA0). simpl in *. subst T0.
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
    split; [reflexivity |]. split; [rewrite ilength_set; exact HL |]. split.
    + rewrite sg_snoc_set by lia. rewrite sg_snoc by lia. rewrite HS. reflexivity.
    + intros p Hp. rewrite iget_set_other by (intros ->; lia). apply HA0. lia.
Qed.

Lemma merge_copy_spec : forall key (A T : array int) lo mid hi,
  (to_Z lo <= to_Z mid <= to_Z hi)%Z -> (to_Z hi <= to_Z (PArray.length A))%Z ->
  (to_Z hi <= to_Z (PArray.length T))%Z ->
  let r := merge_copy key lo mid hi A T in
  PArray.length (fst r) = PArray.length A /\ PArray.length (snd r) = PArray.length T /\
  sg (fst r) lo hi = lmerge (lek key) (sg A lo mid) (sg A mid hi) /\ agree A (fst r) lo hi.
Proof.
  intros key A T lo mid hi Hb HA HT. cbv zeta. unfold merge_copy.
  destruct (merge_spec key A T lo mid hi Hb HT) as [HL HS].
  destruct (copy_spec A (merge key lo mid hi A T) lo hi ltac:(lia) HA) as (E1 & E2 & E3 & E4).
  rewrite E1, HL. split; [exact E2 |]. split; [reflexivity |]. split; [rewrite E3; exact HS | exact E4].
Qed.

(* ------------------------------------------------------------------ *)
(* Merge sort                                                          *)
(* ------------------------------------------------------------------ *)

Lemma guard_true : forall c lo hi, guard c lo hi = true ->
  (to_Z lo < to_Z hi)%Z /\ (to_Z c < to_Z hi - to_Z lo)%Z /\
  (2 * (to_Z (lo + (hi - lo) / 2) - to_Z lo) <= to_Z hi - to_Z lo
     <= 2 * (to_Z (lo + (hi - lo) / 2) - to_Z lo) + 1)%Z.
Proof.
  intros c lo hi H. unfold guard in H. apply andb_prop in H as [H1 H2].
  rewrite Uint63.ltb_spec in H1, H2.
  assert (Hs : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
  rewrite Hs in H2. split; [lia |]. split; [lia |]. sia.
Qed.

Lemma guard_false : forall c lo hi, (to_Z lo <= to_Z hi)%Z -> guard c lo hi = false ->
  (to_Z hi - to_Z lo <= to_Z c)%Z.
Proof.
  intros c lo hi Hle H. unfold guard in H.
  destruct (lo <? hi) eqn:E1; simpl in H.
  - rewrite Uint63.ltb_spec in E1.
    assert (Hs : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
    assert (~ (to_Z c < to_Z (hi - lo))%Z) by (rewrite <- Uint63.ltb_spec; congruence). lia.
  - assert (~ (to_Z lo < to_Z hi))%Z by (rewrite <- Uint63.ltb_spec; congruence).
    pose proof (to_Z_bounded c). lia.
Qed.

Lemma msort_eq : forall key lo hi A T H,
  msort_rec key lo hi A T H =
  match bdec (guard 1 lo hi) with
  | left Hg =>
      let m := lo + (hi - lo) / 2 in
      let '(A, T) := msort_rec key lo m A T (Acc_inv H (dec_left 1 lo hi Hg)) in
      let '(A, T) := msort_rec key m hi A T (Acc_inv H (dec_right 1 lo hi Hg one_ge_1)) in
      merge_copy key lo m hi A T
  | right _ => (A, T)
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma SS_short : forall {X} (Rl : X -> X -> Prop) (l : list X), (List.length l <= 1)%nat ->
  StronglySorted Rl l.
Proof.
  intros X Rl [| a [| b l]] H; simpl in H; try lia; repeat constructor.
Qed.

Section Msort.
Variable key : array float.
Variable K : int -> R.
Variable Pd : int -> Prop.
Hypothesis Hle : forall a b, Pd a -> Pd b -> (lek key a b = true <-> (K a <= K b)%R).

Lemma msort_spec : forall (A T : array int) lo hi H,
  (to_Z lo <= to_Z hi)%Z -> (to_Z hi <= to_Z (PArray.length A))%Z ->
  (to_Z hi <= to_Z (PArray.length T))%Z -> Forall Pd (sg A lo hi) ->
  let r := msort_rec key lo hi A T H in
  PArray.length (fst r) = PArray.length A /\ PArray.length (snd r) = PArray.length T /\
  Permutation (sg (fst r) lo hi) (sg A lo hi) /\
  StronglySorted (Rk K) (sg (fst r) lo hi) /\ agree A (fst r) lo hi.
Proof.
  assert (G : forall nn (A T : array int) lo hi H, gap hi lo = nn ->
    (to_Z lo <= to_Z hi)%Z -> (to_Z hi <= to_Z (PArray.length A))%Z ->
    (to_Z hi <= to_Z (PArray.length T))%Z -> Forall Pd (sg A lo hi) ->
    let r := msort_rec key lo hi A T H in
    PArray.length (fst r) = PArray.length A /\ PArray.length (snd r) = PArray.length T /\
    Permutation (sg (fst r) lo hi) (sg A lo hi) /\
    StronglySorted (Rk K) (sg (fst r) lo hi) /\ agree A (fst r) lo hi).
  2: { intros. eapply G; eauto. }
  intros nn. induction nn as [nn IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros A T lo hi H En Hlh HA HT HP. cbv zeta. rewrite msort_eq.
  destruct (bdec (guard 1 lo hi)) as [Hg | Hg].
  - pose proof (guard_true _ _ _ Hg) as (Hlt & Hc & Hm). cbv zeta.
    set (m := lo + (hi - lo) / 2) in *.
    pose proof (ilength_bound A).
    rewrite (sg_app A lo m hi) in HP by lia. apply Forall_app in HP as [HP1 HP2].
    match goal with |- context [msort_rec key lo m A T ?H1] => set (Hl := H1) end.
    pose proof (IH (gap m lo) ltac:(rewrite <- En; apply (dec_left 1 lo hi Hg))
       A T lo m Hl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HP1) as R1.
    cbv zeta in R1.
    destruct (msort_rec key lo m A T Hl) as [A1 T1]. simpl in R1.
    destruct R1 as (L1 & LT1 & P1 & S1 & G1).
    assert (E2 : sg A1 m hi = sg A m hi) by (apply (agree_sg A A1 lo m); auto; lia).
    match goal with |- context [msort_rec key m hi A1 T1 ?H1] => set (Hr := H1) end.
    pose proof (IH (gap hi m) ltac:(rewrite <- En; apply (dec_right 1 lo hi Hg one_ge_1))
       A1 T1 m hi Hr eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite E2; exact HP2)) as R2.
    cbv zeta in R2.
    destruct (msort_rec key m hi A1 T1 Hr) as [A2 T2]. simpl in R2.
    destruct R2 as (L2 & LT2 & P2 & S2 & G2).
    assert (E1 : sg A2 lo m = sg A1 lo m) by (apply (agree_sg A1 A2 m hi); auto; lia).
    pose proof (merge_copy_spec key A2 T2 lo m hi ltac:(lia) ltac:(lia) ltac:(lia)) as R3.
    cbv zeta in R3. destruct (merge_copy key lo m hi A2 T2) as [A3 T3]. simpl in R3 |- *.
    destruct R3 as (L3 & LT3 & HS3 & G3).
    split; [congruence |]. split; [congruence |].
    assert (PL : Permutation (sg A2 lo m) (sg A lo m)) by (rewrite E1; exact P1).
    assert (PR : Permutation (sg A2 m hi) (sg A m hi)) by (rewrite <- E2; exact P2).
    split; [| split].
    + rewrite HS3, (sg_app A lo m hi) by lia.
      eapply perm_trans; [apply lmerge_perm |]. apply Permutation_app; auto.
    + rewrite HS3. apply (lmerge_sorted _ K Pd Hle).
      * apply (Permutation_Forall (Permutation_sym PL)). exact HP1.
      * apply (Permutation_Forall (Permutation_sym PR)). exact HP2.
      * rewrite E1; exact S1.
      * exact S2.
    + apply (agree_tr A A2 A3 lo hi); [| exact G3].
      apply (agree_tr A A1 A2 lo hi).
      * apply (agree_widen A A1 lo hi lo m G1); lia.
      * apply (agree_widen A1 A2 lo hi m hi G2); lia.
  - pose proof (guard_false _ _ _ Hlh Hg) as Hs. simpl.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [apply SS_short; rewrite sg_length; change (to_Z 1) with 1%Z in Hs; lia | apply agree_refl].
Qed.

End Msort.

(* ------------------------------------------------------------------ *)
(* The greedy lower bound, on the math side                            *)
(* ------------------------------------------------------------------ *)

Section Greedy.
Variables (a : R) (ls rs : list R).
Local Open Scope R_scope.

(* a selection, as a list of indices of intervals *)
Definition Valid (sel : list N) : Prop := forall i, In i sel -> (i < len ls)%N.

(* sel covers [a, y] *)
Definition CovL (sel : list N) (y : R) : Prop :=
  forall z, a <= z <= y -> exists i, In i sel /\ get_list_R ls i <= z <= get_list_R rs i.

Lemma chain_ge : forall (c : nat -> R) m, c 0%nat = a ->
  (forall j, (j < m)%nat -> c j <= c (S j)) -> forall j, (j <= m)%nat -> a <= c j.
Proof.
  intros c m H0 Hm j. induction j as [| j IH]; intros Hj.
  - rewrite H0; lra.
  - specialize (Hm j ltac:(lia)). specialize (IH ltac:(lia)). lra.
Qed.

(* c_0 = a, and c_{j+1} bounds c_j and the reach of every interval
   starting at or before c_j: a selection of at most m intervals covering
   [a, y] has y <= c_m. *)
Lemma lb : forall m (c : nat -> R), c 0%nat = a ->
  (forall j, (j < m)%nat -> c j <= c (S j)) ->
  (forall j i, (j < m)%nat -> (i < len ls)%N -> get_list_R ls i <= c j -> get_list_R rs i <= c (S j)) ->
  forall sel y, (List.length sel <= m)%nat -> Valid sel -> a <= y -> CovL sel y -> y <= c m.
Proof.
  induction m as [| m IH]; intros c H0 Hmono Hstep sel y HS HV Hay Hcov.
  - destruct sel; [| simpl in HS; lia].
    destruct (Hcov a ltac:(lra)) as (i & [] & _).
  - destruct (Hcov y ltac:(lra)) as (j & Hj & Hlj & Hrj).
    destruct (Rle_lt_dec (get_list_R ls j) (c m)) as [Hle | Hlt].
    + pose proof (Hstep m j ltac:(lia) (HV j Hj) Hle). lra.
    + exfalso.
      pose proof (chain_ge c (S m) H0 Hmono m ltac:(lia)) as Ham.
      set (y' := (c m + get_list_R ls j) / 2).
      assert (Hy' : y' <= c m).
      { apply (IH c H0 (fun k Hk => Hmono k ltac:(lia)) (fun k i Hk => Hstep k i ltac:(lia))
                (remove N.eq_dec j sel) y').
        - pose proof (remove_length_lt N.eq_dec sel j Hj). lia.
        - intros i Hi. apply in_remove in Hi as [Hi _]. apply HV, Hi.
        - unfold y'. lra.
        - intros z Hz. destruct (Hcov z ltac:(unfold y' in Hz; lra)) as (i & Hi & Hli & Hri).
          exists i. split; [| lra]. apply in_in_remove; [| exact Hi].
          intros ->. unfold y' in Hz. lra. }
      unfold y' in Hy'. lra.
Qed.

Lemma covering_conv : forall b t, Prelude.covering a b ls rs t -> Valid t /\ CovL t b.
Proof.
  intros b t [HV HC]. split.
  - intros i Hi. apply In_nth with (d := 0%N) in Hi as (k & Hk & <-).
    specialize (HV (N.of_nat k)). unfold get_list_N, len in HV. rewrite Nat2N.id in HV.
    apply HV. lia.
  - intros z Hz. destruct (HC z Hz) as (k & Hk & Hin).
    exists (get_list_N t k). split; [| exact Hin].
    unfold get_list_N. apply nth_In. unfold len in Hk. lia.
Qed.

End Greedy.

(* ------------------------------------------------------------------ *)
(* The output copy                                                     *)
(* ------------------------------------------------------------------ *)

Lemma copy_out_spec : forall (W : array int) (k : int), (to_Z k <= 4194303)%Z ->
  let O := loop k (fun _ _ => true) (copy_out W) 0 (PArray.make k 0) in
  PArray.length O = k /\ (forall q, (to_Z q < to_Z k)%Z -> O.[q] = W.[q]).
Proof.
  intros W n Hn. cbv zeta.
  assert (Lm : PArray.length (PArray.make n 0) = n).
  { rewrite ilength_make. replace (n <=? max_length) with true; [reflexivity |].
    symmetry. rewrite Uint63.leb_spec. exact Hn. }
  apply (for_inv (fun k (P : array int) => PArray.length P = n /\
     (forall q, (to_Z q < to_Z k)%Z -> P.[q] = W.[q]))).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - split; [exact Lm |]. intros q Hq. change (to_Z 0) with 0%Z in Hq. pose proof (to_Z_bounded q). lia.
  - intros k P Hk (HL & HP). unfold copy_out. split; [rewrite ilength_set; exact HL |].
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
    intros q Hq. destruct (Z.eq_dec (to_Z q) (to_Z k)) as [E | E].
    + apply to_Z_inj in E. subst q. apply iget_set_same. rewrite Uint63.ltb_spec, HL. lia.
    + rewrite iget_set_other by (intros ->; lia). apply HP. lia.
Qed.

Lemma t_nth : forall (f : nat -> N) K j d, (j < K)%nat -> nth j (map f (seq 0 K)) d = f j.
Proof.
  intros f K j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The main section                                                    *)
(* ------------------------------------------------------------------ *)

Section Main.
Variables (a b : R) (ls rs : list R) (x y : float) (xs ys : array float).
Hypothesis Hv : valid_input a b ls rs.
Hypothesis Hx : repr x a.
Hypothesis Hy : repr y b.
Hypothesis Hxs : repr xs ls.
Hypothesis Hys : repr ys rs.

Local Notation n := (PArray.length xs).

Definition Lm (i : int) : R := get_list_R ls (Z.to_N (to_Z i)).
Definition Rm (i : int) : R := get_list_R rs (Z.to_N (to_Z i)).

Lemma len_ls : Z.of_nat (List.length ls) = to_Z n.
Proof. exact (proj1 Hxs). Qed.

Lemma len_rs : Z.of_nat (List.length rs) = to_Z n.
Proof.
  rewrite <- len_ls. pose proof (vi_lengths _ _ _ _ Hv) as E. unfold len in E. lia.
Qed.

Lemma n_bounds : (1 <= to_Z n <= 20000)%Z.
Proof. rewrite <- len_ls. pose proof (vi_length _ _ _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma len_ys : Z.of_nat (List.length rs) = to_Z (PArray.length ys).
Proof. exact (proj1 Hys). Qed.

Lemma repr_nth : forall (l : list R) (t : array float) (i : int), repr t l ->
  (to_Z i < Z.of_nat (List.length l))%Z -> repr t.[i] (nth (Z.to_nat (to_Z i)) l 0%R).
Proof.
  intros l t i [_ H] Hi. destruct (H (Z.to_nat (to_Z i)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in R. exact R.
Qed.

Lemma repr_L : forall i, (to_Z i < to_Z n)%Z -> repr xs.[i] (Lm i).
Proof.
  intros i Hi. unfold Lm, get_list_R. rewrite Z_N_nat.
  refine (repr_nth ls xs i Hxs _). rewrite len_ls; exact Hi.
Qed.

Lemma repr_R : forall i, (to_Z i < to_Z n)%Z -> repr ys.[i] (Rm i).
Proof.
  intros i Hi. unfold Rm, get_list_R. rewrite Z_N_nat.
  refine (repr_nth rs ys i Hys _). rewrite len_rs; exact Hi.
Qed.

Lemma lek_L : forall i j, (to_Z i < to_Z n)%Z -> (to_Z j < to_Z n)%Z ->
  (lek xs i j = true <-> (Lm i <= Lm j)%R).
Proof. intros i j Hi Hj. unfold lek. apply repr_leb_iff; apply repr_L; assumption. Qed.

(* what the sweep needs of the sorted index array *)
Definition Pgood (P : array int) : Prop :=
  (forall p, (to_Z p < to_Z n)%Z -> (to_Z P.[p] < to_Z n)%Z) /\
  (forall i, (to_Z i < to_Z n)%Z -> exists p, (to_Z p < to_Z n)%Z /\ P.[p] = i) /\
  (forall p p', (to_Z p <= to_Z p' < to_Z n)%Z -> (Lm P.[p] <= Lm P.[p'])%R).

Definition ext (c : nat -> R) (k : nat) (v : R) : nat -> R :=
  fun j => if Nat.eqb j (S k) then v else c j.

Lemma ext_new : forall c k v, ext c k v (S k) = v.
Proof. intros. unfold ext. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma ext_old : forall c k v j, j <> S k -> ext c k v j = c j.
Proof. intros c k v j H. unfold ext. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Section Sweep.
Variable P : array int.
Hypothesis HP : Pgood P.

Lemma HPin : forall p, (to_Z p < to_Z n)%Z -> (to_Z P.[p] < to_Z n)%Z.
Proof. exact (proj1 HP). Qed.
Lemma HPsort : forall p p', (to_Z p <= to_Z p' < to_Z n)%Z -> (Lm P.[p] <= Lm P.[p'])%R.
Proof. exact (proj2 (proj2 HP)). Qed.

Lemma all_pos : forall i : N, (i < len ls)%N ->
  exists p, (to_Z p < to_Z n)%Z /\ Lm P.[p] = get_list_R ls i /\ Rm P.[p] = get_list_R rs i.
Proof.
  intros i Hi. unfold len in Hi. pose proof len_ls. pose proof (flength_bound xs).
  set (m := of_Z (Z.of_N i)).
  assert (Em : to_Z m = Z.of_N i) by (apply to_Z_of_Z_small; pose proof wB_big; lia).
  destruct (proj1 (proj2 HP) m ltac:(lia)) as (p & Hp & Ep).
  exists p. split; [exact Hp |]. unfold Lm, Rm. rewrite Ep, Em, N2Z.id. split; reflexivity.
Qed.

Lemma scan_spec : forall q cur cr, repr cur cr -> (to_Z q <= to_Z n)%Z ->
  forall q' found best bi,
  loop n (scan_cont xs P cur) (scan_step ys P) q (q, false, cur, 0) = (q', found, best, bi) ->
  (to_Z q <= to_Z q' <= to_Z n)%Z /\
  ((to_Z q' < to_Z n)%Z -> (cr < Lm P.[q'])%R) /\
  exists br, repr best br /\ (cr <= br)%R /\
  (forall p, (to_Z q <= to_Z p < to_Z q')%Z -> (Lm P.[p] <= cr)%R /\ (Rm P.[p] <= br)%R) /\
  (found = true -> (to_Z q < to_Z q')%Z /\ (to_Z bi < to_Z n)%Z /\ (Lm bi <= cr)%R /\ Rm bi = br) /\
  (found = false -> br = cr /\ forall p, (to_Z q <= to_Z p < to_Z q')%Z -> (Rm P.[p] < cr)%R).
Proof.
  intros q cur cr Hc Hq q' found best bi E. pose proof (flength_bound xs) as Hml.
  pose proof (loop_inv (fun j (st : int * bool * float * int) =>
    let '(qq, f, bst, bj) := st in qq = j /\
    exists br, repr bst br /\ (cr <= br)%R /\
    (forall p, (to_Z q <= to_Z p < to_Z j)%Z -> (Lm P.[p] <= cr)%R /\ (Rm P.[p] <= br)%R) /\
    (f = true -> (to_Z q < to_Z j)%Z /\ (to_Z bj < to_Z n)%Z /\ (Lm bj <= cr)%R /\ Rm bj = br) /\
    (f = false -> br = cr /\ forall p, (to_Z q <= to_Z p < to_Z j)%Z -> (Rm P.[p] < cr)%R))
    n q (scan_cont xs P cur) (scan_step ys P) (q, false, cur, 0) Hq) as G.
  rewrite E in G.
  destruct G as (j & Hj & Inv & Hend).
  - split; [reflexivity |]. exists cr. split; [exact Hc |]. split; [lra |].
    split; [intros p Hp; lia |]. split; [discriminate |]. split; [reflexivity | intros p Hp; lia].
  - intros j [[[qq f] bst] bj] Hj (-> & br & Hb & Hcb & Hall & Hf & Hnf) Hcont.
    unfold scan_cont in Hcont.
    assert (HPj : (to_Z P.[j] < to_Z n)%Z) by (apply HPin; lia).
    assert (HL : (Lm P.[j] <= cr)%R) by (apply (repr_leb_iff _ _ _ _ (repr_L _ HPj) Hc); exact Hcont).
    assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
    pose proof (repr_R _ HPj) as HR.
    unfold scan_step. destruct (bst <=? ys.[P.[j]])%float eqn:Eb.
    + apply (repr_leb_iff _ _ _ _ Hb HR) in Eb.
      split; [reflexivity |]. exists (Rm P.[j]). split; [exact HR |]. split; [lra |].
      split.
      * intros p Hp. destruct (Z.eq_dec (to_Z p) (to_Z j)) as [Ep | Ep].
        -- apply to_Z_inj in Ep. subst p. split; lra.
        -- destruct (Hall p ltac:(lia)). split; lra.
      * split; [intros _; split; [lia |]; split; [exact HPj |]; split; [exact HL | reflexivity] | discriminate].
    + assert (Eb' : ~ (br <= Rm P.[j])%R) by (rewrite <- (repr_leb_iff _ _ _ _ Hb HR); congruence).
      split; [reflexivity |]. exists br. split; [exact Hb |]. split; [exact Hcb |].
      split; [| split].
      * intros p Hp. destruct (Z.eq_dec (to_Z p) (to_Z j)) as [Ep | Ep].
        -- apply to_Z_inj in Ep. subst p. split; lra.
        -- apply Hall. lia.
      * intros Hf'. destruct (Hf Hf') as (H1 & H2 & H3 & H4). split; [lia |]. auto.
      * intros Hf'. destruct (Hnf Hf') as [H1 H2]. split; [exact H1 |].
        intros p Hp. destruct (Z.eq_dec (to_Z p) (to_Z j)) as [Ep | Ep].
        -- apply to_Z_inj in Ep. subst p. lra.
        -- apply H2. lia.
  - destruct Inv as (Eq & br & Hb & Hcb & Hall & Hf & Hnf). subst q'.
    split; [lia |]. split.
    + intros Hlt. destruct Hend as [Hend | [_ Hc2]]; [lia |].
      unfold scan_cont in Hc2.
      assert (HPj : (to_Z P.[j] < to_Z n)%Z) by (apply HPin; lia).
      destruct (Rlt_le_dec cr (Lm P.[j])) as [Hl | Hl]; [exact Hl |].
      apply (repr_leb_iff _ _ _ _ (repr_L _ HPj) Hc) in Hl. congruence.
    + exists br. split; [exact Hb |]. split; [exact Hcb |]. split; [exact Hall |]. split; [exact Hf | exact Hnf].
Qed.

(* the reach of a round bounds every interval starting at or before cur *)
Lemma ub_round : forall q q' cr br,
  (to_Z q <= to_Z q')%Z -> (cr <= br)%R ->
  (forall p, (to_Z p < to_Z q)%Z -> (Rm P.[p] <= cr)%R) ->
  (forall p, (to_Z q <= to_Z p < to_Z q')%Z -> (Rm P.[p] <= br)%R) ->
  ((to_Z q' < to_Z n)%Z -> (cr < Lm P.[q'])%R) ->
  forall i, (i < len ls)%N -> (get_list_R ls i <= cr)%R -> (get_list_R rs i <= br)%R.
Proof.
  intros q q' cr br Hqq Hcb H1 H2 H3 i Hi Hli.
  destruct (all_pos i Hi) as (p & Hp & EL & ER). rewrite <- EL in Hli. rewrite <- ER.
  destruct (Z_lt_le_dec (to_Z p) (to_Z q)) as [Hpq | Hpq].
  - specialize (H1 p Hpq). lra.
  - destruct (Z_lt_le_dec (to_Z p) (to_Z q')) as [Hpq' | Hpq'].
    + apply H2; lia.
    + exfalso. assert (Hq'n : (to_Z q' < to_Z n)%Z) by lia.
      pose proof (H3 Hq'n). pose proof (HPsort q' p ltac:(lia)). lra.
Qed.

Definition Inv (q cnt : int) (k : nat) (cur : float) (W : array int) (c : nat -> R) : Prop :=
  (to_Z q <= to_Z n)%Z /\ (to_Z cnt <= to_Z q)%Z /\ Z.of_nat k = to_Z cnt /\
  PArray.length W = n /\
  (forall j, (to_Z j < to_Z cnt)%Z -> (to_Z W.[j] < to_Z n)%Z) /\
  repr cur (c k) /\ c O = a /\
  (forall j, (j < k)%nat -> (c j <= c (S j))%R) /\
  (forall j i, (j < k)%nat -> (i < len ls)%N -> (get_list_R ls i <= c j)%R ->
     (get_list_R rs i <= c (S j))%R) /\
  (forall j, (0 < j <= k)%nat -> (c j < b)%R) /\
  (forall p, (to_Z p < to_Z q)%Z -> (Rm P.[p] <= c k)%R) /\
  ((0 < k)%nat -> forall z, (a <= z <= c k)%R ->
     exists j, (to_Z j < to_Z cnt)%Z /\ (Lm W.[j] <= z <= Rm W.[j])%R) /\
  (to_Z cnt = 0%Z -> to_Z q = 0%Z).

Definition Post (r : option (array int * int)) : Prop :=
  match r with
  | Some (W, k) => (0 < to_Z k <= to_Z n)%Z /\ PArray.length W = n /\
      (forall j, (to_Z j < to_Z k)%Z -> (to_Z W.[j] < to_Z n)%Z) /\
      (forall z, (a <= z <= b)%R -> exists j, (to_Z j < to_Z k)%Z /\ (Lm W.[j] <= z <= Rm W.[j])%R) /\
      (forall sel, Valid ls sel -> CovL a ls rs sel b -> (Z.to_nat (to_Z k) <= List.length sel)%nat)
  | None => forall sel, Valid ls sel -> ~ CovL a ls rs sel b
  end.

Lemma sweep_eq : forall q cnt cur W H,
  sweep xs ys y P n q cnt cur W H =
  match loop n (scan_cont xs P cur) (scan_step ys P) q (q, false, cur, 0) with
  | (q', found, best, bi) =>
    if andb found (orb (cnt =? 0)%uint63 (cur <? best)%float) then
      let W := W.[cnt <- bi] in
      if (y <=? best)%float then Some (W, cnt + 1)
      else match bdec (adv n q q') with
           | left Ha => sweep xs ys y P n q' (cnt + 1) best W (Acc_inv H (dec_adv n q q' Ha))
           | right _ => None
           end
    else None
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma sweep_spec : forall q cnt k cur W c H, Inv q cnt k cur W c ->
  Post (sweep xs ys y P n q cnt cur W H).
Proof.
  assert (G : forall nn q cnt k cur W c H, gap n q = nn -> Inv q cnt k cur W c ->
    Post (sweep xs ys y P n q cnt cur W H)).
  2: { intros. eapply G; eauto. }
  intros nn. induction nn as [nn IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros q cnt k cur W c H En HI. rewrite sweep_eq.
  destruct HI as (Hq & Hcq & Hk & HW & HWv & Hcur & Hc0 & Hmono & Hstep & Hlb & Hpre & Hcov & H0).
  pose proof (flength_bound xs) as Hml. pose proof n_bounds as Hn.
  pose proof (vi_target _ _ _ _ Hv) as Hab.
  destruct (loop n (scan_cont xs P cur) (scan_step ys P) q (q, false, cur, 0))
    as [[[q' found] best] bi] eqn:E.
  destruct (scan_spec q cur (c k) Hcur Hq q' found best bi E)
    as (Hqq & Hstop & br & Hbr & Hcb & Hscan & Hf & Hnf).
  destruct (andb found (orb (cnt =? 0)%uint63 (cur <? best)%float)) eqn:Eok.
  - apply andb_prop in Eok as [Ef Eok2]. subst found.
    destruct (Hf eq_refl) as (Hqlt & Hbi & HLbi & HRbi).
    assert (Hcn : (to_Z cnt < to_Z n)%Z) by lia.
    assert (Ecnt : to_Z (cnt + 1) = (to_Z cnt + 1)%Z) by sia.
    set (W1 := W.[cnt <- bi]).
    assert (HW1 : PArray.length W1 = n) by (unfold W1; rewrite ilength_set; exact HW).
    assert (HW1a : forall j, (to_Z j < to_Z cnt)%Z -> W1.[j] = W.[j])
      by (intros j Hj; unfold W1; apply iget_set_other; intros ->; lia).
    assert (HW1b : W1.[cnt] = bi)
      by (unfold W1; apply iget_set_same; rewrite Uint63.ltb_spec, HW; lia).
    assert (HW1v : forall j, (to_Z j < to_Z (cnt + 1))%Z -> (to_Z W1.[j] < to_Z n)%Z).
    { intros j Hj. destruct (Z.eq_dec (to_Z j) (to_Z cnt)) as [Ej | Ej].
      - apply to_Z_inj in Ej. subst j. rewrite HW1b. exact Hbi.
      - rewrite HW1a by lia. apply HWv. lia. }
    assert (HUB : forall i, (i < len ls)%N -> (get_list_R ls i <= c k)%R -> (get_list_R rs i <= br)%R).
    { apply (ub_round q q' (c k) br); auto; [lia |].
      intros p Hp. exact (proj2 (Hscan p Hp)). }
    assert (HCov1 : forall z, (a <= z <= br)%R ->
      exists j, (to_Z j < to_Z (cnt + 1))%Z /\ (Lm W1.[j] <= z <= Rm W1.[j])%R).
    { intros z Hz. destruct (Rle_lt_dec z (c k)) as [Hzc | Hzc].
      - destruct (Nat.eq_dec k 0) as [Hk0 | Hk0].
        + exists cnt. split; [lia |]. rewrite HW1b. subst k. rewrite Hc0 in HLbi. lra.
        + destruct (Hcov ltac:(lia) z ltac:(lra)) as (j & Hj & Hjz).
          exists j. split; [lia |]. rewrite HW1a by exact Hj. exact Hjz.
      - exists cnt. split; [lia |]. rewrite HW1b. lra. }
    destruct (y <=? best)%float eqn:Eb.
    + apply (repr_leb_iff _ _ _ _ Hy Hbr) in Eb.
      simpl. split; [lia |]. split; [exact HW1 |]. split; [exact HW1v |]. split.
      * intros z Hz. apply HCov1. lra.
      * intros sel HV HC. replace (Z.to_nat (to_Z (cnt + 1))) with (S k) by lia.
        destruct (le_lt_dec (S k) (List.length sel)) as [Hle | Hlt]; [exact Hle | exfalso].
        destruct (List.length sel) as [| m] eqn:ES.
        -- destruct sel; [| discriminate]. destruct (HC a ltac:(lra)) as (i & [] & _).
        -- pose proof (lb a ls rs (S m) c Hc0 (fun j Hj => Hmono j ltac:(lia))
             (fun j i Hj => Hstep j i ltac:(lia)) sel b ltac:(lia) HV Hab HC) as Hbm.
           pose proof (Hlb (S m) ltac:(lia)). lra.
    + assert (Hbb : (br < b)%R).
      { destruct (Rlt_le_dec br b) as [Hl | Hl]; [exact Hl |].
        apply (repr_leb_iff _ _ _ _ Hy Hbr) in Hl. congruence. }
      assert (Hadv : adv n q q' = true).
      { unfold adv. apply andb_true_intro. split; [rewrite Uint63.ltb_spec | rewrite Uint63.leb_spec]; lia. }
      destruct (bdec (adv n q q')) as [Ha | Ha]; [| congruence].
      apply (IH (gap n q')) with (k := S k) (c := ext c k br).
      * rewrite <- En. apply dec_adv; exact Ha.
      * reflexivity.
      * unfold Inv. split; [lia |]. split; [lia |]. split; [lia |].
        split; [exact HW1 |]. split; [exact HW1v |].
        split; [rewrite ext_new; exact Hbr |].
        split; [rewrite ext_old by lia; exact Hc0 |].
        split.
        { intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hjk].
          - rewrite ext_new, ext_old by lia. exact Hcb.
          - rewrite !ext_old by lia. apply Hmono. lia. }
        split.
        { intros j i Hj Hi Hli. destruct (Nat.eq_dec j k) as [-> | Hjk].
          - rewrite ext_new. rewrite ext_old in Hli by lia. apply HUB; assumption.
          - rewrite ext_old in Hli by lia. rewrite ext_old by lia. apply Hstep; auto; lia. }
        split.
        { intros j Hj. destruct (Nat.eq_dec j (S k)) as [-> | Hjk].
          - rewrite ext_new. exact Hbb.
          - rewrite ext_old by exact Hjk. apply Hlb. lia. }
        split.
        { intros p Hp. rewrite ext_new. destruct (Z_lt_le_dec (to_Z p) (to_Z q)) as [Hpq | Hpq].
          - specialize (Hpre p Hpq). lra.
          - apply Hscan. lia. }
        split.
        { intros _. rewrite ext_new. exact HCov1. }
        intros Hz. lia.
  - simpl. intros sel HV HC.
    destruct (Nat.eq_dec k 0) as [Hk0 | Hk0].
    + subst k. assert (Hq0 : to_Z q = 0%Z) by (apply H0; lia).
      assert (Ec0 : (cnt =? 0) = true) by (rewrite Uint63.eqb_spec; apply to_Z_inj; simpl in Hk; rewrite <- Hk; reflexivity).
      rewrite Ec0 in Eok. simpl in Eok. destruct found; [discriminate |].
      destruct (Hnf eq_refl) as [Ebr Hlt].
      destruct (HC a ltac:(lra)) as (i & Hi & Hli & Hri).
      destruct (all_pos i (HV i Hi)) as (p & Hp & EL & ER).
      rewrite Hc0 in Hstop, Hlt.
      destruct (Z_lt_le_dec (to_Z p) (to_Z q')) as [Hpq | Hpq].
      * specialize (Hlt p ltac:(lia)). lra.
      * assert (Hq'n : (to_Z q' < to_Z n)%Z) by lia.
        pose proof (Hstop Hq'n). pose proof (HPsort q' p ltac:(lia)). lra.
    + assert (Hsc : forall p, (to_Z q <= to_Z p < to_Z q')%Z -> (Rm P.[p] <= c k)%R).
      { intros p Hp. destruct found.
        - destruct (Hcb) as [Hlt' | Heq']; [| ].
          + assert (Hnl : ~ (c k < br)%R).
            { rewrite <- (repr_ltb_iff _ _ _ _ Hcur Hbr). intros Hl. rewrite Hl in Eok. simpl in Eok. destruct (cnt =? 0)%uint63; discriminate. }
            lra.
          + subst br. exact (proj2 (Hscan p Hp)).
        - destruct (Hnf eq_refl) as [_ Hlt]. specialize (Hlt p Hp). lra. }
      assert (Hfix : forall i, (i < len ls)%N -> (get_list_R ls i <= c k)%R -> (get_list_R rs i <= c k)%R).
      { exact (ub_round q q' (c k) (c k) ltac:(lia) (Rle_refl _) Hpre Hsc Hstop). }
      set (c' := fun j => c (Nat.min j k)).
      assert (Hcb' : (b <= c' (List.length sel + k)%nat)%R).
      { refine (lb a ls rs (List.length sel + k) c' _ _ _ sel b _ HV Hab HC); [| | | lia].
        - unfold c'. rewrite Nat.min_l by lia. exact Hc0.
        - intros j Hj. unfold c'. destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk].
          + rewrite Nat.min_l by lia. rewrite Nat.min_l by lia. apply Hmono. lia.
          + rewrite !Nat.min_r by lia. lra.
        - intros j i Hj Hi Hli. unfold c' in *. destruct (Nat.lt_ge_cases j k) as [Hjk | Hjk].
          + rewrite Nat.min_l in Hli by lia. rewrite Nat.min_l by lia. apply Hstep; auto.
          + rewrite Nat.min_r in Hli by lia. rewrite Nat.min_r by lia. apply Hfix; auto. }
      unfold c' in Hcb'. rewrite Nat.min_r in Hcb' by lia.
      pose proof (Hlb k ltac:(lia)). lra.
Qed.

End Sweep.

(* ------------------------------------------------------------------ *)
(* The whole function                                                  *)
(* ------------------------------------------------------------------ *)

Lemma iota_spec : forall n : int, (to_Z n <= 4194303)%Z ->
  let P := loop n (fun _ _ => true) iota_step 0 (PArray.make n 0) in
  PArray.length P = n /\ (forall q, (to_Z q < to_Z n)%Z -> P.[q] = q).
Proof.
  intros n Hn. cbv zeta.
  assert (Lm : PArray.length (PArray.make n 0) = n).
  { rewrite ilength_make. replace (n <=? max_length) with true; [reflexivity |].
    symmetry. rewrite Uint63.leb_spec. exact Hn. }
  apply (for_inv (fun k (P : array int) => PArray.length P = n /\
     (forall q, (to_Z q < to_Z k)%Z -> P.[q] = q))).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - split; [exact Lm |]. intros q Hq. change (to_Z 0) with 0%Z in Hq. pose proof (to_Z_bounded q). lia.
  - intros k P Hk (HL & HP). unfold iota_step. split; [rewrite ilength_set; exact HL |].
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
    intros q Hq. destruct (Z.eq_dec (to_Z q) (to_Z k)) as [E | E].
    + apply to_Z_inj in E. subst q. apply iget_set_same. rewrite Uint63.ltb_spec, HL. lia.
    + rewrite iget_set_other by (intros ->; lia). apply HP. lia.
Qed.

Lemma cover_main : exists o : option (list N),
  repr (cover x y xs ys) o /\ cover_spec a b ls rs o.
Proof.
  unfold cover. pose proof n_bounds as Hn. pose proof (flength_bound xs) as Hml.
  destruct (iota_spec n ltac:(lia)) as [LP HP].
  set (P := loop n (fun _ _ => true) iota_step 0 (PArray.make n 0)) in *. clearbody P.
  assert (Z0 : to_Z 0 = 0%Z) by reflexivity.
  assert (Lmk : PArray.length (PArray.make n 0) = n).
  { rewrite ilength_make. replace (n <=? max_length) with true; [reflexivity |].
    symmetry. rewrite Uint63.leb_spec. exact Hml. }
  assert (InP : forall i, In i (sg P 0 n) <-> (to_Z i < to_Z n)%Z).
  { intros i. rewrite sg_In. split.
    - intros (p & Hp & <-). rewrite HP by lia. lia.
    - intros Hi. exists i. pose proof (to_Z_bounded i).
      split; [lia | apply HP; lia]. }
  pose proof (msort_spec xs Lm (fun i => (to_Z i < to_Z n)%Z) lek_L P (PArray.make n 0) 0 n
     (Zwf_well_founded 0 (gap n 0)) ltac:(lia) ltac:(lia) ltac:(lia)
     ltac:(rewrite Forall_forall; intros i Hi; apply InP; exact Hi)) as R1.
  cbv zeta in R1. destruct (msort_rec xs 0 n P (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))) as [P1 T1].
  simpl in R1. destruct R1 as (LP1 & _ & Perm1 & S1 & _).
  assert (InP1 : forall i, In i (sg P1 0 n) <-> (to_Z i < to_Z n)%Z).
  { intros i. rewrite <- InP. split; apply Permutation_in; [exact Perm1 | apply Permutation_sym; exact Perm1]. }
  assert (HG : Pgood P1).
  { split; [| split].
    - intros p Hp. apply InP1. apply sg_In. exists p. split; [lia | reflexivity].
    - intros i Hi. apply InP1 in Hi. apply sg_In in Hi as (p & Hp & E). exists p. split; [lia | exact E].
    - intros p p' Hpp. destruct (Z.eq_dec (to_Z p) (to_Z p')) as [E | E].
      + apply to_Z_inj in E. subst p'. lra.
      + pose proof (SS_nth _ (sg P1 0 n) (Z.to_nat (to_Z p)) (Z.to_nat (to_Z p')) 0 S1) as Hs.
        rewrite sg_length in Hs. rewrite !sg_nth in Hs by lia.
        rewrite Z0 in Hs. simpl in Hs.
        rewrite !Z2Nat.id in Hs by (pose proof (to_Z_bounded p); pose proof (to_Z_bounded p'); lia).
        rewrite !of_to_Z in Hs. apply Hs. lia. }
  assert (Hinit : Inv P1 0 0 0 x (PArray.make n 0) (fun _ => a)).
  { unfold Inv. rewrite Z0. split; [lia |]. split; [lia |]. split; [reflexivity |].
    split; [exact Lmk |]. split; [intros j Hj; pose proof (to_Z_bounded j); lia |].
    split; [exact Hx |]. split; [reflexivity |].
    split; [intros j Hj; lia |]. split; [intros j i Hj; lia |].
    split; [intros j Hj; lia |]. split; [intros p Hp; pose proof (to_Z_bounded p); lia |].
    split; [intros Hk; lia |]. intros _; reflexivity. }
  pose proof (sweep_spec P1 HG 0 0 0 x (PArray.make n 0) (fun _ => a)
     (Zwf_well_founded 0 (gap n 0)) Hinit) as HS.
  destruct (sweep xs ys y P1 n 0 0 x (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)))
    as [[W k] |]; simpl in HS.
  - destruct HS as (Hk & HWl & HWv & HC & Hmin).
    set (K := Z.to_nat (to_Z k)).
    set (f := fun j : nat => Z.to_N (to_Z W.[of_nat j])).
    exists (Some (map f (seq 0 K))).
    destruct (copy_out_spec W k ltac:(lia)) as [LO HO].
    set (O := loop k (fun _ _ => true) (copy_out W) 0 (PArray.make k 0)) in *. clearbody O.
    assert (Hlt : List.length (map f (seq 0 K)) = K) by (rewrite length_map, length_seq; reflexivity).
    assert (Eof : forall j, (j < K)%nat -> to_Z (of_nat j) = Z.of_nat j).
    { intros j Hj. rewrite of_Z_spec. apply Z.mod_small. pose proof wB_big. unfold K in Hj. lia. }
    split.
    + simpl. split.
      * rewrite Hlt. transitivity (to_Z k); [unfold K; lia | exact (f_equal to_Z (eq_sym LO))].
      * intros j Hj. rewrite Hlt in Hj. exists (f j). split.
        -- rewrite (nth_error_nth' _ 0%N) by (rewrite Hlt; exact Hj). f_equal. apply t_nth. exact Hj.
        -- simpl. unfold f.
           assert (Hq : (to_Z (of_nat j) < to_Z k)%Z) by (rewrite Eof by exact Hj; unfold K in Hj; lia).
           exact (f_equal (fun v => Z.to_N (to_Z v)) (HO (of_nat j) Hq)).
    + simpl. split; [split |].
      * intros j Hj. unfold get_list_N. unfold len in Hj. rewrite Hlt in Hj.
        rewrite t_nth by lia. unfold f.
        assert (Hj' : (to_Z (of_nat (N.to_nat j)) < to_Z k)%Z) by (rewrite Eof by lia; unfold K in Hj; lia).
        pose proof (HWv _ Hj'). pose proof len_ls. unfold len. lia.
      * intros z Hz. destruct (HC z Hz) as (j & Hj & Hjz).
        exists (Z.to_N (to_Z j)). split.
        -- unfold len. rewrite Hlt. unfold K. pose proof (to_Z_bounded j). lia.
        -- unfold get_list_N. rewrite t_nth by (unfold K; pose proof (to_Z_bounded j); lia).
           unfold f. rewrite Z_N_nat.
           replace (of_nat (Z.to_nat (to_Z j))) with j.
           ++ exact Hjz.
           ++ apply to_Z_inj. rewrite Eof by (unfold K; pose proof (to_Z_bounded j); lia).
              pose proof (to_Z_bounded j). lia.
      * intros t' Ht'. destruct (covering_conv a ls rs b t' Ht') as [HV' HC'].
        pose proof (Hmin t' HV' HC'). unfold len. rewrite Hlt. unfold K in *. lia.
  - exists None. split; [exact I |].
    intros t Ht. destruct (covering_conv a ls rs b t Ht) as [HV' HC']. exact (HS t HV' HC').
Qed.

End Main.

Lemma cover_correct :
  forall (a b : R) (ls rs : list R) (x y : float) (xs ys : array float),
    valid_input a b ls rs -> repr x a -> repr y b -> repr xs ls -> repr ys rs ->
    exists o : option (list N), repr (cover x y xs ys) o /\ cover_spec a b ls rs o.
Proof. intros. eapply cover_main; eassumption. Qed.

(* ================================================================== *)
(* Cost                                                                *)
(* ================================================================== *)

(* The bound cover_time (see the README's Complexity section).
   [Elpi complexity] translates, callee first, sumbool, bdec, andb, orb,
   guard, wloop, loop, merge_step, merge, copy_step, merge_copy,
   msort_rec, iota_step, scan_cont, scan_step, adv, sweep, copy_out and
   cover (above, after each definition).  The proof:
   - wloop_time_gen / loop_time_gen: the generic loop, each step costing at
     most K (plus a potential), at most (2 K + 25) (hi - i) + 30 in all;
   - wloop_time_amort / loop_time_amort: the same, paid by the distance the
     index travels (read on the final state), for the scan of a round;
   - merge_time, merge_copy_time (320 L + 200), msort_time
     (cost + 1000 <= 400 L log2_up L + 2000 max L 1, L = hi - lo);
   - scan_time (cost + 85 (n - q') <= 85 (n - q) + 65, q' the position
     reached), sweep_time (400 (n - q) + 400: potential n - q, each round
     moves q forward, adv q q');
   - sweep_len (the answer has at most n cells), main_time and cover_time
     (c1 = c2 = 3000).
   cbn (inside cost_simpl) must not unfold gap (φ of a variable) nor the
   well-founded functions applied to an Acc proof: the local [simpl never]
   below. *)

#[local] Arguments gap : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. unfold bdec_cost. destruct w; cbn; lia. Qed.

Lemma gap_succ hi k : (k <? hi) = true -> Z.to_nat (gap hi (k + 1)) = (Z.to_nat (gap hi k) - 1)%nat /\ (0 < Z.to_nat (gap hi k))%nat.
Proof. intros H. rewrite Uint63.ltb_spec in H. unfold gap.
  assert (φ (k + 1) = φ k + 1)%Z by (pose proof (to_Z_bounded hi); sia). lia. Qed.

Ltac zero_partials := repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch T with forall _, _ => change (@cost T X) with 0%nat end end.

Section W.
Context {St : Type} (StC : St -> Type).
Lemma wloop_time_gen (Inv : int -> St -> Prop) (Pot : St -> nat) (K : nat)
  hi hiC cont contC f fC
  (Hc : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z ->
     (cost (contC j jC) + cost (extract (contC j jC) t tC) <= K)%nat)
  (Hf : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z -> cont j t = true ->
     (cost (fC j jC) + cost (extract (fC j jC) t tC) + Pot (f j t) <= Pot t + K)%nat)
  (HI : forall j t, Inv j t -> (φ j < φ hi)%Z -> cont j t = true -> Inv (j + 1) (f j t))
  i iC s sC H HC : Inv i s ->
  (cost (extract (extract (extract (extract (extract (extract (wloop_cost stepsCM St StC) hi hiC) cont contC) f fC) i iC) s sC) H HC) <= (2 * K + 25) * Z.to_nat (gap hi i) + Pot s + 10)%nat.
Proof.
  unfold wloop_cost. cbn.
  match goal with |- context [@cost ?T (?G hi hiC cont contC f fC i iC s sC H HC)] =>
    assert (HG : forall k i iC s sC H HC, (Z.to_nat (gap hi i) <= k)%nat -> Inv i s ->
       (cost (G hi hiC cont contC f fC i iC s sC H HC) <= (2 * K + 25) * k + Pot s + 10)%nat) end.
  { induction k as [|k IH]; intros i' iC' s' sC' [g] HC' Hk Hinv;
      cost_simpl;
      pose proof (bdec_time (i' <? hi) (bool_w (i' <? hi))) as HB;
      cost_destruct (bdec (i' <? hi)); cost_simpl.
    - exfalso. destruct (gap_succ _ _ e). lia.
    - lia.
    - pose proof e as Hlt. rewrite Uint63.ltb_spec in Hlt.
      pose proof (Hc i' iC' s' sC' Hinv Hlt) as HC1. cost_align HC1.
      cost_destruct_eqn (cont i' s') Ec.
      + cost_simpl.
        destruct (gap_succ _ _ e) as [Eg Pg].
        pose proof (Hf i' iC' s' sC' Hinv Hlt Ec) as HF1.
        match goal with |- context [@cost ?T (?G' hi hiC cont contC f fC (i' + 1)%uint63 ?w ?c ?wc ?h ?e)] =>
          pose proof (IH (i' + 1)%uint63 w c wc h e : _ -> _ -> (@cost T (G' hi hiC cont contC f fC (i' + 1)%uint63 w c wc h e) <= _)%nat) as HI2 end.
        specialize (HI2 ltac:(lia) (HI _ _ Hinv Hlt Ec)). cost_align HF1. cost_align HI2. cost_align HC1. clear -HF1 HI2 HC1 HB. assert (EM : ((K + (K + 0) + 25) * S k = (2 * K + 25) * k + 2 * K + 25)%nat) by nia. rewrite EM. lia.
      + cost_simpl. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G hi hiC cont contC f fC i iC s sC H HC)] =>
    exact (HG _ i iC s sC H HC (le_n _) : _ -> (@cost T (G hi hiC cont contC f fC i iC s sC H HC) <= _)%nat) end.
Qed.

(* The amortised form: the loop's cost is paid by the distance the index
   travels, read on the final state through idx. *)
Lemma wloop_time_amort (Inv : int -> St -> Prop) (idx : St -> int) (K : nat)
  hi hiC cont contC f fC
  (Hc : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z ->
     (cost (contC j jC) + cost (extract (contC j jC) t tC) <= K)%nat)
  (Hf : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z -> cont j t = true ->
     (cost (fC j jC) + cost (extract (fC j jC) t tC) <= K)%nat)
  (HI : forall j t, Inv j t -> (φ j < φ hi)%Z -> cont j t = true -> Inv (j + 1) (f j t))
  (Hidx : forall j t, Inv j t -> idx t = j)
  i iC s sC H HC : Inv i s ->
  (cost (extract (extract (extract (extract (extract (extract (wloop_cost stepsCM St StC) hi hiC) cont contC) f fC) i iC) s sC) H HC)
     + (2 * K + 25) * Z.to_nat (gap hi (idx (wloop hi cont f i s H))) <= (2 * K + 25) * Z.to_nat (gap hi i) + K + 15)%nat.
Proof.
  unfold wloop_cost. cbn.
  match goal with |- context [@cost ?T (?G hi hiC cont contC f fC i iC s sC H HC)] =>
    assert (HG : forall k i iC s sC H HC, (Z.to_nat (gap hi i) <= k)%nat -> Inv i s ->
       (cost (G hi hiC cont contC f fC i iC s sC H HC) + (2 * K + 25) * Z.to_nat (gap hi (idx (wloop hi cont f i s H)))
          <= (2 * K + 25) * Z.to_nat (gap hi i) + K + 15)%nat) end.
  { induction k as [|k IH]; intros i' iC' s' sC' [g] HC' Hk Hinv;
      cost_simpl;
      pose proof (bdec_time (i' <? hi) (bool_w (i' <? hi))) as HB;
      cost_destruct (bdec (i' <? hi)); cost_simpl.
    - exfalso. destruct (gap_succ _ _ e). lia.
    - rewrite (Hidx _ _ Hinv). lia.
    - pose proof e as Hlt. rewrite Uint63.ltb_spec in Hlt.
      pose proof (Hc i' iC' s' sC' Hinv Hlt) as HC1. cost_align HC1.
      cost_destruct_eqn (cont i' s') Ec.
      + cost_simpl.
        destruct (gap_succ _ _ e) as [Eg Pg].
        pose proof (Hf i' iC' s' sC' Hinv Hlt Ec) as HF1.
        match goal with |- context [@cost ?T (?G' hi hiC cont contC f fC (i' + 1)%uint63 ?w ?c ?wc ?h ?e)] =>
          pose proof (IH (i' + 1)%uint63 w c wc h e : _ -> _ -> (@cost T (G' hi hiC cont contC f fC (i' + 1)%uint63 w c wc h e) + _ <= _)%nat) as HI2 end.
        specialize (HI2 ltac:(lia) (HI _ _ Hinv Hlt Ec)). cost_align HF1. cost_align HI2. cost_align HC1.
        rewrite Eg in HI2. 
        match goal with |- context [Z.to_nat (gap hi (idx ?X))] => match type of HI2 with context [Z.to_nat (gap hi (idx ?Y))] =>
          change X with Y end end.
        clear -HF1 HI2 HC1 HB Pg. nia.
      + cost_simpl. rewrite (Hidx _ _ Hinv). lia.
    - rewrite (Hidx _ _ Hinv). lia. }
  match goal with |- context [@cost ?T (?G hi hiC cont contC f fC i iC s sC H HC)] =>
    exact (HG _ i iC s sC H HC (le_n _) : _ -> (@cost T (G hi hiC cont contC f fC i iC s sC H HC) + _ <= _)%nat) end.
Qed.
End W.

Section L.
Context {St : Type} (StC : St -> Type).
Lemma loop_time_gen (Inv : int -> St -> Prop) (Pot : St -> nat) (K : nat)
  hi hiC cont contC f fC
  (Hc : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z ->
     (cost (contC j jC) + cost (extract (contC j jC) t tC) <= K)%nat)
  (Hf : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z -> cont j t = true ->
     (cost (fC j jC) + cost (extract (fC j jC) t tC) + Pot (f j t) <= Pot t + K)%nat)
  (HI : forall j t, Inv j t -> (φ j < φ hi)%Z -> cont j t = true -> Inv (j + 1) (f j t))
  i iC s sC : Inv i s ->
  (cost (extract (extract (extract (extract (extract (loop_cost stepsCM St StC) hi hiC) cont contC) f fC) i iC) s sC) <= (2 * K + 25) * Z.to_nat (gap hi i) + Pot s + 30)%nat.
Proof.
  intros Hinv. unfold loop_cost. cost_simpl.
  zero_partials.
  match goal with |- context [@cost ?T ?X] =>
    pose proof (wloop_time_gen StC Inv Pot K hi hiC cont contC f fC Hc Hf HI i iC s sC _ erased_I Hinv : (@cost T X <= _)%nat) end.
  lia.
Qed.

Lemma loop_time_amort (Inv : int -> St -> Prop) (idx : St -> int) (K : nat)
  hi hiC cont contC f fC
  (Hc : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z ->
     (cost (contC j jC) + cost (extract (contC j jC) t tC) <= K)%nat)
  (Hf : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z -> cont j t = true ->
     (cost (fC j jC) + cost (extract (fC j jC) t tC) <= K)%nat)
  (HI : forall j t, Inv j t -> (φ j < φ hi)%Z -> cont j t = true -> Inv (j + 1) (f j t))
  (Hidx : forall j t, Inv j t -> idx t = j)
  i iC s sC : Inv i s ->
  (cost (extract (extract (extract (extract (extract (loop_cost stepsCM St StC) hi hiC) cont contC) f fC) i iC) s sC)
     + (2 * K + 25) * Z.to_nat (gap hi (idx (loop hi cont f i s))) <= (2 * K + 25) * Z.to_nat (gap hi i) + K + 35)%nat.
Proof.
  intros Hinv. unfold loop_cost. cost_simpl.
  zero_partials.
  match goal with |- context [@cost ?T ?X] =>
    pose proof (wloop_time_amort StC Inv idx K hi hiC cont contC f fC Hc Hf HI Hidx i iC s sC _ erased_I Hinv : (@cost T X + _ <= _)%nat) end.
  unfold loop. lia.
Qed.
End L.

Ltac if_destruct := match goal with |- context [@cost _ (?F ?w)] =>
  lazymatch F with ?h ?a => fail | _ => match type of w with bool_cost _ ?b => cost_destruct b end end end.

Ltac prim_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | set_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (set_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (set_cost _ _ _) _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (extract (set_cost _ _ _) _ _) _ _) _ _ => change (@cost T X) with 1%nat
  | make_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (make_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (make_cost _ _ _) _ _) _ _ => change (@cost T X) with 1%nat
  end end.

Lemma orb_time a aC : (cost (orb_cost stepsCM a aC) <= 2)%nat.
Proof. unfold orb_cost. destruct aC; cost_simpl; lia. Qed.
Lemma orb_time2 a aC b bC : (cost (extract (orb_cost stepsCM a aC) b bC) <= 2)%nat.
Proof. unfold orb_cost. destruct aC; cost_simpl; lia. Qed.
Lemma andb_time a aC : (cost (andb_cost stepsCM a aC) <= 2)%nat.
Proof. unfold andb_cost. destruct aC; cost_simpl; lia. Qed.
Lemma andb_time2 a aC b bC : (cost (extract (andb_cost stepsCM a aC) b bC) <= 2)%nat.
Proof. unfold andb_cost. destruct aC; cost_simpl; lia. Qed.

Ltac gen_cost T X lem := let H := fresh "Hc" in let c := fresh "cc" in pose proof (lem : (@cost T X <= _)%nat) as H; revert H; generalize (@cost T X); intros c H.

Ltac bool_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | orb_cost stepsCM ?a ?aC => gen_cost T X (orb_time a aC)
  | extract (orb_cost stepsCM ?a ?aC) ?b ?bC => gen_cost T X (orb_time2 a aC b bC)
  | andb_cost stepsCM ?a ?aC => gen_cost T X (andb_time a aC)
  | extract (andb_cost stepsCM ?a ?aC) ?b ?bC => gen_cost T X (andb_time2 a aC b bC)
  end end.

Ltac if_costs30 := repeat match goal with |- context [@cost ?T ?X] =>
  match X with ?F ?w => lazymatch F with ?h ?a => fail | _ => match type of w with bool_cost _ ?b =>
    let H := fresh "Hif" in assert (H : (@cost T X <= 30)%nat) by (cost_destruct b; cbn; lia);
    revert H; generalize (@cost T X); intros ? H end end end end.

Lemma merge_step_time key keyC A AC mid midC hi hiC k kC st stC :
  (cost (merge_step_cost stepsCM key keyC) + cost (extract (merge_step_cost stepsCM key keyC) A AC)
   + cost (extract (extract (merge_step_cost stepsCM key keyC) A AC) mid midC)
   + cost (extract (extract (extract (merge_step_cost stepsCM key keyC) A AC) mid midC) hi hiC)
   + cost (extract (extract (extract (extract (merge_step_cost stepsCM key keyC) A AC) mid midC) hi hiC) k kC)
   + cost (extract (extract (extract (extract (extract (merge_step_cost stepsCM key keyC) A AC) mid midC) hi hiC) k kC) st stC)
   <= 100)%nat.
Proof.
  destruct stC as [p pC T TC]. destruct pC as [i iC j jC].
  unfold merge_step_cost. cost_simpl. zero_partials. prim_costs.
  repeat (if_destruct; cost_simpl; zero_partials; prim_costs).
  all: lia.
Qed.

Definition gn (hm k : int) : nat := Z.to_nat (gap hm k).
Arguments gn : simpl never.

Lemma copy_step_time k kC st stC :
  (cost (copy_step_cost stepsCM k kC) + cost (extract (copy_step_cost stepsCM k kC) st stC) <= 30)%nat.
Proof. destruct stC. unfold copy_step_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

Lemma merge_time key keyC lo loC mid midC hi hiC A AC T TC :
  (cost (extract (extract (extract (extract (extract (merge_cost stepsCM key keyC) lo loC) mid midC) hi hiC) A AC) T TC) <= gn hi lo * 230 + 100)%nat.
Proof.
  unfold merge_cost. cost_simpl. zero_partials.
  match goal with |- context [@cost ?T ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 100 hi hiC cont contC f fC
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; cbv beta; pose proof (merge_step_time key keyC A AC mid midC hi hiC j jC t tC) as HH; cost_align HH; lia)
         ltac:(intros; exact I) i iC s sC I : (@cost T XX <= _)%nat) as H;
      revert H; generalize (@cost T XX); intros c H
    end end.
  cost_destruct_witness (loop hi (fun (_ : int) (_ : int * int * array int) => true) (merge_step key A mid hi) lo (lo, mid, T)) as [p pC T' TC'] eqn:E.
  destruct pC as [i' iC' j' jC']. cost_simpl.
  assert (Z.to_nat (gap hi lo) = gn hi lo) by reflexivity. lia.
Qed.

Lemma merge_copy_time key keyC lo loC mid midC hi hiC A AC T TC :
  (cost (extract (extract (extract (extract (extract (merge_copy_cost stepsCM key keyC) lo loC) mid midC) hi hiC) A AC) T TC) <= gn hi lo * 320 + 200)%nat.
Proof.
  unfold merge_copy_cost. cost_simpl. zero_partials.
  repeat match goal with |- context [@cost ?TT ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (merge_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
      gen_cost TT XX (merge_time a aC b bC c cC d dC e eC f fC)
    end end.
  match goal with |- context [@cost ?T ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 30 hi hiC cont contC f fC
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; cbv beta; pose proof (copy_step_time j jC t tC) as HH; cost_align HH; lia)
         ltac:(intros; exact I) i iC s sC I : (@cost T XX <= _)%nat) as H;
      revert H; generalize (@cost T XX); intros c H
    end end.
  assert (Z.to_nat (gap hi lo) = gn hi lo) by reflexivity. lia.
Qed.

Lemma guard_time c cC lo loC hi hiC :
  (cost (guard_cost stepsCM c cC) + cost (extract (guard_cost stepsCM c cC) lo loC)
    + cost (extract (extract (guard_cost stepsCM c cC) lo loC) hi hiC) <= 20)%nat.
Proof. unfold guard_cost. cost_simpl. zero_partials. bool_costs. lia. Qed.

Lemma ms_facts lo hi : guard 1 lo hi = true ->
  gn (lo + (hi - lo) / 2) lo = (gn hi lo / 2)%nat /\ gn hi (lo + (hi - lo) / 2) = (gn hi lo - gn hi lo / 2)%nat
  /\ (2 <= gn hi lo)%nat.
Proof.
  intros H. unfold guard in H. apply andb_prop in H as [H1 H2]. rewrite Uint63.ltb_spec in H1, H2.
  change (φ 1) with 1%Z in H2. pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
  assert (E : φ (hi - lo) = (φ hi - φ lo)%Z) by sia.
  assert (E2 : φ ((hi - lo) / 2) = ((φ hi - φ lo) / 2)%Z) by (rewrite Uint63.div_spec, E; reflexivity).
  assert (E3 : φ (lo + (hi - lo) / 2) = (φ lo + (φ hi - φ lo) / 2)%Z).
  { rewrite Uint63.add_spec, E2. apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
    assert ((φ hi - φ lo) / 2 <= φ hi - φ lo)%Z by (apply Z.div_le_upper_bound; lia). lia. }
  unfold gn, gap. rewrite E3.
  replace (φ lo + (φ hi - φ lo) / 2 - φ lo)%Z with ((φ hi - φ lo) / 2)%Z by lia.
  rewrite Z2Nat.inj_div by lia. change (Z.to_nat 2) with 2%nat.
  rewrite E in H2. assert (0 <= (φ hi - φ lo) / 2)%Z by (apply Z.div_pos; lia).
  assert ((φ hi - φ lo) / 2 <= φ hi - φ lo)%Z by (apply Z.div_le_upper_bound; lia).
  split; [reflexivity|]. split; [|lia].
  rewrite <- (Z2Nat.inj_div _ 2) by lia. rewrite <- Z2Nat.inj_sub by lia. f_equal. lia.
Qed.

Lemma half_facts L : (2 * (L / 2) <= L <= 2 * (L / 2) + 1)%nat.
Proof. pose proof (Nat.div_mod L 2 ltac:(lia)). pose proof (Nat.mod_upper_bound L 2 ltac:(lia)). lia. Qed.

Lemma lu_half L : (2 <= L)%nat -> (Nat.log2_up (L - L / 2) <= Nat.log2_up L - 1)%nat.
Proof.
  intros HL. pose proof (Nat.log2_up_spec L ltac:(lia)) as [_ S2].
  assert (1 <= Nat.log2_up L)%nat by (apply Nat.log2_up_pos; lia).
  apply Nat.log2_up_le_pow2; [pose proof (half_facts L); lia|].
  replace (Nat.log2_up L) with (S (Nat.log2_up L - 1)) in S2 by lia. rewrite Nat.pow_succ_r' in S2.
  pose proof (half_facts L). lia.
Qed.

Lemma ms_arith (L l1 l2 lu1 lu2 lu c1 c2 c3 : nat) :
  (2 <= L)%nat -> l1 = (L / 2)%nat -> l2 = (L - L / 2)%nat -> (lu1 <= lu - 1)%nat -> (lu2 <= lu - 1)%nat -> (1 <= lu)%nat ->
  (c1 + 1000 <= 400 * l1 * lu1 + 2000 * Nat.max l1 1)%nat ->
  (c2 + 1000 <= 400 * l2 * lu2 + 2000 * Nat.max l2 1)%nat ->
  (c3 <= L * 320 + 200)%nat ->
  (c1 + c2 + c3 + 300 + 1000 <= 400 * L * lu + 2000 * Nat.max L 1)%nat.
Proof.
  intros HL E1 E2 H1 H2 H3 C1 C2 C3.
  pose proof (half_facts L).
  assert (1 <= l1)%nat by (subst; lia).
  assert (l1 <= l2)%nat by (subst; lia).
  assert (Hs : (l1 + l2 = L)%nat) by (subst; lia).
  rewrite Nat.max_l in C1 by lia. rewrite Nat.max_l in C2 by lia. rewrite Nat.max_l by lia.
  assert (400 * l1 * lu1 <= 400 * l1 * (lu - 1))%nat by (apply Nat.mul_le_mono_l; lia).
  assert (400 * l2 * lu2 <= 400 * l2 * (lu - 1))%nat by (apply Nat.mul_le_mono_l; lia).
  assert (400 * l1 * (lu - 1) + 400 * l2 * (lu - 1) + 400 * L = 400 * L * lu)%nat.
  { replace (400 * L * lu)%nat with (400 * L * (S (lu - 1)))%nat by (f_equal; lia). rewrite <- Hs. nia. }
  lia.
Qed.

Lemma bdec_time' b w : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. exact (bdec_time b w). Qed.
Ltac bdec_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with bdec_cost stepsCM ?b ?w => gen_cost T X (bdec_time' b w) end end.

Definition msb (L : nat) : nat := 400 * L * Nat.log2_up L + 2000 * Nat.max L 1.
Arguments msb : simpl never.

#[local] Arguments msort_rec : simpl never.
#[local] Arguments Zwf_well_founded : simpl never.
#[local] Arguments guard : simpl never.

Lemma msort_time key keyC lo loC hi hiC A AC T TC H HC :
  (cost (extract (extract (extract (extract (extract (msort_rec_cost stepsCM key keyC) lo loC) hi hiC) A AC) T TC) H HC) + 1000 <= msb (gn hi lo))%nat.
Proof.
  unfold msort_rec_cost. cbn.
  match goal with |- context [@cost ?TT (?G key keyC lo loC hi hiC A AC T TC H HC)] =>
    assert (HG : forall N lo loC hi hiC A AC T TC H HC, (gn hi lo <= N)%nat ->
       (cost (G key keyC lo loC hi hiC A AC T TC H HC) + 1000 <= msb (gn hi lo))%nat) end.
  { induction N as [|N IH]; intros lo' loC' hi' hiC' A' AC' T' TC' [g] HC' HN;
      cost_simpl; zero_partials; bdec_costs.
    all: match goal with |- context [guard_cost stepsCM ?c ?cC] =>
      pose proof (guard_time c cC lo' loC' hi' hiC') as HGd; cost_align HGd end.
    all: cost_destruct (bdec (guard 1 lo' hi')); cost_simpl.
    all: zero_partials.
    1: exfalso; destruct (ms_facts _ _ e) as (_ & _ & ?); lia.
    1,3: unfold msb; lia.
    destruct (ms_facts _ _ e) as (Em1 & Em2 & HL).
    match goal with |- context [@cost ?TT (?G' key keyC lo' loC' ?md ?w A' AC' T' TC' ?a ?e)] =>
      let H := fresh "HI" in let c := fresh "cc" in
      pose proof (IH lo' loC' md w A' AC' T' TC' a e ltac:(rewrite Em1; pose proof (half_facts (gn hi' lo')); lia) : (@cost TT (G' key keyC lo' loC' md w A' AC' T' TC' a e) + _ <= _)%nat) as H;
      revert H; generalize (@cost TT (G' key keyC lo' loC' md w A' AC' T' TC' a e)); intros c H end.
    cost_destruct_witness (msort_rec key lo' (lo' + (hi' - lo') / 2) A' T' (g (gap (lo' + (hi' - lo') / 2) lo') (dec_left 1 lo' hi' e))) as [A1 A1C T1 T1C] eqn:E1.
    cost_simpl. zero_partials.
    match goal with |- context [@cost ?TT (?G' key keyC ?md ?mdC hi' hiC' A1 A1C T1 T1C ?a ?e)] =>
      let H := fresh "HI" in let c := fresh "cc" in
      pose proof (IH md mdC hi' hiC' A1 A1C T1 T1C a e ltac:(rewrite Em2; pose proof (half_facts (gn hi' lo')); lia) : (@cost TT (G' key keyC md mdC hi' hiC' A1 A1C T1 T1C a e) + _ <= _)%nat) as H;
      revert H; generalize (@cost TT (G' key keyC md mdC hi' hiC' A1 A1C T1 T1C a e)); intros c H end.
    cost_destruct_witness (msort_rec key (lo' + (hi' - lo') / 2) hi' A1 T1 (g (gap hi' (lo' + (hi' - lo') / 2)) (dec_right 1 lo' hi' e one_ge_1))) as [A2 A2C T2 T2C] eqn:E2.
    cost_simpl. zero_partials.
    repeat match goal with |- context [@cost ?TT ?XX] =>
      match XX with
      | extract (extract (extract (extract (extract (merge_copy_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
        gen_cost TT XX (merge_copy_time a aC b bC c cC d dC e eC f fC)
      end end.
    clear IH. unfold msb in *. rewrite Em1 in HI. rewrite Em2 in HI0.
    pose proof (lu_half _ HL) as LU2.
    assert (LU1 : (Nat.log2_up (gn hi' lo' / 2) <= Nat.log2_up (gn hi' lo' - gn hi' lo' / 2))%nat)
      by (apply Nat.log2_up_le_mono; pose proof (half_facts (gn hi' lo')); lia).
    assert (LU : (1 <= Nat.log2_up (gn hi' lo'))%nat) by (apply Nat.log2_up_pos; lia).
    pose proof (ms_arith (gn hi' lo') (gn hi' lo' / 2) (gn hi' lo' - gn hi' lo' / 2) (Nat.log2_up (gn hi' lo' / 2)) (Nat.log2_up (gn hi' lo' - gn hi' lo' / 2)) (Nat.log2_up (gn hi' lo')) cc0 cc1 cc2 HL eq_refl eq_refl ltac:(lia) LU2 LU ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    lia. }
  match goal with |- context [@cost ?TT (?G key keyC lo loC hi hiC A AC T TC H HC)] =>
    exact (HG _ lo loC hi hiC A AC T TC H HC (le_n _) : (@cost TT (G key keyC lo loC hi hiC A AC T TC H HC) + _ <= _)%nat) end.
Qed.

Definition sidx (st : int * bool * float * int) : int := fst (fst (fst st)).

Lemma scan_fact ls rs P cur n q : (φ q <= φ n)%Z ->
  let r := loop n (scan_cont ls P cur) (scan_step rs P) q (q, false, cur, 0) in
  (φ q <= φ (sidx r) <= φ n)%Z /\ (snd (fst (fst r)) = true -> (φ q < φ (sidx r))%Z).
Proof.
  intros Hq r.
  destruct (loop_inv (fun j st => sidx st = j /\ (snd (fst (fst st)) = true -> (φ q < φ j)%Z))
              n q (scan_cont ls P cur) (scan_step rs P) (q, false, cur, 0) Hq) as (j & Hj & [Ej Fj] & _).
  - split; [reflexivity | discriminate].
  - intros j t Hjr [Et Ft] _. destruct t as [[[p f] best] bi]. unfold sidx in Et; cbn in Et. subst p.
    assert (φ (j + 1) = φ j + 1)%Z by (pose proof (to_Z_bounded n); sia).
    unfold scan_step; destruct (best <=? rs.[P.[j]])%float; unfold sidx; cbn [fst snd]; split; try reflexivity; intros; lia.
  - fold r in Ej, Fj. rewrite Ej. split; [lia | exact Fj].
Qed.

Lemma sweep_eq' ls rs b P n q cnt cur W H :
  sweep ls rs b P n q cnt cur W H =
  match loop n (scan_cont ls P cur) (scan_step rs P) q (q, false, cur, 0) with
  | (q', found, best, bi) =>
    if andb found (orb (cnt =? 0)%uint63 (cur <? best)%float) then
      let W := W.[cnt <- bi] in
      if (b <=? best)%float then Some (W, cnt + 1)
      else match bdec (adv n q q') with
           | left Ha => sweep ls rs b P n q' (cnt + 1) best W (Acc_inv H (dec_adv n q q' Ha))
           | right _ => None
           end
    else None
  end.
Proof. destruct H; reflexivity. Qed.

Lemma sweep_len ls rs b P n : forall N q cnt cur W H W' k,
  (Z.to_nat (φ n - φ q) <= N)%nat -> (φ cnt <= φ q <= φ n)%Z ->
  sweep ls rs b P n q cnt cur W H = Some (W', k) -> (φ k <= φ n)%Z.
Proof.
  induction N as [|N IH]; intros q cnt cur W H W' k HN Hb Hs; rewrite sweep_eq' in Hs;
  pose proof (scan_fact ls rs P cur n q ltac:(lia)) as [Hr Hf]; cbv zeta in Hr, Hf;
  destruct (loop n (scan_cont ls P cur) (scan_step rs P) q (q, false, cur, 0)) as [[[q2 found] best] bi];
  unfold sidx in Hr, Hf; cbn [fst snd] in Hr, Hf;
  (destruct (found && ((cnt =? 0) || (cur <? best)%float))%bool eqn:Ef; [|discriminate]);
  apply andb_prop in Ef as [Ef _]; specialize (Hf Ef).
  - exfalso. lia.
  - destruct (b <=? best)%float.
    + injection Hs as _ <-. pose proof (to_Z_bounded n).
      assert (φ (cnt + 1) = φ cnt + 1)%Z by sia. lia.
    + destruct (bdec (adv n q q2)) as [Ha|]; [|discriminate].
      apply (IH q2 (cnt + 1) best (W.[cnt <- bi]) _ W' k ltac:(lia) ltac:(pose proof (to_Z_bounded n); assert (φ (cnt + 1) = φ cnt + 1)%Z by sia; lia) Hs).
Qed.

Lemma iota_step_time k kC P PC :
  (cost (extract (iota_step_cost stepsCM k kC) P PC) + cost (iota_step_cost stepsCM k kC) <= 20)%nat.
Proof. unfold iota_step_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

Lemma copy_out_time W WC k kC O OC :
  (cost (extract (copy_out_cost stepsCM W WC) k kC) + cost (extract (extract (copy_out_cost stepsCM W WC) k kC) O OC) <= 20)%nat.
Proof. unfold copy_out_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

#[local] Arguments sweep : simpl never.
#[local] Arguments loop : simpl never.
#[local] Arguments wloop : simpl never.
#[local] Arguments adv : simpl never.

Lemma scan_cont_time ls lsC P PC cur curC p pC st stC :
  (cost (extract (extract (extract (scan_cont_cost stepsCM ls lsC) P PC) cur curC) p pC)
   + cost (extract (extract (extract (extract (scan_cont_cost stepsCM ls lsC) P PC) cur curC) p pC) st stC) <= 20)%nat.
Proof. unfold scan_cont_cost. cost_simpl. zero_partials. lia. Qed.

Lemma scan_step_time rs rsC P PC p pC st stC :
  (cost (extract (extract (scan_step_cost stepsCM rs rsC) P PC) p pC)
   + cost (extract (extract (extract (scan_step_cost stepsCM rs rsC) P PC) p pC) st stC) <= 30)%nat.
Proof.
  destruct stC as [s1 s1C bi biC]. destruct s1C as [s2 s2C best bestC]. destruct s2C as [q qC f fC].
  unfold scan_step_cost. cost_simpl. zero_partials.
  repeat (if_destruct; cost_simpl; zero_partials).
  all: lia.
Qed.

Lemma adv_time n nC q qC q' q'C :
  (cost (adv_cost stepsCM n nC) + cost (extract (adv_cost stepsCM n nC) q qC)
    + cost (extract (extract (adv_cost stepsCM n nC) q qC) q' q'C) <= 20)%nat.
Proof. unfold adv_cost. cost_simpl. zero_partials. bool_costs. lia. Qed.


Notation SCF := (prod_cost stepsCM (int * bool * float) (prod_cost stepsCM (int * bool) (prod_cost stepsCM int (int_cost stepsCM) bool (bool_cost stepsCM)) float (float_cost stepsCM)) int (int_cost stepsCM)).

Lemma scan_time ls lsC rs rsC P PC cur curC n nC q qC (sC : SCF (q, false, cur, 0%uint63)) :
  (cost (extract (extract (extract (extract (extract (loop_cost stepsCM (int * bool * float * int) SCF) n nC)
     (scan_cont ls P cur) (extract (extract (extract (scan_cont_cost stepsCM ls lsC) P PC) cur curC)))
     (scan_step rs P) (extract (extract (scan_step_cost stepsCM rs rsC) P PC))) q qC)
     (q, false, cur, 0%uint63) sC)
   + 85 * gn n (sidx (loop n (scan_cont ls P cur) (scan_step rs P) q (q, false, cur, 0%uint63)))
   <= 85 * gn n q + 65)%nat.
Proof.
  pose proof (loop_time_amort SCF (fun j st => sidx st = j) sidx 30 n nC _ _ _ _
      ltac:(intros j jC t tC _ _; pose proof (scan_cont_time ls lsC P PC cur curC j jC t tC) as HH; cost_align HH; lia)
      ltac:(intros j jC t tC _ _ _; pose proof (scan_step_time rs rsC P PC j jC t tC) as HH; cost_align HH; lia)
      ltac:(intros j t Hj _ _; destruct t as [[[? ?] ?] ?]; unfold sidx in *; cbn in *; subst; destruct (_ <=? _)%float; reflexivity)
      ltac:(intros j t Hj; exact Hj)
      q qC _ sC eq_refl) as HH.
  unfold gn. lia.
Qed.

Lemma sweep_time ls lsC rs rsC b bC P PC n nC q qC cnt cntC cur curC W WC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (sweep_cost stepsCM ls lsC) rs rsC) b bC) P PC) n nC) q qC) cnt cntC) cur curC) W WC) H HC)
    <= gn n q * 400 + 400)%nat.
Proof.
  unfold sweep_cost. cbn.
  match goal with |- context [@cost ?TT (?G ls lsC rs rsC b bC P PC n nC q qC cnt cntC cur curC W WC H HC)] =>
    assert (HG : forall N q qC cnt cntC cur curC W WC H HC, (gn n q <= N)%nat ->
       (cost (G ls lsC rs rsC b bC P PC n nC q qC cnt cntC cur curC W WC H HC) <= gn n q * 400 + 400)%nat) end.
  { induction N as [|N IH]; intros q' qC' cnt' cntC' cur' curC' W' WC' [g] HC' HN;
      cost_simpl; zero_partials.
    all: (match goal with |- context [@cost ?T ?X] =>
      match X with
      | extract (extract (extract (extract (extract (loop_cost stepsCM _ SCF) ?nn ?nnC) _ (extract (extract (extract (scan_cont_cost stepsCM ?l ?lC) ?PP ?PPC) ?cu ?cuC))) _ (extract (extract (scan_step_cost stepsCM ?r ?rC) _ _))) ?qq ?qqC) _ ?sC =>
        pose proof (scan_time l lC r rC PP PPC cu cuC nn nnC qq qqC sC : (@cost T X + _ <= _)%nat) as Hs;
        revert Hs; generalize (@cost T X); intros cs Hs
      end end).
    all: (match goal with |- context [loop ?nn (scan_cont ?l ?PP ?cu) ?f ?qq ?s] => cost_destruct_witness (loop nn (scan_cont l PP cu) f qq s) as [p pC bi biC] eqn:E end).
    all: destruct pC as [p0 p0C best bestC]; destruct p0C as [q2 q2C found foundC].
    all: unfold sidx in Hs; cbn [fst] in Hs.
    all: cost_simpl; zero_partials; bool_costs; prim_costs.
    all: if_destruct; cost_simpl; zero_partials; prim_costs.
    all: try (unfold gn in *; lia).
    all: if_destruct; cost_simpl; zero_partials; prim_costs.
    all: try (unfold gn in *; lia).
    all: (match goal with |- context [adv_cost stepsCM ?a ?aC] => match goal with |- context [extract (extract (adv_cost stepsCM a aC) ?b ?bC) ?c ?cC] =>
            pose proof (adv_time a aC b bC c cC) as HA; cost_align HA end end).
    all: bdec_costs.
    all: (match goal with |- context [bdec (adv ?a ?b ?c)] => cost_destruct (bdec (adv a b c)) end); cost_simpl; zero_partials.
    all: try (unfold gn in *; lia).
    all: pose proof e as Ha; unfold adv in Ha; apply andb_prop in Ha as [Ha1 Ha2];
         rewrite Uint63.ltb_spec in Ha1; rewrite Uint63.leb_spec in Ha2.
    1: exfalso; unfold gn, gap in HN; lia.
    match goal with |- context [@cost ?TT (?G' ls lsC rs rsC b bC P PC n nC q2 q2C ?c1 ?c1C best bestC ?w ?wC ?a ?e)] =>
      let H := fresh "HI" in let c := fresh "cc" in
      pose proof (IH q2 q2C c1 c1C best bestC w wC a e ltac:(unfold gn, gap in *; lia) : (@cost TT (G' ls lsC rs rsC b bC P PC n nC q2 q2C c1 c1C best bestC w wC a e) <= _)%nat) as H;
      revert H; generalize (@cost TT (G' ls lsC rs rsC b bC P PC n nC q2 q2C c1 c1C best bestC w wC a e)); intros c H end.
    assert (gn n q2 + 1 <= gn n q')%nat by (unfold gn, gap; lia).
    clear IH. lia. }
  match goal with |- context [@cost ?TT (?G ls lsC rs rsC b bC P PC n nC q qC cnt cntC cur curC W WC H HC)] =>
    exact (HG _ q qC cnt cntC cur curC W WC H HC (le_n _) : (@cost TT (G ls lsC rs rsC b bC P PC n nC q qC cnt cntC cur curC W WC H HC) <= _)%nat) end.
Qed.

#[local] Arguments Uint63.to_Z : simpl never.

Ltac bridge N EN := repeat match goal with H : context [Z.to_nat (φ ?t)] |- _ =>
  lazymatch t with context [length] => let E := fresh in
    assert (E : Z.to_nat (φ t) = N) by (rewrite EN; reflexivity); rewrite E in H; clear E end end.

Lemma main_time x y ls rs : (cost4 cover_cost x y ls rs <= msb (size ls) + size ls * 600 + 600)%nat.
Proof.
  remember (size ls) as N eqn:EN.
  unfold cost4, cover_cost. cost_simpl. zero_partials. prim_costs.
  match goal with |- context [@cost ?T ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f (iota_step_cost stepsCM)) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 20 hi hiC cont contC f (iota_step_cost stepsCM)
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; cbv beta; pose proof (iota_step_time j jC t tC) as HH; cost_align HH; lia)
         ltac:(intros; exact I) i iC s sC I : (@cost T XX <= _)%nat) as H;
      revert H; generalize (@cost T XX); intros c H
    end end.
  match goal with |- context [@cost ?TT (extract (extract (extract (extract (extract (msort_rec_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC)] =>
      let H := fresh "Hm" in let cm := fresh "cm" in
      pose proof (msort_time a aC b bC c cC d dC e eC f fC : (@cost TT (extract (extract (extract (extract (extract (msort_rec_cost stepsCM a aC) b bC) c cC) d dC) e eC) f fC) + _ <= _)%nat) as H;
      revert H; generalize (@cost TT (extract (extract (extract (extract (extract (msort_rec_cost stepsCM a aC) b bC) c cC) d dC) e eC) f fC)); intros cm H end.
  match goal with |- context [msort_rec ?a ?b ?c ?d ?e ?f] => cost_destruct_witness (msort_rec a b c d e f) as [P0 P0C T0 T0C] eqn:EM end.
  cost_simpl. zero_partials. prim_costs.
  match goal with |- context [@cost ?TT ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (extract (extract (extract (extract (sweep_cost stepsCM ?a1 ?a1C) ?a2 ?a2C) ?a3 ?a3C) ?a4 ?a4C) ?a5 ?a5C) ?a6 ?a6C) ?a7 ?a7C) ?a8 ?a8C) ?a9 ?a9C) ?a10 ?a10C =>
      gen_cost TT XX (sweep_time a1 a1C a2 a2C a3 a3C a4 a4C a5 a5C a6 a6C a7 a7C a8 a8C a9 a9C a10 a10C)
    end end.
  pose proof (flength_bound ls) as Hn.
  match goal with |- context [sweep ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10] =>
    pose proof (fun W k => sweep_len a1 a2 a3 a4 a5 _ a6 a7 a8 a9 a10 W k (le_n _)) as HL;
    cost_destruct_witness (sweep a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) as [p pC|] eqn:ES end.
  - destruct pC as [W WC k kC]. specialize (HL W k ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (length ls)); lia) eq_refl).
    cost_simpl. zero_partials. prim_costs.
    match goal with |- context [@cost ?T ?XX] =>
      match XX with
      | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f (extract (copy_out_cost stepsCM ?W0 ?W0C))) ?i ?iC) ?s ?sC =>
        let H := fresh "Hc" in let c := fresh "cc" in
        pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 20 hi hiC cont contC f (extract (copy_out_cost stepsCM W0 W0C))
           ltac:(intros; cbn; lia)
           ltac:(intros j jC t tC _ _ _; cbv beta; pose proof (copy_out_time W0 W0C j jC t tC) as HH; cost_align HH; lia)
           ltac:(intros; exact I) i iC s sC I : (@cost T XX <= _)%nat) as H;
        revert H; generalize (@cost T XX); intros c H
      end end.
    assert (E0 : gn (length ls) 0 = Z.to_nat (φ (length ls))) by (unfold gn, gap; change (φ 0) with 0%Z; f_equal; lia).
    rewrite E0 in Hm, Hc0. unfold gap in Hc. change (φ 0) with 0%Z in Hc. rewrite Z.sub_0_r in Hc. bridge N EN.
    match type of HL with (_ <= φ ?t)%Z => assert (HtN : Z.to_nat (φ t) = N) by (rewrite EN; reflexivity) end.
    assert (Hk : (Z.to_nat (gap k 0) <= N)%nat) by (unfold gap; change (φ 0) with 0%Z; lia).
    clear -Hc Hm Hc0 Hc1 Hk. lia.
  - cost_simpl. zero_partials. prim_costs.
    assert (E0 : gn (length ls) 0 = Z.to_nat (φ (length ls))) by (unfold gn, gap; change (φ 0) with 0%Z; f_equal; lia).
    rewrite E0 in Hm, Hc0. unfold gap in Hc. change (φ 0) with 0%Z in Hc. rewrite Z.sub_0_r in Hc. bridge N EN.
    clear -Hc Hm Hc0. lia.
Qed.

Lemma lu_le_log2 N : (Nat.log2_up N <= Nat.log2 N + 1)%nat.
Proof. pose proof (Nat.le_log2_up_succ_log2 N). lia. Qed.

Lemma msb_le N : (msb N <= 400 * (N * Nat.log2 N) + 2400 * N + 2000)%nat.
Proof. unfold msb. pose proof (lu_le_log2 N).
  assert (400 * N * Nat.log2_up N <= 400 * N * (Nat.log2 N + 1))%nat by (apply Nat.mul_le_mono_l; lia).
  assert (Nat.max N 1 <= N + 1)%nat by lia. nia. Qed.

Theorem cover_time : exists c1 c2 : nat,
  forall (target_left target_right : R) (lefts rights : list
  R)
  (target_left_float target_right_float : float)
  (lefts_arr rights_arr : array float),
  valid_input target_left target_right lefts rights ->
  repr target_left_float target_left ->
  repr target_right_float target_right ->
  repr lefts_arr lefts -> repr rights_arr rights ->
  (cost4 cover_cost target_left_float target_right_float lefts_arr rights_arr <= c1 * ((size lefts_arr + 1) * (Nat.log2 (size lefts_arr) + 1)) + c2)%nat.
Proof.
  exists 3000%nat, 3000%nat. intros a b ls rs x y xs ys _ _ _ _ _.
  pose proof (main_time x y xs ys) as H. pose proof (msb_le (size xs)) as H2.
  remember (size xs) as N. clear HeqN. nia.
Qed.
