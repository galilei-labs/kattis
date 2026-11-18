(* Implementation of nonnegpartsums (nonnegpartsums.spec): count the
   cyclic shifts of a whose prefix sums are all nonnegative.

   Code.  P = the n+1 prefix sums of a (P.[0] = 0, P.[i+1] = P.[i] + a.[i]),
   one array; tot = P.[n].  The doubled sequence of prefix sums is read
   through [qv]: Q(j) = P.[j] for j <= n, tot + P.[j-n] beyond, never
   materialised.  Shift k is good iff Q(k) <= min Q over the window
   [k+1, k+n].  One sweep j = 1 .. 2n-1 keeps a monotone deque of indices of
   the window [max(1, j-n+1), j] (increasing indices, strictly increasing Q
   values): pop the front indices that left the window, pop the back
   indices whose Q is >= Q(j), push j; when j >= n the front is the window
   minimum and shift k = j-n is tested.  The deque is one flat array of n
   cells used as a circular buffer: two monotone int cursors h <= t, cell
   c mod n (the deque never holds more than n indices).  Sums and
   comparisons of prefix sums are signed (Sint63 [lesb]); indices are
   unsigned.  No Z, no nat, no list in the code.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap _ _)] proof, as in template/polymul1.  The prefix
   array and the deque are threaded linearly, allocated once before the
   sweeps; the input array is only read. *)

From Nonnegpartsums.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
From KattisLib Require Import Cost.
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

Lemma aget_make : forall (n : int) (b : int) (i : int), (PArray.make n b).[i] = b.
Proof. intros n b i. exact (get_make int b n i). Qed.

Lemma sadd : forall x y : int,
  (- 4611686018427387904 <= Sint63.to_Z x + Sint63.to_Z y < 4611686018427387904)%Z ->
  Sint63.to_Z (x + y) = (Sint63.to_Z x + Sint63.to_Z y)%Z.
Proof.
  intros x y H. rewrite Sint63.add_spec. apply Sint63.cmod_small.
  rewrite wB_val. change (9223372036854775808 / 2)%Z with 4611686018427387904%Z.
  lia.
Qed.

Lemma sleb_iff : forall x y : int,
  PrimInt63.lesb x y = true <-> (Sint63.to_Z x <= Sint63.to_Z y)%Z.
Proof. intros x y. exact (Sint63.leb_spec x y). Qed.

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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.
Arguments gap : simpl never.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_back : forall t h : int,
  (h <? t) = true -> Zwf 0 (gap (t - 1) h) (gap t h).
Proof.
  intros t h H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded h).
  assert (H1 : (φ (t - 1)) = ((φ t) - 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Cells i+1 .. n of P receive their prefix sum. *)
Fixpoint prefix_loop (x : array int) (n i : int) (P : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      prefix_loop x n (i + 1) (P.[i + 1 <- P.[i] + x.[i]])
        (Acc_inv H (dec_step n i Hi))
  | right _ => P
  end.
Elpi complexity prefix_loop.
Arguments prefix_loop_cost : simpl never.

Lemma prefix_loop_eq : forall x n i P H,
  prefix_loop x n i P H =
  match bdec (i <? n) with
  | left Hi =>
      prefix_loop x n (i + 1) (P.[i + 1 <- P.[i] + x.[i]])
        (Acc_inv H (dec_step n i Hi))
  | right _ => P
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The prefix sum of index j of the doubled sequence (0 <= j <= 2n). *)
Definition qv (P : array int) (n tot j : int) : int :=
  if j <=? n then P.[j] else tot + P.[j - n].
Elpi complexity qv.
Arguments qv_cost : simpl never.

(* Advance the front cursor past the indices that left the window
   (index + n <= j). *)
Fixpoint pop_front (dq : array int) (n j h t : int)
    (H : Acc (Zwf 0) (gap t h)) {struct H} : int :=
  match bdec (h <? t) with
  | left Hh =>
      if dq.[h mod n] + n <=? j
      then pop_front dq n j (h + 1) t (Acc_inv H (dec_step t h Hh))
      else h
  | right _ => h
  end.
Elpi complexity pop_front.
Arguments pop_front_cost : simpl never.

Lemma pop_front_eq : forall dq n j h t H,
  pop_front dq n j h t H =
  match bdec (h <? t) with
  | left Hh =>
      if dq.[h mod n] + n <=? j
      then pop_front dq n j (h + 1) t (Acc_inv H (dec_step t h Hh))
      else h
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Move the back cursor down past the indices whose prefix sum is >= qj. *)
Fixpoint pop_back (dq P : array int) (n tot qj h t : int)
    (H : Acc (Zwf 0) (gap t h)) {struct H} : int :=
  match bdec (h <? t) with
  | left Hh =>
      if PrimInt63.lesb qj (qv P n tot dq.[(t - 1) mod n])
      then pop_back dq P n tot qj h (t - 1) (Acc_inv H (dec_back t h Hh))
      else t
  | right _ => t
  end.
Elpi complexity pop_back.
Arguments pop_back_cost : simpl never.

Lemma pop_back_eq : forall dq P n tot qj h t H,
  pop_back dq P n tot qj h t H =
  match bdec (h <? t) with
  | left Hh =>
      if PrimInt63.lesb qj (qv P n tot dq.[(t - 1) mod n])
      then pop_back dq P n tot qj h (t - 1) (Acc_inv H (dec_back t h Hh))
      else t
  | right _ => t
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The sweep over the doubled sequence, j = current index .. m - 1. *)
Fixpoint sweep (P : array int) (n tot m j h t cnt : int) (dq : array int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : int :=
  match bdec (j <? m) with
  | left Hj =>
      let h1 := pop_front dq n j h t (Zwf_well_founded 0 (gap t h)) in
      let qj := qv P n tot j in
      let t1 := pop_back dq P n tot qj h1 t (Zwf_well_founded 0 (gap t h1)) in
      let dq1 := dq.[t1 mod n <- j] in
      let cnt1 :=
        if n <=? j then
          (if PrimInt63.lesb (qv P n tot (j - n)) (qv P n tot dq1.[h1 mod n])
           then cnt + 1 else cnt)
        else cnt in
      sweep P n tot m (j + 1) h1 (t1 + 1) cnt1 dq1
        (Acc_inv H (dec_step m j Hj))
  | right _ => cnt
  end.
Elpi complexity sweep.
Arguments sweep_cost : simpl never.

Lemma sweep_eq : forall P n tot m j h t cnt dq H,
  sweep P n tot m j h t cnt dq H =
  match bdec (j <? m) with
  | left Hj =>
      let h1 := pop_front dq n j h t (Zwf_well_founded 0 (gap t h)) in
      let qj := qv P n tot j in
      let t1 := pop_back dq P n tot qj h1 t (Zwf_well_founded 0 (gap t h1)) in
      let dq1 := dq.[t1 mod n <- j] in
      let cnt1 :=
        if n <=? j then
          (if PrimInt63.lesb (qv P n tot (j - n)) (qv P n tot dq1.[h1 mod n])
           then cnt + 1 else cnt)
        else cnt in
      sweep P n tot m (j + 1) h1 (t1 + 1) cnt1 dq1
        (Acc_inv H (dec_step m j Hj))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition count_impl (x : array sint) : uint :=
  let n := PArray.length x in
  let P := prefix_loop x n 0 (PArray.make (n + 1) 0)
             (Zwf_well_founded 0 (gap n 0)) in
  let tot := P.[n] in
  sweep P n tot (n + n) 1 0 0 0 (PArray.make n 0)
    (Zwf_well_founded 0 (gap (n + n) 1)).
Elpi complexity count_impl.
Arguments count_impl_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Math side                                                           *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Lemma sum_Z_app : forall l1 l2, sum_Z (l1 ++ l2) = sum_Z l1 + sum_Z l2.
Proof. induction l1 as [| v l IH]; intros l2; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sum_firstn_add : forall (l : list Z) (k i : nat),
  sum_Z (firstn (k + i) l) = sum_Z (firstn k l) + sum_Z (firstn i (skipn k l)).
Proof.
  induction l as [| v l IH]; intros k i.
  - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
  - destruct k as [| k]; simpl; [reflexivity|]. rewrite IH. lia.
Qed.

Lemma firstn1_skipn : forall (l : list Z) (j : nat), (j < List.length l)%nat ->
  firstn 1 (skipn j l) = [nth j l 0].
Proof.
  induction l as [| v l IH]; intros j Hj; simpl in Hj; [lia|].
  destruct j as [| j]; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma sum_firstn_bound : forall (l : list Z) (i : nat),
  Forall (fun v => -1000 <= v <= 1000) l ->
  -1000 * Z.of_nat i <= sum_Z (firstn i l) <= 1000 * Z.of_nat i.
Proof.
  induction l as [| v l IH]; intros i Hf.
  - rewrite firstn_nil. cbn [sum_Z fold_right]. lia.
  - destruct i as [| i]; cbn [firstn sum_Z fold_right]; [lia|]. inversion Hf; subst.
     specialize (IH i H2). lia.
Qed.

(* The prefix sums of the doubled sequence. *)
Definition Qm (a : list Z) (j : Z) : Z := sum_Z (firstn (Z.to_nat j) (a ++ a)).

Lemma Qm_bound : forall a, Forall (fun v => -1000 <= v <= 1000) a ->
  forall j, 0 <= j -> -1000 * j <= Qm a j <= 1000 * j.
Proof.
  intros a Ha j Hj. unfold Qm.
  pose proof (sum_firstn_bound (a ++ a) (Z.to_nat j) ltac:(apply Forall_app; auto)).
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma Qm_succ : forall a j, 0 <= j < Z.of_nat (List.length a) ->
  Qm a (j + 1) = Qm a j + nth (Z.to_nat j) a 0.
Proof.
  intros a j Hj. unfold Qm.
  rewrite Z2Nat.inj_add by lia. rewrite sum_firstn_add.
  rewrite firstn1_skipn by (rewrite length_app; lia). simpl.
  rewrite app_nth1 by lia. lia.
Qed.

Lemma Qm_n : forall a, Qm a (Z.of_nat (List.length a)) = sum_Z a.
Proof.
  intros a. unfold Qm. rewrite Nat2Z.id, firstn_app, firstn_all.
  rewrite Nat.sub_diag. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma Qm_lo : forall a j, 0 <= j <= Z.of_nat (List.length a) ->
  Qm a j = sum_Z (firstn (Z.to_nat j) a).
Proof.
  intros a j Hj. unfold Qm. rewrite firstn_app.
  replace (Z.to_nat j - List.length a)%nat with 0%nat by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma Qm_hi : forall a j, 0 <= j <= Z.of_nat (List.length a) ->
  Qm a (Z.of_nat (List.length a) + j) = Qm a (Z.of_nat (List.length a)) + Qm a j.
Proof.
  intros a j Hj. rewrite Qm_n, (Qm_lo a j Hj). unfold Qm.
  rewrite firstn_app, firstn_all2 by lia. rewrite sum_Z_app.
  replace (Z.to_nat (Z.of_nat (List.length a) + j) - List.length a)%nat with (Z.to_nat j) by lia.
  reflexivity.
Qed.

(* The rotation by k is the window [k, k+n) of the doubled sequence. *)
Lemma rot_sum : forall (a : list Z) (k i : nat),
  (k < List.length a)%nat -> (i <= List.length a)%nat ->
  sum_Z (firstn i (rotate k a)) = Qm a (Z.of_nat (k + i)) - Qm a (Z.of_nat k).
Proof.
  intros a k i Hk Hi.
  assert (R : rotate k a = firstn (List.length a) (skipn k (a ++ a))).
  { unfold rotate. rewrite skipn_app.
    replace (k - List.length a)%nat with 0%nat by lia. cbn [skipn].
    rewrite firstn_app, length_skipn.
    assert (Hs : firstn (List.length a) (skipn k a) = skipn k a)
      by (apply firstn_all2; rewrite length_skipn; lia).
    rewrite Hs.
    f_equal. f_equal. lia. }
  rewrite R, firstn_firstn, Nat.min_l by lia.
  unfold Qm. rewrite !Nat2Z.id. rewrite sum_firstn_add. lia.
Qed.

Lemma length_rotate : forall (a : list Z) (k : nat), (k <= List.length a)%nat ->
  List.length (rotate k a) = List.length a.
Proof.
  intros a k Hk. unfold rotate. rewrite length_app, length_skipn, length_firstn. lia.
Qed.

(* Shift k is good iff Q(k) is at most every Q(m), m in [k+1, k+n]. *)
Lemma good_iff : forall (a : list Z) (k : nat), (k < List.length a)%nat ->
  good_shift a k = true <->
  forall m, Z.of_nat k + 1 <= m <= Z.of_nat k + Z.of_nat (List.length a) ->
            Qm a (Z.of_nat k) <= Qm a m.
Proof.
  intros a k Hk. unfold good_shift, nonneg_prefix_sums.
  rewrite forallb_forall, length_rotate by lia.
  split.
  - intros H m Hm.
    specialize (H (Z.to_nat m - k)%nat ltac:(apply in_seq; lia)).
    rewrite Z.leb_le in H. rewrite rot_sum in H by lia.
    replace (Z.of_nat (k + (Z.to_nat m - k))) with m in H by lia. lia.
  - intros H i Hi. apply in_seq in Hi. apply Z.leb_le. rewrite rot_sum by lia.
    specialize (H (Z.of_nat (k + i)) ltac:(lia)). lia.
Qed.

(* The number of good shifts below K. *)
Definition cntm (a : list Z) (K : nat) : nat :=
  List.length (filter (good_shift a) (seq 0 K)).

Lemma cntm_S_true : forall a K, good_shift a K = true -> cntm a (S K) = S (cntm a K).
Proof.
  intros a K G. unfold cntm. rewrite seq_S, filter_app, length_app.
  cbn [filter Nat.add]. rewrite G. cbn [List.length]. lia.
Qed.

Lemma cntm_S_false : forall a K, good_shift a K = false -> cntm a (S K) = cntm a K.
Proof.
  intros a K G. unfold cntm. rewrite seq_S, filter_app, length_app.
  cbn [filter Nat.add]. rewrite G. cbn [List.length]. lia.
Qed.

Lemma cntm_le : forall a K, (cntm a K <= K)%nat.
Proof.
  intros a K. induction K as [| K IH]; [unfold cntm; simpl; lia|].
  destruct (good_shift a K) eqn:G;
    [rewrite cntm_S_true by exact G | rewrite cntm_S_false by exact G]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Machine side                                                        *)
(* ------------------------------------------------------------------ *)

Section Proofs.

Variable a : list Z.
Variable x : array sint.
Hypothesis Hv : valid_input a.
Hypothesis Hx : repr x a.

Local Notation nZ := (Z.of_nat (List.length a)).
Local Notation nm := (PArray.length x).

Lemma n_val : (φ nm) = nZ /\ 1 <= nZ <= 1000000.
Proof.
  pose proof Hx as [Hl _]. pose proof Hv as [Hlen _]. unfold len in Hlen.
  split; [symmetry; exact Hl | lia].
Qed.

Lemma nth_bound : forall k, (k < List.length a)%nat -> -1000 <= nth k a 0 <= 1000.
Proof.
  intros k Hk. pose proof Hv as [_ Hf]. rewrite Forall_nth in Hf. apply Hf. exact Hk.
Qed.

Lemma Qb : forall j, 0 <= j <= 2 * nZ -> -2000000000 <= Qm a j <= 2000000000.
Proof.
  destruct n_val as [Hn Hnb]. intros j Hj.
  pose proof Hv as [_ Hf]. pose proof (Qm_bound a Hf j ltac:(lia)). lia.
Qed.

Lemma repr_get : forall i : int, (φ i) < nZ ->
  Sint63.to_Z (@PArray.get int x i) = nth (Z.to_nat (φ i)) a 0.
Proof.
  intros i Hi. pose proof Hx as [Hl Hc]. pose proof (to_Z_bounded i) as Bi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
  transitivity m; [exact Hr|]. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma prefix_spec : forall (z : Z) (i : int) (P : array int)
    (H : Acc (Zwf 0) (gap nm i)),
  gap nm i = z ->
  PArray.length P = (nm + 1)%uint63 ->
  (φ i) <= nZ ->
  (forall k : int, (φ k) <= (φ i) -> Sint63.to_Z P.[k] = Qm a (φ k)) ->
  PArray.length (prefix_loop x nm i P H) = (nm + 1)%uint63 /\
  forall k : int, (φ k) <= nZ ->
    Sint63.to_Z (prefix_loop x nm i P H).[k] = Qm a (φ k).
Proof.
  destruct n_val as [Hn Hnb].
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i P H Hz Hl Hi Hinv.
  rewrite prefix_loop_eq.
  destruct (bdec (i <? nm)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite alength_set. exact Hl.
    + lia.
    + intros k Hk. rewrite Hi1 in Hk.
      destruct (Z.eq_dec (φ k) ((φ i) + 1)) as [E | E].
      * assert (k = (i + 1)%uint63) by (apply to_Z_inj; lia). subst k.
        rewrite aget_set_same by (rewrite Hl, ltb_spec; sia).
        pose proof (Qb (φ i) ltac:(lia)).
        pose proof (nth_bound (Z.to_nat (φ i)) ltac:(lia)).
        rewrite sadd; rewrite (Hinv i), repr_get by lia.
        -- rewrite Hi1, Qm_succ by lia. reflexivity.
        -- lia.
      * rewrite aget_set_other by (intro F; apply E; rewrite <- F; exact Hi1).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Hl|]. intros k Hk. apply Hinv. lia.
Qed.

Lemma idx_mod : forall c : int, (c mod nm)%uint63 = of_Z ((φ c) mod nZ).
Proof.
  destruct n_val as [Hn Hnb]. intros c. apply to_Z_inj.
  rewrite mod_spec, of_Z_spec, Hn.
  rewrite (Z.mod_small ((φ c) mod nZ)); [reflexivity|].
  pose proof (Z.mod_pos_bound (φ c) nZ ltac:(lia)). rewrite wB_val. lia.
Qed.

(* The deque cell of cursor c. *)
Definition Dv (dq : array int) (c : Z) : Z := (φ (dq.[of_Z (c mod nZ)])).

(* The deque invariant: cursors h <= t, indices in [lo, hi], increasing
   at least as fast as the cursors, strictly increasing prefix sums, and
   every index of [lo, hi] dominated by a later deque index. *)
Record Inv (dq : array int) (h t lo hi : Z) : Prop := {
  iv_ht : 0 <= h <= t;
  iv_rng : forall c, h <= c < t -> lo <= Dv dq c <= hi;
  iv_gap : forall c c', h <= c /\ c < c' /\ c' < t -> c' - c <= Dv dq c' - Dv dq c;
  iv_q : forall c c', h <= c /\ c < c' /\ c' < t -> Qm a (Dv dq c) < Qm a (Dv dq c');
  iv_dom : forall m, lo <= m <= hi ->
    exists c, h <= c < t /\ m <= Dv dq c /\ Qm a (Dv dq c) <= Qm a m
}.

Lemma inv_front : forall dq h t h1 j,
  Inv dq h t (Z.max 1 (j - nZ)) (j - 1) -> h <= h1 <= t ->
  (forall c, h <= c < h1 -> Dv dq c + nZ <= j) ->
  (h1 < t -> j < Dv dq h1 + nZ) ->
  Inv dq h1 t (Z.max 1 (j - nZ + 1)) (j - 1).
Proof.
  intros dq h t h1 j [I1 I2 I3 I4 I5] Hh1 Hpop Hstop.
  constructor.
  - lia.
  - intros c Hc. pose proof (I2 c ltac:(lia)). split; [|lia].
    destruct (Z.eq_dec c h1) as [->|Ne].
    + specialize (Hstop ltac:(lia)). lia.
    + pose proof (I3 h1 c ltac:(lia)). specialize (Hstop ltac:(lia)). lia.
  - intros c c' Hc. apply I3. lia.
  - intros c c' Hc. apply I4. lia.
  - intros m Hm. destruct (I5 m ltac:(lia)) as (c & Hc & Hmc & Hq).
    exists c. split; [|split; assumption].
    destruct (Z_lt_le_dec c h1) as [Lt|Ge]; [|lia].
    specialize (Hpop c ltac:(lia)). lia.
Qed.

Lemma inv_push : forall dq h1 t t1 j,
  1 <= j ->
  Inv dq h1 t (Z.max 1 (j - nZ + 1)) (j - 1) ->
  h1 <= t1 <= t ->
  (forall c, t1 <= c < t -> Qm a j <= Qm a (Dv dq c)) ->
  (h1 < t1 -> Qm a (Dv dq (t1 - 1)) < Qm a j) ->
  forall (jm : int), (φ jm) = j -> PArray.length dq = nm ->
  Inv (dq.[of_Z (t1 mod nZ) <- jm]) h1 (t1 + 1) (Z.max 1 (j - nZ + 1)) j.
Proof.
  destruct n_val as [Hn Hnb].
  intros dq h1 t t1 j Hj [I1 I2 I3 I4 I5] Ht1 Hpop Hstop jm Hjm Hl.
  assert (Hsz : t1 - h1 <= nZ - 1).
  { destruct (Z_lt_le_dec h1 t1) as [Lt|Ge]; [|lia].
    pose proof (I2 h1 ltac:(lia)). pose proof (I2 (t1 - 1) ltac:(lia)).
    destruct (Z.eq_dec h1 (t1 - 1)) as [E|Ne]; [lia|].
    pose proof (I3 h1 (t1 - 1) ltac:(lia)). lia. }
  assert (Hidx : forall c, 0 <= c -> (φ (of_Z (c mod nZ))) = c mod nZ).
  { intros c Hc. rewrite of_Z_spec. apply Z.mod_small.
    pose proof (Z.mod_pos_bound c nZ ltac:(lia)). rewrite wB_val. lia. }
  assert (Hnew : Dv (dq.[of_Z (t1 mod nZ) <- jm]) t1 = j).
  { unfold Dv. rewrite aget_set_same; [exact Hjm|].
    rewrite Hl, ltb_spec, Hidx, Hn by lia. apply Z.mod_pos_bound. lia. }
  assert (Hold : forall c, h1 <= c < t1 ->
            Dv (dq.[of_Z (t1 mod nZ) <- jm]) c = Dv dq c).
  { intros c Hc. unfold Dv. rewrite aget_set_other; [reflexivity|].
    intro F. apply (f_equal to_Z) in F. rewrite !Hidx in F by lia.
    assert (G : (t1 - c) mod nZ = 0)
      by (rewrite Zminus_mod, F, Z.sub_diag; apply Z.mod_0_l; lia).
    rewrite Z.mod_small in G by lia. lia. }
  constructor.
  - lia.
  - intros c Hc. destruct (Z.eq_dec c t1) as [->|Ne]; [rewrite Hnew; lia|].
    rewrite Hold by lia. pose proof (I2 c ltac:(lia)). lia.
  - intros c c' Hc. destruct (Z.eq_dec c' t1) as [->|Ne].
    + rewrite Hnew, Hold by lia. pose proof (I2 (t1 - 1) ltac:(lia)).
      destruct (Z.eq_dec c (t1 - 1)) as [->|Ne']; [lia|].
      pose proof (I3 c (t1 - 1) ltac:(lia)). lia.
    + rewrite !Hold by lia. apply I3. lia.
  - intros c c' Hc. destruct (Z.eq_dec c' t1) as [->|Ne].
    + rewrite Hnew, Hold by lia. specialize (Hstop ltac:(lia)).
      destruct (Z.eq_dec c (t1 - 1)) as [->|Ne']; [lia|].
      pose proof (I4 c (t1 - 1) ltac:(lia)). lia.
    + rewrite !Hold by lia. apply I4. lia.
  - intros m Hm. destruct (Z.eq_dec m j) as [->|Ne].
    + exists t1. rewrite Hnew. split; [lia|]. split; lia.
    + destruct (I5 m ltac:(lia)) as (c & Hc & Hmc & Hq).
      destruct (Z_lt_le_dec c t1) as [Lt|Ge].
      * exists c. rewrite Hold by lia. split; [lia|]. split; assumption.
      * exists t1. rewrite Hnew. specialize (Hpop c ltac:(lia)).
        split; [lia|]. split; lia.
Qed.

(* The front of a nonempty deque is the minimum over the window. *)
Lemma inv_min : forall dq h t lo hi, Inv dq h t lo hi -> h < t ->
  lo <= Dv dq h <= hi /\ forall m, lo <= m <= hi -> Qm a (Dv dq h) <= Qm a m.
Proof.
  intros dq h t lo hi [I1 I2 I3 I4 I5] Hht. split; [apply I2; lia|].
  intros m Hm. destruct (I5 m Hm) as (c & Hc & _ & Hq).
  destruct (Z.eq_dec c h) as [->|Ne]; [exact Hq|].
  pose proof (I4 h c ltac:(lia)). lia.
Qed.

Section Sweep.

Variable P : array int.
Hypothesis HPv : forall k : int, (φ k) <= nZ -> Sint63.to_Z P.[k] = Qm a (φ k).
Variable tot : int.
Hypothesis Htot : tot = P.[nm].

Lemma qv_spec : forall e : int, (φ e) <= 2 * nZ ->
  Sint63.to_Z (qv P nm tot e) = Qm a (φ e).
Proof.
  destruct n_val as [Hn Hnb]. intros e He. unfold qv.
  destruct (e <=? nm)%uint63 eqn:E.
  - rewrite leb_spec in E. apply HPv. lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec in E.
    assert (Hd : (φ (e - nm))%uint63 = (φ e) - nZ) by sia.
    subst tot.
    pose proof (Qb nZ ltac:(lia)). pose proof (Qb ((φ e) - nZ) ltac:(lia)).
    rewrite sadd; rewrite (HPv nm), (HPv (e - nm)%uint63), Hd, Hn by lia.
    + rewrite <- Qm_hi by lia. f_equal. lia.
    + lia.
Qed.

Lemma pop_front_spec : forall (dq : array int) (j : int) (z : Z) (h t : int)
    (H : Acc (Zwf 0) (gap t h)),
  gap t h = z -> (φ h) <= (φ t) ->
  (forall c, (φ h) <= c < (φ t) -> Dv dq c <= 2 * nZ) ->
  forall h1, h1 = pop_front dq nm j h t H ->
  (φ h) <= (φ h1) <= (φ t) /\
  (forall c, (φ h) <= c < (φ h1) -> Dv dq c + nZ <= (φ j)) /\
  ((φ h1) < (φ t) -> (φ j) < Dv dq (φ h1) + nZ).
Proof.
  destruct n_val as [Hn Hnb].
  intros dq j z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h t H Hz Hht Hb h1 Eh1. subst h1.
  rewrite pop_front_eq.
  destruct (bdec (h <? t)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hh1 : (φ (h + 1))%uint63 = (φ h) + 1) by sia.
    assert (Hd : (φ (dq.[h mod nm] + nm))%uint63 = Dv dq (φ h) + nZ).
    { rewrite idx_mod. pose proof (Hb (φ h) ltac:(lia)) as B. unfold Dv in *.
      rewrite add_spec, Hn. apply Z.mod_small.
      pose proof (to_Z_bounded (dq.[of_Z ((φ h) mod nZ)])). rewrite wB_val. lia. }
    destruct (dq.[h mod nm] + nm <=? j)%uint63 eqn:E.
    + rewrite leb_spec, Hd in E.
      destruct (IH (gap t (h + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; exact Hlt)
                  (h + 1)%uint63 t (Acc_inv H (dec_step t h Hlt)) eq_refl ltac:(lia)
                  ltac:(intros c Hc; apply Hb; lia) _ eq_refl) as (A & B & C).
      split; [lia|]. split; [|exact C].
      intros c Hc. destruct (Z.eq_dec c (φ h)) as [->|Ne]; [exact E|]. apply B. lia.
    + rewrite <- Bool.not_true_iff_false, leb_spec, Hd in E.
      split; [lia|]. split; [intros c Hc; lia|]. intros _. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [lia|]. split; [intros c Hc; lia | intros; lia].
Qed.

Lemma pop_back_spec : forall (dq : array int) (qj h : int) (z : Z) (t : int)
    (H : Acc (Zwf 0) (gap t h)),
  gap t h = z -> (φ h) <= (φ t) ->
  (forall c, (φ h) <= c < (φ t) -> Dv dq c <= 2 * nZ) ->
  forall t1, t1 = pop_back dq P nm tot qj h t H ->
  (φ h) <= (φ t1) <= (φ t) /\
  (forall c, (φ t1) <= c < (φ t) -> Sint63.to_Z qj <= Qm a (Dv dq c)) /\
  ((φ h) < (φ t1) -> Qm a (Dv dq ((φ t1) - 1)) < Sint63.to_Z qj).
Proof.
  destruct n_val as [Hn Hnb].
  intros dq qj h z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t H Hz Hht Hb t1 Et1. subst t1.
  rewrite pop_back_eq.
  destruct (bdec (h <? t)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded h).
    assert (Ht1 : (φ (t - 1))%uint63 = (φ t) - 1) by sia.
    assert (Hq : Sint63.to_Z (qv P nm tot dq.[(t - 1) mod nm]%uint63)
                 = Qm a (Dv dq ((φ t) - 1))).
    { rewrite idx_mod. rewrite qv_spec.
      - unfold Dv. rewrite Ht1. reflexivity.
      - pose proof (Hb ((φ t) - 1) ltac:(lia)) as B. unfold Dv in B.
        rewrite Ht1. exact B. }
    destruct (PrimInt63.lesb qj (qv P nm tot dq.[(t - 1) mod nm]%uint63)) eqn:E.
    + rewrite sleb_iff, Hq in E.
      destruct (IH (gap (t - 1)%uint63 h) ltac:(rewrite <- Hz; apply dec_back; exact Hlt)
                  (t - 1)%uint63 (Acc_inv H (dec_back t h Hlt)) eq_refl ltac:(lia)
                  ltac:(intros c Hc; apply Hb; lia) _ eq_refl) as (A & B & C).
      split; [lia|]. split; [|exact C].
      intros c Hc. destruct (Z.eq_dec c ((φ t) - 1)) as [->|Ne]; [exact E|].
      apply B. lia.
    + rewrite <- Bool.not_true_iff_false, sleb_iff, Hq in E.
      split; [lia|]. split; [intros c Hc; lia|]. intros _. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [lia|]. split; [intros c Hc; lia | intros; lia].
Qed.

Lemma sweep_spec : forall (z : Z) (j h t cnt : int) (dq : array int)
    (H : Acc (Zwf 0) (gap (nm + nm)%uint63 j)),
  gap (nm + nm)%uint63 j = z ->
  1 <= (φ j) <= 2 * nZ ->
  PArray.length dq = nm ->
  (φ t) <= (φ j) - 1 ->
  Inv dq (φ h) (φ t) (Z.max 1 ((φ j) - nZ)) ((φ j) - 1) ->
  (φ cnt) = Z.of_nat (cntm a (Z.to_nat ((φ j) - nZ))) ->
  (φ (sweep P nm tot (nm + nm)%uint63 j h t cnt dq H)) = Z.of_nat (cntm a (List.length a)).
Proof.
  destruct n_val as [Hn Hnb].
  assert (Hm : (φ (nm + nm))%uint63 = 2 * nZ) by sia.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j h t cnt dq H Hz Hj Hl Ht Hinv Hcnt.
  rewrite sweep_eq.
  destruct (bdec (j <? nm + nm)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec, Hm in Hlt'.
    cbv zeta.
    pose proof (iv_ht _ _ _ _ _ Hinv) as Hht.
    assert (Hb : forall c, (φ h) <= c < (φ t) -> Dv dq c <= 2 * nZ).
    { intros c Hc. pose proof (iv_rng _ _ _ _ _ Hinv c Hc). lia. }
    destruct (pop_front_spec dq j _ h t (Zwf_well_founded 0 (gap t h)) eq_refl
                ltac:(lia) Hb _ eq_refl) as (F1 & F2 & F3).
    set (h1 := pop_front dq nm j h t (Zwf_well_founded 0 (gap t h))) in *.
    pose proof (inv_front dq (φ h) (φ t) (φ h1) (φ j) Hinv F1 F2 F3) as Hinv1.
    assert (Hb1 : forall c, (φ h1) <= c < (φ t) -> Dv dq c <= 2 * nZ)
      by (intros c Hc; apply Hb; lia).
    destruct (pop_back_spec dq (qv P nm tot j) h1 _ t (Zwf_well_founded 0 (gap t h1))
                eq_refl ltac:(lia) Hb1 _ eq_refl) as (B1 & B2 & B3).
    set (t1 := pop_back dq P nm tot (qv P nm tot j) h1 t
                 (Zwf_well_founded 0 (gap t h1))) in *.
    rewrite qv_spec in B2, B3 by lia.
    assert (Ht1 : (φ (t1 + 1))%uint63 = (φ t1) + 1) by sia.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    rewrite (idx_mod t1), (idx_mod h1).
    pose proof (inv_push dq (φ h1) (φ t) (φ t1) (φ j) ltac:(lia) Hinv1 B1 B2 B3
                  j eq_refl Hl) as Hinv2.
    set (dq1 := dq.[of_Z ((φ t1) mod nZ) <- j]) in *.
    assert (Hl1 : PArray.length dq1 = nm) by (unfold dq1; rewrite alength_set; exact Hl).
    eapply IH; [ | reflexivity | lia | exact Hl1 | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite Ht1, Hj1.
      replace ((φ j) + 1 - nZ) with ((φ j) - nZ + 1) by lia.
      replace ((φ j) + 1 - 1) with (φ j) by lia. exact Hinv2.
    + rewrite Hj1.
      destruct (nm <=? j)%uint63 eqn:Enj.
      * rewrite leb_spec, Hn in Enj.
        destruct (inv_min _ _ _ _ _ Hinv2 ltac:(lia)) as [Mr Mm].
        assert (Hk : Sint63.to_Z (qv P nm tot (j - nm)%uint63) = Qm a ((φ j) - nZ)).
        { rewrite qv_spec by sia. f_equal. sia. }
        assert (Hf : Sint63.to_Z (qv P nm tot dq1.[of_Z ((φ h1) mod nZ)])
                     = Qm a (Dv dq1 (φ h1))).
        { rewrite qv_spec; [reflexivity|]. unfold Dv in Mr. lia. }
        pose proof (good_iff a (Z.to_nat ((φ j) - nZ)) ltac:(lia)) as G.
        rewrite Z2Nat.id in G by lia.
        pose proof (cntm_le a (Z.to_nat ((φ j) - nZ))) as Cle.
        replace (Z.to_nat ((φ j) + 1 - nZ)) with (S (Z.to_nat ((φ j) - nZ))) by lia.
        destruct (PrimInt63.lesb (qv P nm tot (j - nm)%uint63)
                    (qv P nm tot dq1.[of_Z ((φ h1) mod nZ)])) eqn:E.
        -- rewrite sleb_iff, Hk, Hf in E.
           rewrite cntm_S_true.
           ++ assert ((φ (cnt + 1))%uint63 = (φ cnt) + 1) by sia. lia.
           ++ apply G. intros m Hm'. specialize (Mm m ltac:(lia)). lia.
        -- rewrite <- Bool.not_true_iff_false, sleb_iff, Hk, Hf in E.
           rewrite cntm_S_false; [exact Hcnt|].
           apply Bool.not_true_iff_false. intro Gt. rewrite G in Gt.
           apply E. apply Gt. lia.
      * rewrite <- Bool.not_true_iff_false, leb_spec, Hn in Enj.
        replace (Z.to_nat ((φ j) + 1 - nZ)) with (Z.to_nat ((φ j) - nZ)) by lia.
        exact Hcnt.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hm in Hge.
    rewrite Hcnt. replace (Z.to_nat ((φ j) - nZ)) with (List.length a) by lia.
    reflexivity.
Qed.

End Sweep.

Lemma count_impl_value : (φ (count_impl x)) = Z.of_nat (cntm a (List.length a)).
Proof.
  destruct n_val as [Hn Hnb].
  unfold count_impl. cbv zeta.
  assert (HmP : PArray.length (PArray.make (nm + 1)%uint63 (0 : int)) = (nm + 1)%uint63).
  { rewrite alength_make.
    replace (nm + 1 <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. sia. }
  destruct (prefix_spec _ 0 _ (Zwf_well_founded 0 (gap nm 0)) eq_refl HmP
              ltac:(change (φ 0) with 0; lia)) as [HPl HPv].
  { intros k Hk. change (φ 0) with 0 in Hk.
    assert (Hk0 : (φ k) = 0) by (pose proof (to_Z_bounded k); lia).
    rewrite Hk0. transitivity (Sint63.to_Z 0%uint63); [f_equal; apply aget_make | reflexivity]. }
  set (P := prefix_loop x nm 0 (PArray.make (nm + 1)%uint63 0%uint63) (Zwf_well_founded 0 (gap nm 0)))
    in *.
  assert (Hdq : PArray.length (PArray.make nm (0 : int)) = nm).
  { rewrite alength_make.
    replace (nm <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  apply (sweep_spec P HPv (P.[nm]) eq_refl _ 1%uint63 0%uint63 0%uint63 0%uint63 (PArray.make nm 0%uint63) _ eq_refl);
    change (φ 1) with 1; change (φ 0) with 0.
  - lia.
  - exact Hdq.
  - lia.
  - constructor; intros; lia.
  - replace (Z.to_nat (1 - nZ)) with 0%nat by lia. reflexivity.
Qed.

End Proofs.

Lemma count_impl_correct : forall (a : list Z) (x : array sint),
  valid_input a -> repr x a ->
  exists c : N, repr (count_impl x) c /\ count_good_shifts_spec a c.
Proof.
  intros a x Hv Hx. exists (len (good_shifts a)). split; [|reflexivity].
  unfold repr, repr_uint. rewrite (count_impl_value a x Hv Hx).
  unfold len, good_shifts, cntm. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition count_good_shifts : array sint -> uint := count_impl.
Elpi complexity count_good_shifts.

Definition count_good_shifts_correct : forall (a : list Z) (x : array sint),
  valid_input a -> repr x a ->
  exists c : N, repr (count_good_shifts x) c /\ count_good_shifts_spec a c
  := count_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* Each loop is bounded on its cost twin by strong induction on a nat
   bound of its measure (the Acc proof destructed so that cost_simpl
   unfolds the fix once, cost_destruct on the tests), the callees' bounds
   generalized in their callers' goals (the callees' twins are kept folded
   by `Arguments ... : simpl never`; their partial applications cost 0 by
   conversion).  `gap` and `zn` are never unfolded by cbn: cbn must never
   meet φ of a variable.

   The amortised argument.  The two pop loops are bounded by the distance
   their cursor travels, stated against the loop's own result:
     pop_front_time : cost + zn h * 40 <= zn h1 * 40 + 40      (h1 its result)
     pop_back_time  : cost + zn t1 * 60 <= zn t * 60 + 60      (t1 its result)
   and the sweep carries the deque size t - h as a potential:
     sweep_time : cost (sweep .. j h t ..) <= gap m j * 400 + (t - h) * 60 + 20
   With h <= h1 <= t1 <= t (pop_front_range, pop_back_range) and the next
   deque size t1 + 1 - h1, the pops of one step are paid by the drop of the
   potential, (t - h) - (t1 + 1 - h1) = (h1 - h) + (t - t1) - 1: every
   index is pushed once and popped at most once. *)

Open Scope uint63_scope.

Definition zn (x : int) : nat := Z.to_nat (φ x).
Arguments zn : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma qv_time P PC n nC tot totC j jC :
  (cost (extract (extract (extract (qv_cost stepsCM P PC) n nC) tot totC) j jC) <= 20)%nat.
Proof.
  unfold qv_cost. cost_simpl. cost_destruct (j <=? n); cost_simpl; lia.
Qed.

Lemma zn_pred (h t : int) : (h <? t) = true -> zn t = S (zn (t - 1)).
Proof. intros H. apply ltb_spec in H. pose proof (to_Z_bounded h). unfold zn. assert (φ (t - 1) = φ t - 1)%Z by sia. lia. Qed.

Lemma gap_pred (h t : int) N : (h <? t) = true -> (Z.to_nat (gap t h) <= S N)%nat -> (Z.to_nat (gap (t - 1) h) <= N)%nat.
Proof. intros H HN. apply ltb_spec in H. pose proof (to_Z_bounded h). unfold gap in *. assert (φ (t - 1) = φ t - 1)%Z by sia. lia. Qed.

Lemma gap_zero (h t : int) : (h <? t) = true -> (Z.to_nat (gap t h) <= 0)%nat -> False.
Proof. intros H HN. apply ltb_spec in H. unfold gap in *. lia. Qed.
Lemma zn_succ (h t : int) : (h <? t) = true -> zn (h + 1) = S (zn h).
Proof. intros H. apply ltb_spec in H. unfold zn. assert (φ (h + 1) = φ h + 1)%Z by sia. lia. Qed.
Lemma gap_succ (h t : int) N : (h <? t) = true -> (Z.to_nat (gap t h) <= S N)%nat -> (Z.to_nat (gap t (h + 1)) <= N)%nat.
Proof. intros H HN. apply ltb_spec in H. unfold gap in *. assert (φ (h + 1) = φ h + 1)%Z by sia. lia. Qed.
Lemma pop_front_time dq dqC n nC j jC h hC t tC H HC :
  (cost (extract (extract (extract (extract (extract (pop_front_cost stepsCM dq dqC) n nC) j jC) h hC) t tC) H HC)
    + zn h * 40 <= zn (pop_front dq n j h t H) * 40 + 40)%nat.
Proof.
  unfold pop_front_cost. cbn.
  match goal with |- context [@cost ?T (?G dq dqC n nC j jC h hC t tC H HC)] =>
    assert (HG : forall N h hC H HC, (Z.to_nat (gap t h) <= N)%nat ->
       (cost (G dq dqC n nC j jC h hC t tC H HC) + zn h * 40 <= zn (pop_front dq n j h t H) * 40 + 40)%nat) end.
  { induction N as [|N IH]; intros h' hC' [g] HC' HN;
      cost_simpl;
      pose proof (bdec_time (h' <? t) (bool_w (h' <? t))) as HB;
      cost_destruct (bdec (h' <? t)); cost_simpl.
    - exfalso. exact (gap_zero _ _ e HN).
    - lia.
    - pose proof (zn_succ _ _ e) as Ez. pose proof (gap_succ _ _ _ e HN) as HN'.
      cost_destruct (dq.[h' mod n] + n <=? j); cost_simpl.
      + match goal with |- context [@cost ?T (?G' dq dqC n nC j jC (h' + 1)%uint63 ?w t tC ?a ?e)] =>
          pose proof (IH (h' + 1)%uint63 w a e HN' : (@cost T (G' dq dqC n nC j jC (h' + 1)%uint63 w t tC a e) + _ <= _)%nat) as HI end.
        rewrite Ez in HI. lia.
      + lia.
    - lia. }
  match goal with |- context [@cost ?T (?G dq dqC n nC j jC h hC t tC H HC)] =>
    exact (HG _ h hC H HC (le_n _) : (@cost T (G dq dqC n nC j jC h hC t tC H HC) + _ <= _)%nat) end.
Qed.
Lemma pop_back_time dq dqC P PC n nC tot totC qj qjC h hC t tC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (pop_back_cost stepsCM dq dqC) P PC) n nC) tot totC) qj qjC) h hC) t tC) H HC)
    + zn (pop_back dq P n tot qj h t H) * 60 <= zn t * 60 + 60)%nat.
Proof.
  unfold pop_back_cost. cbn.
  match goal with |- context [@cost ?T (?G dq dqC P PC n nC tot totC qj qjC h hC t tC H HC)] =>
    assert (HG : forall N t tC H HC, (Z.to_nat (gap t h) <= N)%nat ->
       (cost (G dq dqC P PC n nC tot totC qj qjC h hC t tC H HC) + zn (pop_back dq P n tot qj h t H) * 60 <= zn t * 60 + 60)%nat) end.
  { induction N as [|N IH]; intros t' tC' [g] HC' HN;
      cost_simpl;
      pose proof (bdec_time (h <? t') (bool_w (h <? t'))) as HB;
      cost_destruct (bdec (h <? t')); cost_simpl.
    - exfalso. exact (gap_zero _ _ e HN).
    - lia.
    - pose proof (zn_pred _ _ e) as Ez. pose proof (gap_pred _ _ _ e HN) as HN'.
      change (cost (qv_cost stepsCM P PC)) with 0%nat.
      change (cost (extract (qv_cost stepsCM P PC) n nC)) with 0%nat.
      change (cost (extract (extract (qv_cost stepsCM P PC) n nC) tot totC)) with 0%nat.
      repeat match goal with |- context [@cost ?T ?X] =>
        lazymatch X with
        | extract (extract (extract (qv_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
            let Hc := fresh "Hqv" in
            pose proof (qv_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
            revert Hc; generalize (@cost T X); intros ? Hc
        end end.
      cost_destruct (lesb qj (qv P n tot dq.[(t' - 1) mod n])); cost_simpl.
      + match goal with |- context [@cost ?T (?G' dq dqC P PC n nC tot totC qj qjC h hC (t' - 1)%uint63 ?w ?a ?e)] =>
          pose proof (IH (t' - 1)%uint63 w a e HN' : (@cost T (G' dq dqC P PC n nC tot totC qj qjC h hC (t' - 1)%uint63 w a e) + _ <= _)%nat) as HI end.
        rewrite Ez. lia.
      + lia.
    - lia. }
  match goal with |- context [@cost ?T (?G dq dqC P PC n nC tot totC qj qjC h hC t tC H HC)] =>
    exact (HG _ t tC H HC (le_n _) : (@cost T (G dq dqC P PC n nC tot totC qj qjC h hC t tC H HC) + _ <= _)%nat) end.
Qed.

Lemma pop_front_range : forall dq n j (z : Z) h t (H : Acc (Zwf 0) (gap t h)),
  gap t h = z -> (φ h <= φ t)%Z -> (φ h <= φ (pop_front dq n j h t H) <= φ t)%Z.
Proof.
  intros dq n j z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h t H Hz Hht. rewrite pop_front_eq.
  destruct (bdec (h <? t)) as [Hlt | Hge]; [|lia].
  pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
  assert (Hh1 : (φ (h + 1) = φ h + 1)%Z) by sia.
  destruct (dq.[h mod n] + n <=? j); [|lia].
  pose proof (IH (gap t (h + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hlt)
                (h + 1) t (Acc_inv H (dec_step t h Hlt)) eq_refl ltac:(lia)). lia.
Qed.

Lemma pop_back_range : forall dq P n tot qj h (z : Z) t (H : Acc (Zwf 0) (gap t h)),
  gap t h = z -> (φ h <= φ t)%Z -> (φ h <= φ (pop_back dq P n tot qj h t H) <= φ t)%Z.
Proof.
  intros dq P n tot qj h z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t H Hz Hht. rewrite pop_back_eq.
  destruct (bdec (h <? t)) as [Hlt | Hge]; [|lia].
  pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'. pose proof (to_Z_bounded h).
  assert (Ht1 : (φ (t - 1) = φ t - 1)%Z) by sia.
  destruct (lesb qj (qv P n tot dq.[(t - 1) mod n])); [|lia].
  pose proof (IH (gap (t - 1) h) ltac:(rewrite <- Hz; apply dec_back; exact Hlt)
                (t - 1) (Acc_inv H (dec_back t h Hlt)) eq_refl ltac:(lia)). lia.
Qed.

Arguments qv : simpl never.

Ltac zero_partials :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch T with forall _, _ => change (@cost T X) with 0%nat end end.
Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  end.
Ltac gen_callees :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (qv_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
        let Hc := fresh "Hqv" in
        pose proof (qv_time a aC b bC c cC d dC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (pop_front_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
        let Hc := fresh "Hpf" in
        pose proof (pop_front_time a aC b bC c cC d dC e eC f fC : (@cost T X + _ <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (extract (extract (pop_back_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?k ?kC =>
        let Hc := fresh "Hpb" in
        pose proof (pop_back_time a aC b bC c cC d dC e eC f fC g gC k kC : (@cost T X + _ <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.

Ltac zero_pairs := repeat match goal with |- context [@cost ?T (?z, ?x)] => change (@cost T (z, x)) with 0%nat end.

Lemma sweep_arith (m j h t h1 t1 : int) : (j <? m) = true ->
  (φ h <= φ h1 <= φ t)%Z -> (φ h1 <= φ t1 <= φ t)%Z -> (φ t < φ j)%Z ->
  Z.to_nat (gap m j) = S (Z.to_nat (gap m (j + 1))) /\ zn (t1 + 1) = S (zn t1) /\
  (zn h <= zn h1 <= zn t1)%nat /\ (zn t1 <= zn t)%nat /\
  (φ h1 <= φ (t1 + 1))%Z /\ (φ (t1 + 1) < φ (j + 1))%Z.
Proof.
  intros Hj H1 H2 H3. apply ltb_spec in Hj. pose proof (to_Z_bounded m).
  assert (E1 : (φ (j + 1) = φ j + 1)%Z) by sia.
  assert (E2 : (φ (t1 + 1) = φ t1 + 1)%Z) by sia.
  unfold gap, zn. rewrite E1, E2. lia.
Qed.

(* the induction hypothesis of the sweep, at the recursive call *)
Ltac use_IH IH HN2 A5 A6 :=
  match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?j2 ?w ?h2 ?hC2 ?t2 ?tC2 ?c2 ?cC2 ?d2 ?dC2 ?a ?e)] =>
    let HI := fresh "HI" in
    pose proof (IH _ HN2 j2 w h2 hC2 t2 tC2 c2 cC2 d2 dC2 a e (le_n _) A5 A6
      : (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 j2 w h2 hC2 t2 tC2 c2 cC2 d2 dC2 a e) <= _)%nat) as HI;
    revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 j2 w h2 hC2 t2 tC2 c2 cC2 d2 dC2 a e)); intros ? HI
  end.

Lemma sweep_time P PC n nC tot totC m mC j jC h hC t tC cnt cntC dq dqC H HC :
  (φ h <= φ t)%Z -> (φ t < φ j)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (sweep_cost stepsCM P PC) n nC) tot totC) m mC) j jC) h hC) t tC) cnt cntC) dq dqC) H HC)
    <= Z.to_nat (gap m j) * 400 + (zn t - zn h) * 60 + 20)%nat.
Proof.
  unfold sweep_cost. cbn.
  match goal with |- context [@cost ?T (?G P PC n nC tot totC m mC j jC h hC t tC cnt cntC dq dqC H HC)] =>
    assert (HG : forall N j jC h hC t tC cnt cntC dq dqC H HC, (Z.to_nat (gap m j) <= N)%nat ->
       (φ h <= φ t)%Z -> (φ t < φ j)%Z ->
       (cost (G P PC n nC tot totC m mC j jC h hC t tC cnt cntC dq dqC H HC)
         <= Z.to_nat (gap m j) * 400 + (zn t - zn h) * 60 + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros j' jC' h' hC' t' tC' c' cC' d' dC' [g] HC' HN Hht Htj.
    cost_simpl.
    pose proof (bdec_time (j' <? m) (bool_w (j' <? m))) as HB.
    cost_destruct (bdec (j' <? m)). cost_simpl.
    2:{ zero_pairs. lia. }
    zero_partials. set_simpl. gen_callees.
    pose proof (pop_front_range d' n j' (gap t' h') h' t' (Zwf_well_founded 0 (gap t' h')) eq_refl Hht) as R1.
    set (h1 := pop_front d' n j' h' t' (Zwf_well_founded 0 (gap t' h'))) in *.
    pose proof (pop_back_range d' P n tot (qv P n tot j') h1 (gap t' h1) t' (Zwf_well_founded 0 (gap t' h1)) eq_refl ltac:(lia)) as R2.
    set (t1 := pop_back d' P n tot (qv P n tot j') h1 t' (Zwf_well_founded 0 (gap t' h1))) in *.
    destruct (sweep_arith m j' h' t' h1 t1 e R1 R2 Htj) as (A1 & A2 & A3 & A4 & A5 & A6).
    assert (HN2 : (Z.to_nat (gap m (j' + 1)) < N)%nat) by lia.
    cost_destruct (n <=? j').
    - cost_simpl.
      cost_destruct (lesb (qv P n tot (j' - n)) (qv P n tot d'.[t1 mod n <- j'].[h1 mod n])).
      + cost_simpl. zero_pairs. use_IH IH HN2 A5 A6. lia.
      + cost_simpl. zero_pairs. use_IH IH HN2 A5 A6. lia.
    - cost_simpl. zero_pairs. use_IH IH HN2 A5 A6. lia. }
  intros Hht Htj.
  match goal with |- context [@cost ?T (?G P PC n nC tot totC m mC j jC h hC t tC cnt cntC dq dqC H HC)] =>
    exact (HG _ j jC h hC t tC cnt cntC dq dqC H HC (le_n _) Hht Htj : (@cost T (G P PC n nC tot totC m mC j jC h hC t tC cnt cntC dq dqC H HC) <= _)%nat) end.
Qed.

Lemma gap_S (i n : int) : (i <? n) = true -> Z.to_nat (gap n i) = S (Z.to_nat (gap n (i + 1))).
Proof.
  intros Hx. apply ltb_spec in Hx. unfold gap.
  assert (E1 : (φ (i + 1) = φ i + 1)%Z) by sia. rewrite E1. lia.
Qed.

Lemma prefix_loop_time x xC n nC i iC P PC H HC :
  (cost (extract (extract (extract (extract (prefix_loop_cost stepsCM x xC) n nC) i iC) P PC) H HC)
    <= Z.to_nat (gap n i) * 40 + 20)%nat.
Proof.
  unfold prefix_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC i iC P PC H HC)] =>
    assert (HG : forall N i iC P PC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G x xC n nC i iC P PC H HC) <= Z.to_nat (gap n i) * 40 + 20)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' P' PC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials. set_simpl.
      assert (E : Z.to_nat (gap n i') = S (Z.to_nat (gap n (i' + 1))))
        by (match goal with Hx : (i' <? n) = true |- _ => exact (gap_S _ _ Hx) end).
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?i2 ?iC2 ?P2 ?PC2 ?a ?e)] =>
        pose proof (IH _ HN2 i2 iC2 P2 PC2 a e (le_n _)
          : (@cost T (G' a1 a2 a3 a4 i2 iC2 P2 PC2 a e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 i2 iC2 P2 PC2 a e)); intros ? HI
      end.
      lia.
    - zero_pairs. lia. }
  match goal with |- context [@cost ?T (?G x xC n nC i iC P PC H HC)] =>
    exact (HG _ i iC P PC H HC (le_n _) : (@cost T (G x xC n nC i iC P PC H HC) <= _)%nat) end.
Qed.

Ltac make_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.

Lemma le00 : (φ 0 <= φ 0)%Z.
Proof. reflexivity. Qed.
Lemma lt01 : (φ 0 < φ 1)%Z.
Proof. reflexivity. Qed.

Lemma len_arith (n : int) : (φ n <= φ max_length)%Z ->
  Z.to_nat (gap n 0) = zn n /\ (Z.to_nat (gap (n + n) 1) <= zn n * 2)%nat /\ (zn 0 - zn 0 = 0)%nat.
Proof.
  intros Hn. rewrite max_length_val in Hn. pose proof (to_Z_bounded n).
  assert (E : (φ (n + n) = φ n + φ n)%Z) by sia.
  unfold gap, zn. rewrite E. change (φ 0) with 0%Z. change (φ 1) with 1%Z. lia.
Qed.

Lemma count_impl_time x xC :
  (cost (count_impl_cost stepsCM x xC) <= 1000 * (zn (PArray.length x) + 1) + 0)%nat.
Proof.
  unfold count_impl_cost. cost_simpl.
  zero_partials. make_simpl.
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (prefix_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
        let Hc := fresh "Hpl" in
        pose proof (prefix_loop_time a aC b bC c cC d dC e eC : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    | extract (extract (extract (extract (extract (extract (extract (extract (extract (sweep_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?k ?kC) ?l ?lC) ?o ?oC =>
        let Hc := fresh "Hsw" in
        pose proof (sweep_time a aC b bC c cC d dC e eC f fC g gC k kC l lC o oC le00 lt01 : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.
  pose proof (len_arith (PArray.length x) ltac:(apply leb_spec, leb_length)) as (L1 & L2 & L3).
  lia.
Qed.

Theorem count_good_shifts_time : exists c1 c2 : nat,
  forall (sequence : list Z) (sequence_arr : array sint),
  valid_input sequence -> repr sequence_arr sequence ->
  (cost1 count_good_shifts_cost sequence_arr <= c1 * (size sequence_arr + 1) + c2)%nat.
Proof.
  exists 1000%nat, 0%nat. intros sequence x _ _.
  unfold cost1, count_good_shifts_cost.
  pose proof (count_impl_time x (witness x)) as Hc.
  change (size x) with (zn (PArray.length x)).
  exact Hc.
Qed.
