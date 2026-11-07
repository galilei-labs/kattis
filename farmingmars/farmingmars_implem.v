(* Implementation of farmingmars.spec: Mo's algorithm over dense ids.

   Code.
   - [msort le n]: bottom-up merge sort of the index array 0 .. n-1 under
     the comparator [le], ping-ponging between two flat arrays (runs of
     width 1, 2, 4, ...).  Used twice: once on the acres, compared by pH
     (float [<=?]), once on the queries, in Mo's order (block of the left
     end, block size [blk n] = ceil(sqrt n), then right end).
   - [mk_ids]: the id of acre i is the lower bound of ph_i in the sorted
     acres (binary search [bs]): the number of acres with a smaller pH.
     Two acres get the same id iff their pH are equal reals; ids < n.
   - [mo_step]: for each query in Mo's order, [move] slides the current
     window [L, R) (0-based, half-open) one acre at a time to [l-1, r),
     maintaining cnt[v] (acres of id v in the window) and ge[c] (ids with
     cnt >= c, for c >= 1).  The interval is usable iff
     ge[(r-l+1)/2 + 1] > 0: one read.  The answer is written at the
     query's own index.
   Every loop is the combinator [loop] (erased Acc on hi - i) except the
   binary search and [move], which recurse on their own erased Acc.  All
   tables are flat, threaded linearly.  No Z, no nat in the code.

   Proof.  The sort: the output holds indices < n, every index occurs in
   it (membership, not a permutation: that is all the proof needs), and,
   for a total preorder on 0 .. n-1, it is sorted.  The ids: the lower
   bound characterisation.  The window: cnt and ge are the counting
   functions [cz] of the window, and ge[t] > 0 iff some pH value has
   count >= t in the acres l..r (the spec's [usable]). *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Respeced Require Import Repr ReprFloat.
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

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

(* The loop combinator: for i = lo, lo+1, ... while i < hi and
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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* -- Merge sort of the indices 0 .. n-1 -- *)

Definition iota (n : int) : array int :=
  loop n (fun _ _ => true) (fun i a => a.[i <- i]) 0 (PArray.make n 0).

(* one output cell k of the merge of src[lo, mid) and src[mid, hi) *)
Definition merge_step (le : int -> int -> bool) (src : array int) (mid hi : int)
    (k : int) (st : int * int * array int) : int * int * array int :=
  let '(i, j, dst) := st in
  if i <? mid then
    if j <? hi then
      if le src.[i] src.[j] then (i + 1, j, dst.[k <- src.[i]])
      else (i, j + 1, dst.[k <- src.[j]])
    else (i + 1, j, dst.[k <- src.[i]])
  else (i, j + 1, dst.[k <- src.[j]]).

Definition merge (le : int -> int -> bool) (src dst : array int) (lo mid hi : int)
    : array int :=
  snd (loop hi (fun _ _ => true) (merge_step le src mid hi) lo (lo, mid, dst)).

Definition seg_mid (n w lo : int) : int := if lo + w <? n then lo + w else n.

(* one pass: runs of width w of src merged pairwise into dst *)
Definition pass (le : int -> int -> bool) (n w : int) (src dst : array int) : array int :=
  let w2 := w + w in
  loop ((n + w2 - 1) / w2) (fun _ _ => true)
    (fun s d => let lo := s * w2 in
                merge le src d lo (seg_mid n w lo) (seg_mid n w2 lo)) 0 dst.

Definition msort (le : int -> int -> bool) (n : int) : array int :=
  snd (fst (loop 23 (fun _ st => fst (fst st) <? n)
     (fun _ st => let '(w, src, dst) := st in (w + w, pass le n w src dst, src))
     0 (1, iota n, PArray.make n 0))).

(* -- Dense ids -- *)

Lemma dec_bs_r : forall lo hi : int, (lo <? hi) = true ->
  Zwf 0 (gap hi (lo + (hi - lo) / 2 + 1)) (gap hi lo).
Proof.
  intros lo hi H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  pose proof (to_Z_bounded lo). unfold Zwf, gap. sia.
Qed.

Lemma dec_bs_l : forall lo hi : int, (lo <? hi) = true ->
  Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof.
  intros lo hi H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  pose proof (to_Z_bounded lo). unfold Zwf, gap. sia.
Qed.

(* the first position k of [lo, hi) with not (ph[P[k]] < v) *)
Fixpoint bs (p : array float) (P : array int) (v : float) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : int :=
  match bdec (lo <? hi) with
  | left Hlt =>
      if (p.[P.[lo + (hi - lo) / 2]] <? v)%float
      then bs p P v (lo + (hi - lo) / 2 + 1) hi (Acc_inv H (dec_bs_r lo hi Hlt))
      else bs p P v lo (lo + (hi - lo) / 2) (Acc_inv H (dec_bs_l lo hi Hlt))
  | right _ => lo
  end.

Definition lbound (p : array float) (P : array int) (n : int) (v : float) : int :=
  bs p P v 0 n (Zwf_well_founded 0 (gap n 0)).

Definition mk_ids (p : array float) (P : array int) (n : int) : array int :=
  loop n (fun _ _ => true) (fun i a => a.[i <- lbound p P n p.[i]]) 0 (PArray.make n 0).

(* -- Mo's order -- *)

(* the least b >= 1 with b * b >= n *)
Definition blk (n : int) : int := loop n (fun _ b => b * b <? n) (fun _ b => b + 1) 0 1.

Definition mo_le (ls rs : array int) (B : int) (a b : int) : bool :=
  let ba := (ls.[a] - 1) / B in
  let bb := (ls.[b] - 1) / B in
  if ba <? bb then true else if bb <? ba then false else rs.[a] <=? rs.[b].

(* -- The window -- *)

Definition add (ids : array int) (pos : int) (cnt ge : array int) : array int * array int :=
  let v := ids.[pos] in
  let c := cnt.[v] + 1 in
  (cnt.[v <- c], ge.[c <- ge.[c] + 1]).

Definition rem (ids : array int) (pos : int) (cnt ge : array int) : array int * array int :=
  let v := ids.[pos] in
  let c := cnt.[v] in
  (cnt.[v <- c - 1], ge.[c <- ge.[c] - 1]).

Definition mmeas (tl tr L R : int) : Z :=
  (Z.abs (to_Z L - to_Z tl) + Z.abs (to_Z R - to_Z tr))%Z.

Lemma dec_m1 : forall tl tr L R : int, (tl <? L) = true ->
  Zwf 0 (mmeas tl tr (L - 1) R) (mmeas tl tr L R).
Proof.
  intros tl tr L R H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded tl).
  assert (to_Z (L - 1) = (to_Z L - 1)%Z) by sia. unfold Zwf, mmeas. lia.
Qed.

Lemma dec_m2 : forall tl tr L R : int, (R <? tr) = true ->
  Zwf 0 (mmeas tl tr L (R + 1)) (mmeas tl tr L R).
Proof.
  intros tl tr L R H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded tr).
  assert (to_Z (R + 1) = (to_Z R + 1)%Z) by sia. unfold Zwf, mmeas. lia.
Qed.

Lemma dec_m3 : forall tl tr L R : int, (L <? tl) = true ->
  Zwf 0 (mmeas tl tr (L + 1) R) (mmeas tl tr L R).
Proof.
  intros tl tr L R H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded tl).
  assert (to_Z (L + 1) = (to_Z L + 1)%Z) by sia. unfold Zwf, mmeas. lia.
Qed.

Lemma dec_m4 : forall tl tr L R : int, (tr <? R) = true ->
  Zwf 0 (mmeas tl tr L (R - 1)) (mmeas tl tr L R).
Proof.
  intros tl tr L R H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded tr).
  assert (to_Z (R - 1) = (to_Z R - 1)%Z) by sia. unfold Zwf, mmeas. lia.
Qed.

(* slide the window [L, R) to [tl, tr): grow first, then shrink *)
Fixpoint move (ids : array int) (tl tr L R : int) (cnt ge : array int)
    (H : Acc (Zwf 0) (mmeas tl tr L R)) {struct H}
    : int * int * array int * array int :=
  match bdec (tl <? L) with
  | left H1 =>
      let '(c, g) := add ids (L - 1) cnt ge in
      move ids tl tr (L - 1) R c g (Acc_inv H (dec_m1 tl tr L R H1))
  | right _ =>
      match bdec (R <? tr) with
      | left H2 =>
          let '(c, g) := add ids R cnt ge in
          move ids tl tr L (R + 1) c g (Acc_inv H (dec_m2 tl tr L R H2))
      | right _ =>
          match bdec (L <? tl) with
          | left H3 =>
              let '(c, g) := rem ids L cnt ge in
              move ids tl tr (L + 1) R c g (Acc_inv H (dec_m3 tl tr L R H3))
          | right _ =>
              match bdec (tr <? R) with
              | left H4 =>
                  let '(c, g) := rem ids (R - 1) cnt ge in
                  move ids tl tr L (R - 1) c g (Acc_inv H (dec_m4 tl tr L R H4))
              | right _ => (L, R, cnt, ge)
              end
          end
      end
  end.

Definition mo_step (ids ls rs Q : array int) (k : int)
    (st : int * int * array int * array int * array bool)
    : int * int * array int * array int * array bool :=
  let '(L, R, cnt, ge, ans) := st in
  let q := Q.[k] in
  let tl := ls.[q] - 1 in
  let tr := rs.[q] in
  let '(L', R', cnt', ge') :=
    move ids tl tr L R cnt ge (Zwf_well_founded 0 (mmeas tl tr L R)) in
  (L', R', cnt', ge', ans.[q <- 0 <? ge'.[(tr - tl) / 2 + 1]]).

Definition farm (p : array float) (ls rs : array uint) : array bool :=
  let n := PArray.length p in
  let m := PArray.length ls in
  let P := msort (fun a b => (p.[a] <=? p.[b])%float) n in
  let ids := mk_ids p P n in
  let Q := msort (mo_le ls rs (blk n)) m in
  snd (loop m (fun _ _ => true) (mo_step ids ls rs Q) 0
         (0, 0, PArray.make n 0, PArray.make (n + 1) 0, PArray.make m false)).

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
(* PArray plumbing                                                     *)
(* ------------------------------------------------------------------ *)

Lemma length_bound : forall (A : Set) (t : array A), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H. rewrite Uint63.leb_spec in H. exact H.
Qed.

Lemma length_make_small : forall (A : Set) (n : int) (v : A), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros A n v H. pose proof (length_make A n v) as E.
  replace (n <=? max_length) with true in E; [exact E |].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma gss : forall (A : Set) (t : array A) (i : int) (v : A),
  (to_Z i < to_Z (PArray.length t))%Z -> t.[i <- v].[i] = v.
Proof.
  intros A t i v H. pose proof (get_set_same A t i v) as G.
  rewrite Uint63.ltb_spec in G. exact (G H).
Qed.

Lemma gso : forall (A : Set) (t : array A) (i j : int) (v : A),
  to_Z i <> to_Z j -> t.[i <- v].[j] = t.[j].
Proof.
  intros A t i j v H. pose proof (get_set_other A t i j v) as G.
  exact (G ltac:(intro E; apply H; rewrite E; reflexivity)).
Qed.

Lemma lset : forall (A : Set) (t : array A) (i : int) (v : A),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros A t i v. exact (length_set A t i v). Qed.

Lemma gmake : forall (A : Set) (m i : int) (v : A), (PArray.make m v).[i] = v.
Proof. intros A m i v. exact (get_make A v m i). Qed.

Lemma small_add : forall a b : int, (to_Z a + to_Z b < wB)%Z ->
  to_Z (a + b) = (to_Z a + to_Z b)%Z.
Proof. intros a b H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). sia. Qed.

Lemma small_sub : forall a b : int, (to_Z b <= to_Z a)%Z ->
  to_Z (a - b) = (to_Z a - to_Z b)%Z.
Proof. intros a b H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). sia. Qed.

Lemma succ_small : forall a : int, (to_Z a < 4194304)%Z -> to_Z (a + 1) = (to_Z a + 1)%Z.
Proof. intros a H. pose proof (to_Z_bounded a). sia. Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma ieq : forall a b : int, to_Z a = to_Z b -> a = b.
Proof. exact to_Z_inj. Qed.

(* ------------------------------------------------------------------ *)
(* The sort                                                            *)
(* ------------------------------------------------------------------ *)

Section Sort.
Variable le : int -> int -> bool.
Variable n : int.
Hypothesis Hn : (to_Z n <= 4194303)%Z.

(* le is a total preorder on 0 .. n-1 *)
Definition ST : Prop :=
  (forall a b, (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z -> le a b = false -> le b a = true) /\
  (forall a b c, (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z -> (to_Z c < to_Z n)%Z ->
     le a b = true -> le b c = true -> le a c = true).

Definition sorted_on (a : array int) (lo hi : Z) : Prop :=
  forall k1 k2 : int, (lo <= to_Z k1 < to_Z k2)%Z -> (to_Z k2 < hi)%Z ->
    le a.[k1] a.[k2] = true.

Section Merge.
Variables (src dst : array int) (lo mid hi : int).
Hypothesis Hsrc : PArray.length src = n.
Hypothesis Hdst : PArray.length dst = n.
Hypothesis Hlmh : (to_Z lo <= to_Z mid <= to_Z hi)%Z.
Hypothesis Hhi : (to_Z hi <= to_Z n)%Z.
Hypothesis Hrange : forall k, (to_Z k < to_Z n)%Z -> (to_Z src.[k] < to_Z n)%Z.

Definition MI (k i j : int) (d : array int) : Prop :=
  PArray.length d = n /\
  (to_Z lo <= to_Z i <= to_Z mid)%Z /\ (to_Z mid <= to_Z j <= to_Z hi)%Z /\
  (to_Z k - to_Z lo = (to_Z i - to_Z lo) + (to_Z j - to_Z mid))%Z /\
  (forall k', (to_Z k' < to_Z lo)%Z -> d.[k'] = dst.[k']) /\
  (forall k', (to_Z lo <= to_Z k' < to_Z k)%Z -> exists i',
     ((to_Z lo <= to_Z i' < to_Z i) \/ (to_Z mid <= to_Z i' < to_Z j))%Z /\ d.[k'] = src.[i']) /\
  (forall i', ((to_Z lo <= to_Z i' < to_Z i) \/ (to_Z mid <= to_Z i' < to_Z j))%Z ->
     exists k', (to_Z lo <= to_Z k' < to_Z k)%Z /\ d.[k'] = src.[i']) /\
  (ST -> sorted_on src (to_Z lo) (to_Z mid) -> sorted_on src (to_Z mid) (to_Z hi) ->
     sorted_on d (to_Z lo) (to_Z k) /\
     forall k', (to_Z lo <= to_Z k' < to_Z k)%Z ->
       (forall i', (to_Z i <= to_Z i' < to_Z mid)%Z -> le d.[k'] src.[i'] = true) /\
       (forall j', (to_Z j <= to_Z j' < to_Z hi)%Z -> le d.[k'] src.[j'] = true)).

Lemma MI_step_i : forall k i j d, (to_Z lo <= to_Z k < to_Z hi)%Z -> MI k i j d ->
  (to_Z i < to_Z mid)%Z ->
  (ST -> sorted_on src (to_Z lo) (to_Z mid) -> sorted_on src (to_Z mid) (to_Z hi) ->
     (to_Z j < to_Z hi)%Z -> le src.[i] src.[j] = true) ->
  MI (k + 1) (i + 1) j d.[k <- src.[i]].
Proof.
  intros k i j d Hk (Hl & Hi & Hj & Hc & Hb & Hf & Hm & Hs) Hlt Hp.
  assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
  assert (Ei : to_Z (i + 1) = (to_Z i + 1)%Z) by (apply succ_small; lia).
  assert (Hkd : (to_Z k < to_Z (PArray.length d))%Z) by (rewrite Hl; lia).
  unfold MI. rewrite Ek, Ei.
  split; [rewrite lset; exact Hl |].
  split; [lia |]. split; [lia |]. split; [lia |].
  split.
  { intros k' Hk'. rewrite gso by lia. apply Hb; exact Hk'. }
  split.
  { intros k' Hk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E | E].
    - apply ieq in E. subst k'. rewrite gss by exact Hkd. exists i. split; [lia | reflexivity].
    - rewrite gso by lia. destruct (Hf k' ltac:(lia)) as (i' & Hi' & Ei'). exists i'.
      split; [lia | exact Ei']. }
  split.
  { intros i' Hi'. destruct (Z.eq_dec (to_Z i') (to_Z i)) as [E | E].
    - apply ieq in E. subst i'. exists k. split; [lia |]. rewrite gss by exact Hkd. reflexivity.
    - destruct (Hm i' ltac:(lia)) as (k' & Hk' & Ek'). exists k'. split; [lia |].
      rewrite gso by lia. exact Ek'. }
  intros HST S1 S2. destruct (Hs HST S1 S2) as [Hso Hle].
  pose proof HST as [Htot Htr].
  assert (Rg : forall x, (to_Z lo <= to_Z x < to_Z hi)%Z -> (to_Z src.[x] < to_Z n)%Z)
    by (intros x Hx; apply Hrange; lia).
  split.
  - intros k1 k2 H1 H2. rewrite (gso _ _ k k1) by lia.
    destruct (Z.eq_dec (to_Z k2) (to_Z k)) as [E | E].
    + apply ieq in E. subst k2. rewrite gss by exact Hkd.
      apply (proj1 (Hle k1 ltac:(lia))). lia.
    + rewrite gso by lia. apply Hso; lia.
  - intros k' Hk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E | E].
    + apply ieq in E. subst k'. rewrite gss by exact Hkd. split.
      * intros i' Hi'. apply S1; lia.
      * intros j' Hj'. destruct (Z.eq_dec (to_Z j') (to_Z j)) as [E | E].
        -- apply ieq in E. subst j'. apply Hp; [exact HST | exact S1 | exact S2 | lia].
        -- apply (Htr _ src.[j] _); try (apply Rg; lia).
           ++ apply Hp; [exact HST | exact S1 | exact S2 | lia].
           ++ apply S2; lia.
    + rewrite gso by lia. destruct (Hle k' ltac:(lia)) as [A B]. split.
      * intros i' Hi'. apply A. lia.
      * exact B.
Qed.

Lemma MI_step_j : forall k i j d, (to_Z lo <= to_Z k < to_Z hi)%Z -> MI k i j d ->
  (to_Z j < to_Z hi)%Z ->
  (ST -> sorted_on src (to_Z lo) (to_Z mid) -> sorted_on src (to_Z mid) (to_Z hi) ->
     (to_Z i < to_Z mid)%Z -> le src.[j] src.[i] = true) ->
  MI (k + 1) i (j + 1) d.[k <- src.[j]].
Proof.
  intros k i j d Hk (Hl & Hi & Hj & Hc & Hb & Hf & Hm & Hs) Hlt Hp.
  assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
  assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by (apply succ_small; lia).
  assert (Hkd : (to_Z k < to_Z (PArray.length d))%Z) by (rewrite Hl; lia).
  unfold MI. rewrite Ek, Ej.
  split; [rewrite lset; exact Hl |].
  split; [lia |]. split; [lia |]. split; [lia |].
  split.
  { intros k' Hk'. rewrite gso by lia. apply Hb; exact Hk'. }
  split.
  { intros k' Hk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E | E].
    - apply ieq in E. subst k'. rewrite gss by exact Hkd. exists j. split; [lia | reflexivity].
    - rewrite gso by lia. destruct (Hf k' ltac:(lia)) as (i' & Hi' & Ei'). exists i'.
      split; [lia | exact Ei']. }
  split.
  { intros i' Hi'. destruct (Z.eq_dec (to_Z i') (to_Z j)) as [E | E].
    - apply ieq in E. subst i'. exists k. split; [lia |]. rewrite gss by exact Hkd. reflexivity.
    - destruct (Hm i' ltac:(lia)) as (k' & Hk' & Ek'). exists k'. split; [lia |].
      rewrite gso by lia. exact Ek'. }
  intros HST S1 S2. destruct (Hs HST S1 S2) as [Hso Hle].
  pose proof HST as [Htot Htr].
  assert (Rg : forall x, (to_Z lo <= to_Z x < to_Z hi)%Z -> (to_Z src.[x] < to_Z n)%Z)
    by (intros x Hx; apply Hrange; lia).
  split.
  - intros k1 k2 H1 H2. rewrite (gso _ _ k k1) by lia.
    destruct (Z.eq_dec (to_Z k2) (to_Z k)) as [E | E].
    + apply ieq in E. subst k2. rewrite gss by exact Hkd.
      apply (proj2 (Hle k1 ltac:(lia))). lia.
    + rewrite gso by lia. apply Hso; lia.
  - intros k' Hk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E | E].
    + apply ieq in E. subst k'. rewrite gss by exact Hkd. split.
      * intros i' Hi'. destruct (Z.eq_dec (to_Z i') (to_Z i)) as [E | E].
        -- apply ieq in E. subst i'. apply Hp; [exact HST | exact S1 | exact S2 | lia].
        -- apply (Htr _ src.[i] _); try (apply Rg; lia).
           ++ apply Hp; [exact HST | exact S1 | exact S2 | lia].
           ++ apply S1; lia.
      * intros j' Hj'. apply S2; lia.
    + rewrite gso by lia. destruct (Hle k' ltac:(lia)) as [A B]. split.
      * exact A.
      * intros j' Hj'. apply B. lia.
Qed.

Lemma merge_spec :
  let res := merge le src dst lo mid hi in
  PArray.length res = n /\
  (forall k, (to_Z k < to_Z lo)%Z -> res.[k] = dst.[k]) /\
  (forall k, (to_Z lo <= to_Z k < to_Z hi)%Z ->
     exists i, (to_Z lo <= to_Z i < to_Z hi)%Z /\ res.[k] = src.[i]) /\
  (forall i, (to_Z lo <= to_Z i < to_Z hi)%Z ->
     exists k, (to_Z lo <= to_Z k < to_Z hi)%Z /\ res.[k] = src.[i]) /\
  (ST -> sorted_on src (to_Z lo) (to_Z mid) -> sorted_on src (to_Z mid) (to_Z hi) ->
     sorted_on res (to_Z lo) (to_Z hi)).
Proof.
  unfold merge.
  pose proof (for_inv (fun k st => MI k (fst (fst st)) (snd (fst st)) (snd st))
    hi lo (merge_step le src mid hi) (lo, mid, dst) ltac:(lia)) as H.
  cbv beta in H.
  destruct H as (Hl & Hi & Hj & Hc & Hb & Hf & Hm & Hs).
  - simpl. split; [exact Hdst |]. split; [lia |]. split; [lia |]. split; [lia |].
    split; [intros; reflexivity |].
    split; [intros k' Hk'; lia |].
    split; [intros i' Hi'; lia |].
    intros _ _ _. split; [intros k1 k2 H1 H2; lia | intros k' Hk'; lia].
  - intros k [[i j] d] Hk HI. simpl in HI |- *. unfold merge_step.
    pose proof HI as (Hl & Hi & Hj & Hc & _).
    destruct (i <? mid) eqn:E1.
    + rewrite Uint63.ltb_spec in E1. destruct (j <? hi) eqn:E2.
      * rewrite Uint63.ltb_spec in E2. destruct (le src.[i] src.[j]) eqn:E3.
        -- apply MI_step_i; auto.
        -- apply MI_step_j; auto. intros [Htot _] _ _ _. simpl.
           apply Htot; [apply Hrange; lia | apply Hrange; lia | exact E3].
      * rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E2.
        apply MI_step_i; auto; intros; lia.
    + rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E1.
      apply MI_step_j; auto; try lia; intros; lia.
  - simpl. split; [exact Hl |]. split; [exact Hb |].
    assert (Ei : to_Z (fst (fst (loop hi (fun _ _ => true) (merge_step le src mid hi) lo (lo, mid, dst)))) = to_Z mid) by lia.
    assert (Ej : to_Z (snd (fst (loop hi (fun _ _ => true) (merge_step le src mid hi) lo (lo, mid, dst)))) = to_Z hi) by lia.
    rewrite Ei, Ej in *.
    split; [intros k Hk; destruct (Hf k Hk) as (i' & H1 & H2); exists i'; split; [lia | exact H2] |].
    split; [intros i' Hi'; apply Hm; lia |].
    intros HST S1 S2. exact (proj1 (Hs HST S1 S2)).
Qed.

End Merge.

Lemma div_in : forall w q k, (0 < w -> w * q <= k < w * q + w -> k / w = q)%Z.
Proof.
  intros w q k Hw Hk. symmetry. apply (Z.div_unique k w q (k - w * q)); lia.
Qed.

Lemma div_below : forall w q k, (0 < w -> 0 <= k < w * q -> k / w < q)%Z.
Proof. intros w q k Hw Hk. apply Z.div_lt_upper_bound; lia. Qed.

Lemma nseg_lt : forall N W s, (0 < W -> 0 <= s -> s < (N + W - 1) / W -> s * W < N)%Z.
Proof.
  intros N W s HW Hs Hlt. pose proof (Z.mul_div_le (N + W - 1) W HW). nia.
Qed.

Lemma nseg_ge : forall N W, (0 < W -> N <= ((N + W - 1) / W) * W)%Z.
Proof.
  intros N W HW. pose proof (Z.div_mod (N + W - 1) W ltac:(lia)).
  pose proof (Z.mod_pos_bound (N + W - 1) W HW). nia.
Qed.

Definition runs (a : array int) (w : Z) : Prop :=
  forall k1 k2 : int, (to_Z k1 < to_Z k2 < to_Z n)%Z -> (to_Z k1 / w = to_Z k2 / w)%Z ->
    le a.[k1] a.[k2] = true.

Lemma seg_mid_spec : forall w lo : int, (to_Z lo + to_Z w < wB)%Z ->
  to_Z (seg_mid n w lo) = Z.min (to_Z lo + to_Z w) (to_Z n).
Proof.
  intros w lo H. unfold seg_mid. rewrite <- (small_add lo w H).
  destruct (lo + w <? n) eqn:E;
    [rewrite Uint63.ltb_spec in E | rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E];
    lia.
Qed.

Section Pass.
Variables (w : int) (src : array int).
Hypothesis Hw : (1 <= to_Z w)%Z.
Hypothesis Hwn : (to_Z w < to_Z n)%Z.
Hypothesis Hsrc : PArray.length src = n.
Hypothesis Hrange : forall k, (to_Z k < to_Z n)%Z -> (to_Z src.[k] < to_Z n)%Z.

Definition PI (s : int) (d : array int) : Prop :=
  let lo := Z.min (to_Z s * (2 * to_Z w)) (to_Z n) in
  PArray.length d = n /\
  (forall k, (to_Z k < lo)%Z -> exists i, (to_Z i < to_Z n)%Z /\ d.[k] = src.[i]) /\
  (forall i, (to_Z i < lo)%Z -> exists k, (to_Z k < lo)%Z /\ d.[k] = src.[i]) /\
  (ST -> runs src (to_Z w) -> forall k1 k2 : int, (to_Z k1 < to_Z k2 < lo)%Z ->
     (to_Z k1 / (2 * to_Z w) = to_Z k2 / (2 * to_Z w))%Z -> le d.[k1] d.[k2] = true).

Lemma pass_spec : forall dst, PArray.length dst = n ->
  let res := pass le n w src dst in
  PArray.length res = n /\
  (forall k, (to_Z k < to_Z n)%Z -> exists i, (to_Z i < to_Z n)%Z /\ res.[k] = src.[i]) /\
  (forall i, (to_Z i < to_Z n)%Z -> exists k, (to_Z k < to_Z n)%Z /\ res.[k] = src.[i]) /\
  (ST -> runs src (to_Z w) -> runs res (2 * to_Z w)).
Proof.
  intros dst Hdst. unfold pass.
  assert (Ew2 : to_Z (w + w) = (2 * to_Z w)%Z) by (rewrite small_add; lia).
  assert (Enum : to_Z (n + (w + w) - 1) = (to_Z n + 2 * to_Z w - 1)%Z).
  { rewrite small_sub; rewrite small_add; rewrite ?Ew2; lia. }
  set (W := (2 * to_Z w)%Z) in *.
  assert (Ens : to_Z ((n + (w + w) - 1) / (w + w)) = ((to_Z n + W - 1) / W)%Z).
  { rewrite Uint63.div_spec, Enum, Ew2. reflexivity. }
  pose proof (Z.div_pos (to_Z n + W - 1) W ltac:(lia) ltac:(lia)) as Hnsp.
  pose proof (for_inv PI ((n + (w + w) - 1) / (w + w)) 0
    (fun s d => merge le src d (s * (w + w)) (seg_mid n w (s * (w + w)))
                  (seg_mid n (w + w) (s * (w + w)))) dst ltac:(rewrite Ens; change (to_Z 0) with 0%Z; lia))
    as H.
  destruct H as (Hl & Hf & Hm & Hs).
  - unfold PI. change (to_Z 0) with 0%Z. rewrite Z.mul_0_l.
    replace (Z.min 0 (to_Z n)) with 0%Z by (pose proof (to_Z_bounded n); lia).
    split; [exact Hdst |].
    split; [intros k Hk; pose proof (to_Z_bounded k); lia |].
    split; [intros k Hk; pose proof (to_Z_bounded k); lia |].
    intros _ _ k1 k2 Hk. pose proof (to_Z_bounded k1); lia.
  - intros s d Hsr (Hl & Hf & Hm & Hs). change (to_Z 0) with 0%Z in Hsr. rewrite Ens in Hsr.
    pose proof (nseg_lt (to_Z n) W (to_Z s) ltac:(lia) ltac:(lia) ltac:(lia)) as Hlo.
    assert (Elo : to_Z (s * (w + w)) = (to_Z s * W)%Z).
    { rewrite Uint63.mul_spec, Ew2. apply Z.mod_small. pose proof (to_Z_bounded s). rewrite wB_val. lia. }
    set (lo := s * (w + w)) in *.
    assert (Emid : to_Z (seg_mid n w lo) = Z.min (to_Z lo + to_Z w) (to_Z n))
      by (apply seg_mid_spec; rewrite wB_val; lia).
    assert (Ehi : to_Z (seg_mid n (w + w) lo) = Z.min (to_Z lo + W) (to_Z n))
      by (rewrite seg_mid_spec; rewrite ?Ew2; [reflexivity | rewrite wB_val; lia]).
    set (mid := seg_mid n w lo) in *. set (hi := seg_mid n (w + w) lo) in *.
    assert (Hsn : (to_Z s < to_Z n)%Z).
    { pose proof (to_Z_bounded s).
      pose proof (Z.mul_le_mono_nonneg_l 1 W (to_Z s) ltac:(lia) ltac:(lia)). lia. }
    assert (Es1 : to_Z (s + 1) = (to_Z s + 1)%Z) by (apply succ_small; lia).
    unfold PI in *. change (2 * to_Z w)%Z with W in Hf, Hm, Hs |- *. rewrite Es1.
    replace (Z.min ((to_Z s + 1) * W) (to_Z n)) with (to_Z hi)
      by (rewrite Ehi, Elo; f_equal; ring).
    replace (Z.min (to_Z s * W) (to_Z n)) with (to_Z lo) in *
      by (rewrite Elo; symmetry; apply Z.min_l; lia).
    clear Hsr Ens Enum Hnsp.
    destruct (merge_spec src d lo mid hi Hsrc Hl ltac:(lia) ltac:(lia) Hrange)
      as (Rl & Rb & Rf & Rm & Rs).
    split; [exact Rl |].
    split.
    { intros k Hk. destruct (Z.lt_ge_cases (to_Z k) (to_Z lo)) as [C | C].
      - rewrite Rb by exact C. apply Hf; exact C.
      - destruct (Rf k ltac:(lia)) as (i & Hi & Ei). exists i. split; [lia | exact Ei]. }
    split.
    { intros i Hi. destruct (Z.lt_ge_cases (to_Z i) (to_Z lo)) as [C | C].
      - destruct (Hm i C) as (k & Hk & Ek). exists k. split; [lia |].
        rewrite Rb by exact Hk. exact Ek.
      - destruct (Rm i ltac:(lia)) as (k & Hk & Ek). exists k. split; [lia | exact Ek]. }
    intros HST Hrw k1 k2 Hk Hdiv. clear Hf Hm Rf Rm Rl.
    assert (EloW : to_Z lo = (to_Z w * (2 * to_Z s))%Z) by (rewrite Elo; unfold W; ring).
    assert (EloW1 : (to_Z lo + to_Z w = to_Z w * (2 * to_Z s + 1))%Z) by (rewrite EloW; ring).
    assert (M1 : (to_Z mid <= to_Z lo + to_Z w)%Z) by (rewrite Emid; apply Z.le_min_l).
    assert (M5 : (to_Z mid <= to_Z n)%Z) by (rewrite Emid; apply Z.le_min_r).
    assert (M2 : (to_Z hi <= to_Z lo + W)%Z) by (rewrite Ehi; apply Z.le_min_l).
    assert (M3 : (to_Z hi <= to_Z n)%Z) by (rewrite Ehi; apply Z.le_min_r).
    assert (M4 : (to_Z mid = to_Z lo + to_Z w \/ to_Z mid = to_Z n)%Z)
      by (rewrite Emid; clear; lia).
    assert (EW : W = (2 * to_Z w)%Z) by reflexivity.
    clearbody W lo mid hi.
    assert (S1 : sorted_on src (to_Z lo) (to_Z mid)).
    { intros a b Hab Hb. apply Hrw; [clear - Hab Hb M5; lia |].
      rewrite (div_in (to_Z w) (2 * to_Z s) (to_Z a)) by (clear - Hw Hab Hb M1 EloW; lia).
      rewrite (div_in (to_Z w) (2 * to_Z s) (to_Z b)) by (clear - Hw Hab Hb M1 EloW; lia).
      reflexivity. }
    assert (S2 : sorted_on src (to_Z mid) (to_Z hi)).
    { intros a b Hab Hb. apply Hrw; [clear - Hab Hb M3; lia |].
      assert (Ha : (to_Z lo + to_Z w <= to_Z a)%Z) by (clear - Hab Hb M3 M4; lia).
      rewrite (div_in (to_Z w) (2 * to_Z s + 1) (to_Z a))
        by (clear - Hw Hab Hb Ha M2 EloW1 EW; lia).
      rewrite (div_in (to_Z w) (2 * to_Z s + 1) (to_Z b))
        by (clear - Hw Hab Hb Ha M2 EloW1 EW; lia).
      reflexivity. }
    pose proof (Rs HST S1 S2) as Rso.
    destruct (Z.lt_ge_cases (to_Z k2) (to_Z lo)) as [C2 | C2].
    + rewrite (Rb k1) by (clear - Hk C2; lia). rewrite (Rb k2) by exact C2.
      apply (Hs HST Hrw); [clear - Hk C2; lia | exact Hdiv].
    + destruct (Z.lt_ge_cases (to_Z k1) (to_Z lo)) as [C1 | C1].
      * exfalso. pose proof (to_Z_bounded k1) as Hb1.
        assert (EloS : to_Z lo = (W * to_Z s)%Z) by (rewrite Elo; ring).
        pose proof (div_below W (to_Z s) (to_Z k1) ltac:(lia) ltac:(clear - C1 EloS Hb1; lia)).
        rewrite (div_in W (to_Z s) (to_Z k2)) in Hdiv by (clear - Hk C2 M2 EloS EW Hw; lia).
        lia.
      * apply Rso; clear - Hk C1 M3; lia.
  - change (to_Z 0) with 0%Z in *. rewrite Ens in *.
    pose proof (nseg_ge (to_Z n) W ltac:(lia)) as Hge.
    assert (Emn : Z.min ((to_Z n + W - 1) / W * (2 * to_Z w)) (to_Z n) = to_Z n)
      by (change (2 * to_Z w)%Z with W; lia).
    rewrite Emn in Hf, Hm, Hs.
    split; [exact Hl |]. split; [exact Hf |]. split.
    + intros i Hi. exact (Hm i Hi).
    + intros HST Hrw k1 k2 Hk Hdiv. apply (Hs HST Hrw); [lia | exact Hdiv].
Qed.

End Pass.

Lemma iota_spec : PArray.length (iota n) = n /\
  forall i, (to_Z i < to_Z n)%Z -> (iota n).[i] = i.
Proof.
  unfold iota.
  apply (for_inv (fun j a => PArray.length a = n /\
                    forall i, (to_Z i < to_Z j)%Z -> a.[i] = i) n 0).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - split; [apply length_make_small; exact Hn |].
    intros i Hi. change (to_Z 0) with 0%Z in Hi. pose proof (to_Z_bounded i). lia.
  - intros j a Hj [Hl Ha]. split; [rewrite lset; exact Hl |].
    rewrite succ_small by lia. intros i Hi.
    destruct (Z.eq_dec (to_Z i) (to_Z j)) as [E | E].
    + apply ieq in E. subst i. apply gss. rewrite Hl. lia.
    + rewrite gso by lia. apply Ha. lia.
Qed.

Definition WI (j : int) (st : int * array int * array int) : Prop :=
  let '(w, src, dst) := st in
  to_Z w = (2 ^ to_Z j)%Z /\ PArray.length src = n /\ PArray.length dst = n /\
  (forall k, (to_Z k < to_Z n)%Z -> (to_Z src.[k] < to_Z n)%Z) /\
  (forall x, (to_Z x < to_Z n)%Z -> exists k, (to_Z k < to_Z n)%Z /\ src.[k] = x) /\
  (ST -> runs src (to_Z w)).

Lemma msort_spec :
  PArray.length (msort le n) = n /\
  (forall k, (to_Z k < to_Z n)%Z -> (to_Z (msort le n).[k] < to_Z n)%Z) /\
  (forall x, (to_Z x < to_Z n)%Z -> exists k, (to_Z k < to_Z n)%Z /\ (msort le n).[k] = x) /\
  (ST -> sorted_on (msort le n) 0 (to_Z n)).
Proof.
  unfold msort.
  destruct iota_spec as [Il Ii].
  destruct (loop_inv WI 23 0 (fun _ st => fst (fst st) <? n)
     (fun _ st => let '(w, src, dst) := st in (w + w, pass le n w src dst, src))
     (1, iota n, PArray.make n 0)) as (j & Hj & HI & Hend).
  - change (to_Z 0) with 0%Z. change (to_Z 23) with 23%Z. lia.
  - simpl. split; [reflexivity |]. split; [exact Il |].
    split; [apply length_make_small; exact Hn |].
    split; [intros k Hk; rewrite Ii by exact Hk; exact Hk |].
    split; [intros x Hx; exists x; split; [exact Hx | apply Ii; exact Hx] |].
    intros _ k1 k2 Hk Hd. rewrite !Z.div_1_r in Hd. lia.
  - intros i [[w src] dst] Hi (Ew & Hsl & Hdl & Hr & Hm & Hs) Hc.
    simpl in Hc. rewrite Uint63.ltb_spec in Hc.
    change (to_Z 0) with 0%Z in Hi. change (to_Z 23) with 23%Z in Hi.
    assert (Hw1 : (1 <= to_Z w)%Z).
    { rewrite Ew. pose proof (Z.pow_pos_nonneg 2 (to_Z i) ltac:(lia) ltac:(lia)). lia. }
    destruct (pass_spec w src Hw1 Hc Hsl Hr dst Hdl) as (Pl & Pf & Pm & Ps).
    simpl. split.
    { rewrite small_add by (rewrite wB_val; lia). rewrite succ_small by lia.
      rewrite Z.pow_add_r by lia. rewrite <- Ew. lia. }
    split; [exact Pl |]. split; [exact Hsl |].
    split.
    { intros k Hk. destruct (Pf k Hk) as (i' & Hi' & E). rewrite E. apply Hr; exact Hi'. }
    split.
    { intros x Hx. destruct (Hm x Hx) as (k & Hk & Ek). destruct (Pm k Hk) as (k' & Hk' & Ek').
      exists k'. split; [exact Hk' | rewrite Ek'; exact Ek]. }
    intros HST. rewrite small_add by (rewrite wB_val; lia).
    replace (to_Z w + to_Z w)%Z with (2 * to_Z w)%Z by ring.
    apply Ps; [exact HST | apply Hs; exact HST].
  - destruct (loop 23 (fun _ st => fst (fst st) <? n)
       (fun _ st => let '(w, src, dst) := st in (w + w, pass le n w src dst, src))
       0 (1, iota n, PArray.make n 0)) as [[w src] dst] eqn:Eq.
    simpl in HI |- *. destruct HI as (Ew & Hsl & Hdl & Hr & Hm & Hs).
    assert (Hwn : (to_Z n <= to_Z w)%Z).
    { destruct Hend as [E | [_ E]].
      - change (to_Z 23) with 23%Z in E. rewrite Ew, E. lia.
      - simpl in E. rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E. lia. }
    split; [exact Hsl |]. split; [exact Hr |]. split; [exact Hm |].
    intros HST k1 k2 Hk Hk2. apply (Hs HST); [lia |].
    pose proof (to_Z_bounded k1). rewrite !Z.div_small by lia. reflexivity.
Qed.

End Sort.

(* ------------------------------------------------------------------ *)
(* The ids                                                             *)
(* ------------------------------------------------------------------ *)

Lemma bs_eq : forall p P v lo hi H, bs p P v lo hi H =
  match bdec (lo <? hi) with
  | left Hlt =>
      if (p.[P.[lo + (hi - lo) / 2]] <? v)%float
      then bs p P v (lo + (hi - lo) / 2 + 1) hi (Acc_inv H (dec_bs_r lo hi Hlt))
      else bs p P v lo (lo + (hi - lo) / 2) (Acc_inv H (dec_bs_l lo hi Hlt))
  | right _ => lo
  end.
Proof. intros. destruct H; reflexivity. Qed.

Section Ids.
Variable ph : list R.
Variable p : array float.
Hypothesis Hp : repr p ph.

Let n := PArray.length p.

Definition X (a : int) : R := nth (Z.to_nat (to_Z a)) ph 0%R.

Lemma len_ph : Z.of_nat (List.length ph) = to_Z n.
Proof. exact (proj1 Hp). Qed.

Lemma n_small : (to_Z n <= 4194303)%Z.
Proof. apply length_bound. Qed.

Lemma repr_X : forall a, (to_Z a < to_Z n)%Z -> repr p.[a] (X a).
Proof.
  intros a Ha. destruct Hp as [_ H]. pose proof (to_Z_bounded a).
  destruct (H (Z.to_nat (to_Z a)) ltac:(pose proof len_ph; lia)) as (m & E & R).
  unfold X. rewrite (nth_error_nth _ _ _ E).
  rewrite Z2Nat.id in R by lia. rewrite of_to_Z in R. exact R.
Qed.

Definition flt (a b : int) : bool := (p.[a] <=? p.[b])%float.

Lemma flt_iff : forall a b, (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z ->
  (flt a b = true <-> (X a <= X b)%R).
Proof. intros a b Ha Hb. apply repr_leb_iff; apply repr_X; assumption. Qed.

Lemma flt_ST : ST flt n.
Proof.
  split.
  - intros a b Ha Hb E. apply flt_iff; auto.
    assert (~ (X a <= X b)%R) by (rewrite <- flt_iff by auto; congruence). lra.
  - intros a b c Ha Hb Hc E1 E2. apply flt_iff; auto.
    apply flt_iff in E1; auto. apply flt_iff in E2; auto. lra.
Qed.

Let P := msort flt n.

Lemma P_spec : PArray.length P = n /\
  (forall k, (to_Z k < to_Z n)%Z -> (to_Z P.[k] < to_Z n)%Z) /\
  (forall x, (to_Z x < to_Z n)%Z -> exists k, (to_Z k < to_Z n)%Z /\ P.[k] = x) /\
  (forall k1 k2, (0 <= to_Z k1 < to_Z k2)%Z -> (to_Z k2 < to_Z n)%Z -> (X P.[k1] <= X P.[k2])%R).
Proof.
  destruct (msort_spec flt n n_small) as (A & B & C & D).
  split; [exact A |]. split; [exact B |]. split; [exact C |].
  intros k1 k2 H1 H2. apply flt_iff; [apply B; lia | apply B; lia |].
  apply (D flt_ST); lia.
Qed.

(* r is the lower bound of rv in the sorted acres *)
Definition LB (rv : R) (r : int) : Prop :=
  (to_Z r <= to_Z n)%Z /\
  (forall k, (to_Z k < to_Z r)%Z -> (X P.[k] < rv)%R) /\
  (forall k, (to_Z r <= to_Z k < to_Z n)%Z -> (rv <= X P.[k])%R).

Lemma LB_unique : forall rv r1 r2, LB rv r1 -> LB rv r2 -> r1 = r2.
Proof.
  intros rv r1 r2 (A1 & B1 & C1) (A2 & B2 & C2). apply ieq.
  destruct (Z.lt_total (to_Z r1) (to_Z r2)) as [L | [E | L]]; [| exact E |].
  - pose proof (B2 r1 L). pose proof (C1 r1 ltac:(lia)). lra.
  - pose proof (B1 r2 L). pose proof (C2 r2 ltac:(lia)). lra.
Qed.

Lemma bs_spec : forall (v : float) rv, repr v rv ->
  forall z lo hi H, gap hi lo = z -> (to_Z lo <= to_Z hi <= to_Z n)%Z ->
  (forall k, (to_Z k < to_Z lo)%Z -> (X P.[k] < rv)%R) ->
  (forall k, (to_Z hi <= to_Z k < to_Z n)%Z -> (rv <= X P.[k])%R) ->
  LB rv (bs p P v lo hi H).
Proof.
  intros v rv Hv z. destruct P_spec as (Pl & Pr & _ & Ps).
  induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros lo hi H Ez Hlh Hlo Hhi. rewrite bs_eq.
  destruct (bdec (lo <? hi)) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
    pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
    assert (Em : to_Z (lo + (hi - lo) / 2) = (to_Z lo + (to_Z hi - to_Z lo) / 2)%Z) by sia.
    set (mid := lo + (hi - lo) / 2) in *.
    assert (Hm : (to_Z lo <= to_Z mid < to_Z hi)%Z) by (rewrite Em; sia).
    assert (RXm : repr p.[P.[mid]] (X P.[mid])) by (apply repr_X, Pr; lia).
    destruct (p.[P.[mid]] <? v)%float eqn:C.
    + apply (repr_ltb_iff _ _ _ _ RXm Hv) in C.
      assert (Em1 : to_Z (mid + 1) = (to_Z mid + 1)%Z) by (apply succ_small; pose proof n_small; lia).
      apply (IH (gap hi (mid + 1))); [rewrite <- Ez; apply dec_bs_r; exact Hlt | reflexivity | lia | | exact Hhi].
      intros k Hk. rewrite Em1 in Hk. pose proof (to_Z_bounded k).
      destruct (Z.eq_dec (to_Z k) (to_Z mid)) as [E | E].
      * apply ieq in E. subst k. exact C.
      * pose proof (Ps k mid ltac:(lia) ltac:(lia)). lra.
    + assert (C' : ~ (X P.[mid] < rv)%R) by (rewrite <- (repr_ltb_iff _ _ _ _ RXm Hv); congruence).
      apply (IH (gap mid lo)); [rewrite <- Ez; apply dec_bs_l; exact Hlt | reflexivity | lia | exact Hlo |].
      intros k Hk.
      destruct (Z.eq_dec (to_Z k) (to_Z mid)) as [E | E].
      * apply ieq in E. subst k. lra.
      * pose proof (Ps mid k ltac:(lia) ltac:(lia)). lra.
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hge.
    split; [lia |]. split; [exact Hlo |].
    intros k Hk. apply Hhi. lia.
Qed.

Lemma lbound_spec : forall a, (to_Z a < to_Z n)%Z -> LB (X a) (lbound p P n p.[a]).
Proof.
  intros a Ha. unfold lbound. apply (bs_spec _ _ (repr_X a Ha) _ 0 n _ eq_refl).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - intros k Hk. change (to_Z 0) with 0%Z in Hk. pose proof (to_Z_bounded k). lia.
  - intros k Hk. lia.
Qed.

Let ids := mk_ids p P n.

Lemma ids_LB : PArray.length ids = n /\ forall a, (to_Z a < to_Z n)%Z -> LB (X a) ids.[a].
Proof.
  unfold ids, mk_ids.
  apply (for_inv (fun j t => PArray.length t = n /\
                    forall a, (to_Z a < to_Z j)%Z -> LB (X a) t.[a]) n 0).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - split; [apply length_make_small; exact n_small |].
    intros a Ha. change (to_Z 0) with 0%Z in Ha. pose proof (to_Z_bounded a). lia.
  - intros j t Hj [Hl Ht]. split; [rewrite lset; exact Hl |].
    rewrite succ_small by (pose proof n_small; lia). intros a Ha.
    destruct (Z.eq_dec (to_Z a) (to_Z j)) as [E | E].
    + apply ieq in E. subst a. rewrite gss by (rewrite Hl; lia). apply lbound_spec. lia.
    + rewrite gso by lia. apply Ht. lia.
Qed.

Lemma ids_len : PArray.length ids = n.
Proof. exact (proj1 ids_LB). Qed.

Lemma ids_lt : forall a, (to_Z a < to_Z n)%Z -> (to_Z ids.[a] < to_Z n)%Z.
Proof.
  intros a Ha. destruct (proj2 ids_LB a Ha) as (A & B & C).
  destruct P_spec as (_ & _ & Pm & _). destruct (Pm a Ha) as (k & Hk & Ek).
  destruct (Z.lt_ge_cases (to_Z k) (to_Z ids.[a])) as [L | L]; [| lia].
  pose proof (B k L) as F. rewrite Ek in F. lra.
Qed.

Lemma ids_eq : forall a b, (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z ->
  (ids.[a] = ids.[b] <-> X a = X b).
Proof.
  intros a b Ha Hb. pose proof (proj2 ids_LB a Ha) as La. pose proof (proj2 ids_LB b Hb) as Lb.
  split.
  - intros E. destruct P_spec as (_ & _ & Pm & _).
    destruct (Pm a Ha) as (ka & Hka & Eka). destruct (Pm b Hb) as (kb & Hkb & Ekb).
    destruct La as (A1 & B1 & C1). destruct Lb as (A2 & B2 & C2).
    destruct (Rtotal_order (X a) (X b)) as [L | [L | L]]; [exfalso | exact L | exfalso].
    + (* ids a <= ka < ids b *)
      assert (H1 : (to_Z ids.[a] <= to_Z ka)%Z).
      { destruct (Z.lt_ge_cases (to_Z ka) (to_Z ids.[a])) as [C | C]; [| exact C].
        pose proof (B1 ka C) as F. rewrite Eka in F. lra. }
      assert (H2 : (to_Z ka < to_Z ids.[b])%Z).
      { destruct (Z.lt_ge_cases (to_Z ka) (to_Z ids.[b])) as [C | C]; [exact C |].
        pose proof (C2 ka ltac:(lia)) as F. rewrite Eka in F. lra. }
      rewrite E in H1. lia.
    + assert (H1 : (to_Z ids.[b] <= to_Z kb)%Z).
      { destruct (Z.lt_ge_cases (to_Z kb) (to_Z ids.[b])) as [C | C]; [| exact C].
        pose proof (B2 kb C) as F. rewrite Ekb in F. lra. }
      assert (H2 : (to_Z kb < to_Z ids.[a])%Z).
      { destruct (Z.lt_ge_cases (to_Z kb) (to_Z ids.[a])) as [C | C]; [exact C |].
        pose proof (C1 kb ltac:(lia)) as F. rewrite Ekb in F. lra. }
      rewrite E in H2. lia.
  - intros E. rewrite E in La. exact (LB_unique _ _ _ La Lb).
Qed.

End Ids.

(* ------------------------------------------------------------------ *)
(* Counting                                                            *)
(* ------------------------------------------------------------------ *)

Definition b2z (b : bool) : Z := if b then 1%Z else 0%Z.

(* #{q < k | f q} *)
Fixpoint cz (f : Z -> bool) (k : nat) : Z :=
  match k with
  | O => 0%Z
  | S k' => (cz f k' + b2z (f (Z.of_nat k')))%Z
  end.

Lemma b2z_bound : forall b, (0 <= b2z b <= 1)%Z.
Proof. intros []; simpl; lia. Qed.

Lemma cz_diff : forall f k1 k2, (k1 <= k2)%nat ->
  (0 <= cz f k2 - cz f k1 <= Z.of_nat k2 - Z.of_nat k1)%Z.
Proof.
  intros f k1 k2 Hk. induction k2 as [| k2 IH].
  - assert (k1 = 0%nat) by lia. subst. simpl. lia.
  - destruct (Nat.eq_dec k1 (S k2)) as [E | E]; [subst; lia |].
    cbn [cz]. rewrite Nat2Z.inj_succ.
    pose proof (b2z_bound (f (Z.of_nat k2))). specialize (IH ltac:(lia)). lia.
Qed.

Lemma cz_nonneg : forall f k, (0 <= cz f k)%Z.
Proof. intros f k. pose proof (cz_diff f 0 k ltac:(lia)). simpl in H. lia. Qed.

Lemma cz_ext : forall f g k, (forall q, (0 <= q < Z.of_nat k)%Z -> f q = g q) ->
  cz f k = cz g k.
Proof.
  intros f g k. induction k as [| k IH]; intros H; simpl; [reflexivity |].
  rewrite IH by (intros q Hq; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma cz_upd : forall f g k z0, (0 <= z0 < Z.of_nat k)%Z ->
  (forall q, (0 <= q < Z.of_nat k)%Z -> q <> z0 -> f q = g q) ->
  cz g k = (cz f k - b2z (f z0) + b2z (g z0))%Z.
Proof.
  intros f g k z0. induction k as [| k IH]; intros Hz H; [simpl in Hz; lia |].
  simpl. destruct (Z.eq_dec z0 (Z.of_nat k)) as [E | E].
  - subst z0. rewrite (cz_ext f g k) by (intros q Hq; apply H; lia). lia.
  - rewrite IH by (try lia; intros q Hq Hq'; apply H; lia).
    rewrite (H (Z.of_nat k)) by lia. lia.
Qed.

Lemma cz_pos : forall f k1 k2, (k1 <= k2)%nat -> (0 < cz f k2 - cz f k1)%Z ->
  exists q, (Z.of_nat k1 <= q < Z.of_nat k2)%Z /\ f q = true.
Proof.
  intros f k1 k2 Hk. induction k2 as [| k2 IH]; intros Hp.
  - assert (k1 = 0%nat) by lia. subst. simpl in Hp. lia.
  - destruct (Nat.eq_dec k1 (S k2)) as [E | E]; [subst; lia |].
    simpl in Hp. destruct (f (Z.of_nat k2)) eqn:Ef.
    + exists (Z.of_nat k2). split; [lia | exact Ef].
    + simpl in Hp. destruct (IH ltac:(lia) ltac:(lia)) as (q & Hq & Eq).
      exists q. split; [lia | exact Eq].
Qed.

Lemma cz_one : forall f k1 k2 q, (Z.of_nat k1 <= q < Z.of_nat k2)%Z -> f q = true ->
  (1 <= cz f k2 - cz f k1)%Z.
Proof.
  intros f k1 k2 q Hq Ef.
  assert (E : cz f k2 = (cz (fun x => if Z.eq_dec x q then false else f x) k2 + 1)%Z).
  { rewrite (cz_upd (fun x => if Z.eq_dec x q then false else f x) f k2 q) by
      (try lia; intros x Hx Hx'; destruct (Z.eq_dec x q); congruence).
    rewrite Ef. destruct (Z.eq_dec q q); [simpl; lia | congruence]. }
  assert (E1 : cz f k1 = cz (fun x => if Z.eq_dec x q then false else f x) k1).
  { apply cz_ext. intros x Hx. destruct (Z.eq_dec x q); [lia | reflexivity]. }
  pose proof (cz_diff (fun x => if Z.eq_dec x q then false else f x) k1 k2 ltac:(lia)).
  lia.
Qed.

Lemma cz_step : forall f z, (0 <= z)%Z ->
  cz f (Z.to_nat (z + 1)) = (cz f (Z.to_nat z) + b2z (f z))%Z.
Proof.
  intros f z Hz. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The window                                                          *)
(* ------------------------------------------------------------------ *)

Section Window.
Variables (ids : array int) (n : int).
Hypothesis Hn : (to_Z n <= 4194303)%Z.
Hypothesis Hidl : PArray.length ids = n.
Hypothesis Hidr : forall a, (to_Z a < to_Z n)%Z -> (to_Z ids.[a] < to_Z n)%Z.

Definition fid (v : Z) : Z -> bool := fun q => Z.eqb (to_Z ids.[of_Z q]) v.

Definition wc (v L R : Z) : Z := (cz (fid v) (Z.to_nat R) - cz (fid v) (Z.to_nat L))%Z.

Definition G (cnt : array int) (c : Z) : Z :=
  cz (fun v => Z.leb c (to_Z cnt.[of_Z v])) (Z.to_nat (to_Z n)).

Definition CI (L R : int) (cnt ge : array int) : Prop :=
  (to_Z L <= to_Z R <= to_Z n)%Z /\
  PArray.length cnt = n /\ PArray.length ge = n + 1 /\
  (forall v : int, (to_Z v < to_Z n)%Z -> to_Z cnt.[v] = wc (to_Z v) (to_Z L) (to_Z R)) /\
  (forall c : int, (1 <= to_Z c <= to_Z n)%Z -> to_Z ge.[c] = G cnt (to_Z c)).

Lemma wc_bound : forall v L R, (0 <= L <= R)%Z -> (0 <= wc v L R <= R - L)%Z.
Proof.
  intros v L R H. unfold wc. pose proof (cz_diff (fid v) (Z.to_nat L) (Z.to_nat R) ltac:(lia)). lia.
Qed.

Lemma G_bound : forall cnt c, (0 <= G cnt c <= to_Z n)%Z.
Proof.
  intros cnt c. unfold G. pose proof (cz_diff (fun v => Z.leb c (to_Z cnt.[of_Z v])) 0 (Z.to_nat (to_Z n)) ltac:(lia)).
  simpl in H. pose proof (to_Z_bounded n). lia.
Qed.

Lemma of_Z_to_Z_small : forall q, (0 <= q < to_Z n)%Z -> to_Z (of_Z q) = q.
Proof. intros q Hq. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. Qed.

Lemma ge1 : to_Z (n + 1) = (to_Z n + 1)%Z.
Proof. apply succ_small. lia. Qed.

(* the update of cnt at v0 changes G by the change of one indicator *)
Lemma G_upd : forall (cnt : array int) (v0 : int) (y : int) (c : Z),
  PArray.length cnt = n -> (to_Z v0 < to_Z n)%Z ->
  G (cnt.[v0 <- y]) c = (G cnt c - b2z (Z.leb c (to_Z cnt.[v0])) + b2z (Z.leb c (to_Z y)))%Z.
Proof.
  intros cnt v0 y c Hl Hv. unfold G. pose proof (to_Z_bounded v0).
  rewrite (cz_upd (fun v => Z.leb c (to_Z cnt.[of_Z v])) _ _ (to_Z v0)) by
    (first [lia | intros q Hq Hq'; rewrite gso; [reflexivity | rewrite of_Z_to_Z_small by lia; lia]]).
  rewrite of_to_Z. rewrite gss by (rewrite Hl; lia). reflexivity.
Qed.

Lemma add_ok : forall L R L' R' pos cnt ge, CI L R cnt ge ->
  (to_Z L' <= to_Z R' <= to_Z n)%Z -> (to_Z pos < to_Z n)%Z ->
  (forall v, wc v (to_Z L') (to_Z R') = (wc v (to_Z L) (to_Z R) + b2z (Z.eqb (to_Z ids.[pos]) v))%Z) ->
  CI L' R' (fst (add ids pos cnt ge)) (snd (add ids pos cnt ge)).
Proof.
  intros L R L' R' pos cnt ge (HLR & Hcl & Hgl & Hc & Hg) HLR' Hpos Hw.
  unfold add. cbv zeta. simpl fst. simpl snd.
  pose proof (Hw (to_Z ids.[pos])) as Hw0. rewrite Z.eqb_refl in Hw0. simpl in Hw0.
  pose proof (Hidr pos Hpos) as Hv0.
  set (v0 := ids.[pos]) in *.
  pose proof (to_Z_bounded L). pose proof (to_Z_bounded L').
  assert (Ex : to_Z cnt.[v0] = wc (to_Z v0) (to_Z L) (to_Z R)) by (apply Hc; exact Hv0).
  pose proof (wc_bound (to_Z v0) (to_Z L') (to_Z R') ltac:(lia)) as B'.
  assert (Ec : to_Z (cnt.[v0] + 1) = (to_Z cnt.[v0] + 1)%Z) by (apply succ_small; lia).
  set (c := cnt.[v0] + 1) in *.
  split; [exact HLR' |].
  split; [rewrite lset; exact Hcl |].
  split; [rewrite lset; exact Hgl |].
  split.
  - intros v Hv. destruct (Z.eq_dec (to_Z v) (to_Z v0)) as [E | E].
    + apply ieq in E. subst v. rewrite gss by (rewrite Hcl; lia). rewrite Ec, Ex, Hw0. reflexivity.
    + rewrite gso by lia. rewrite Hc by exact Hv. rewrite Hw.
      replace (Z.eqb (to_Z v0) (to_Z v)) with false by (symmetry; apply Z.eqb_neq; lia).
      simpl. lia.
  - intros c' Hc'. rewrite G_upd by (try exact Hcl; exact Hv0).
    rewrite Ec.
    assert (Hcn : (to_Z c < to_Z (PArray.length ge))%Z) by (rewrite Hgl, ge1; lia).
    destruct (Z.eq_dec (to_Z c') (to_Z c)) as [E | E].
    + apply ieq in E. subst c'. rewrite gss by exact Hcn.
      pose proof (G_bound cnt (to_Z c)) as GB.
      rewrite succ_small by (rewrite Hg by lia; lia). rewrite Hg by lia. rewrite Ec.
      replace (Z.leb (to_Z cnt.[v0] + 1) (to_Z cnt.[v0])) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite Z.leb_refl. simpl. lia.
    + rewrite gso by lia. rewrite Hg by exact Hc'.
      destruct (Z.leb_spec (to_Z c') (to_Z cnt.[v0])); destruct (Z.leb_spec (to_Z c') (to_Z cnt.[v0] + 1));
        simpl; lia.
Qed.

Lemma rem_ok : forall L R L' R' pos cnt ge, CI L R cnt ge ->
  (to_Z L' <= to_Z R' <= to_Z n)%Z -> (to_Z pos < to_Z n)%Z ->
  (forall v, wc v (to_Z L) (to_Z R) = (wc v (to_Z L') (to_Z R') + b2z (Z.eqb (to_Z ids.[pos]) v))%Z) ->
  CI L' R' (fst (rem ids pos cnt ge)) (snd (rem ids pos cnt ge)).
Proof.
  intros L R L' R' pos cnt ge (HLR & Hcl & Hgl & Hc & Hg) HLR' Hpos Hw.
  unfold rem. cbv zeta. simpl fst. simpl snd.
  pose proof (Hw (to_Z ids.[pos])) as Hw0. rewrite Z.eqb_refl in Hw0. simpl in Hw0.
  pose proof (Hidr pos Hpos) as Hv0.
  set (v0 := ids.[pos]) in *.
  pose proof (to_Z_bounded L). pose proof (to_Z_bounded L').
  assert (Ex : to_Z cnt.[v0] = wc (to_Z v0) (to_Z L) (to_Z R)) by (apply Hc; exact Hv0).
  pose proof (wc_bound (to_Z v0) (to_Z L') (to_Z R') ltac:(lia)) as B'.
  pose proof (wc_bound (to_Z v0) (to_Z L) (to_Z R) ltac:(lia)) as B.
  assert (Ec : to_Z (cnt.[v0] - 1) = (to_Z cnt.[v0] - 1)%Z) by (rewrite small_sub; change (to_Z 1) with 1%Z; lia).
  set (c := cnt.[v0]) in *.
  split; [exact HLR' |].
  split; [rewrite lset; exact Hcl |].
  split; [rewrite lset; exact Hgl |].
  split.
  - intros v Hv. destruct (Z.eq_dec (to_Z v) (to_Z v0)) as [E | E].
    + apply ieq in E. subst v. rewrite gss by (rewrite Hcl; lia). rewrite Ec, Ex. lia.
    + rewrite gso by lia. rewrite Hc by exact Hv. rewrite Hw.
      replace (Z.eqb (to_Z v0) (to_Z v)) with false by (symmetry; apply Z.eqb_neq; lia).
      simpl. lia.
  - intros c' Hc'. rewrite G_upd by (try exact Hcl; exact Hv0).
    fold c. rewrite Ec.
    assert (Hcn : (to_Z c < to_Z (PArray.length ge))%Z) by (rewrite Hgl, ge1; lia).
    destruct (Z.eq_dec (to_Z c') (to_Z c)) as [E | E].
    + apply ieq in E. subst c'. rewrite gss by exact Hcn.
      assert (GU : G (cnt.[v0 <- c - 1]) (to_Z c) = (G cnt (to_Z c) - 1)%Z).
      { rewrite G_upd by (try exact Hcl; exact Hv0). fold c. rewrite Ec, Z.leb_refl.
        replace (Z.leb (to_Z c) (to_Z c - 1)) with false by (symmetry; apply Z.leb_gt; lia).
        simpl. lia. }
      pose proof (G_bound (cnt.[v0 <- c - 1]) (to_Z c)) as NN.
      rewrite small_sub by (change (to_Z 1) with 1%Z; rewrite Hg by lia; lia).
      rewrite Hg by lia. rewrite Z.leb_refl.
      replace (Z.leb (to_Z c) (to_Z c - 1)) with false by (symmetry; apply Z.leb_gt; lia).
      simpl. change (to_Z 1) with 1%Z. lia.
    + rewrite gso by lia. rewrite Hg by exact Hc'.
      destruct (Z.leb_spec (to_Z c') (to_Z c)); destruct (Z.leb_spec (to_Z c') (to_Z c - 1));
        simpl; lia.
Qed.

End Window.

Lemma move_eq : forall ids tl tr L R cnt ge H, move ids tl tr L R cnt ge H =
  match bdec (tl <? L) with
  | left H1 =>
      let '(c, g) := add ids (L - 1) cnt ge in
      move ids tl tr (L - 1) R c g (Acc_inv H (dec_m1 tl tr L R H1))
  | right _ =>
      match bdec (R <? tr) with
      | left H2 =>
          let '(c, g) := add ids R cnt ge in
          move ids tl tr L (R + 1) c g (Acc_inv H (dec_m2 tl tr L R H2))
      | right _ =>
          match bdec (L <? tl) with
          | left H3 =>
              let '(c, g) := rem ids L cnt ge in
              move ids tl tr (L + 1) R c g (Acc_inv H (dec_m3 tl tr L R H3))
          | right _ =>
              match bdec (tr <? R) with
              | left H4 =>
                  let '(c, g) := rem ids (R - 1) cnt ge in
                  move ids tl tr L (R - 1) c g (Acc_inv H (dec_m4 tl tr L R H4))
              | right _ => (L, R, cnt, ge)
              end
          end
      end
  end.
Proof. intros. destruct H; reflexivity. Qed.

Section Move.
Variables (ids : array int) (n : int).
Hypothesis Hn : (to_Z n <= 4194303)%Z.
Hypothesis Hidl : PArray.length ids = n.
Hypothesis Hidr : forall a, (to_Z a < to_Z n)%Z -> (to_Z ids.[a] < to_Z n)%Z.
Variables (tl tr : int).
Hypothesis Htlr : (to_Z tl < to_Z tr <= to_Z n)%Z.

Lemma wc_left : forall v L R, (1 <= L)%Z ->
  wc ids v (L - 1) R = (wc ids v L R + b2z (fid ids v (L - 1)))%Z.
Proof.
  intros v L R HL. unfold wc.
  replace (Z.to_nat L) with (Z.to_nat (L - 1 + 1)) by (f_equal; lia).
  rewrite cz_step by lia. lia.
Qed.

Lemma wc_right : forall v L R, (0 <= R)%Z ->
  wc ids v L (R + 1) = (wc ids v L R + b2z (fid ids v R))%Z.
Proof. intros v L R HR. unfold wc. rewrite cz_step by lia. lia. Qed.

Lemma fid_pos : forall v pos, fid ids v (to_Z pos) = Z.eqb (to_Z ids.[pos]) v.
Proof. intros v pos. unfold fid. rewrite of_to_Z. reflexivity. Qed.

Lemma move_spec : forall z L R cnt ge H, mmeas tl tr L R = z -> CI ids n L R cnt ge ->
  let r := move ids tl tr L R cnt ge H in
  fst (fst (fst r)) = tl /\ snd (fst (fst r)) = tr /\ CI ids n tl tr (snd (fst r)) (snd r).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros L R cnt ge H Ez HC. rewrite move_eq.
  pose proof HC as (HLR & _).
  pose proof (to_Z_bounded tl) as Btl. pose proof (to_Z_bounded L) as BL.
  pose proof (to_Z_bounded R) as BR. cbv zeta.
  destruct (bdec (tl <? L)) as [H1 | H1].
  { pose proof H1 as H1'. rewrite Uint63.ltb_spec in H1'.
    assert (EL : to_Z (L - 1) = (to_Z L - 1)%Z) by (apply small_sub; change (to_Z 1) with 1%Z; lia).
    assert (Hw : forall v, wc ids v (to_Z (L - 1)) (to_Z R)
                 = (wc ids v (to_Z L) (to_Z R) + b2z (Z.eqb (to_Z ids.[L - 1]) v))%Z).
    { intros v. rewrite <- fid_pos, EL. apply wc_left. lia. }
    pose proof (add_ok ids n Hn Hidl Hidr L R (L - 1) R (L - 1) cnt ge HC
                  ltac:(lia) ltac:(lia) Hw) as HC'.
    destruct (add ids (L - 1) cnt ge) as [c g]. simpl in HC'.
    apply (IH (mmeas tl tr (L - 1) R)); [rewrite <- Ez; apply dec_m1; exact H1 | reflexivity | exact HC']. }
  rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in H1.
  destruct (bdec (R <? tr)) as [H2 | H2].
  { pose proof H2 as H2'. rewrite Uint63.ltb_spec in H2'.
    assert (ER : to_Z (R + 1) = (to_Z R + 1)%Z) by (apply succ_small; lia).
    assert (Hw : forall v, wc ids v (to_Z L) (to_Z (R + 1))
                 = (wc ids v (to_Z L) (to_Z R) + b2z (Z.eqb (to_Z ids.[R]) v))%Z).
    { intros v. rewrite <- fid_pos, ER. apply wc_right. lia. }
    pose proof (add_ok ids n Hn Hidl Hidr L R L (R + 1) R cnt ge HC
                  ltac:(lia) ltac:(lia) Hw) as HC'.
    destruct (add ids R cnt ge) as [c g]. simpl in HC'.
    apply (IH (mmeas tl tr L (R + 1))); [rewrite <- Ez; apply dec_m2; exact H2 | reflexivity | exact HC']. }
  rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in H2.
  destruct (bdec (L <? tl)) as [H3 | H3].
  { pose proof H3 as H3'. rewrite Uint63.ltb_spec in H3'.
    assert (EL : to_Z (L + 1) = (to_Z L + 1)%Z) by (apply succ_small; lia).
    assert (Hw : forall v, wc ids v (to_Z L) (to_Z R)
                 = (wc ids v (to_Z (L + 1)) (to_Z R) + b2z (Z.eqb (to_Z ids.[L]) v))%Z).
    { intros v. rewrite <- fid_pos, EL.
      pose proof (wc_left v (to_Z L + 1) (to_Z R) ltac:(lia)) as W.
      replace (to_Z L + 1 - 1)%Z with (to_Z L) in W by lia. exact W. }
    pose proof (rem_ok ids n Hn Hidl Hidr L R (L + 1) R L cnt ge HC
                  ltac:(lia) ltac:(lia) Hw) as HC'.
    destruct (rem ids L cnt ge) as [c g]. simpl in HC'.
    apply (IH (mmeas tl tr (L + 1) R)); [rewrite <- Ez; apply dec_m3; exact H3 | reflexivity | exact HC']. }
  rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in H3.
  destruct (bdec (tr <? R)) as [H4 | H4].
  { pose proof H4 as H4'. rewrite Uint63.ltb_spec in H4'.
    assert (ER : to_Z (R - 1) = (to_Z R - 1)%Z) by (apply small_sub; change (to_Z 1) with 1%Z; lia).
    assert (Hw : forall v, wc ids v (to_Z L) (to_Z R)
                 = (wc ids v (to_Z L) (to_Z (R - 1)) + b2z (Z.eqb (to_Z ids.[R - 1]) v))%Z).
    { intros v. rewrite <- fid_pos, ER.
      pose proof (wc_right v (to_Z L) (to_Z R - 1) ltac:(lia)) as W.
      replace (to_Z R - 1 + 1)%Z with (to_Z R) in W by lia. exact W. }
    pose proof (rem_ok ids n Hn Hidl Hidr L R L (R - 1) (R - 1) cnt ge HC
                  ltac:(lia) ltac:(lia) Hw) as HC'.
    destruct (rem ids (R - 1) cnt ge) as [c g]. simpl in HC'.
    apply (IH (mmeas tl tr L (R - 1))); [rewrite <- Ez; apply dec_m4; exact H4 | reflexivity | exact HC']. }
  rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in H4.
  assert (EL : L = tl) by (apply ieq; lia). assert (ER : R = tr) by (apply ieq; lia).
  subst L R. simpl. split; [reflexivity |]. split; [reflexivity | exact HC].
Qed.

End Move.

(* ------------------------------------------------------------------ *)
(* The acres l..r as a window of the counting function                 *)
(* ------------------------------------------------------------------ *)

Lemma firstn_S_snoc : forall (A : Type) (xs : list A) k d, (k < List.length xs)%nat ->
  firstn (S k) xs = firstn k xs ++ [nth k xs d].
Proof.
  intros A xs. induction xs as [| a t IH]; intros k d Hk; simpl in Hk; [lia |].
  destruct k as [| k]; [reflexivity |].
  change (firstn (S (S k)) (a :: t)) with (a :: firstn (S k) t).
  rewrite (IH k d) by lia. reflexivity.
Qed.

Lemma filt_firstn : forall (f : R -> bool) xs k, (k <= List.length xs)%nat ->
  Z.of_nat (List.length (filter f (firstn k xs))) = cz (fun q => f (nth (Z.to_nat q) xs 0%R)) k.
Proof.
  intros f xs k. induction k as [| k IH]; intros Hk; [reflexivity |].
  rewrite (firstn_S_snoc _ xs k 0%R) by lia. rewrite filter_app, length_app.
  cbn [cz]. rewrite <- IH by lia. rewrite Nat2Z.id. simpl.
  unfold b2z. destruct (f (nth k xs 0%R)); simpl; lia.
Qed.

Definition XZ (ph : list R) (rv : R) : Z -> bool :=
  fun q => if Req_EM_T (nth (Z.to_nat q) ph 0%R) rv then true else false.

Lemma count_acres : forall ph rv (l r : N), (1 <= l <= r)%N -> (N.to_nat r <= List.length ph)%nat ->
  Z.of_N (count_ph rv (acres ph l r)) =
  (cz (XZ ph rv) (N.to_nat r) - cz (XZ ph rv) (N.to_nat (l - 1)))%Z.
Proof.
  intros ph rv l r Hlr Hr. unfold count_ph, acres, len. rewrite nat_N_Z.
  set (g := fun x => if Req_EM_T x rv then true else false).
  rewrite firstn_skipn_comm.
  replace (N.to_nat (l - 1) + N.to_nat (r - l + 1))%nat with (N.to_nat r) by lia.
  set (s := N.to_nat (l - 1)).
  assert (Hs : (s <= N.to_nat r)%nat) by (unfold s; lia).
  pose proof (firstn_skipn s (firstn (N.to_nat r) ph)) as E.
  assert (E2 : Z.of_nat (List.length (filter g (firstn (N.to_nat r) ph))) =
               (Z.of_nat (List.length (filter g (firstn s (firstn (N.to_nat r) ph)))) +
                Z.of_nat (List.length (filter g (skipn s (firstn (N.to_nat r) ph)))))%Z).
  { rewrite <- E at 1. rewrite filter_app, length_app. lia. }
  rewrite firstn_firstn in E2. replace (Init.Nat.min s (N.to_nat r)) with s in E2 by lia.
  rewrite (filt_firstn g ph (N.to_nat r) Hr) in E2.
  rewrite (filt_firstn g ph s ltac:(lia)) in E2.
  replace (XZ ph rv) with (fun q => g (nth (Z.to_nat q) ph 0%R)) by reflexivity. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The answer of one query                                             *)
(* ------------------------------------------------------------------ *)

Definition idsf (p : array float) : array int :=
  mk_ids p (msort (flt p) (PArray.length p)) (PArray.length p).

Section Bridge.
Variable ph : list R.
Variable p : array float.
Hypothesis Hp : repr p ph.

Let n := PArray.length p.

Lemma ofz : forall q, (0 <= q < to_Z n)%Z -> to_Z (of_Z q) = q.
Proof. intros q Hq. pose proof (n_small p). rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. Qed.

Lemma wc_wr : forall q a b, (0 <= q < to_Z n)%Z -> (0 <= a <= b)%Z -> (b <= to_Z n)%Z ->
  wc (idsf p) (to_Z (idsf p).[of_Z q]) a b =
  (cz (XZ ph (nth (Z.to_nat q) ph 0%R)) (Z.to_nat b) - cz (XZ ph (nth (Z.to_nat q) ph 0%R)) (Z.to_nat a))%Z.
Proof.
  intros q a b Hq Hab Hb. unfold wc.
  assert (Hf : forall q', (0 <= q' < to_Z n)%Z ->
     fid (idsf p) (to_Z (idsf p).[of_Z q]) q' = XZ ph (nth (Z.to_nat q) ph 0%R) q').
  { intros q' Hq'. unfold fid, XZ.
    pose proof (ids_eq ph p Hp (of_Z q') (of_Z q) ltac:(rewrite ofz; lia) ltac:(rewrite ofz; lia)) as E.
    unfold X in E. rewrite !ofz in E by lia. fold (idsf p) in E.
    destruct (Z.eqb_spec (to_Z (idsf p).[of_Z q']) (to_Z (idsf p).[of_Z q])) as [Z1 | Z1];
    destruct (Req_EM_T (nth (Z.to_nat q') ph 0%R) (nth (Z.to_nat q) ph 0%R)) as [R1 | R1];
      try reflexivity.
    - exfalso. apply R1, E, ieq, Z1.
    - exfalso. apply Z1. f_equal. apply E, R1. }
  rewrite (cz_ext _ _ (Z.to_nat b) (fun q' Hq' => Hf q' ltac:(lia))).
  rewrite (cz_ext _ _ (Z.to_nat a) (fun q' Hq' => Hf q' ltac:(lia))).
  reflexivity.
Qed.

Lemma answer_ok : forall (tl tr : int) cnt ge (l r : N),
  CI (idsf p) n tl tr cnt ge -> to_Z tl = (Z.of_N l - 1)%Z -> to_Z tr = Z.of_N r ->
  (1 <= l <= r)%N -> (Z.of_N r <= to_Z n)%Z ->
  ((0 <? ge.[(tr - tl) / 2 + 1]) = true <-> usable ph l r).
Proof.
  intros tl tr cnt ge l r (HLR & Hcl & Hgl & Hc & Hg) Etl Etr Hlr Hrn.
  pose proof (n_small p) as Hn.
  assert (Et : to_Z ((tr - tl) / 2 + 1) = ((Z.of_N r - Z.of_N l + 1) / 2 + 1)%Z).
  { rewrite succ_small. - rewrite Uint63.div_spec, small_sub by lia. rewrite Etl, Etr.
      change (to_Z 2) with 2%Z. f_equal. f_equal. lia.
    - rewrite Uint63.div_spec, small_sub by lia. change (to_Z 2) with 2%Z.
      pose proof (Z.div_le_upper_bound (to_Z tr - to_Z tl) 2 (to_Z n) ltac:(lia) ltac:(lia)). lia. }
  set (t := (tr - tl) / 2 + 1) in *.
  set (T := ((Z.of_N r - Z.of_N l + 1) / 2 + 1)%Z) in *.
  assert (HT : (1 <= T <= to_Z n)%Z).
  { unfold T. pose proof (Z.div_pos (Z.of_N r - Z.of_N l + 1) 2 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (Z.of_N r - Z.of_N l + 1) 2 (to_Z n) ltac:(lia) ltac:(lia)). lia. }
  assert (ETN : Z.of_N ((r - l + 1) / 2 + 1) = T).
  { unfold T. rewrite N2Z.inj_add, N2Z.inj_div, N2Z.inj_add, N2Z.inj_sub by lia. reflexivity. }
  assert (Er : N.to_nat r = Z.to_nat (to_Z tr)) by lia.
  assert (El : N.to_nat (l - 1) = Z.to_nat (to_Z tl)) by lia.
  assert (Hph : (N.to_nat r <= List.length ph)%nat) by (pose proof (len_ph ph p Hp); fold n in H; lia).
  rewrite Uint63.ltb_spec. change (to_Z 0) with 0%Z. rewrite (Hg t) by lia. rewrite Et.
  unfold usable. split.
  - intros HG. unfold G in HG.
    destruct (cz_pos (fun v => (T <=? to_Z cnt.[of_Z v])%Z) 0 (Z.to_nat (to_Z n)) ltac:(lia) ltac:(simpl; lia)) as (v & Hv & Ev).
    apply Z.leb_le in Ev. rewrite Hc in Ev by (rewrite ofz; lia). rewrite ofz in Ev by lia.
    assert (Hw : (0 < wc (idsf p) v (to_Z tl) (to_Z tr))%Z) by lia.
    unfold wc in Hw.
    destruct (cz_pos _ (Z.to_nat (to_Z tl)) (Z.to_nat (to_Z tr)) ltac:(lia) Hw) as (q & Hq & Eq).
    unfold fid in Eq. apply Z.eqb_eq in Eq.
    exists (nth (Z.to_nat q) ph 0%R).
    apply N2Z.inj_le. rewrite ETN, count_acres by lia. rewrite Er, El.
    rewrite <- wc_wr by lia. rewrite Eq. lia.
  - intros [rv Hrv]. apply N2Z.inj_le in Hrv. rewrite ETN, count_acres in Hrv by lia.
    rewrite Er, El in Hrv.
    destruct (cz_pos (XZ ph rv) (Z.to_nat (to_Z tl)) (Z.to_nat (to_Z tr)) ltac:(lia) ltac:(lia)) as (q & Hq & Eq).
    unfold XZ in Eq. destruct (Req_EM_T (nth (Z.to_nat q) ph 0%R) rv) as [Eq' | Eq']; [| discriminate].
    rewrite <- Eq' in Hrv. rewrite <- wc_wr in Hrv by lia.
    pose proof (ids_lt ph p Hp (of_Z q) ltac:(rewrite ofz; lia)) as Hw. fold (idsf p) in Hw. fold n in Hw.
    set (w := to_Z (idsf p).[of_Z q]) in *.
    pose proof (to_Z_bounded (idsf p).[of_Z q]).
    unfold G. apply (Z.lt_le_trans _ 1); [lia |].
    replace (cz (fun v => (T <=? to_Z cnt.[of_Z v])%Z) (Z.to_nat (to_Z n)))
      with (cz (fun v => (T <=? to_Z cnt.[of_Z v])%Z) (Z.to_nat (to_Z n)) - cz (fun v => (T <=? to_Z cnt.[of_Z v])%Z) 0)%Z
      by (simpl; lia).
    apply (cz_one _ _ _ w); [lia |].
    apply Z.leb_le. rewrite Hc by (rewrite ofz; lia). rewrite ofz by lia. exact Hrv.
Qed.

End Bridge.

(* ------------------------------------------------------------------ *)
(* The main loop and the contract                                      *)
(* ------------------------------------------------------------------ *)

Lemma cz_false : forall k, cz (fun _ => false) k = 0%Z.
Proof. induction k as [| k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma repr_u : forall (l : list N) (t : array uint) (a : int), repr t l ->
  (to_Z a < Z.of_nat (List.length l))%Z ->
  to_Z t.[a] = Z.of_N (get_list_N l (Z.to_N (to_Z a))).
Proof.
  intros l t a [_ H] Ha. pose proof (to_Z_bounded a).
  destruct (H (Z.to_nat (to_Z a)) ltac:(lia)) as (v & E & R).
  unfold get_list_N. rewrite Z_N_nat, (nth_error_nth _ _ _ E).
  rewrite Z2Nat.id in R by lia. rewrite of_to_Z in R. unfold repr, repr_uint in R.
  rewrite <- R. pose proof (to_Z_bounded t.[a]). lia.
Qed.

Section Main.
Variables (ph : list R) (ls rs : list N) (p : array float) (x y : array uint).
Hypothesis Hv : valid_input ph ls rs.
Hypothesis Hp : repr p ph.
Hypothesis Hx : repr x ls.
Hypothesis Hy : repr y rs.

Let n := PArray.length p.
Let m := PArray.length x.

Lemma n_bounds : (1 <= to_Z n <= 10000)%Z.
Proof. pose proof (vi_n _ _ _ Hv). pose proof (len_ph ph p Hp). unfold len in H. fold n in H0. lia. Qed.

Lemma m_len : Z.of_nat (List.length ls) = to_Z m.
Proof. exact (proj1 Hx). Qed.

Lemma m_bounds : (1 <= to_Z m <= 10000)%Z.
Proof. pose proof (vi_m _ _ _ Hv). pose proof m_len. unfold len in H. lia. Qed.

Lemma rs_len : Z.of_nat (List.length rs) = Z.of_nat (List.length ls).
Proof. pose proof (vi_rs _ _ _ Hv). unfold len in H. lia. Qed.

Definition lq (q : int) : N := get_list_N ls (Z.to_N (to_Z q)).
Definition rq (q : int) : N := get_list_N rs (Z.to_N (to_Z q)).

Lemma query_facts : forall q, (to_Z q < to_Z m)%Z ->
  (1 <= lq q <= rq q)%N /\ (Z.of_N (rq q) <= to_Z n)%Z /\
  to_Z x.[q] = Z.of_N (lq q) /\ to_Z y.[q] = Z.of_N (rq q).
Proof.
  intros q Hq. pose proof m_len. pose proof rs_len. pose proof (to_Z_bounded q).
  destruct (vi_lr _ _ _ Hv (Z.to_N (to_Z q)) ltac:(unfold len; lia)) as [A B].
  pose proof (len_ph ph p Hp). fold n in H2. unfold len in B.
  unfold lq, rq. split; [exact A |]. split; [lia |].
  split; [exact (repr_u ls x q Hx ltac:(lia)) | exact (repr_u rs y q Hy ltac:(lia))].
Qed.

Let Q := msort (mo_le x y (blk n)) m.

Lemma Q_spec : (forall k, (to_Z k < to_Z m)%Z -> (to_Z Q.[k] < to_Z m)%Z) /\
  (forall j, (to_Z j < to_Z m)%Z -> exists k, (to_Z k < to_Z m)%Z /\ Q.[k] = j).
Proof.
  destruct (msort_spec (mo_le x y (blk n)) m ltac:(pose proof m_bounds; lia)) as (_ & A & B & _).
  split; [exact A | exact B].
Qed.

Definition MLI (k : int) (st : int * int * array int * array int * array bool) : Prop :=
  let '(L, R, cnt, ge, ans) := st in
  CI (idsf p) n L R cnt ge /\ PArray.length ans = m /\
  forall j, (to_Z j < to_Z m)%Z -> (exists k', (to_Z k' < to_Z k)%Z /\ Q.[k'] = j) ->
    (ans.[j] = true <-> usable ph (lq j) (rq j)).

Lemma main_loop : MLI m (loop m (fun _ _ => true) (mo_step (idsf p) x y Q) 0
  (0, 0, PArray.make n 0, PArray.make (n + 1) 0, PArray.make m false)).
Proof.
  pose proof n_bounds as Bn. pose proof m_bounds as Bm.
  assert (Hn : (to_Z n <= 4194303)%Z) by lia.
  pose proof (ids_len ph p Hp) as Il. pose proof (ids_lt ph p Hp) as Ilt.
  fold n in Il, Ilt. fold (idsf p) in Il, Ilt.
  apply for_inv.
  - change (to_Z 0) with 0%Z. lia.
  - simpl. split; [| split].
    + split; [change (to_Z 0) with 0%Z; lia |].
      split; [apply length_make_small; exact Hn |].
      split; [apply length_make_small; rewrite succ_small by lia; lia |].
      split.
      * intros v Hv'. rewrite gmake. unfold wc. change (to_Z 0) with 0%Z. lia.
      * intros c Hc. rewrite gmake. unfold G.
        rewrite (cz_ext _ (fun _ => false)); [rewrite cz_false; reflexivity |].
        intros q Hq. rewrite gmake. apply Z.leb_gt. change (to_Z 0) with 0%Z. lia.
    + apply length_make_small. lia.
    + intros j Hj (k' & Hk' & _). change (to_Z 0) with 0%Z in Hk'.
      pose proof (to_Z_bounded k'). lia.
  - intros k [[[[L R] cnt] ge] ans] Hk (HC & Hal & Ha).
    change (to_Z 0) with 0%Z in Hk.
    unfold mo_step. cbn beta iota zeta.
    destruct Q_spec as [Qr Qm].
    pose proof (Qr k ltac:(lia)) as Hq.
    destruct (query_facts _ Hq) as (Hlr & Hrn & Ex & Ey).
    set (q := Q.[k]) in *.
    assert (Ex' : to_Z (@PArray.get int x q) = Z.of_N (lq q)) by exact Ex.
    assert (Ey' : to_Z (@PArray.get int y q) = Z.of_N (rq q)) by exact Ey.
    clear Ex Ey.
    assert (Etl : to_Z (@PArray.get int x q - 1) = (Z.of_N (lq q) - 1)%Z)
      by (rewrite small_sub; change (to_Z 1) with 1%Z; lia).
    set (tl := @PArray.get int x q - 1) in *. set (tr := @PArray.get int y q) in *.
    pose proof (move_spec (idsf p) n Hn Il Ilt tl tr ltac:(lia) _ L R cnt ge
                  (Zwf_well_founded 0 (mmeas tl tr L R)) eq_refl HC) as MS.
    cbv zeta in MS.
    destruct (move (idsf p) tl tr L R cnt ge (Zwf_well_founded 0 (mmeas tl tr L R)))
      as [[[L' R'] c'] g'].
    simpl in MS. destruct MS as (EL & ER & HC'). subst L' R'.
    simpl. split; [exact HC' |]. split; [rewrite lset; exact Hal |].
    intros j Hj (k' & Hk' & Ek').
    destruct (Z.eq_dec (to_Z j) (to_Z q)) as [E | E].
    + apply ieq in E. rewrite E. rewrite gss by (rewrite Hal; lia).
      apply (answer_ok ph p Hp tl tr c' g'); auto.
    + rewrite gso by lia. apply Ha; [exact Hj |]. exists k'. split; [| exact Ek'].
      rewrite succ_small in Hk' by lia.
      destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E' | E']; [| lia].
      apply ieq in E'. subst k'. exfalso. apply E. rewrite <- Ek'. reflexivity.
Qed.

Lemma farm_correct_main : exists o : list bool, repr (farm p x y) o /\ farmingmars_spec ph ls rs o.
Proof.
  pose proof main_loop as ML.
  assert (Ef : farm p x y = snd (loop m (fun _ _ => true) (mo_step (idsf p) x y Q) 0
            (0, 0, PArray.make n 0, PArray.make (n + 1) 0, PArray.make m false))) by reflexivity.
  rewrite Ef.
  destruct (loop m (fun _ _ => true) (mo_step (idsf p) x y Q) 0
            (0, 0, PArray.make n 0, PArray.make (n + 1) 0, PArray.make m false))
    as [[[[L R] cnt] ge] ans].
  simpl in ML |- *. destruct ML as (_ & Hal & Ha).
  pose proof m_len as Lm. pose proof m_bounds as Bm.
  destruct Q_spec as [_ Qm].
  set (o := map (fun k => ans.[of_nat k]) (seq 0 (List.length ls))).
  assert (Lo : List.length o = List.length ls) by (unfold o; rewrite length_map, length_seq; reflexivity).
  assert (No : forall k, (k < List.length ls)%nat -> nth_error o k = Some ans.[of_nat k]).
  { intros k Hk. unfold o. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec k (List.length ls)); [reflexivity | lia]. }
  assert (Ofn : forall k, (k < List.length ls)%nat -> to_Z (of_nat k) = Z.of_nat k).
  { intros k Hk. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
  exists o. split.
  - split.
    + rewrite Lo, Lm. exact (f_equal to_Z (eq_sym Hal)).
    + intros k Hk. rewrite Lo in Hk. exists ans.[of_nat k]. split; [apply No; exact Hk | reflexivity].
  - split.
    + unfold len. rewrite Lo. reflexivity.
    + intros j Hj. unfold len in Hj.
      rewrite (nth_error_nth _ _ _ (No (N.to_nat j) ltac:(lia))).
      assert (Ej : to_Z (of_nat (N.to_nat j)) = Z.of_N j) by (rewrite Ofn by lia; lia).
      assert (U1 : lq (of_nat (N.to_nat j)) = get_list_N ls j) by (unfold lq; rewrite Ej, N2Z.id; reflexivity).
      assert (U2 : rq (of_nat (N.to_nat j)) = get_list_N rs j) by (unfold rq; rewrite Ej, N2Z.id; reflexivity).
      rewrite <- U1, <- U2.
      pose proof (Ha (of_nat (N.to_nat j)) ltac:(lia) ltac:(apply Qm; lia)) as HH. exact HH.
Qed.

End Main.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition farmingmars : array float -> array uint -> array uint -> array bool := farm.

Definition farmingmars_correct :
  forall (ph : list R) (ls rs : list N) (p : array float) (x y : array uint),
    valid_input ph ls rs -> repr p ph -> repr x ls -> repr y rs ->
    exists o : list bool, repr (farmingmars p x y) o /\ farmingmars_spec ph ls rs o
  := farm_correct_main.
