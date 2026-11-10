(* Implementation of sumsets (sumsets.spec): meet in the middle around a
   chained hash table of pair sums.

   Code.  With n = |x| and P = n(n-1)/2 pairs, the table has cap = P + 1
   buckets and cap entry slots (slot 0 is the nil of the chains, entries are
   numbered 1 .. P).  Every pair i < j is inserted: its entry stores the code
   i * 2^12 + j (n <= 4000 < 2^12) and the link to the previous head of its
   bucket, the bucket being a multiply-shift hash of the 63-bit word
   x.[i] + x.[j].  Then for every d = x.[k] (skipped when it cannot beat the
   best answer so far) and every c = x.[l], l <> k, the chain of the bucket of
   x.[k] - x.[l] is walked looking for an entry whose pair (i, j) avoids k
   and l and sums to x.[k] - x.[l]; the largest such x.[k] is the answer.

   The three columns of the table (heads, links, codes) hold up to 7998001
   cells, more than one PArray: each is a [big], four flat arrays of 2^21
   cells (fewer when cap is small), cell k living in array k >> 21 at offset
   k - ((k >> 21) << 21).  All arrays are threaded linearly.

   No Z, no nat in the code.  Termination: every loop recurses on an erased
   [Acc (Zwf 0) _] proof; the chain walk on the entry number itself, the
   link being followed only when it is smaller (always the case, checked at
   run time so that termination needs no invariant).

   Proof.  The walk is sound whatever the table holds: an entry is accepted
   only after its pair has been checked against x.  Completeness rests on the
   invariant [TI]: every inserted pair has an entry reachable along the
   decreasing links from the head of its bucket. *)

From Sumsets.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
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

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

(* ------------------------------------------------------------------ *)
(* Big arrays: four flat arrays of at most 2^21 cells                  *)
(* ------------------------------------------------------------------ *)

Record big := Big { b0 : array int; b1 : array int; b2 : array int; b3 : array int }.

Definition chunk (b : big) (q : int) : array int :=
  if q =? 0 then b0 b else if q =? 1 then b1 b else if q =? 2 then b2 b else b3 b.

Definition upd (b : big) (q : int) (a : array int) : big :=
  if q =? 0 then Big a (b1 b) (b2 b) (b3 b)
  else if q =? 1 then Big (b0 b) a (b2 b) (b3 b)
  else if q =? 2 then Big (b0 b) (b1 b) a (b3 b)
  else Big (b0 b) (b1 b) (b2 b) a.

Definition bget (b : big) (k : int) : int :=
  let q := k >> 21 in (chunk b q).[k - (q << 21)].

Definition bset (b : big) (k v : int) : big :=
  let q := k >> 21 in upd b q (chunk b q).[k - (q << 21) <- v].

(* the length of array q for a capacity cap *)
Definition clen (cap q : int) : int :=
  let lo := q << 21 in
  if cap <=? lo then 0 else if cap - lo <=? 2097152 then cap - lo else 2097152.

Definition bmake (cap v : int) : big :=
  Big (PArray.make (clen cap 0) v) (PArray.make (clen cap 1) v)
      (PArray.make (clen cap 2) v) (PArray.make (clen cap 3) v).

Lemma q_cases : forall q : int, ((φ q) < 4)%Z -> q = 0 \/ q = 1 \/ q = 2 \/ q = 3.
Proof.
  intros q Hq. pose proof (to_Z_bounded q).
  assert (E : ((φ q) = 0 \/ (φ q) = 1 \/ (φ q) = 2 \/ (φ q) = 3)%Z) by lia.
  destruct E as [E|[E|[E|E]]];
    [left|right;left|right;right;left|right;right;right];
    apply to_Z_inj; rewrite E; reflexivity.
Qed.

Lemma chunk_upd_same : forall b q a, ((φ q) < 4)%Z -> chunk (upd b q a) q = a.
Proof. intros b q a Hq. destruct (q_cases q Hq) as [->|[->|[->| ->]]]; reflexivity. Qed.

Lemma chunk_upd_other : forall b q q' a, ((φ q) < 4)%Z -> ((φ q') < 4)%Z -> q <> q' ->
  chunk (upd b q a) q' = chunk b q'.
Proof.
  intros b q q' a Hq Hq' Hne.
  destruct (q_cases q Hq) as [->|[->|[->| ->]]];
  destruct (q_cases q' Hq') as [->|[->|[->| ->]]];
  first [reflexivity | congruence].
Qed.

Lemma bq_spec : forall k : int, (φ (k >> 21)) = ((φ k) / 2097152)%Z.
Proof. intros k. rewrite lsr_spec. reflexivity. Qed.

Lemma br_spec : forall k : int, (φ (k - ((k >> 21) << 21))) = ((φ k) mod 2097152)%Z.
Proof.
  intros k. rewrite sub_spec, lsl_spec, bq_spec.
  change (2 ^ (φ 21))%Z with 2097152%Z.
  pose proof (to_Z_bounded k). rewrite wB_val in *.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma big_q_lt : forall k : int, ((φ k) < 8388608)%Z -> ((φ (k >> 21)) < 4)%Z.
Proof.
  intros k Hk. rewrite bq_spec. pose proof (to_Z_bounded k).
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma bidx_inj : forall k k' : int, k <> k' -> k >> 21 = k' >> 21 ->
  k - ((k >> 21) << 21) <> k' - ((k' >> 21) << 21).
Proof.
  intros k k' Hne E F. apply Hne. apply to_Z_inj.
  apply (f_equal to_Z) in E. apply (f_equal to_Z) in F.
  rewrite !bq_spec in E. rewrite !br_spec in F.
  pose proof (Z.div_mod (φ k) 2097152 ltac:(lia)).
  pose proof (Z.div_mod (φ k') 2097152 ltac:(lia)).
  lia.
Qed.

Definition bvalid (cap : Z) (b : big) : Prop :=
  forall k : int, ((φ k) < cap)%Z ->
    ((φ (k - ((k >> 21) << 21))) < (φ (PArray.length (chunk b (k >> 21)))))%Z.

Lemma bget_bset_same : forall cap b k v, (cap <= 8388608)%Z -> bvalid cap b ->
  ((φ k) < cap)%Z -> bget (bset b k v) k = v.
Proof.
  intros cap b k v Hc Hb Hk. unfold bget, bset. cbv zeta.
  rewrite chunk_upd_same by (apply big_q_lt; lia).
  apply aget_set_same. rewrite ltb_spec. apply Hb. exact Hk.
Qed.

Lemma bget_bset_other : forall b k k' v, ((φ k) < 8388608)%Z -> ((φ k') < 8388608)%Z ->
  k <> k' -> bget (bset b k v) k' = bget b k'.
Proof.
  intros b k k' v Hk Hk' Hne. unfold bget, bset. cbv zeta.
  pose proof (big_q_lt k Hk) as Qk. pose proof (big_q_lt k' Hk') as Qk'.
  destruct (Uint63.eqb (k >> 21) (k' >> 21)) eqn:E.
  - rewrite eqb_spec in E.
    pose proof (bidx_inj k k' Hne E) as Hr.
    rewrite <- E. rewrite <- E in Hr. rewrite chunk_upd_same by exact Qk.
    apply aget_set_other. exact Hr.
  - rewrite chunk_upd_other; try assumption.
    + reflexivity.
    + intro F. rewrite <- eqb_spec in F. congruence.
Qed.

Lemma bvalid_set : forall cap b k v, bvalid cap b -> (cap <= 8388608)%Z ->
  ((φ k) < 8388608)%Z -> bvalid cap (bset b k v).
Proof.
  intros cap b k v Hb Hc Hk k' Hk'. unfold bset. cbv zeta.
  pose proof (big_q_lt k Hk) as Qk. pose proof (big_q_lt k' ltac:(lia)) as Qk'.
  pose proof (Hb k' Hk') as Hb'.
  destruct (Uint63.eqb (k >> 21) (k' >> 21)) eqn:E.
  - rewrite eqb_spec in E. rewrite <- E. rewrite <- E in Hb'.
    rewrite chunk_upd_same by exact Qk. rewrite alength_set. exact Hb'.
  - rewrite chunk_upd_other; try assumption.
    intro F. rewrite <- eqb_spec in F. congruence.
Qed.

Lemma clen_spec : forall cap q : int, ((φ q) < 4)%Z -> ((φ cap) <= 8388608)%Z ->
  (φ (clen cap q)) = Z.max 0 (Z.min 2097152 ((φ cap) - (φ q) * 2097152)).
Proof.
  intros cap q Hq Hc. unfold clen. cbv zeta.
  assert (Hlo : (φ (q << 21)) = ((φ q) * 2097152)%Z).
  { rewrite lsl_spec. change (2 ^ (φ 21))%Z with 2097152%Z.
    pose proof (to_Z_bounded q). apply Z.mod_small. rewrite wB_val. lia. }
  destruct (cap <=? q << 21) eqn:E1.
  - rewrite leb_spec in E1. change (φ 0) with 0%Z. lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec in E1.
    destruct (cap - (q << 21) <=? 2097152) eqn:E2.
    + rewrite leb_spec in E2. rewrite sub_spec, Hlo in *.
      rewrite Z.mod_small in * by (pose proof (to_Z_bounded cap); rewrite wB_val; lia).
      lia.
    + rewrite <- Bool.not_true_iff_false, leb_spec in E2.
      rewrite sub_spec, Hlo in *.
      rewrite Z.mod_small in * by (pose proof (to_Z_bounded cap); rewrite wB_val; lia).
      change (φ 2097152) with 2097152%Z in *. lia.
Qed.

Lemma chunk_bmake : forall cap v q, ((φ q) < 4)%Z ->
  chunk (bmake cap v) q = PArray.make (clen cap q) v.
Proof. intros cap v q Hq. destruct (q_cases q Hq) as [->|[->|[->| ->]]]; reflexivity. Qed.

Lemma bvalid_make : forall cap v, ((φ cap) <= 8388608)%Z -> bvalid (φ cap) (bmake cap v).
Proof.
  intros cap v Hc k Hk.
  pose proof (big_q_lt k ltac:(lia)) as Qk.
  rewrite chunk_bmake by exact Qk. rewrite alength_make.
  pose proof (clen_spec cap (k >> 21) Qk Hc) as Hl.
  destruct (clen cap (k >> 21) <=? max_length) eqn:E.
  - rewrite Hl, br_spec, bq_spec. rewrite bq_spec in Hl.
    pose proof (Z.div_mod (φ k) 2097152 ltac:(lia)).
    pose proof (Z.mod_pos_bound (φ k) 2097152 ltac:(lia)).
    pose proof (to_Z_bounded k). lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec, max_length_val in E. lia.
Qed.

Lemma bget_make : forall cap v k, ((φ k) < 8388608)%Z -> bget (bmake cap v) k = v.
Proof.
  intros cap v k Hk. unfold bget. cbv zeta.
  rewrite chunk_bmake by (apply big_q_lt; exact Hk). apply aget_make.
Qed.

(* ------------------------------------------------------------------ *)
(* The hash: multiply-shift onto [0, cap)                              *)
(* ------------------------------------------------------------------ *)

Definition HA : int := 2177342782468422677.

Definition hash (cap s : int) : int := (((s * HA) >> 40) * cap) >> 23.

Lemma hash_lt : forall cap s, (0 < (φ cap) <= 8388608)%Z -> ((φ (hash cap s)) < (φ cap))%Z.
Proof.
  intros cap s Hc. unfold hash.
  rewrite lsr_spec, mul_spec, lsr_spec.
  change (2 ^ (φ 40))%Z with 1099511627776%Z. change (2 ^ (φ 23))%Z with 8388608%Z.
  pose proof (to_Z_bounded (s * HA)) as Bw. rewrite wB_val in *.
  assert (Hq : (0 <= (φ (s * HA)) / 1099511627776 < 8388608)%Z).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite Z.mod_small by nia.
  apply Z.div_lt_upper_bound; nia.
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

Lemma dec_lt : forall e' e : int, (e' <? e) = true -> Zwf 0 (φ e') (φ e).
Proof.
  intros e' e H. rewrite ltb_spec in H. pose proof (to_Z_bounded e').
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition code (i j : int) : int := (i << 12) + j.

(* the entry of code c answers the query (k, l, t) *)
Definition chk (x : array int) (n k l t c : int) : bool :=
  let i := c >> 12 in
  let j := c - (i << 12) in
  (i <? n) && (j <? n) && negb (i =? j) && negb (i =? k) && negb (i =? l)
  && negb (j =? k) && negb (j =? l) && (x.[i] + x.[j] =? t).

(* walk the chain from entry e *)
Fixpoint walk (x : array int) (nx cd : big) (n k l t e : int)
    (H : Acc (Zwf 0) (φ e)) {struct H} : bool :=
  match bdec (e =? 0) with
  | left _ => false
  | right _ =>
      if chk x n k l t (bget cd e) then true
      else
        let e' := bget nx e in
        match bdec (e' <? e) with
        | left Hlt => walk x nx cd n k l t e' (Acc_inv H (dec_lt e' e Hlt))
        | right _ => false
        end
  end.

Lemma walk_eq : forall x nx cd n k l t e H,
  walk x nx cd n k l t e H =
  match bdec (e =? 0) with
  | left _ => false
  | right _ =>
      if chk x n k l t (bget cd e) then true
      else
        let e' := bget nx e in
        match bdec (e' <? e) with
        | left Hlt => walk x nx cd n k l t e' (Acc_inv H (dec_lt e' e Hlt))
        | right _ => false
        end
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the table: bucket heads, links, codes, number of entries *)
Record tbl := Tbl { th : big; tn : big; tc : big; tk : int }.

Definition ins (x : array int) (cap i j : int) (T : tbl) : tbl :=
  let e := tk T + 1 in
  let h := hash cap (x.[i] + x.[j]) in
  let old := bget (th T) h in
  let nx := bset (tn T) e old in
  let cd := bset (tc T) e (code i j) in
  let hd := bset (th T) h e in
  Tbl hd nx cd e.

Fixpoint build_in (x : array int) (cap n i j : int) (T : tbl)
    (H : Acc (Zwf 0) (gap n j)) {struct H} : tbl :=
  match bdec (j <? n) with
  | left Hj => build_in x cap n i (j + 1) (ins x cap i j T) (Acc_inv H (dec_step n j Hj))
  | right _ => T
  end.

Lemma build_in_eq : forall x cap n i j T H,
  build_in x cap n i j T H =
  match bdec (j <? n) with
  | left Hj => build_in x cap n i (j + 1) (ins x cap i j T) (Acc_inv H (dec_step n j Hj))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Fixpoint build_out (x : array int) (cap n i : int) (T : tbl)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : tbl :=
  match bdec (i <? n) with
  | left Hi =>
      build_out x cap n (i + 1)
        (build_in x cap n i (i + 1) T (Zwf_well_founded 0 (gap n (i + 1))))
        (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.

Lemma build_out_eq : forall x cap n i T H,
  build_out x cap n i T H =
  match bdec (i <? n) with
  | left Hi =>
      build_out x cap n (i + 1)
        (build_in x cap n i (i + 1) T (Zwf_well_founded 0 (gap n (i + 1))))
        (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* is x.[k] = x.[l] + x.[i] + x.[j] for some pair i, j avoiding k and l *)
Definition query (x : array int) (T : tbl) (cap n k l : int) : bool :=
  let t := x.[k] - x.[l] in
  let e := bget (th T) (hash cap t) in
  walk x (tn T) (tc T) n k l t e (Zwf_well_founded 0 (φ e)).

(* some l >= l0, l <> k, answers the query *)
Fixpoint any_l (x : array int) (T : tbl) (cap n k l : int)
    (H : Acc (Zwf 0) (gap n l)) {struct H} : bool :=
  match bdec (l <? n) with
  | left Hl =>
      if l =? k then any_l x T cap n k (l + 1) (Acc_inv H (dec_step n l Hl))
      else if query x T cap n k l then true
      else any_l x T cap n k (l + 1) (Acc_inv H (dec_step n l Hl))
  | right _ => false
  end.

Lemma any_l_eq : forall x T cap n k l H,
  any_l x T cap n k l H =
  match bdec (l <? n) with
  | left Hl =>
      if l =? k then any_l x T cap n k (l + 1) (Acc_inv H (dec_step n l Hl))
      else if query x T cap n k l then true
      else any_l x T cap n k (l + 1) (Acc_inv H (dec_step n l Hl))
  | right _ => false
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the largest x.[k], k >= k0, that is such a sum *)
Fixpoint best_k (x : array int) (T : tbl) (cap n k : int) (found : bool) (best : int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : option int :=
  match bdec (k <? n) with
  | left Hk =>
      if andb found (Sint63.leb x.[k] best)
      then best_k x T cap n (k + 1) found best (Acc_inv H (dec_step n k Hk))
      else if any_l x T cap n k 0 (Zwf_well_founded 0 (gap n 0))
      then best_k x T cap n (k + 1) true x.[k] (Acc_inv H (dec_step n k Hk))
      else best_k x T cap n (k + 1) found best (Acc_inv H (dec_step n k Hk))
  | right _ => if found then Some best else None
  end.

Lemma best_k_eq : forall x T cap n k found best H,
  best_k x T cap n k found best H =
  match bdec (k <? n) with
  | left Hk =>
      if andb found (Sint63.leb x.[k] best)
      then best_k x T cap n (k + 1) found best (Acc_inv H (dec_step n k Hk))
      else if any_l x T cap n k 0 (Zwf_well_founded 0 (gap n 0))
      then best_k x T cap n (k + 1) true x.[k] (Acc_inv H (dec_step n k Hk))
      else best_k x T cap n (k + 1) found best (Acc_inv H (dec_step n k Hk))
  | right _ => if found then Some best else None
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition sumsets_impl (x : array int) : option int :=
  let n := PArray.length x in
  let cap := ((n * (n - 1)) >> 1) + 1 in
  let T0 := Tbl (bmake cap 0) (bmake cap 0) (bmake cap 0) 0 in
  let T := build_out x cap n 0 T0 (Zwf_well_founded 0 (gap n 0)) in
  best_k x T cap n 0 false 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Chains                                                              *)
(* ------------------------------------------------------------------ *)

(* entry e is reached from f along decreasing links *)
Inductive reach (nx : big) : int -> int -> Prop :=
| reach_here : forall e, e <> 0 -> reach nx e e
| reach_next : forall f e, f <> 0 -> ((φ (bget nx f)) < (φ f))%Z ->
    reach nx (bget nx f) e -> reach nx f e.

Lemma reach_le : forall nx f e, reach nx f e -> ((φ e) <= (φ f))%Z.
Proof. intros nx f e R. induction R; lia. Qed.

Lemma reach_set : forall nx p v f e, reach nx f e -> ((φ f) < (φ p))%Z ->
  ((φ p) < 8388608)%Z -> reach (bset nx p v) f e.
Proof.
  intros nx p v f e R. induction R as [e He | f e Hf Hlt R IH]; intros Hfp Hp.
  - apply reach_here. exact He.
  - assert (Ef : bget (bset nx p v) f = bget nx f).
    { apply bget_bset_other; lia. }
    apply reach_next; [exact Hf | rewrite Ef; exact Hlt |].
    rewrite Ef. apply IH; lia.
Qed.

Lemma walk_complete : forall x nx cd n k l t f e, reach nx f e ->
  chk x n k l t (bget cd e) = true ->
  forall H, walk x nx cd n k l t f H = true.
Proof.
  intros x nx cd n k l t f e R. induction R as [e He | f e Hf Hlt R IH]; intros Hc H;
    rewrite walk_eq.
  - destruct (bdec (e =? 0)) as [E|E]; [rewrite eqb_spec in E; contradiction|].
    rewrite Hc. reflexivity.
  - destruct (bdec (f =? 0)) as [E|E]; [rewrite eqb_spec in E; contradiction|].
    destruct (chk x n k l t (bget cd f)); [reflexivity|]. cbv zeta.
    destruct (bdec (bget nx f <? f)) as [L|L].
    + apply IH. exact Hc.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in L. lia.
Qed.

Lemma walk_sound : forall x nx cd n k l t z f H, (φ f) = z ->
  walk x nx cd n k l t f H = true -> exists c, chk x n k l t c = true.
Proof.
  intros x nx cd n k l t z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros f H Hz W. rewrite walk_eq in W.
  destruct (bdec (f =? 0)); [discriminate|].
  destruct (chk x n k l t (bget cd f)) eqn:C; [eauto|].
  cbv zeta in W.
  destruct (bdec (bget nx f <? f)) as [L|L]; [|discriminate].
  eapply IH; [| reflexivity | exact W].
  rewrite <- Hz. apply dec_lt. exact L.
Qed.

Lemma les_spec : forall u v : int,
  Sint63.leb u v = true <-> (Sint63.to_Z u <= Sint63.to_Z v)%Z.
Proof. intros u v. exact (Sint63.leb_spec u v). Qed.

Lemma code_dec : forall i j : int, ((φ i) < 4096)%Z -> ((φ j) < 4096)%Z ->
  code i j >> 12 = i /\ code i j - ((code i j >> 12) << 12) = j.
Proof.
  intros i j Hi Hj. unfold code.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  assert (E : ((i << 12) + j) >> 12 = i).
  { apply to_Z_inj. rewrite lsr_spec, add_spec, lsl_spec.
    change (2 ^ (φ 12))%Z with 4096%Z. rewrite wB_val.
    Z.to_euclidean_division_equations; lia. }
  split; [exact E|]. rewrite E.
  apply to_Z_inj. rewrite sub_spec, add_spec, lsl_spec.
  change (2 ^ (φ 12))%Z with 4096%Z. rewrite wB_val.
  Z.to_euclidean_division_equations; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Correctness                                                         *)
(* ------------------------------------------------------------------ *)

Section Correct.

Variable a : list Z.
(* x is read at type int, as the code reads it; it represents a as an
   array of sint *)
Variable x : array int.
Hypothesis Hv : valid_input a.
Hypothesis Hx : @repr (array sint) (list Z) _ x a.

Local Notation N := (Z.of_nat (List.length a)).
Local Notation A i := (nth (Z.to_nat i) a 0%Z).

Lemma Hn : (φ (PArray.length x)) = N.
Proof. destruct Hx as [Hl _]. symmetry. exact Hl. Qed.

Lemma HN : (1 <= N <= 4000)%Z.
Proof. destruct Hv as [Hvn _ _]. unfold len in Hvn. lia. Qed.

Lemma xget : forall i : int, ((φ i) < N)%Z -> Sint63.to_Z x.[i] = A (φ i).
Proof.
  intros i Hi. destruct Hx as [Hl Hc].
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  transitivity m; [exact Hr | symmetry; apply nth_error_nth; exact Hm].
Qed.

Lemma Abound : forall i : Z, (0 <= i < N)%Z -> (-536870912 <= A i <= 536870911)%Z.
Proof.
  intros i Hi. destruct Hv as [_ _ Hvr].
  rewrite Forall_forall in Hvr. apply Hvr. apply nth_In. lia.
Qed.

Lemma Ainj : forall i j : Z, (0 <= i < N)%Z -> (0 <= j < N)%Z -> A i = A j -> i = j.
Proof.
  intros i j Hi Hj E. destruct Hv as [_ Hvd _].
  rewrite (NoDup_nth a 0%Z) in Hvd.
  assert (Z.to_nat i = Z.to_nat j) by (apply Hvd; [lia | lia | exact E]). lia.
Qed.

Lemma sum_eq : forall i j k l : int,
  ((φ i) < N)%Z -> ((φ j) < N)%Z -> ((φ k) < N)%Z -> ((φ l) < N)%Z ->
  (x.[i] + x.[j] = x.[k] - x.[l]) <-> (A (φ i) + A (φ j) = A (φ k) - A (φ l))%Z.
Proof.
  intros i j k l Hi Hj Hk Hl.
  pose proof (Abound (φ i) ltac:(pose proof (to_Z_bounded i); lia)).
  pose proof (Abound (φ j) ltac:(pose proof (to_Z_bounded j); lia)).
  pose proof (Abound (φ k) ltac:(pose proof (to_Z_bounded k); lia)).
  pose proof (Abound (φ l) ltac:(pose proof (to_Z_bounded l); lia)).
  split.
  - intro E. apply (f_equal to_Z) in E. rewrite add_spec, sub_spec in E.
    rewrite <- !Sint63.to_Z_mod_Uint63to_Z in E.
    rewrite !xget in E by assumption.
    rewrite wB_val in E. Z.to_euclidean_division_equations; lia.
  - intro E. apply to_Z_inj. rewrite add_spec, sub_spec.
    rewrite <- !Sint63.to_Z_mod_Uint63to_Z. rewrite !xget by assumption.
    rewrite <- Zplus_mod, <- Zminus_mod, E. reflexivity.
Qed.

(* the pair (i, j) answers the query (k, l) *)
Definition Qp (k l i j : int) : Prop :=
  ((φ i) < N)%Z /\ ((φ j) < N)%Z /\ i <> j /\ i <> k /\ i <> l /\ j <> k /\ j <> l /\
  (A (φ i) + A (φ j) = A (φ k) - A (φ l))%Z.

Lemma Qp_sym : forall k l i j, Qp k l i j -> Qp k l j i.
Proof.
  intros k l i j (Hi & Hj & D1 & D2 & D3 & D4 & D5 & S).
  unfold Qp. repeat split; try assumption; try congruence. lia.
Qed.

Lemma chk_sound : forall k l c, ((φ k) < N)%Z -> ((φ l) < N)%Z ->
  chk x (PArray.length x) k l (x.[k] - x.[l]) c = true -> exists i j, Qp k l i j.
Proof.
  intros k l c Hk Hl C. unfold chk in C. cbv zeta in C.
  rewrite !Bool.andb_true_iff in C.
  destruct C as [[[[[[[C1 C2] C3] C4] C5] C6] C7] C8].
  rewrite Bool.negb_true_iff, eqb_false_spec in C3, C4, C5, C6, C7.
  rewrite ltb_spec, Hn in C1, C2. rewrite eqb_spec in C8.
  exists (c >> 12), (c - ((c >> 12) << 12)).
  unfold Qp. repeat split; try assumption.
  apply sum_eq; assumption.
Qed.

Lemma chk_complete : forall k l i j, ((φ k) < N)%Z -> ((φ l) < N)%Z -> ((φ i) < (φ j))%Z ->
  Qp k l i j -> chk x (PArray.length x) k l (x.[k] - x.[l]) (code i j) = true.
Proof.
  intros k l i j Hk Hl Hij HQ.
  pose proof HQ as (Hi & Hj & D1 & D2 & D3 & D4 & D5 & S).
  pose proof HN.
  destruct (code_dec i j ltac:(lia) ltac:(lia)) as [E1 E2].
  unfold chk. cbv zeta. rewrite E2, E1.
  rewrite (proj2 (ltb_spec i _)) by (rewrite Hn; lia).
  rewrite (proj2 (ltb_spec j _)) by (rewrite Hn; lia).
  rewrite (proj2 (eqb_false_spec i j)) by exact D1.
  rewrite (proj2 (eqb_false_spec i k)) by exact D2.
  rewrite (proj2 (eqb_false_spec i l)) by exact D3.
  rewrite (proj2 (eqb_false_spec j k)) by exact D4.
  rewrite (proj2 (eqb_false_spec j l)) by exact D5.
  simpl. apply eqb_spec. apply sum_eq; assumption.
Qed.

(* the table invariant: every pair of Ins has a reachable entry *)
Definition TI (cap : int) (T : tbl) (Ins : int -> int -> Prop) : Prop :=
  bvalid (φ cap) (th T) /\ bvalid (φ cap) (tn T) /\ bvalid (φ cap) (tc T) /\
  (forall b : int, ((φ b) < (φ cap))%Z -> ((φ (bget (th T) b)) <= (φ (tk T)))%Z) /\
  (forall i j, Ins i j -> exists e,
     reach (tn T) (bget (th T) (hash cap (x.[i] + x.[j]))) e /\ bget (tc T) e = code i j).

Lemma TI_mono : forall cap T (Ins Ins' : int -> int -> Prop), TI cap T Ins ->
  (forall i j, Ins' i j -> Ins i j) -> TI cap T Ins'.
Proof.
  intros cap T Ins Ins' (V1 & V2 & V3 & H4 & H5) Hm.
  split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact H4|].
  intros i j Hij. apply H5. apply Hm. exact Hij.
Qed.

Lemma ins_TI : forall cap T Ins i j, (0 < (φ cap) <= 8388608)%Z ->
  ((φ (tk T)) + 1 < (φ cap))%Z -> TI cap T Ins ->
  TI cap (ins x cap i j T) (fun i' j' => Ins i' j' \/ (i' = i /\ j' = j)).
Proof.
  intros cap T Ins i j Hc Hk (V1 & V2 & V3 & Hh & Hp).
  pose proof (to_Z_bounded (tk T)) as Bk.
  unfold ins. cbv zeta.
  remember (tk T + 1) as e eqn:Ee.
  assert (He : (φ e) = ((φ (tk T)) + 1)%Z) by (rewrite Ee; sia).
  remember (hash cap (x.[i] + x.[j])) as h eqn:Eh.
  assert (Hh' : ((φ h) < (φ cap))%Z) by (rewrite Eh; apply hash_lt; lia).
  pose proof (Hh h Hh') as Hold.
  unfold TI; cbn [th tn tc tk].
  split; [apply bvalid_set; [exact V1 | lia | lia] |].
  split; [apply bvalid_set; [exact V2 | lia | lia] |].
  split; [apply bvalid_set; [exact V3 | lia | lia] |].
  split.
  - intros b Hb. destruct (Uint63.eqb h b) eqn:E.
    + rewrite eqb_spec in E. rewrite <- E.
      rewrite (bget_bset_same (φ cap)) by (first [exact V1 | lia]). lia.
    + rewrite eqb_false_spec in E.
      rewrite bget_bset_other by (first [exact E | lia]).
      specialize (Hh b Hb). lia.
  - intros i' j' [Hin | [-> ->]].
    + destruct (Hp i' j' Hin) as (e0 & R & C).
      assert (Hh2 : ((φ (hash cap (x.[i'] + x.[j']))) < (φ cap))%Z) by (apply hash_lt; lia).
      pose proof (Hh _ Hh2) as Hle2.
      pose proof (reach_le _ _ _ R) as Hle.
      exists e0. split.
      * destruct (Uint63.eqb h (hash cap (x.[i'] + x.[j']))) eqn:E.
        -- rewrite eqb_spec in E. rewrite <- E. rewrite <- E in R.
           rewrite (bget_bset_same (φ cap)) by (first [exact V1 | lia]).
           apply reach_next.
           ++ intro F. rewrite F in He. change (φ 0) with 0%Z in He. lia.
           ++ rewrite (bget_bset_same (φ cap)) by (first [exact V2 | lia]). lia.
           ++ rewrite (bget_bset_same (φ cap)) by (first [exact V2 | lia]).
              apply reach_set; [exact R | lia | lia].
        -- rewrite eqb_false_spec in E.
           rewrite bget_bset_other by (first [exact E | lia]).
           apply reach_set; [exact R | lia | lia].
      * rewrite bget_bset_other by lia. exact C.
    + exists e. rewrite <- Eh. split.
      * rewrite (bget_bset_same (φ cap)) by (first [exact V1 | lia]).
        apply reach_here. intro F. rewrite F in He. change (φ 0) with 0%Z in He. lia.
      * rewrite (bget_bset_same (φ cap)) by (first [exact V3 | lia]). reflexivity.
Qed.

(* the pairs inserted before (i0, j0) *)
Definition Ins_at (i0 j0 : int) (i j : int) : Prop :=
  ((φ i) < (φ j) < N)%Z /\ (((φ i) < (φ i0))%Z \/ ((φ i) = (φ i0) /\ (φ j) < (φ j0))%Z).

Lemma build_in_spec : forall cap, ((φ cap) = N * (N - 1) / 2 + 1)%Z ->
  (0 < (φ cap) <= 8388608)%Z ->
  forall i0 : int, ((φ i0) < N)%Z ->
  forall z j0 T H, gap (PArray.length x) j0 = z ->
  ((φ i0) < (φ j0) <= N)%Z ->
  (2 * (φ (tk T)) = (φ i0) * (2 * N - (φ i0) - 1) + 2 * ((φ j0) - (φ i0) - 1))%Z ->
  TI cap T (Ins_at i0 j0) ->
  TI cap (build_in x cap (PArray.length x) i0 j0 T H) (Ins_at i0 (PArray.length x)) /\
  (2 * (φ (tk (build_in x cap (PArray.length x) i0 j0 T H)))
   = (φ i0) * (2 * N - (φ i0) - 1) + 2 * (N - (φ i0) - 1))%Z.
Proof.
  intros cap Hcap Hc i0 Hi0 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j0 T H Hz Hj0 Hcnt HT.
  rewrite build_in_eq.
  destruct (bdec (j0 <? PArray.length x)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec, Hn in Hj'.
    assert (Hj1 : (φ (j0 + 1)) = ((φ j0) + 1)%Z) by sia.
    assert (Hk1 : ((φ (tk T)) + 1 < (φ cap))%Z).
    { assert (0 <= (N - (φ i0) - 1) * (N - (φ i0) - 2))%Z by (apply Z.mul_nonneg_nonneg; lia).
      assert (2 * ((φ (tk T)) + 1) <= N * (N - 1))%Z by nia.
      rewrite Hcap. set (M := (N * (N - 1))%Z) in *.
      Z.to_euclidean_division_equations; lia. }
    assert (Hk2 : (φ (tk (ins x cap i0 j0 T))) = ((φ (tk T)) + 1)%Z).
    { unfold ins; cbn [tk]. pose proof (to_Z_bounded (tk T)). sia. }
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hj.
    + rewrite Hk2, Hj1. nia.
    + eapply TI_mono.
      * apply ins_TI; [exact Hc | exact Hk1 | exact HT].
      * intros i j [Hij [Hlt | [Heq Hlt]]].
        -- left. split; [exact Hij | left; exact Hlt].
        -- rewrite Hj1 in Hlt. destruct (Z.eq_dec (φ j) (φ j0)) as [Ej | Ej].
           ++ right. split; apply to_Z_inj; assumption.
           ++ left. split; [exact Hij | right; split; [exact Heq | lia]].
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hn in Hj.
    split.
    + eapply TI_mono; [exact HT|]. intros i j [Hij Hor]. split; [exact Hij|].
      rewrite Hn in Hor. lia.
    + assert ((φ j0) = N) by lia. nia.
Qed.

Lemma build_out_spec : forall cap, ((φ cap) = N * (N - 1) / 2 + 1)%Z ->
  (0 < (φ cap) <= 8388608)%Z ->
  forall z i0 T H, gap (PArray.length x) i0 = z ->
  ((φ i0) <= N)%Z ->
  (2 * (φ (tk T)) = (φ i0) * (2 * N - (φ i0) - 1))%Z ->
  TI cap T (Ins_at i0 0) ->
  TI cap (build_out x cap (PArray.length x) i0 T H) (fun i j => ((φ i) < (φ j) < N)%Z).
Proof.
  intros cap Hcap Hc z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i0 T H Hz Hi0 Hcnt HT.
  rewrite build_out_eq.
  destruct (bdec (i0 <? PArray.length x)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec, Hn in Hi'.
    assert (Hi1 : (φ (i0 + 1)) = ((φ i0) + 1)%Z) by sia.
    assert (HT1 : TI cap T (Ins_at i0 (i0 + 1))).
    { eapply TI_mono; [exact HT|]. intros i j [Hij Hor]. split; [exact Hij|].
      change (φ 0) with 0%Z. lia. }
    destruct (build_in_spec cap Hcap Hc i0 Hi' _ (i0 + 1) T
               (Zwf_well_founded 0 (gap (PArray.length x) (i0 + 1))) eq_refl
               ltac:(lia) ltac:(nia) HT1) as [HT2 Hcnt2].
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite Hi1. nia.
    + eapply TI_mono; [exact HT2|]. intros i j [Hij Hor]. split; [exact Hij|].
      rewrite Hn. rewrite Hi1 in Hor. change (φ 0) with 0%Z in Hor. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hn in Hi.
    eapply TI_mono; [exact HT|]. intros i j Hij. split; [exact Hij|]. lia.
Qed.

Lemma TI_init : forall cap, ((φ cap) <= 8388608)%Z ->
  TI cap (Tbl (bmake cap 0) (bmake cap 0) (bmake cap 0) 0) (Ins_at 0 0).
Proof.
  intros cap Hc. unfold TI; cbn [th tn tc tk].
  split; [apply bvalid_make; exact Hc|].
  split; [apply bvalid_make; exact Hc|].
  split; [apply bvalid_make; exact Hc|].
  split.
  - intros b Hb. rewrite bget_make by lia. lia.
  - intros i j [_ Hor]. change (φ 0) with 0%Z in Hor. pose proof (to_Z_bounded i). lia.
Qed.

Lemma query_complete : forall cap T k l i j, (0 < (φ cap) <= 8388608)%Z ->
  TI cap T (fun i j => ((φ i) < (φ j) < N)%Z) ->
  ((φ k) < N)%Z -> ((φ l) < N)%Z -> ((φ i) < (φ j))%Z -> Qp k l i j ->
  query x T cap (PArray.length x) k l = true.
Proof.
  intros cap T k l i j Hc HT Hk Hl Hij HQ.
  destruct HT as (_ & _ & _ & _ & Hp).
  pose proof HQ as (Hi & Hj & _ & _ & _ & _ & _ & S).
  destruct (Hp i j ltac:(lia)) as (e & R & C).
  assert (Es : x.[i] + x.[j] = x.[k] - x.[l]) by (apply sum_eq; assumption).
  rewrite Es in R.
  unfold query. cbv zeta.
  eapply walk_complete; [exact R|].
  rewrite C. apply chk_complete; assumption.
Qed.

Lemma query_spec : forall cap T k l, (0 < (φ cap) <= 8388608)%Z ->
  TI cap T (fun i j => ((φ i) < (φ j) < N)%Z) ->
  ((φ k) < N)%Z -> ((φ l) < N)%Z ->
  query x T cap (PArray.length x) k l = true <-> exists i j, Qp k l i j.
Proof.
  intros cap T k l Hc HT Hk Hl. split.
  - intro W. unfold query in W. cbv zeta in W.
    destruct (walk_sound x _ _ _ _ _ _ _ _ _ eq_refl W) as [c C].
    exact (chk_sound k l c Hk Hl C).
  - intros (i & j & HQ).
    destruct (Z.lt_trichotomy (φ i) (φ j)) as [L | [E | L]].
    + eapply query_complete; eassumption.
    + exfalso. destruct HQ as (_ & _ & D & _). apply D. apply to_Z_inj. exact E.
    + eapply query_complete; [eassumption | eassumption | eassumption | eassumption
                              | exact L | apply Qp_sym; exact HQ].
Qed.

(* x.[k] is such a sum *)
Definition goodI (k : int) : Prop :=
  exists l, ((φ l) < N)%Z /\ l <> k /\ exists i j, Qp k l i j.

Lemma any_l_spec : forall cap T k, (0 < (φ cap) <= 8388608)%Z ->
  TI cap T (fun i j => ((φ i) < (φ j) < N)%Z) -> ((φ k) < N)%Z ->
  forall z l0 H, gap (PArray.length x) l0 = z -> ((φ l0) <= N)%Z ->
  (any_l x T cap (PArray.length x) k l0 H = true <->
   exists l, ((φ l0) <= (φ l) < N)%Z /\ l <> k /\ exists i j, Qp k l i j).
Proof.
  intros cap T k Hc HT Hk z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros l0 H Hz Hl0. rewrite any_l_eq.
  destruct (bdec (l0 <? PArray.length x)) as [Hl | Hl].
  - pose proof Hl as Hl'. rewrite ltb_spec, Hn in Hl'.
    assert (Hl1 : (φ (l0 + 1)) = ((φ l0) + 1)%Z) by sia.
    assert (Hdec : Zwf 0 (gap (PArray.length x) (l0 + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hl).
    destruct (l0 =? k) eqn:Ek.
    + rewrite eqb_spec in Ek.
      rewrite (IH _ Hdec (l0 + 1) _ eq_refl ltac:(lia)).
      split; intros (l & Hlr & Hne & HQ); exists l; (split; [|split; [exact Hne | exact HQ]]).
      * lia.
      * assert ((φ l) <> (φ l0)) by (intro F; apply Hne; rewrite <- Ek; apply to_Z_inj; exact F).
        lia.
    + destruct (query x T cap (PArray.length x) k l0) eqn:Q.
      * split; [intros _ | reflexivity]. exists l0. split; [lia|]. split.
        -- rewrite eqb_false_spec in Ek. exact Ek.
        -- apply (query_spec cap T k l0 Hc HT Hk ltac:(lia)). exact Q.
      * rewrite (IH _ Hdec (l0 + 1) _ eq_refl ltac:(lia)).
        split; intros (l & Hlr & Hne & HQ); exists l; (split; [|split; [exact Hne | exact HQ]]).
        -- lia.
        -- destruct (Z.eq_dec (φ l) (φ l0)) as [F | F]; [|lia].
           assert (l = l0) by (apply to_Z_inj; exact F). subst l.
           rewrite <- (query_spec cap T k l0 Hc HT Hk ltac:(lia)) in HQ. congruence.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hn in Hl.
    split; [discriminate|]. intros (l & Hlr & _). lia.
Qed.

Lemma good_any : forall cap T k H, (0 < (φ cap) <= 8388608)%Z ->
  TI cap T (fun i j => ((φ i) < (φ j) < N)%Z) -> ((φ k) < N)%Z ->
  any_l x T cap (PArray.length x) k 0 H = true <-> goodI k.
Proof.
  intros cap T k H Hc HT Hk.
  rewrite (any_l_spec cap T k Hc HT Hk _ 0 H eq_refl ltac:(change (φ 0) with 0%Z; lia)).
  unfold goodI. split; intros (l & Hl & Hne & HQ); exists l.
  - split; [lia | split; assumption].
  - split; [change (φ 0) with 0%Z; pose proof (to_Z_bounded l); lia | split; assumption].
Qed.

(* the result of the search *)
Definition Res (r : option int) : Prop :=
  (r = None /\ forall k, ((φ k) < N)%Z -> ~ goodI k) \/
  (exists k', r = Some x.[k'] /\ ((φ k') < N)%Z /\ goodI k' /\
     forall k, ((φ k) < N)%Z -> goodI k -> (A (φ k) <= A (φ k'))%Z).

Lemma best_k_spec : forall cap T, (0 < (φ cap) <= 8388608)%Z ->
  TI cap T (fun i j => ((φ i) < (φ j) < N)%Z) ->
  forall z k0 found best H, gap (PArray.length x) k0 = z -> ((φ k0) <= N)%Z ->
  (found = false -> forall k, ((φ k) < (φ k0))%Z -> ~ goodI k) ->
  (found = true -> exists k', best = x.[k'] /\ ((φ k') < N)%Z /\ goodI k' /\
     forall k, ((φ k) < (φ k0))%Z -> goodI k -> (A (φ k) <= A (φ k'))%Z) ->
  Res (best_k x T cap (PArray.length x) k0 found best H).
Proof.
  intros cap T Hc HT z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k0 found best H Hz Hk0 Hf Ht. rewrite best_k_eq.
  destruct (bdec (k0 <? PArray.length x)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec, Hn in Hk'.
    assert (Hk1 : (φ (k0 + 1)) = ((φ k0) + 1)%Z) by sia.
    assert (Hdec : Zwf 0 (gap (PArray.length x) (k0 + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hk).
    destruct (andb found (Sint63.leb x.[k0] best)) eqn:Eskip.
    + apply Bool.andb_true_iff in Eskip. destruct Eskip as [Ef Ele]. subst found.
      apply (IH _ Hdec); [reflexivity | lia | intros F; discriminate F |].
      intros _. destruct (Ht eq_refl) as (k' & Eb & Hk'' & Hg & Hmax).
      exists k'. split; [exact Eb|]. split; [exact Hk''|]. split; [exact Hg|].
      intros k Hk2 Hgk. destruct (Z.eq_dec (φ k) (φ k0)) as [F | F].
      * assert (k = k0) by (apply to_Z_inj; exact F). subst k.
        rewrite les_spec in Ele. subst best.
        rewrite !xget in Ele by lia. lia.
      * apply Hmax; [lia | exact Hgk].
    + destruct (any_l x T cap (PArray.length x) k0 0
                  (Zwf_well_founded 0 (gap (PArray.length x) 0))) eqn:Eany.
      * assert (Hg0 : goodI k0)
          by (apply (proj1 (good_any cap T k0 (Zwf_well_founded 0 (gap (PArray.length x) 0)) Hc HT ltac:(lia))); exact Eany).
        apply (IH _ Hdec); [reflexivity | lia | intros F; discriminate F |].
        intros _. exists k0. split; [reflexivity|]. split; [lia|]. split; [exact Hg0|].
        intros k Hk2 Hgk. destruct (Z.eq_dec (φ k) (φ k0)) as [F | F].
        -- assert (k = k0) by (apply to_Z_inj; exact F). subst k. lia.
        -- destruct found.
           ++ destruct (Ht eq_refl) as (k' & Eb & Hk'' & Hg & Hmax).
              cbn in Eskip.
              pose proof (Hmax k ltac:(lia) Hgk) as Hkk.
              assert (Hlt : ~ (Sint63.to_Z x.[k0] <= Sint63.to_Z best)%Z)
                by (rewrite <- les_spec; congruence).
              subst best. rewrite !xget in Hlt by lia. lia.
           ++ exfalso. exact (Hf eq_refl k ltac:(lia) Hgk).
      * assert (Hng : ~ goodI k0).
        { rewrite <- (good_any cap T k0 (Zwf_well_founded 0 (gap (PArray.length x) 0)) Hc HT ltac:(lia)). congruence. }
        apply (IH _ Hdec); [reflexivity | lia | |].
        -- intros Ef k Hk2. destruct (Z.eq_dec (φ k) (φ k0)) as [F | F].
           ++ assert (k = k0) by (apply to_Z_inj; exact F). subst k. exact Hng.
           ++ apply Hf; [exact Ef | lia].
        -- intros Ef. destruct (Ht Ef) as (k' & Eb & Hk'' & Hg & Hmax).
           exists k'. split; [exact Eb|]. split; [exact Hk''|]. split; [exact Hg|].
           intros k Hk2 Hgk. destruct (Z.eq_dec (φ k) (φ k0)) as [F | F].
           ++ assert (k = k0) by (apply to_Z_inj; exact F). subst k. contradiction.
           ++ apply Hmax; [lia | exact Hgk].
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hn in Hk.
    destruct found.
    + right. destruct (Ht eq_refl) as (k' & Eb & Hk'' & Hg & Hmax).
      exists k'. subst best. split; [reflexivity|]. split; [exact Hk''|].
      split; [exact Hg|]. intros k Hk2 Hgk. apply Hmax; [lia | exact Hgk].
    + left. split; [reflexivity|]. intros k Hk2. apply Hf; [reflexivity | lia].
Qed.

(* from indices to the spec's sums *)
Lemma In_idx : forall v, In v a -> exists i : int, ((φ i) < N)%Z /\ A (φ i) = v.
Proof.
  intros v Hin. destruct (In_nth a v 0%Z Hin) as (p & Hp & E).
  exists (of_Z (Z.of_nat p)).
  assert (Ep : (φ (of_Z (Z.of_nat p))) = Z.of_nat p).
  { rewrite of_Z_spec. apply Z.mod_small. pose proof HN. rewrite wB_val. lia. }
  rewrite Ep. split; [lia|]. rewrite Nat2Z.id. exact E.
Qed.

Lemma good_sum : forall k, ((φ k) < N)%Z -> goodI k -> sum_of_three a (A (φ k)).
Proof.
  intros k Hk (l & Hl & Hlk & i & j & Hi & Hj & D1 & D2 & D3 & D4 & D5 & S).
  assert (Hne : forall p q : int, ((φ p) < N)%Z -> ((φ q) < N)%Z -> p <> q ->
                A (φ p) <> A (φ q)).
  { intros p q Hp Hq Hpq E. apply Hpq. apply to_Z_inj.
    pose proof (to_Z_bounded p). pose proof (to_Z_bounded q).
    apply Ainj; [lia | lia | exact E]. }
  exists (A (φ i)), (A (φ j)), (A (φ l)).
  split; [apply nth_In; lia|]. split; [apply nth_In; lia|].
  split; [apply nth_In; lia|]. split; [apply nth_In; lia|].
  split; [apply Hne; assumption|]. split; [apply Hne; assumption|].
  split; [apply Hne; assumption|]. split; [apply Hne; assumption|].
  split; [apply Hne; assumption|]. split; [apply Hne; assumption|].
  lia.
Qed.

Lemma sum_good : forall d, sum_of_three a d ->
  exists k, ((φ k) < N)%Z /\ A (φ k) = d /\ goodI k.
Proof.
  intros d (va & vb & vc & Ha & Hb & Hc & Hd & D1 & D2 & D3 & D4 & D5 & D6 & S).
  destruct (In_idx va Ha) as (i & Hi & Ei).
  destruct (In_idx vb Hb) as (j & Hj & Ej).
  destruct (In_idx vc Hc) as (l & Hl & El).
  destruct (In_idx d Hd) as (k & Hk & Ek).
  exists k. split; [exact Hk|]. split; [exact Ek|].
  exists l. split; [exact Hl|]. split; [intro F; subst; congruence|].
  exists i, j. unfold Qp.
  split; [exact Hi|]. split; [exact Hj|].
  split; [intro F; subst; congruence|]. split; [intro F; subst; congruence|].
  split; [intro F; subst; congruence|]. split; [intro F; subst; congruence|].
  split; [intro F; subst; congruence|].
  lia.
Qed.

Lemma cap_spec : forall cap, cap = ((PArray.length x * (PArray.length x - 1)) >> 1) + 1 ->
  ((φ cap) = N * (N - 1) / 2 + 1)%Z /\ (0 < (φ cap) <= 8388608)%Z.
Proof.
  intros cap ->. pose proof HN as HN'. pose proof Hn as Hn'.
  assert (E1 : (φ (PArray.length x - 1)) = (N - 1)%Z).
  { rewrite sub_spec, Hn'. change (φ 1) with 1%Z. apply Z.mod_small. rewrite wB_val. lia. }
  assert (B : (0 <= N * (N - 1) <= 4000 * 3999)%Z) by nia.
  assert (E2 : (φ (PArray.length x * (PArray.length x - 1))) = (N * (N - 1))%Z).
  { rewrite mul_spec, E1, Hn'. apply Z.mod_small. rewrite wB_val. lia. }
  assert (E3 : (φ ((PArray.length x * (PArray.length x - 1)) >> 1)) = (N * (N - 1) / 2)%Z).
  { rewrite lsr_spec, E2. reflexivity. }
  assert (E4 : (φ (((PArray.length x * (PArray.length x - 1)) >> 1) + 1))
               = (N * (N - 1) / 2 + 1)%Z).
  { rewrite add_spec, E3. change (φ 1) with 1%Z. apply Z.mod_small. rewrite wB_val.
    set (M := (N * (N - 1))%Z) in *. Z.to_euclidean_division_equations; lia. }
  rewrite E4. split; [reflexivity|].
  set (M := (N * (N - 1))%Z) in *. Z.to_euclidean_division_equations; lia.
Qed.

Theorem sumsets_impl_correct :
  exists o : option Z, @repr (option sint) (option Z) _ (sumsets_impl x) o /\ sumsets_spec a o.
Proof.
  pose proof HN as HN'.
  unfold sumsets_impl. cbv zeta.
  set (cap := ((PArray.length x * (PArray.length x - 1)) >> 1) + 1).
  destruct (cap_spec cap eq_refl) as [Hcap Hc].
  pose proof (build_out_spec cap Hcap Hc _ 0 (Tbl (bmake cap 0) (bmake cap 0) (bmake cap 0) 0)
     (Zwf_well_founded 0 (gap (PArray.length x) 0)) eq_refl
     ltac:(change (φ 0) with 0%Z; lia)
     ltac:(cbn [tk]; change (φ 0) with 0%Z; lia)
     (TI_init cap ltac:(lia))) as HT.
  pose proof (best_k_spec cap _ Hc HT _ 0 false 0
     (Zwf_well_founded 0 (gap (PArray.length x) 0)) eq_refl
     ltac:(change (φ 0) with 0%Z; lia)
     ltac:(intros _ k Hk; change (φ 0) with 0%Z in Hk; pose proof (to_Z_bounded k); lia)
     ltac:(intros F; discriminate F)) as HR.
  destruct HR as [[E Hnone] | (k' & E & Hk' & Hg & Hmax)]; rewrite E.
  - exists None. split; [exact I|]. unfold sumsets_spec. intros d Hd.
    destruct (sum_good d Hd) as (k & Hk & _ & Hgk). exact (Hnone k Hk Hgk).
  - exists (Some (A (φ k'))). split.
    + exact (xget k' Hk').
    + unfold sumsets_spec. split; [exact (good_sum k' Hk' Hg)|].
      intros d' Hd'. destruct (sum_good d' Hd') as (k & Hk & <- & Hgk).
      exact (Hmax k Hk Hgk).
Qed.

End Correct.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition sumsets : array sint -> option sint := sumsets_impl.

Definition sumsets_correct : forall (s : list Z) (x : array sint),
  valid_input s -> repr x s ->
  exists o : option Z, repr (sumsets x) o /\ sumsets_spec s o
  := sumsets_impl_correct.
