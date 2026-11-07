(* Implementation of babelfish (babelfish.spec): two-level perfect hashing
   (FKS, CLRS 11.5) over the static key set [foreign].

   Code.
   - Hash family: polynomial hashing of a PrimString.string modulo the prime
     p = 2^31 - 1, [hash a s = (sum_k (s[k]+1) * a^(len-1-k)) mod p] by
     Horner, with a in [1, p-1]; reduced modulo the table size.
   - Parameters are drawn by a deterministic 63-bit LCG threaded through the
     construction (no I/O, no Random).
   - Level 1: nb = max(n, 1) buckets; draw a1 until sum_b cnt_b^2 <= 4n
     (at most 32 draws, the last one kept anyway).  Bucket of key i stored
     in [bk].
   - Layout, one flat [meta] array of 3*nb cells: meta[3b] = offset of the
     second-level table of bucket b in the flat [slot] array, meta[3b+1] =
     its size cnt_b^2, meta[3b+2] = its hash parameter.  Keys are grouped by
     bucket in [order] by a counting sort.
   - Level 2: per bucket, draw a until the bucket's keys land in distinct
     cells (at most 64 draws, the table range cleared between draws).
     A cell holds i+1 for key i, 0 when empty.
   - Lookup of x: one level-1 hash, one level-2 hash, the candidate key
     index i read from [slot], one string comparison f[i] = x.
   - Verification: after construction one pass checks that every key i is
     found at its own cell (slot[pos f[i]] = i+1).  The correctness proof
     rests only on this check, never on the construction or the hash
     family.  If the check fails (all redraws exhausted: practically
     unreachable), every query falls back to a linear scan of [foreign].
   No nat, no Z, no lists in the code; the tables are flat int arrays.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof, as in template/polymul1. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require PrimString PString String Ascii.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Notation pstr := PrimString.string.

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
(* Hashing and the generator                                           *)
(* ------------------------------------------------------------------ *)

Definition prime : int := 2147483647.

(* Horner evaluation of the characters k, k+1, ..., len-1 of s at a. *)
Fixpoint hash_loop (a : int) (s : pstr) (len k acc : int)
    (H : Acc (Zwf 0) (gap len k)) {struct H} : int :=
  match bdec (k <? len) with
  | left Hk =>
      hash_loop a s len (k + 1) ((acc * a + PrimString.get s k + 1) mod prime)
        (Acc_inv H (dec_step len k Hk))
  | right _ => acc
  end.

Definition hash (a : int) (s : pstr) : int :=
  let len := PrimString.length s in
  hash_loop a s len 0 0 (Zwf_well_founded 0 (gap len 0)).

Definition seed : int := 88172645463325252.
Definition rng_next (st : int) : int :=
  st * 6364136223846793005 + 1442695040888963407.
Definition rng_draw (st : int) : int := ((st >> 17) mod (prime - 1)) + 1.

(* ------------------------------------------------------------------ *)
(* Construction                                                        *)
(* ------------------------------------------------------------------ *)

(* Level-1 bucket of every key i in [i, n): bk[i] and the counts. *)
Fixpoint count_loop (a nb : int) (f : array pstr) (n i : int)
    (cnt bk : array int) (H : Acc (Zwf 0) (gap n i)) {struct H}
    : array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let b := hash a f.[i] mod nb in
      count_loop a nb f n (i + 1) cnt.[b <- cnt.[b] + 1] bk.[i <- b]
        (Acc_inv H (dec_step n i Hi))
  | right _ => (cnt, bk)
  end.

(* acc + sum_{b' in [b, nb)} cnt[b']^2 *)
Fixpoint sumsq_loop (cnt : array int) (nb b acc : int)
    (H : Acc (Zwf 0) (gap nb b)) {struct H} : int :=
  match bdec (b <? nb) with
  | left Hb =>
      sumsq_loop cnt nb (b + 1) (acc + cnt.[b] * cnt.[b])
        (Acc_inv H (dec_step nb b Hb))
  | right _ => acc
  end.

(* Draw the level-1 parameter until sum cnt^2 <= 4n (draws t .. tries). *)
Fixpoint level1 (f : array pstr) (n nb tries t st : int) (bk : array int)
    (H : Acc (Zwf 0) (gap tries t)) {struct H}
    : int * int * array int * array int :=
  let st' := rng_next st in
  let a := rng_draw st' in
  let '(cnt, bk') :=
    count_loop a nb f n 0 (PArray.make nb 0) bk (Zwf_well_founded 0 (gap n 0)) in
  match bdec (t <? tries) with
  | left Ht =>
      if sumsq_loop cnt nb 0 0 (Zwf_well_founded 0 (gap nb 0)) <=? 4 * n
      then (a, st', cnt, bk')
      else level1 f n nb tries (t + 1) st' bk' (Acc_inv H (dec_step tries t Ht))
  | right _ => (a, st', cnt, bk')
  end.

(* meta[3b] = offset, meta[3b+1] = cnt[b]^2, cur[b] = first position of
   bucket b in [order]; returns the total table size as well. *)
Fixpoint layout_loop (cnt : array int) (nb b off st : int)
    (meta cur : array int) (H : Acc (Zwf 0) (gap nb b)) {struct H}
    : array int * array int * int :=
  match bdec (b <? nb) with
  | left Hb =>
      let c := cnt.[b] in
      layout_loop cnt nb (b + 1) (off + c * c) (st + c)
        meta.[3 * b <- off].[3 * b + 1 <- c * c] cur.[b <- st]
        (Acc_inv H (dec_step nb b Hb))
  | right _ => (meta, cur, off)
  end.

(* Counting sort of the keys by bucket. *)
Fixpoint distribute (bk : array int) (n i : int) (cur order : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let b := bk.[i] in
      let p := cur.[b] in
      distribute bk n (i + 1) cur.[b <- p + 1] order.[p <- i]
        (Acc_inv H (dec_step n i Hi))
  | right _ => order
  end.

(* Place the keys order[i .. e) in slot[off .. off+sz) with parameter a;
   false at the first collision. *)
Fixpoint place_loop (f : array pstr) (order : array int) (a off sz e i : int)
    (slot : array int) (H : Acc (Zwf 0) (gap e i)) {struct H}
    : array int * bool :=
  match bdec (i <? e) with
  | left Hi =>
      let k := order.[i] in
      let s := off + hash a f.[k] mod sz in
      if slot.[s] =? 0
      then place_loop f order a off sz e (i + 1) slot.[s <- k + 1]
             (Acc_inv H (dec_step e i Hi))
      else (slot, false)
  | right _ => (slot, true)
  end.

(* slot[i .. e) := 0 *)
Fixpoint clear_loop (e i : int) (slot : array int)
    (H : Acc (Zwf 0) (gap e i)) {struct H} : array int :=
  match bdec (i <? e) with
  | left Hi => clear_loop e (i + 1) slot.[i <- 0] (Acc_inv H (dec_step e i Hi))
  | right _ => slot
  end.

(* Draw the level-2 parameter of one bucket until its keys order[st ..
   st+c) land in distinct cells (draws t .. tries). *)
Fixpoint level2 (f : array pstr) (order : array int) (st c off sz tries t rng : int)
    (slot : array int) (H : Acc (Zwf 0) (gap tries t)) {struct H}
    : array int * int * int :=
  let rng' := rng_next rng in
  let a := rng_draw rng' in
  let '(slot1, ok) :=
    place_loop f order a off sz (st + c) st slot
      (Zwf_well_founded 0 (gap (st + c) st)) in
  if ok then (slot1, a, rng')
  else
    match bdec (t <? tries) with
    | left Ht =>
        level2 f order st c off sz tries (t + 1) rng'
          (clear_loop (off + sz) off slot1 (Zwf_well_founded 0 (gap (off + sz) off)))
          (Acc_inv H (dec_step tries t Ht))
    | right _ => (slot1, a, rng')
    end.

(* The second-level tables of the buckets b .. nb-1; st is the position of
   bucket b in [order]. *)
Fixpoint buckets_loop (f : array pstr) (order cnt : array int) (nb b st rng : int)
    (meta slot : array int) (H : Acc (Zwf 0) (gap nb b)) {struct H}
    : array int * array int :=
  match bdec (b <? nb) with
  | left Hb =>
      let c := cnt.[b] in
      if c =? 0
      then buckets_loop f order cnt nb (b + 1) st rng meta slot
             (Acc_inv H (dec_step nb b Hb))
      else
        let off := meta.[3 * b] in
        let sz := meta.[3 * b + 1] in
        let '(slot', a, rng') :=
          level2 f order st c off sz 64 0 rng slot (Zwf_well_founded 0 (gap 64 0)) in
        buckets_loop f order cnt nb (b + 1) (st + c) rng' meta.[3 * b + 2 <- a] slot'
          (Acc_inv H (dec_step nb b Hb))
  | right _ => (meta, slot)
  end.

Record tables := mk_tables {
  t_a1 : int;            (* level-1 parameter *)
  t_nb : int;            (* number of buckets *)
  t_meta : array int;    (* offset, size, parameter of every bucket *)
  t_slot : array int     (* the second-level tables, key index + 1 *)
}.

Definition build (f : array pstr) (n : int) : tables :=
  let nb := if n =? 0 then 1 else n in
  let '(a1, rng, cnt, bk) :=
    level1 f n nb 32 0 seed (PArray.make n 0) (Zwf_well_founded 0 (gap 32 0)) in
  let '(meta, cur, total) :=
    layout_loop cnt nb 0 0 0 (PArray.make (3 * nb) 0) (PArray.make nb 0)
      (Zwf_well_founded 0 (gap nb 0)) in
  let order :=
    distribute bk n 0 cur (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  let '(meta', slot) :=
    buckets_loop f order cnt nb 0 0 rng meta (PArray.make total 0)
      (Zwf_well_founded 0 (gap nb 0)) in
  mk_tables a1 nb meta' slot.

(* The cell of x: past the end of [slot] for an empty bucket. *)
Definition pos (t : tables) (x : pstr) : int :=
  let meta := t_meta t in
  let b := hash (t_a1 t) x mod t_nb t in
  let sz := meta.[3 * b + 1] in
  if sz =? 0 then PArray.length (t_slot t)
  else meta.[3 * b] + hash meta.[3 * b + 2] x mod sz.

(* Every key i in [i, n) sits at its own cell. *)
Fixpoint check_loop (t : tables) (f : array pstr) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : bool :=
  match bdec (i <? n) with
  | left Hi =>
      if (t_slot t).[pos t f.[i]] =? i + 1
      then check_loop t f n (i + 1) (Acc_inv H (dec_step n i Hi))
      else false
  | right _ => true
  end.

(* ------------------------------------------------------------------ *)
(* Queries and the answer                                              *)
(* ------------------------------------------------------------------ *)

(* Fallback: the first index in [i, n) holding x, n if none. *)
Fixpoint scan_loop (f : array pstr) (x : pstr) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      match PrimString.compare f.[i] x with
      | Eq => i
      | _ => scan_loop f x n (i + 1) (Acc_inv H (dec_step n i Hi))
      end
  | right _ => n
  end.

Definition query (e f : array pstr) (n : int) (ok : bool) (t : tables) (x : pstr)
    : option pstr :=
  let i := if ok then (t_slot t).[pos t x] - 1
           else scan_loop f x n 0 (Zwf_well_founded 0 (gap n 0)) in
  if i <? n then
    match PrimString.compare f.[i] x with
    | Eq => Some e.[i]
    | _ => None
    end
  else None.

Fixpoint fill_loop (e f m : array pstr) (n : int) (ok : bool) (t : tables) (L k : int)
    (out : array (option pstr)) (H : Acc (Zwf 0) (gap L k)) {struct H}
    : array (option pstr) :=
  match bdec (k <? L) with
  | left Hk =>
      fill_loop e f m n ok t L (k + 1) out.[k <- query e f n ok t m.[k]]
        (Acc_inv H (dec_step L k Hk))
  | right _ => out
  end.

Definition babelfish_impl (e f m : array pstr) : array (option pstr) :=
  let n := PArray.length f in
  let t := build f n in
  let ok := check_loop t f n 0 (Zwf_well_founded 0 (gap n 0)) in
  let L := PArray.length m in
  fill_loop e f m n ok t L 0 (PArray.make L None) (Zwf_well_founded 0 (gap L 0)).

(* ------------------------------------------------------------------ *)
(* Prop side                                                           *)
(* ------------------------------------------------------------------ *)

(* Unfolding equations of the loops the proof goes through. *)
Lemma check_loop_eq : forall t f n i H,
  check_loop t f n i H =
  match bdec (i <? n) with
  | left Hi =>
      if (t_slot t).[pos t f.[i]] =? i + 1
      then check_loop t f n (i + 1) (Acc_inv H (dec_step n i Hi))
      else false
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_loop_eq : forall f x n i H,
  scan_loop f x n i H =
  match bdec (i <? n) with
  | left Hi =>
      match PrimString.compare f.[i] x with
      | Eq => i
      | _ => scan_loop f x n (i + 1) (Acc_inv H (dec_step n i Hi))
      end
  | right _ => n
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_loop_eq : forall e f m n ok t L k out H,
  fill_loop e f m n ok t L k out H =
  match bdec (k <? L) with
  | left Hk =>
      fill_loop e f m n ok t L (k + 1) out.[k <- query e f n ok t m.[k]]
        (Acc_inv H (dec_step L k Hk))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma of_nat_to_nat : forall i : int, of_Z (Z.of_nat (Z.to_nat (φ i))) = i.
Proof.
  intros i. rewrite Z2Nat.id by (pose proof (to_Z_bounded i); lia).
  apply of_to_Z.
Qed.

Lemma phi_of_nat : forall k : nat, (Z.of_nat k < wB)%Z ->
  (φ (of_Z (Z.of_nat k))) = Z.of_nat k.
Proof. intros k Hk. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

(* The verification pass. *)
Lemma check_loop_spec : forall t f n z i H,
  gap n i = z -> check_loop t f n i H = true ->
  forall j, ((φ i) <= (φ j) < (φ n))%Z -> (t_slot t).[pos t f.[j]] = j + 1.
Proof.
  intros t f n z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i H Hz Hc j Hj. rewrite check_loop_eq in Hc.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - destruct ((t_slot t).[pos t f.[i]] =? i + 1) eqn:E; [| discriminate].
    destruct (Z.eq_dec (φ j) (φ i)) as [Ej | Ej].
    + apply to_Z_inj in Ej. subst j. apply eqb_spec in E. exact E.
    + pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
      assert ((φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      eapply IH; [ | reflexivity | exact Hc | lia].
      rewrite <- Hz. apply dec_step. exact Hi.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. lia.
Qed.

(* The fallback scan. *)
Lemma scan_loop_spec : forall f x n z i H,
  gap n i = z ->
  ((scan_loop f x n i H <? n) = true /\ f.[scan_loop f x n i H] = x)
  \/ (forall j, ((φ i) <= (φ j) < (φ n))%Z -> f.[j] <> x).
Proof.
  intros f x n z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i H Hz. rewrite scan_loop_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Hd : Zwf 0 (gap n (i + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hi).
    destruct (PrimString.compare f.[i] x) eqn:C.
    + left. split; [exact Hi |]. apply PString.compare_eq. exact C.
    + destruct (IH _ Hd (i + 1) (Acc_inv H (dec_step n i Hi)) eq_refl) as [L | R];
        [left; exact L | right].
      intros j Hj Ej. destruct (Z.eq_dec (φ j) (φ i)) as [E | E].
      * apply to_Z_inj in E. subst j. rewrite Ej, PString.compare_refl in C.
        discriminate.
      * apply (R j); [lia | exact Ej].
    + destruct (IH _ Hd (i + 1) (Acc_inv H (dec_step n i Hi)) eq_refl) as [L | R];
        [left; exact L | right].
      intros j Hj Ej. destruct (Z.eq_dec (φ j) (φ i)) as [E | E].
      * apply to_Z_inj in E. subst j. rewrite Ej, PString.compare_refl in C.
        discriminate.
      * apply (R j); [lia | exact Ej].
  - right. intros j Hj. rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. lia.
Qed.

(* The answer read at a candidate index. *)
Lemma query_unfold : forall e f n ok t x,
  query e f n ok t x =
  let i := if ok then (t_slot t).[pos t x] - 1
           else scan_loop f x n 0 (Zwf_well_founded 0 (gap n 0)) in
  if i <? n then
    match PrimString.compare f.[i] x with
    | Eq => Some e.[i]
    | _ => None
    end
  else None.
Proof. reflexivity. Qed.

Lemma answer_at_some : forall (e f : array pstr) n i x y,
  (if i <? n then
     match PrimString.compare f.[i] x with Eq => Some e.[i] | _ => None end
   else None) = Some y ->
  ((φ i) < (φ n))%Z /\ f.[i] = x /\ y = e.[i].
Proof.
  intros e f n i x y H.
  destruct (i <? n) eqn:Hi; [| discriminate].
  rewrite ltb_spec in Hi.
  destruct (PrimString.compare f.[i] x) eqn:C; try discriminate.
  injection H as <-. split; [exact Hi |]. split; [| reflexivity].
  apply PString.compare_eq. exact C.
Qed.

Lemma answer_at_found : forall (e f : array pstr) n i x,
  ((φ i) < (φ n))%Z -> f.[i] = x ->
  (if i <? n then
     match PrimString.compare f.[i] x with Eq => Some e.[i] | _ => None end
   else None) = Some e.[i].
Proof.
  intros e f n i x Hi E.
  replace (i <? n) with true by (symmetry; rewrite ltb_spec; exact Hi).
  rewrite E, PString.compare_refl. reflexivity.
Qed.

Lemma query_some : forall e f n ok t x y,
  query e f n ok t x = Some y ->
  exists i, ((φ i) < (φ n))%Z /\ f.[i] = x /\ y = e.[i].
Proof.
  intros e f n ok t x y H. rewrite query_unfold in H. cbv zeta in H.
  eexists. exact (answer_at_some _ _ _ _ _ _ H).
Qed.

(* Under a successful verification pass (or on the fallback path), a
   None answer means x is no key. *)
Lemma query_none : forall e f n ok t x,
  query e f n ok t x = None ->
  (ok = true -> forall j, ((φ j) < (φ n))%Z -> (t_slot t).[pos t f.[j]] = j + 1) ->
  forall j, ((φ j) < (φ n))%Z -> f.[j] <> x.
Proof.
  intros e f n ok t x Hq Hinv j Hj Ej.
  rewrite query_unfold in Hq. cbv zeta in Hq.
  destruct ok.
  - specialize (Hinv eq_refl j Hj). rewrite Ej in Hinv. rewrite Hinv in Hq.
    replace (j + 1 - 1) with j in Hq by (apply to_Z_inj; sia).
    rewrite (answer_at_found e f n j x Hj Ej) in Hq. discriminate.
  - destruct (scan_loop_spec f x n _ 0 (Zwf_well_founded 0 (gap n 0)) eq_refl)
      as [[L E] | R].
    + rewrite ltb_spec in L.
      rewrite (answer_at_found e f n _ x L E) in Hq. discriminate.
    + apply (R j); [change (φ 0) with 0%Z; pose proof (to_Z_bounded j); lia | exact Ej].
Qed.

(* The output loop. *)
Lemma olength_set : forall (t : array (option pstr)) (i : int) b,
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set _ t i b). Qed.

Lemma oget_set_same : forall (t : array (option pstr)) (i : int) b,
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same _ t i b H). Qed.

Lemma oget_set_other : forall (t : array (option pstr)) (i j : int) b,
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other _ t i j b H). Qed.

Lemma fill_loop_spec : forall e f m n ok t L z k out H,
  gap L k = z -> PArray.length out = L -> ((φ k) <= (φ L))%Z ->
  (forall k', ((φ k') < (φ k))%Z -> out.[k'] = query e f n ok t m.[k']) ->
  PArray.length (fill_loop e f m n ok t L k out H) = L
  /\ forall k', ((φ k') < (φ L))%Z ->
     (fill_loop e f m n ok t L k out H).[k'] = query e f n ok t m.[k'].
Proof.
  intros e f m n ok t L z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k out H Hz Hlen Hkl Hinv.
  rewrite fill_loop_eq.
  destruct (bdec (k <? L)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + rewrite olength_set. exact Hlen.
    + lia.
    + intros k' Hk''. rewrite Hk1 in Hk''.
      destruct (Z.eq_dec (φ k') (φ k)) as [E | E].
      * assert (k' = k) by (apply to_Z_inj; exact E). subst k'.
        apply oget_set_same. rewrite Hlen. exact Hk.
      * rewrite oget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    split; [exact Hlen |].
    intros k' Hk'. apply Hinv. lia.
Qed.

(* Strings: a primitive string represents one math string, and a math
   string is represented by one primitive string. *)
Lemma sget_none : forall (s : String.string) n,
  (String.length s <= n)%nat -> String.get n s = None.
Proof.
  induction s as [| c s IH]; intros n H; [destruct n; reflexivity |].
  destruct n; simpl in *; [lia | apply IH; lia].
Qed.

Lemma repr_str_fun : forall (x : pstr) (w1 w2 : String.string),
  repr x w1 -> repr x w2 -> w1 = w2.
Proof.
  intros x w1 w2 [L1 C1] [L2 C2]. apply String.get_correct. intros k.
  destruct (Nat.lt_ge_cases k (String.length w1)) as [Hk | Hk].
  - destruct (C1 k Hk) as (c1 & G1 & R1).
    destruct (C2 k ltac:(lia)) as (c2 & G2 & R2).
    rewrite G1, G2. f_equal.
    unfold repr, repr_uint in R1, R2.
    rewrite <- (Ascii.ascii_N_embedding c1), <- (Ascii.ascii_N_embedding c2).
    congruence.
  - rewrite !sget_none by lia. reflexivity.
Qed.

Lemma repr_str_inj : forall (x y : pstr) (w : String.string),
  repr x w -> repr y w -> x = y.
Proof.
  intros x y w [Lx Cx] [Ly Cy]. apply PString.string_eq_ext. split.
  - apply to_Z_inj. lia.
  - intros i Hi.
    destruct (Cx (Z.to_nat (φ i)) ltac:(lia)) as (c1 & G1 & R1).
    destruct (Cy (Z.to_nat (φ i)) ltac:(lia)) as (c2 & G2 & R2).
    rewrite G1 in G2. injection G2 as <-.
    unfold repr, repr_uint in R1, R2.
    rewrite of_nat_to_nat in R1, R2.
    apply to_Z_inj.
    pose proof (to_Z_bounded (PrimString.get x i)).
    pose proof (to_Z_bounded (PrimString.get y i)).
    apply Z2N.inj; [lia | lia | congruence].
Qed.

(* Arrays of strings. *)
Lemma repr_len : forall (a : array pstr) (l : list String.string),
  repr a l -> (φ (PArray.length a)) = Z.of_nat (List.length l).
Proof. intros a l [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_cell : forall (a : array pstr) (l : list String.string),
  repr a l -> forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  exists w, nth_error l (Z.to_nat (φ i)) = Some w /\ repr a.[i] w.
Proof.
  intros a l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (w & Hw & Hr).
  exists w. split; [exact Hw |].
  rewrite of_nat_to_nat in Hr. exact Hr.
Qed.

(* One query: its result represents an answer accepted by the spec. *)
Lemma query_answer : forall (english foreign : list String.string)
    (e f : array pstr) ok t (x : pstr) (xm : String.string),
  NoDup foreign -> List.length english = List.length foreign ->
  repr e english -> repr f foreign -> repr x xm ->
  (ok = true -> forall j, ((φ j) < (φ (PArray.length f)))%Z ->
     (t_slot t).[pos t f.[j]] = j + 1) ->
  exists o, repr (query e f (PArray.length f) ok t x) o
            /\ answer english foreign xm o.
Proof.
  intros english foreign e f ok t x xm Hnd Hlen He Hf Hx Hinv.
  pose proof (repr_len f foreign Hf) as Ln.
  destruct (query e f (PArray.length f) ok t x) as [y |] eqn:Q.
  - destruct (query_some _ _ _ _ _ _ _ Q) as (i & Hi & Fi & Ey).
    destruct (repr_cell e english He i ltac:(lia)) as (we & Ge & Re).
    destruct (repr_cell f foreign Hf i ltac:(lia)) as (wf & Gf & Rf).
    exists (Some we). split; [subst y; exact Re |].
    assert (Rf' : repr x wf) by (rewrite <- Fi; exact Rf).
    assert (wf = xm) by exact (repr_str_fun _ _ _ Rf' Hx).
    subst wf.
    intros w. split.
    + intros E. injection E as <-. exists (N.of_nat (Z.to_nat (φ i))).
      unfold at_. rewrite Nat2N.id. split; assumption.
    + intros (i' & G1 & G2). unfold at_ in G1, G2.
      assert (Hb : (N.to_nat i' < List.length foreign)%nat)
        by (apply nth_error_Some; congruence).
      assert (E : N.to_nat i' = Z.to_nat (φ i)).
      { apply (proj1 (NoDup_nth_error foreign) Hnd); [exact Hb | congruence]. }
      rewrite E in G2. congruence.
  - exists None. split; [exact I |].
    intros w. split; [discriminate |].
    intros (i' & G1 & G2). exfalso. unfold at_ in G1.
    assert (Hb : (N.to_nat i' < List.length foreign)%nat)
      by (apply nth_error_Some; congruence).
    pose proof (to_Z_bounded (PArray.length f)) as Bf.
    assert (Hj : (φ (of_Z (Z.of_nat (N.to_nat i')))) = Z.of_nat (N.to_nat i'))
      by (apply phi_of_nat; lia).
    destruct (repr_cell f foreign Hf (of_Z (Z.of_nat (N.to_nat i'))) ltac:(lia))
      as (wf & Gf & Rf).
    rewrite Hj, Nat2Z.id, G1 in Gf. injection Gf as <-.
    apply (query_none e f (PArray.length f) ok t x Q Hinv
             (of_Z (Z.of_nat (N.to_nat i')))); [lia |].
    exact (repr_str_inj _ _ _ Rf Hx).
Qed.

(* Lists from their cells. *)
Lemma build_list : forall {B : Type} (P : nat -> B -> Prop) n,
  (forall k, (k < n)%nat -> exists b, P k b) ->
  exists l : list B, List.length l = n /\
    forall k, (k < n)%nat -> exists b, nth_error l k = Some b /\ P k b.
Proof.
  intros B P n. induction n as [| n IH]; intros Hex.
  - exists []. split; [reflexivity | intros; lia].
  - destruct IH as (l & Hl & Hc); [intros k Hk; apply Hex; lia |].
    destruct (Hex n ltac:(lia)) as (b & Hb).
    exists (l ++ [b]). split; [rewrite length_app; simpl; lia |].
    intros k Hk. destruct (Nat.lt_ge_cases k n) as [Hkn | Hkn].
    + destruct (Hc k Hkn) as (b' & G & Pb). exists b'.
      rewrite nth_error_app1 by lia. split; assumption.
    + assert (k = n) by lia. subst k. exists b.
      rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. split; [reflexivity | exact Hb].
Qed.

Lemma Forall2_nth_intro : forall {A B} (R : A -> B -> Prop) l1 l2,
  List.length l1 = List.length l2 ->
  (forall k a b, nth_error l1 k = Some a -> nth_error l2 k = Some b -> R a b) ->
  Forall2 R l1 l2.
Proof.
  intros A B R l1. induction l1 as [| a l1 IH]; intros [| b l2] Hl Hn;
    simpl in Hl; try discriminate; constructor.
  - apply (Hn 0%nat); reflexivity.
  - apply IH; [lia |]. intros k. apply (Hn (S k)).
Qed.

Lemma babelfish_impl_correct :
  forall (english foreign message : list String.string)
         (e f m : array pstr),
  valid_input english foreign message ->
  repr e english -> repr f foreign -> repr m message ->
  exists out : list (option String.string),
    repr (babelfish_impl e f m) out /\ babelfish_spec english foreign message out.
Proof.
  intros english foreign message e f m Hv He Hf Hm.
  destruct Hv as [Hen _ _ _ _ _ Hnd].
  unfold len in Hen. apply Nat2N.inj in Hen.
  pose proof (repr_len m message Hm) as Lm.
  unfold babelfish_impl.
  set (n := PArray.length f).
  set (t := build f n).
  set (ok := check_loop t f n 0 (Zwf_well_founded 0 (gap n 0))).
  set (L := PArray.length m).
  assert (LmL : (φ L) = Z.of_nat (List.length message)) by exact Lm.
  assert (Hok : ok = true -> forall j, ((φ j) < (φ (PArray.length f)))%Z ->
                  (t_slot t).[pos t f.[j]] = j + 1).
  { intros E j Hj.
    apply (check_loop_spec t f n _ 0 (Zwf_well_founded 0 (gap n 0)) eq_refl E).
    change (φ 0) with 0%Z. pose proof (to_Z_bounded j). fold n in Hj. lia. }
  assert (HmL : PArray.length (PArray.make L (@None pstr)) = L).
  { rewrite length_make. pose proof (leb_length _ m) as B. fold L in B.
    replace (L <=? max_length) with true by (symmetry; exact B).
    reflexivity. }
  destruct (fill_loop_spec e f m n ok t L _ 0 (PArray.make L None)
              (Zwf_well_founded 0 (gap L 0)) eq_refl HmL
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded L); lia)
              ltac:(intros k' Hk'; change (φ 0) with 0%Z in Hk';
                    pose proof (to_Z_bounded k'); lia))
    as [Hrl Hrc].
  set (r := fill_loop e f m n ok t L 0 (PArray.make L None)
              (Zwf_well_founded 0 (gap L 0))) in *.
  destruct (build_list
              (fun k o => repr r.[of_Z (Z.of_nat k)] o /\
                 forall xm, nth_error message k = Some xm ->
                   answer english foreign xm o)
              (List.length message)) as (outl & Hol & Hon).
  { intros k Hk.
    pose proof (to_Z_bounded L) as BL.
    assert (Hkk : (φ (of_Z (Z.of_nat k))) = Z.of_nat k) by (apply phi_of_nat; lia).
    destruct (repr_cell m message Hm (of_Z (Z.of_nat k)) ltac:(lia))
      as (xm & Gm & Rm).
    rewrite Hkk, Nat2Z.id in Gm.
    rewrite Hrc by lia.
    destruct (query_answer english foreign e f ok t _ xm Hnd Hen He Hf Rm Hok)
      as (o & Ro & Ao).
    exists o. split; [exact Ro |].
    intros xm' G'. rewrite Gm in G'. injection G' as <-. exact Ao. }
  exists outl. split.
  - assert (A1 : Z.of_nat (List.length outl) = (φ (PArray.length r)))
      by (rewrite Hrl, Hol; lia).
    assert (A2 : forall k : nat, (k < List.length outl)%nat ->
              exists o, nth_error outl k = Some o /\ repr r.[of_Z (Z.of_nat k)] o).
    { intros k Hk. rewrite Hol in Hk. destruct (Hon k Hk) as (o & G & Ro & _).
      exists o. split; assumption. }
    exact (conj A1 A2).
  - unfold babelfish_spec. apply Forall2_nth_intro; [symmetry; exact Hol |].
    intros k xm o Gm Go.
    assert (Hk : (k < List.length message)%nat)
      by (apply nth_error_Some; congruence).
    destruct (Hon k Hk) as (o' & G & _ & Ao).
    rewrite Go in G. injection G as <-. exact (Ao xm Gm).
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition babelfish :
  array PrimString.string -> array PrimString.string ->
  array PrimString.string -> array (option PrimString.string)
  := babelfish_impl.

Definition babelfish_correct :
  forall (english foreign message : list String.string)
         (e f m : array PrimString.string),
  valid_input english foreign message ->
  repr e english -> repr f foreign -> repr m message ->
  exists out : list (option String.string),
    repr (babelfish e f m) out /\ babelfish_spec english foreign message out
  := babelfish_impl_correct.
