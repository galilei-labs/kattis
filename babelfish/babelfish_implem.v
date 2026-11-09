(* Executable implementation and its required termination dependencies.
   Correctness proofs are in babelfish_proofs.v. *)
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

From Babelfish.spec Require Import Prelude.
From StdGalilei Require Import repr.
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
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition babelfish :
  array PrimString.string -> array PrimString.string ->
  array PrimString.string -> array (option PrimString.string)
  := babelfish_impl.
