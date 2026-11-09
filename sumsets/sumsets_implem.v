(* Executable implementation and its required termination dependencies.
   Correctness proofs are in sumsets_proofs.v. *)
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

(* ------------------------------------------------------------------ *)
(* The hash: multiply-shift onto [0, cap)                              *)
(* ------------------------------------------------------------------ *)

Definition HA : int := 2177342782468422677.

Definition hash (cap s : int) : int := (((s * HA) >> 40) * cap) >> 23.

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

Fixpoint build_out (x : array int) (cap n i : int) (T : tbl)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : tbl :=
  match bdec (i <? n) with
  | left Hi =>
      build_out x cap n (i + 1)
        (build_in x cap n i (i + 1) T (Zwf_well_founded 0 (gap n (i + 1))))
        (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.

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

Definition sumsets_impl (x : array int) : option int :=
  let n := PArray.length x in
  let cap := ((n * (n - 1)) >> 1) + 1 in
  let T0 := Tbl (bmake cap 0) (bmake cap 0) (bmake cap 0) 0 in
  let T := build_out x cap n 0 T0 (Zwf_well_founded 0 (gap n 0)) in
  best_k x T cap n 0 false 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition sumsets : array sint -> option sint := sumsets_impl.
