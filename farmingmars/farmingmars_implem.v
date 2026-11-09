(* Executable implementation and its required termination dependencies.
   Correctness proofs are in farmingmars_proofs.v. *)
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
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
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

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition farmingmars : array float -> array uint -> array uint -> array bool := farm.
