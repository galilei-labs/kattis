(* Executable implementation and its required termination dependencies.
   Correctness proofs are in intervalcover_proofs.v. *)
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
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
From Flocq Require Core.Core.
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

(* Guard of the two recursions: lo < hi and hi - lo > c. *)
Definition guard (c lo hi : int) : bool := (lo <? hi) && (c <? hi - lo).

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

Definition merge (key : array float) (lo mid hi : int) (A T : array int) : array int :=
  let '(_, _, T) := loop hi (fun _ _ => true) (merge_step key A mid hi) lo (lo, mid, T) in T.

Definition copy_step (k : int) (st : array int * array int) : array int * array int :=
  let '(A, T) := st in (A.[k <- T.[k]], T).

Definition merge_copy (key : array float) (lo mid hi : int) (A T : array int)
    : array int * array int :=
  let T := merge key lo mid hi A T in
  loop hi (fun _ _ => true) copy_step lo (A, T).

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

Definition iota_step (k : int) (P : array int) : array int := P.[k <- k].

(* The sweep, one round: from position q of the sorted index array P,
   scan the intervals whose left end is at most cur, keeping the largest
   right end (found, best, its index); the state carries the position
   reached. *)
Definition scan_cont (ls : array float) (P : array int) (cur : float)
    (p : int) (st : int * bool * float * int) : bool :=
  (ls.[P.[p]] <=? cur)%float.

Definition scan_step (rs : array float) (P : array int)
    (p : int) (st : int * bool * float * int) : int * bool * float * int :=
  let '(_, f, best, bi) := st in
  let i := P.[p] in
  let r := rs.[i] in
  if (best <=? r)%float then (p + 1, true, r, i) else (p + 1, f, best, bi).

Definition adv (n q q' : int) : bool := (q <? q') && (q' <=? n).

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

Definition copy_out (W : array int) (k : int) (O : array int) : array int := O.[k <- W.[k]].

Definition cover (x y : float) (ls rs : array float) : option (array uint) :=
  let n := PArray.length ls in
  let P := loop n (fun _ _ => true) iota_step 0 (PArray.make n 0) in
  let '(P, _) := msort_rec ls 0 n P (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  match sweep ls rs y P n 0 0 x (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) with
  | Some (W, k) => Some (loop k (fun _ _ => true) (copy_out W) 0 (PArray.make k 0))
  | None => None
  end.
