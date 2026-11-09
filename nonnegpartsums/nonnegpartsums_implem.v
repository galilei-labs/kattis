(* Executable implementation and its required termination dependencies.
   Correctness proofs are in nonnegpartsums_proofs.v. *)
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

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
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

(* The prefix sum of index j of the doubled sequence (0 <= j <= 2n). *)
Definition qv (P : array int) (n tot j : int) : int :=
  if j <=? n then P.[j] else tot + P.[j - n].

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

Definition count_impl (x : array sint) : uint :=
  let n := PArray.length x in
  let P := prefix_loop x n 0 (PArray.make (n + 1) 0)
             (Zwf_well_founded 0 (gap n 0)) in
  let tot := P.[n] in
  sweep P n tot (n + n) 1 0 0 0 (PArray.make n 0)
    (Zwf_well_founded 0 (gap (n + n) 1)).

(* ------------------------------------------------------------------ *)
(* Math side                                                           *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition count_good_shifts : array sint -> uint := count_impl.
