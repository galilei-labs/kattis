(* Executable implementation and its required termination dependencies.
   Correctness proofs are in tugofwar_proofs.v. *)
(* Implementation of tugofwar (tugofwar.spec): subset-sum dynamic
   programming with a team-size dimension.

   Code.  [tugofwar a] computes the total weight S (one pass), then fills a
   flat boolean table of (K+1) rows of W cells, K = n - n/2 (the larger
   balanced team size) and W = S/2 + 1: cell c*W + s says that some set of
   exactly c of the people processed so far weighs exactly s.  The people
   are processed one by one (from the last to the first); for a person of
   weight x, the rows are updated from c = K down to 1, and in row c the
   cells s = x .. W-1 receive  cell(c-1, s-x)  (an or): since the rows go
   downwards, row c-1 still holds the previous person's values, so the
   update is in place.  The answer is the largest s <= S/2 reachable with
   n/2 or n - n/2 people: (s, S - s).

   Proof.  [reachZ l c s]: some choice of people of l has c people and
   weight s.  The table invariant [Tbl] says each cell is reachZ of the
   suffix of the people processed so far; [reach_cons] is the recurrence.
   A division of the people with balanced team sizes has a team of n/2 or
   n - n/2 people; either that team or the other weighs at most S/2, which
   gives optimality of the largest reachable s <= S/2.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (the template's device).  No nat, no Z, no list in
   the code. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
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

Definition dist (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (dist m (i + 1)) (dist m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, dist. lia.
Qed.

Lemma dec_down : forall i : int,
  (0 <? i) = true -> Zwf 0 (φ (i - 1)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* acc + a.[0] + ... + a.[i-1] *)
Fixpoint sum_loop (a : array uint) (i acc : int)
    (H : Acc (Zwf 0) (φ i)) {struct H} : int :=
  match bdec (0 <? i) with
  | left Hi => sum_loop a (i - 1) (acc + a.[i - 1]) (Acc_inv H (dec_down i Hi))
  | right _ => acc
  end.

(* row c, cells s .. W-1: cell (c, s) |= cell (c-1, s-x) *)
Fixpoint cell_loop (t : array bool) (W x c s : int)
    (H : Acc (Zwf 0) (dist W s)) {struct H} : array bool :=
  match bdec (s <? W) with
  | left Hs =>
      cell_loop (if t.[(c - 1) * W + (s - x)] then t.[c * W + s <- true] else t)
        W x c (s + 1) (Acc_inv H (dec_step W s Hs))
  | right _ => t
  end.

(* rows c, c-1, ..., 1, for a person of weight x *)
Fixpoint row_loop (t : array bool) (W x c : int)
    (H : Acc (Zwf 0) (φ c)) {struct H} : array bool :=
  match bdec (0 <? c) with
  | left Hc =>
      row_loop (cell_loop t W x c x (Zwf_well_founded 0 (dist W x)))
        W x (c - 1) (Acc_inv H (dec_down c Hc))
  | right _ => t
  end.

(* people i-1, i-2, ..., 0 *)
Fixpoint item_loop (a : array uint) (t : array bool) (W K i : int)
    (H : Acc (Zwf 0) (φ i)) {struct H} : array bool :=
  match bdec (0 <? i) with
  | left Hi =>
      item_loop a (row_loop t W a.[i - 1] K (Zwf_well_founded 0 (φ K)))
        W K (i - 1) (Acc_inv H (dec_down i Hi))
  | right _ => t
  end.

(* the largest s' <= s reachable with h or K people *)
Fixpoint best_loop (t : array bool) (W h K s : int)
    (H : Acc (Zwf 0) (φ s)) {struct H} : int :=
  if t.[h * W + s] || t.[K * W + s] then s
  else
    match bdec (0 <? s) with
    | left Hs => best_loop t W h K (s - 1) (Acc_inv H (dec_down s Hs))
    | right _ => 0
    end.

Definition tugofwar_impl (a : array uint) : uint * uint :=
  let n := PArray.length a in
  let S := sum_loop a n 0 (Zwf_well_founded 0 (φ n)) in
  let half := S / 2 in
  let W := half + 1 in
  let h := n / 2 in
  let K := n - h in
  let t0 := (PArray.make ((K + 1) * W) false).[0 <- true] in
  let t := item_loop a t0 W K n (Zwf_well_founded 0 (φ n)) in
  let b := best_loop t W h K half (Zwf_well_founded 0 (φ half)) in
  (b, S - b).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition tugofwar : array uint -> uint * uint := tugofwar_impl.
