(* Executable implementation and its required termination dependencies.
   Correctness proofs are in convexhull_proofs.v. *)
(* Implementation of convexhull (convexhull.spec): Andrew's monotone
   chain.  See README.md, section Implementation. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope bool_scope.
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

Lemma down_dec : forall j : int, (0 <? j) = true -> Zwf 0 (φ (j - 1)) (φ j).
Proof.
  intros j H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

Lemma pop_dec : forall (lim k : int) (b : bool),
  ((lim <? k) && b) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros lim k b H. apply andb_prop in H. destruct H as [H _].
  rewrite ltb_spec in H. pose proof (to_Z_bounded lim).
  unfold Zwf. sia.
Qed.

Definition min_i (a b : int) : int := if a <? b then a else b.

Lemma pass_dec : forall n lo w : int,
  (lo <? min_i (lo + w + w) n) = true ->
  Zwf 0 (gap n (min_i (lo + w + w) n)) (gap n lo).
Proof.
  intros n lo w H. unfold Zwf, gap, min_i in *.
  destruct (lo + w + w <? n) eqn:E; rewrite ltb_spec in *; lia.
Qed.

Definition mz (n w : int) : Z := Z.max 0 ((φ n) - (φ w)).

Lemma sort_dec : forall n w : int,
  ((w <? n) && (w <? w + w)) = true -> Zwf 0 (mz n (w + w)) (mz n w).
Proof.
  intros n w H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, mz. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Twice the signed area of the triangle of the points of indices a b c. *)
Definition cross_m (x y : array int) (a b c : int) : int :=
  let xa := x.[a] in
  let ya := y.[a] in
  (x.[b] - xa) * (y.[c] - ya) - (y.[b] - ya) * (x.[c] - xa).

(* Lexicographic (x, y) comparison of the points of indices a and b. *)
Definition le_pt (x y : array int) (a b : int) : bool :=
  let xa := x.[a] in
  let xb := x.[b] in
  if Sint63.ltb xa xb then true
  else if xa =? xb then Sint63.leb y.[a] y.[b] else false.

Definition take_left (x y src : array int) (mid hi i j : int) : bool :=
  if i <? mid then (if j <? hi then le_pt x y src.[i] src.[j] else true)
  else false.

(* Merge the sorted runs src[i, mid) and src[j, hi) into dst[k, hi). *)
Fixpoint merge (x y src : array int) (mid hi i j k : int) (dst : array int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if take_left x y src mid hi i j
      then merge x y src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
             (Acc_inv H (dec_step hi k Hk))
      else merge x y src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
             (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* One pass of the bottom-up merge sort: runs of width w into runs of
   width 2w, from src into dst, blocks lo, lo + 2w, ... *)
Fixpoint pass (x y src : array int) (w n lo : int) (dst : array int)
    (H : Acc (Zwf 0) (gap n lo)) {struct H} : array int :=
  match bdec (lo <? min_i (lo + w + w) n) with
  | left Hl =>
      pass x y src w n (min_i (lo + w + w) n)
        (merge x y src (min_i (lo + w) n) (min_i (lo + w + w) n)
           lo (min_i (lo + w) n) lo dst
           (Zwf_well_founded 0 (gap (min_i (lo + w + w) n) lo)))
        (Acc_inv H (pass_dec n lo w Hl))
  | right _ => dst
  end.

Fixpoint sortl (x y : array int) (n w : int) (src dst : array int)
    (H : Acc (Zwf 0) (mz n w)) {struct H} : array int :=
  match bdec ((w <? n) && (w <? w + w)) with
  | left Hw =>
      sortl x y n (w + w)
        (pass x y src w n 0 dst (Zwf_well_founded 0 (gap n 0))) src
        (Acc_inv H (sort_dec n w Hw))
  | right _ => src
  end.

Fixpoint initl (n i : int) (a : array int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => initl n (i + 1) a.[i <- i] (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.

(* The indices 0 .. n-1 sorted by (x, y). *)
Definition msort (x y : array int) (n : int) : array int :=
  sortl x y n 1
    (initl n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)))
    (PArray.make n 0) (Zwf_well_founded 0 (mz n 1)).

(* Pop the stack st[0, k) while it has more than lim cells and its two
   top points do not turn strictly left towards q. *)
Fixpoint pop (x y st : array int) (lim k q : int) (H : Acc (Zwf 0) (φ k))
    {struct H} : int :=
  match bdec ((lim <? k) && Sint63.leb (cross_m x y st.[k - 2] st.[k - 1] q) 0)
  with
  | left Hc => pop x y st lim (k - 1) q (Acc_inv H (pop_dec lim k _ Hc))
  | right _ => k
  end.

(* The lower chain: sorted positions i .. n-1. *)
Fixpoint lower (x y ord st : array int) (n k i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * int :=
  match bdec (i <? n) with
  | left Hi =>
      let q := ord.[i] in
      let k' := pop x y st 1 k q (Zwf_well_founded 0 (φ k)) in
      lower x y ord st.[k' <- q] n (k' + 1) (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => (st, k)
  end.

(* The upper chain: sorted positions j-1 down to 0, above the lim cells
   of the lower chain. *)
Fixpoint upper (x y ord st : array int) (lim k j : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : array int * int :=
  match bdec (0 <? j) with
  | left Hj =>
      let q := ord.[j - 1] in
      let k' := pop x y st lim k q (Zwf_well_founded 0 (φ k)) in
      upper x y ord st.[k' <- q] lim (k' + 1) (j - 1) (Acc_inv H (down_dec j Hj))
  | right _ => (st, k)
  end.

Fixpoint copyl (src dst : array int) (h i : int) (H : Acc (Zwf 0) (gap h i))
    {struct H} : array int :=
  match bdec (i <? h) with
  | left Hi => copyl src dst.[i <- src.[i]] h (i + 1) (Acc_inv H (dec_step h i Hi))
  | right _ => dst
  end.

Definition hull (x y : array sint) : array uint :=
  let n := PArray.length x in
  let ord := msort x y n in
  let a := ord.[0] in
  let b := ord.[n - 1] in
  if (x.[a] =? x.[b]) && (y.[a] =? y.[b]) then PArray.make 1 a
  else
    let '(st1, l) := lower x y ord (PArray.make (n + n) 0).[0 <- a] n 1 1
                       (Zwf_well_founded 0 (gap n 1)) in
    let '(st2, k) := upper x y ord st1 l l (n - 1)
                       (Zwf_well_founded 0 (φ (n - 1))) in
    copyl st2 (PArray.make (k - 1) 0) (k - 1) 0
      (Zwf_well_founded 0 (gap (k - 1) 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition convex_hull : array sint -> array sint -> array uint := hull.
