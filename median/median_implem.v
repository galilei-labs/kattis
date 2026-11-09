(* Executable implementation and its required termination dependencies.
   Correctness proofs are in median_proofs.v. *)
(* Implementation of median (median.spec): randomized selection
   (CLRS 9.2) in place on one flat copy of the input.

   Code.  [median x] copies x, then [sel] selects position k = n / 2:
   on the range [lo, hi) holding k it draws a pivot value x = y.[p], p in
   [lo, hi) from a 63-bit linear congruential generator, and runs two
   Lomuto passes ([part]): the first moves the cells < x to the front of
   [lo, hi) (boundary i), the second the cells <= x to the front of
   [i, hi) (boundary m), so [lo, i) < x, [i, m) = x, [m, hi) > x.  It
   recurses into [lo, i) or [m, hi), whichever holds k, and stops when k
   falls in [i, m) (the three-way split keeps inputs with many equal
   values linear).  For odd n the answer is y.[k]; for even n the lower
   middle element is the maximum of the left part [0, k) ([maxl]), and the
   answer is (w + u) / 2 computed as of_uint63 (w + u) / 2. in floats,
   exact (w + u <= 2*10^9 < 2^53, and halving is exact).  All indices and
   values are Uint63 ints; no Z, no nat in the code.

   Termination: every loop recurses on an erased [Acc (Zwf 0) (gap _ _)]
   proof, as in template/polymul1; [sel]'s two recursive calls are guarded
   by tests (i < hi, lo < m) that the proof shows always true.

   Proof.  The cells are read on the math side as [cell y t : N]; [seg]
   is the list of a range of cells.  A swap permutes the range
   ([perm_tau]: a transposition of positions); [part_spec] keeps the range
   a permutation of itself and the rest untouched; [sel_spec] keeps the
   invariant that every cell left of lo is <= every cell from lo on, and
   every cell left of hi <= every cell from hi on, and ends with position
   k having nothing larger before it and nothing smaller after it.  [kth]
   turns this into "position k of the sorted permutation" by counting the
   cells < v and <= v ([sorted_nth], [cnt_perm]).  For even n, swapping
   the maximum of [0, k) into position k-1 gives the same property at
   k - 1. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr ReprFloat.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Stdlib Require Import Sorted Permutation ZifyUint63 Lia Lra Zwf.
From Stdlib Require Import FinFun.
From Flocq Require Core.Core.
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
  intros m i H. rewrite Uint63.ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_left : forall lo hi i : int,
  (lo <? hi) = true -> (i <? hi) = true -> Zwf 0 (gap i lo) (gap hi lo).
Proof.
  intros lo hi i H1 H2. rewrite Uint63.ltb_spec in H1, H2. unfold Zwf, gap. lia.
Qed.

Lemma dec_right : forall lo hi m : int,
  (lo <? hi) = true -> (lo <? m) = true -> Zwf 0 (gap hi m) (gap hi lo).
Proof.
  intros lo hi m H1 H2. rewrite Uint63.ltb_spec in H1, H2. unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* y with cell j set to v (= y.[j]) and cell i to y.[j]'s former partner:
   the exchange of cells i and j, both reads before the writes. *)
Definition swap_with (y : array int) (i j v : int) : array int :=
  let w := y.[i] in y.[i <- v].[j <- w].

(* the partition test: v < x (strict) or v <= x *)
Definition tst (strict : bool) (x v : int) : bool :=
  if strict then v <? x else v <=? x.

(* Lomuto partition of the cells [j, hi) given that [i0, i) pass the test
   and [i, j) fail it: returns the array and the boundary i'. *)
Fixpoint part (strict : bool) (x hi : int) (y : array int) (i j : int)
    (H : Acc (Zwf 0) (gap hi j)) {struct H} : array int * int :=
  match bdec (j <? hi) with
  | left Hj =>
      let v := y.[j] in
      if tst strict x v
      then part strict x hi (swap_with y i j v) (i + 1) (j + 1)
             (Acc_inv H (dec_step hi j Hj))
      else part strict x hi y i (j + 1) (Acc_inv H (dec_step hi j Hj))
  | right _ => (y, i)
  end.

(* the pseudo-random generator: a 63-bit linear congruential step *)
Definition lcg (s : int) : int := s * 6364136223846793005 + 1442695040888963407.

(* Select position k inside [lo, hi): a random pivot x of [lo, hi), then
   two Lomuto passes split [lo, hi) into < x, = x, > x; recurse into the
   side holding k, stop when k falls among the cells equal to x. *)
Fixpoint sel (k : int) (y : array int) (lo hi seed : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int :=
  match bdec (lo <? hi) with
  | left Hlh =>
      let s := lcg seed in
      let x := y.[lo + (s >> 17) mod (hi - lo)] in
      let (y1, i) := part true x hi y lo lo (Zwf_well_founded 0 (gap hi lo)) in
      let (y2, m) := part false x hi y1 i i (Zwf_well_founded 0 (gap hi i)) in
      if k <? i then
        match bdec (i <? hi) with
        | left Hi => sel k y2 lo i s (Acc_inv H (dec_left lo hi i Hlh Hi))
        | right _ => y2
        end
      else if k <? m then y2
      else
        match bdec (lo <? m) with
        | left Hm => sel k y2 m hi s (Acc_inv H (dec_right lo hi m Hlh Hm))
        | right _ => y2
        end
  | right _ => y
  end.

(* the maximum of acc and the cells [j, k) *)
Fixpoint maxl (y : array int) (k j acc : int)
    (H : Acc (Zwf 0) (gap k j)) {struct H} : int :=
  match bdec (j <? k) with
  | left Hj =>
      let v := y.[j] in
      maxl y k (j + 1) (if acc <? v then v else acc) (Acc_inv H (dec_step k j Hj))
  | right _ => acc
  end.

Definition seed0 : int := 88172645463325252.

Definition median_impl (x : array uint) : float :=
  let n := PArray.length x in
  let k := n / 2 in
  let y := sel k (PArray.copy x) 0 n seed0 (Zwf_well_founded 0 (gap n 0)) in
  let u := y.[k] in
  if n mod 2 =? 1 then of_uint63 u
  else
    let w := maxl y k 1 y.[0] (Zwf_well_founded 0 (gap k 1)) in
    (of_uint63 (w + u) / of_uint63 2)%float.

(* ------------------------------------------------------------------ *)
(* The float result                                                    *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Local Close Scope R_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition median : array uint -> float := median_impl.
