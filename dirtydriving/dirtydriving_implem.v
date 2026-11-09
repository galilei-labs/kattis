(* Executable implementation and its required termination dependencies.
   Correctness proofs are in dirtydriving_proofs.v. *)
(* Implementation of dirtydriving (dirtydriving.spec).

   Code.  [dirtydriving p d] sorts the distances ascending with a top-down
   merge sort on flat arrays (the input array, threaded linearly, and one
   scratch buffer of length n: each merge writes the two sorted halves of
   [lo, hi) into the buffer, then copies [lo, hi) back), then makes one
   linear pass over the sorted array s computing
     max (0, max_k (p * (k + 1) + s.[0] - s.[k])),
   the least D with p * (k + 1) + s.[0] <= D + s.[k] for every k: in the
   sorted order the car s.[k] has exactly k cars between, and s.[0] is the
   car directly in front.  Everything is Uint63 arithmetic (the values stay
   below 20 * 100001 + 10^7).

   Termination: every loop and the sort recurse structurally on an erased
   [Acc (Zwf 0) (gap _ _)] proof, as in template/polymul1. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
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

(* A segment [lo, hi) is split when it has at least two cells. *)
Definition split_ok (lo hi : int) : bool := (lo <? hi) && (1 <? hi - lo).
Definition midp (lo hi : int) : int := lo + (hi - lo) / 2.

Lemma split_ok_spec : forall lo hi, split_ok lo hi = true ->
  ((φ lo) + 1 < (φ hi))%Z /\ (φ (midp lo hi)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z.
Proof.
  intros lo hi H. unfold split_ok in H. apply andb_prop in H.
  destruct H as [H1 H2]. rewrite ltb_spec in H1, H2.
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. change (φ 1) with 1%Z in H2.
  split; [lia|]. unfold midp. sia.
Qed.

Lemma dec_l : forall lo hi, split_ok lo hi = true ->
  Zwf 0 (gap (midp lo hi) lo) (gap hi lo).
Proof.
  intros lo hi H. destruct (split_ok_spec lo hi H) as [H1 H2].
  unfold Zwf, gap. rewrite H2. Z.to_euclidean_division_equations. lia.
Qed.

Lemma dec_r : forall lo hi, split_ok lo hi = true ->
  Zwf 0 (gap hi (midp lo hi)) (gap hi lo).
Proof.
  intros lo hi H. destruct (split_ok_spec lo hi H) as [H1 H2].
  unfold Zwf, gap. rewrite H2. Z.to_euclidean_division_equations. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Whether the merge takes the next cell from the left run [i, mid)
   rather than from the right run [j, hi). *)
Definition take_left (a : array int) (mid hi i j : int) : bool :=
  if i <? mid then (if j <? hi then a.[i] <=? a.[j] else true) else false.

(* Merges the sorted runs a[i, mid) and a[j, hi) into t[k, hi). *)
Fixpoint merge_loop (a t : array int) (mid hi i j k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if take_left a mid hi i j then
        merge_loop a t.[k <- a.[i]] mid hi (i + 1) j (k + 1)
          (Acc_inv H (dec_step hi k Hk))
      else
        merge_loop a t.[k <- a.[j]] mid hi i (j + 1) (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => t
  end.

(* Copies src[k, hi) into dst. *)
Fixpoint copy_loop (src dst : array int) (hi k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk => copy_loop src dst.[k <- src.[k]] hi (k + 1)
                 (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* Top-down merge sort of a[lo, hi), t being the scratch buffer. *)
Fixpoint msort (a t : array int) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int * array int :=
  match bdec (split_ok lo hi) with
  | left Hs =>
      let (a1, t1) := msort a t lo (midp lo hi) (Acc_inv H (dec_l lo hi Hs)) in
      let (a2, t2) := msort a1 t1 (midp lo hi) hi (Acc_inv H (dec_r lo hi Hs)) in
      let t3 := merge_loop a2 t2 (midp lo hi) hi lo (midp lo hi) lo
                  (Zwf_well_founded 0 (gap hi lo)) in
      (copy_loop t3 a2 hi lo (Zwf_well_founded 0 (gap hi lo)), t3)
  | right _ => (a, t)
  end.

(* The distance the car at sorted position k asks for:
   max (0, p * (k + 1) + s0 - x). *)
Definition need (p s0 x k : int) : int :=
  let t := p * (k + 1) + s0 in if x <? t then t - x else 0.

Fixpoint max_loop (s : array int) (p s0 n k acc : int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : int :=
  match bdec (k <? n) with
  | left Hk =>
      let v := need p s0 s.[k] k in
      max_loop s p s0 n (k + 1) (if acc <? v then v else acc)
        (Acc_inv H (dec_step n k Hk))
  | right _ => acc
  end.

Definition dirtydriving_impl (p : uint) (d : array uint) : uint :=
  let n := PArray.length d in
  let s := fst (msort d (PArray.make n 0) 0 n (Zwf_well_founded 0 (gap n 0))) in
  max_loop s p s.[0] n 0 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Segments of an array, as lists of Z                                 *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition dirtydriving : uint -> array uint -> uint := dirtydriving_impl.
