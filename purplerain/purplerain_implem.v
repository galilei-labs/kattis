(* Executable implementation and its required termination dependencies.
   Correctness proofs are in purplerain_proofs.v. *)
(* Implementation of purplerain (purplerain.spec): maximum subarray in
   its single-scan form, on the prefix sums of R = +1, B = -1.

   Code.  [purplerain x] scans the string West to East once, keeping the
   running prefix sum P(k) = #R - #B of the first k sections (offset by n
   so that it stays a non-negative Uint63 word), the largest prefix sum seen
   so far with the FIRST index where it occurs, and the smallest one with
   the first index where it occurs.  The best |#R - #B| over a part is
   max P - min P, and the Westernmost optimal part is (a + 1, b) where a < b
   are the first indices of the maximum and of the minimum of P (in
   whichever order they come): no smaller start can reach an extreme with
   the other extreme after it, and the first occurrence of the other
   extreme is the smallest end.  One pass, O(1) extra memory, the string
   read in place with [PrimString.get].  No Z, no array.

   Termination: the scan recurses structurally on an erased
   [Acc (Zwf 0) (gap n k)] proof, as in template/polymul1. *)

From Purplerain.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf.
From Stdlib Require PrimString String.
From Stdlib Require Import Ascii.

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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Sections k .. n-1 still to read; p = n + P(k); mx = n + P(imx) the
   maximum of P(0..k), imx its first index; mn = n + P(imn) the minimum,
   imn its first index.  Byte 82 is 'R'. *)
Fixpoint scan (x : PrimString.string) (n k p mx imx mn imn : int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : int * int :=
  match bdec (k <? n) with
  | left Hk =>
      let p' := if PrimString.get x k =? 82 then p + 1 else p - 1 in
      let k' := k + 1 in
      if mx <? p' then
        scan x n k' p' p' k' mn imn (Acc_inv H (dec_step n k Hk))
      else if p' <? mn then
        scan x n k' p' mx imx p' k' (Acc_inv H (dec_step n k Hk))
      else
        scan x n k' p' mx imx mn imn (Acc_inv H (dec_step n k Hk))
  | right _ => (imx, imn)
  end.

Definition purplerain_impl (x : PrimString.string) : uint * uint :=
  let n := PrimString.length x in
  match scan x n 0 n n 0 n 0 (Zwf_well_founded 0 (gap n 0)) with
  | (a, b) => if a <? b then (a + 1, b) else (b + 1, a)
  end.

Definition purplerain : PrimString.string -> uint * uint := purplerain_impl.
