(* Executable implementation and its required termination dependencies.
   Correctness proofs are in polygonarea_proofs.v. *)
(* Implementation of polygonarea (polygonarea.spec): the shoelace formula,
   one left-to-right pass.

   Code.  [signed_area2 x y] with n = |x| runs i = 0 .. n-2 accumulating
   x.[i] * y.[i+1] - x.[i+1] * y.[i] in one int, then adds the closing term
   x.[n-1] * y.[0] - x.[0] * y.[n-1].  Both arrays are only read, nothing is
   allocated.  The arithmetic is wrapping 63-bit: every operation is exact
   modulo 2^63, and the contract bounds |shoelace| by 2 * 1000 * 10^8 < 2^62,
   so the word read through Sint63 is the exact sum.  No Z in the code.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof, as in template/polymul1. *)

From Polygonarea.spec Require Import Prelude.
From StdGalilei Require Import repr.
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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* acc + sum_{j = i}^{m - 1} (x.[j] * y.[j+1] - x.[j+1] * y.[j]), mod 2^63. *)
Fixpoint area_loop (x y : array int) (m i acc : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : int :=
  match bdec (i <? m) with
  | left Hi =>
      area_loop x y m (i + 1)
        (acc + x.[i] * y.[i + 1] - x.[i + 1] * y.[i])
        (Acc_inv H (dec_step m i Hi))
  | right _ => acc
  end.

Definition signed_area2_impl (x y : array sint) : sint :=
  let m := PArray.length x - 1 in
  let s := area_loop x y m 0 0 (Zwf_well_founded 0 (gap m 0)) in
  s + x.[m] * y.[0] - x.[0] * y.[m].

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition signed_area2 : array sint -> array sint -> sint := signed_area2_impl.
