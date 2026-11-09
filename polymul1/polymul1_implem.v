(* Executable implementation and its required termination dependencies.
   Correctness proofs are in polymul1_proofs.v. *)
(* Implementation of polymul1 (polymul1.spec): the schoolbook product,
   the double loop over the index pairs (i, j) of the two operands.

   Code.  [polymul x y] allocates the result [PArray.make L 0] with
   L = |x| + |y| - 1, then for i = 0 .. |x|-1 and j = 0 .. |y|-1 adds
   x.[i] * y.[j] into cell i + j (read the cell, set it: the result is
   threaded linearly, x and y are only read).  Every product and sum is a
   wrapping 63-bit operation: each cell holds its true coefficient modulo
   2^63, and since [valid_input] bounds every coefficient of the product
   to a signed 32-bit integer, the signed reading of the cell is the
   exact coefficient.  No Z, no list, no nat in the code.

   Termination: both loops recurse structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof (the template's device).

   Proof.  The loops are proven against the coefficient function
   [rows a b I k = sum_{i < I} a_i * b_{k-i}] (inner loop: row I done up
   to column J); the final cells are [conv a b k = rows a b |a| k].  The
   math product [pmul] (sum of shifted scaled copies of b) evaluates to
   eval a x * eval b x and has conv a b k as its k-th coefficient, so it
   is the witness of the existential. *)

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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Row i: for j, j+1, ..., lb-1, cell i + j of r receives ai * y.[j]. *)
Fixpoint row_loop (y : array int) (ai i lb j : int) (r : array int)
    (H : Acc (Zwf 0) (gap lb j)) {struct H} : array int :=
  match bdec (j <? lb) with
  | left Hj =>
      let k := i + j in
      row_loop y ai i lb (j + 1) r.[k <- r.[k] + ai * y.[j]]
        (Acc_inv H (dec_step lb j Hj))
  | right _ => r
  end.

(* Rows i, i+1, ..., la-1. *)
Fixpoint rows_loop (x y : array int) (la lb i : int) (r : array int)
    (H : Acc (Zwf 0) (gap la i)) {struct H} : array int :=
  match bdec (i <? la) with
  | left Hi =>
      rows_loop x y la lb (i + 1)
        (row_loop y x.[i] i lb 0 r (Zwf_well_founded 0 (gap lb 0)))
        (Acc_inv H (dec_step la i Hi))
  | right _ => r
  end.

Definition polymul_impl (x y : array sint) : array sint :=
  let la := PArray.length x in
  let lb := PArray.length y in
  if la =? 0 then PArray.make 0 0
  else if lb =? 0 then PArray.make 0 0
  else
    rows_loop x y la lb 0 (PArray.make (la + lb - 1) 0)
      (Zwf_well_founded 0 (gap la 0)).

(* ------------------------------------------------------------------ *)
(* Math side: the coefficient functions                                *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition polymul : array sint -> array sint -> array sint := polymul_impl.
