(* Executable implementation and its required termination dependencies.
   Correctness proofs are in ada_proofs.v. *)
(* Implementation of ada (ada.spec): Newton's forward-difference table.

   Code.  [ada a] copies a into one flat array t of length n and runs
   n - 1 rounds in place: round k (k = 1 .. n-1) overwrites
   t[j] <- t[j+1] - t[j] for j = 0 .. n-1-k, so after round k the cells
   0 .. n-1-k hold the k-th differences and the cells above hold, each, the
   last entry of an earlier row: at the end t[i] is the last entry of row
   n-1-i.  While a round runs it records whether its row has a non-zero
   entry; d is the last round whose row is non-zero (0 if none).  The answer
   is (d, sum_{k=0}^{d} t[n-1-k]): the last entries of rows 0 .. d, which is
   the extension of the table by one column.  All arithmetic is wrapping
   63-bit; every difference and the sum are bounded by 2^10 * 2*10^6 in
   absolute value, so the words read through Sint63 are exact.  No Z, no
   nat in the code.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof, as in template/polymul1.

   Proof.  The math side models the table with [diffZ k g j] (k-th forward
   difference of g = nth _ v 0).  Over R, a polynomial of length <= k has
   zero k-th differences along x0, x0+h, ... ([diffR_poly], through the
   difference operator [dp] on coefficient lists); this gives minimality
   and, with Newton's identity [newton], the extrapolated value.  The
   existence of a polynomial of degree d goes through Newton-style
   interpolation on the first d+1 nodes ([interp]) and the propagation of
   the zero (d+1)-th row to all n values ([propagate]). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Reals Lra.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope Z_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition acopy (t : array int) : array int := PArray.copy t.

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
  (i <? m)%uint63 = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Section Program.
Local Open Scope uint63_scope.

(* One round: t[j] <- t[j+1] - t[j] for j = j .. m-1; nz records a
   non-zero new entry. *)
Fixpoint row_loop (m j : int) (t : array int) (nz : bool)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int * bool :=
  match bdec (j <? m) with
  | left Hj =>
      let x := t.[j + 1] - t.[j] in
      row_loop m (j + 1) t.[j <- x] (nz || negb (x =? 0))
        (Acc_inv H (dec_step m j Hj))
  | right _ => (t, nz)
  end.

(* Rounds k .. n-1; d is the last round with a non-zero row. *)
Fixpoint rows_loop (n k : int) (t : array int) (d : int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array int * int :=
  match bdec (k <? n) with
  | left Hk =>
      let r := row_loop (n - k) 0 t false (Zwf_well_founded 0 (gap (n - k) 0)) in
      rows_loop n (k + 1) (fst r) (if snd r then k else d)
        (Acc_inv H (dec_step n k Hk))
  | right _ => (t, d)
  end.

(* acc + sum_{q = k}^{e-1} t[top - q]. *)
Fixpoint sum_loop (t : array int) (top e k acc : int)
    (H : Acc (Zwf 0) (gap e k)) {struct H} : int :=
  match bdec (k <? e) with
  | left Hk => sum_loop t top e (k + 1) (acc + t.[top - k])
                 (Acc_inv H (dec_step e k Hk))
  | right _ => acc
  end.

Definition ada_impl (a : array sint) : uint * sint :=
  let n := PArray.length a in
  match rows_loop n 1 (acopy a) 0 (Zwf_well_founded 0 (gap n 1)) with
  | (t, d) => (d, sum_loop t (n - 1) (d + 1) 0 0
                    (Zwf_well_founded 0 (gap (d + 1) 0)))
  end.

End Program.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition ada : array sint -> uint * sint := ada_impl.
