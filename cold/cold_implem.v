(* Executable implementation and its required termination dependencies.
   Correctness proofs are in cold_proofs.v. *)
(* Implementation of cold (cold.spec): count the strictly negative
   entries of an array of signed words.

   Code.  [count_loop x n i acc] scans the indices i .. n-1 of x once, left
   to right, adding 1 to the Uint63 accumulator whenever the cell is below
   zero under the signed comparison [Sint63.ltb].  Nothing is allocated,
   each cell is read once.  No Z, no nat in the extracted code.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap n i)] proof, as in template/polymul1. *)

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

(* acc + the number of negative cells among x.[i] .. x.[n-1]. *)
Fixpoint count_loop (x : array int) (n i acc : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      count_loop x n (i + 1)
        (if Sint63.ltb x.[i] 0 then acc + 1 else acc)
        (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.

Definition count_negatives_impl (x : array sint) : uint :=
  let n := PArray.length x in
  count_loop x n 0 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition count_negatives : array sint -> uint := count_negatives_impl.
