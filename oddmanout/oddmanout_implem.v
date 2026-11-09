(* Executable implementation and its required termination dependencies.
   Correctness proofs are in oddmanout_proofs.v. *)
(* Implementation of oddmanout (oddmanout.spec): XOR fold.

   Code.  [odd_one a] folds [Uint63.lxor] over the cells of [a], left to
   right, into one [int] accumulator started at 0.  One [PArray.get] per
   cell, no [set], no allocation.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap n i)] proof, the shape of the template's loops.

   Proof.  On the math side, [xorl l = fold_left N.lxor l 0].  The loop
   computes [xorl l] (invariant over [skipn i l]); the key lemma
   [xorl_unique_odd] shows by strong induction on the length (peeling all
   occurrences of the head with [remove]) that when every value other than
   v has even multiplicity, [xorl l] is v or 0 according to the parity of
   v's multiplicity; [vi_one_alone] then gives [xorl l = v]. *)

From Oddmanout.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
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

(* acc lxor a.[i] lxor ... lxor a.[n-1] *)
Fixpoint xor_loop (a : array int) (n i acc : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi => xor_loop a n (i + 1) (acc lxor a.[i]) (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.

Definition odd_one_impl (a : array uint) : uint :=
  xor_loop a (PArray.length a) 0 0 (Zwf_well_founded 0 (gap (PArray.length a) 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition odd_one : array uint -> uint := odd_one_impl.
