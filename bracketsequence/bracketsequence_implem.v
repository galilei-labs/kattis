(* Executable implementation and its required termination dependencies.
   Correctness proofs are in bracketsequence_proofs.v. *)
(* Implementation of bracketsequence (bracketsequence.spec): one
   left-to-right pass over the tokens with an explicit stack of
   accumulators.

   Code.  [loop] walks the token array once.  The state is the depth [d]
   (a uint, the index of the top frame), the operator [add] of the top
   level (true: addition, false: multiplication; it flips at every
   bracket) and the stack [stk], one flat [PArray] of uint, threaded
   linearly, frame [j] at cell [j].  A number is folded into the top
   frame, an open bracket pushes the identity of the next level's operator,
   a closing bracket pops the top frame and folds its value into the frame
   below with the operator of that level.  All arithmetic is modulo
   10^9+7 on residues, so no value exceeds 63 bits.  The stack has
   n + 1 cells (the depth never exceeds the number of tokens read).
   A closing bracket at depth 0 (impossible on a bracket sequence) leaves
   the state as is, so the code is total.

   Proof.  The machine state represents a math state (bool, top, below)
   (relation [R]); the math step function [step] and its iteration [run]
   over a token list are the Prop-side model.  [loop_spec] says that the
   loop computes the top of [run] on the remaining tokens.  [item_run] /
   [items_run], by nested induction on the item tree, say that running the
   tokens of an item folds its value (mod 10^9+7) into the top frame;
   hence on [seq_tokens s] the result is [seq_value s mod 10^9+7], for
   every [s] that spells the input.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap n i)] proof, as in template/polymul1. *)

From Bracketsequence.spec Require Import Prelude.
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

Definition Mi : int := 1000000007.

(* Fold v into the accumulator a with the operator of the level. *)
Definition opm (add : bool) (a v : int) : int :=
  if add then (a + v) mod Mi else (a * v) mod Mi.

(* The identity of the operator. *)
Definition idm (add : bool) : int := if add then 0 else 1.

Fixpoint loop (x : array (token uint)) (n i d : int) (add : bool)
    (stk : array int) (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      match x.[i] with
      | Num v =>
          loop x n (i + 1) d add stk.[d <- opm add stk.[d] v]
            (Acc_inv H (dec_step n i Hi))
      | Open =>
          loop x n (i + 1) (d + 1) (negb add) stk.[d + 1 <- idm (negb add)]
            (Acc_inv H (dec_step n i Hi))
      | Close =>
          if d =? 0 then
            loop x n (i + 1) d add stk (Acc_inv H (dec_step n i Hi))
          else
            loop x n (i + 1) (d - 1) (negb add)
              stk.[d - 1 <- opm (negb add) stk.[d - 1] stk.[d]]
              (Acc_inv H (dec_step n i Hi))
      end
  | right _ => stk.[d]
  end.

Definition bracketsequence_impl (x : array (token uint)) : uint :=
  let n := PArray.length x in
  loop x n 0 0 true (PArray.make (n + 1) 0) (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: the math model of the pass                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope N_scope.

Close Scope N_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bracketsequence : array (token uint) -> uint := bracketsequence_impl.
