(* Executable implementation and its required termination dependencies.
   Correctness proofs are in canonical_proofs.v. *)
(* Implementation of canonical (canonical.spec): is a coin system
   canonical (the greedy algorithm always optimal)?

   Code.  With B = c_n + c_(n-1) (the Kozen-Zaks bound), one bottom-up pass
   over the amounts x = 1 .. B-1 fills two flat tables of length B:
   - t.[x], the minimum number of coins for x (unbounded-knapsack DP):
     1 + min over the coins c_j <= x of t.[x - c_j];
   - g.[x], the greedy count for x: 1 + g.[x - c_k] where c_k is the
     largest coin <= x.  The index k is a pointer that only moves forward
     (at most one step per amount, the coins being strictly increasing),
     so the greedy count costs O(1) per amount.
   The pass stops with false at the first amount where t.[x] < g.[x], and
   answers true when none is found below B.

   Proof.  The tables meet the math side (min_coins, greedy_uses) on every
   amount below x (outer_spec).  The reduction to the bound B is the
   Kozen-Zaks argument (kz): if greedy is optimal below c_n + c_(n-1), it
   is optimal everywhere, by strong induction on the amount.

   Termination: both loops recurse on an erased [Acc (Zwf 0) (gap m i)]
   proof, the template's device.  No nat, no Z in the code. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.
Open Scope array_scope.

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

(* min(acc, min_{j <= i < hi} t.[x - c.[i]]) *)
Fixpoint minloop (c t : array int) (x hi j acc : int)
    (H : Acc (Zwf 0) (gap hi j)) {struct H} : int :=
  match bdec (j <? hi) with
  | left Hj =>
      let v := t.[x - c.[j]] in
      minloop c t x hi (j + 1) (if v <? acc then v else acc)
        (Acc_inv H (dec_step hi j Hj))
  | right _ => acc
  end.

(* The largest-coin pointer for amount x, from the one of amount x - 1. *)
Definition kupd (c : array int) (n x k : int) : int :=
  if k + 1 <? n then (if c.[k + 1] <=? x then k + 1 else k) else k.

(* Amounts x, x+1, ..., B-1. *)
Fixpoint outer (c : array int) (n B x k : int) (t g : array int)
    (H : Acc (Zwf 0) (gap B x)) {struct H} : bool :=
  match bdec (x <? B) with
  | left Hx =>
      let k' := kupd c n x k in
      let gx := g.[x - c.[k']] + 1 in
      let tx := minloop c t x (k' + 1) 1 t.[x - 1]
                  (Zwf_well_founded 0 (gap (k' + 1) 1)) + 1 in
      if tx <? gx then false
      else outer c n B (x + 1) k' t.[x <- tx] g.[x <- gx]
             (Acc_inv H (dec_step B x Hx))
  | right _ => true
  end.

(* The Kozen-Zaks bound c_n + c_(n-1). *)
Definition bound (c : array int) : int :=
  let n := PArray.length c in c.[n - 1] + c.[n - 2].

Definition run (c : array int) : bool :=
  let B := bound c in
  outer c (PArray.length c) B 1 0 (PArray.make B 0) (PArray.make B 0)
    (Zwf_well_founded 0 (gap B 1)).

Definition canonical_impl (c : array uint) : bool := run c.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition canonical : array uint -> bool := canonical_impl.
