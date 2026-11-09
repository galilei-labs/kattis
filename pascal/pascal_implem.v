(* Executable implementation and its required termination dependencies.
   Correctness proofs are in pascal_proofs.v. *)
(* Implementation of pascal (pascal.spec): trial division.

   Code.  [pascal n] finds the smallest divisor p >= 2 of n by trying
   p = 2, 3, 4, ... while p <= n and p * p <= n ([sd_loop]); when no
   candidate divides n (n prime, or n = 1) the loop returns n itself.  The
   answer is n - n / p: Frane's loop counts down from n - 1 to the largest
   proper divisor n / p of n.  For n = 1 the loop returns 1 and the answer
   is 1 - 1 = 0.  All arithmetic is on Uint63 [int]; no array, no Z.

   Termination: [sd_loop] recurses structurally on an erased
   [Acc (Zwf 0) (gap n p)] proof, gap n p = n + 1 - p (the template's
   device); the test [p <? n] makes the decrease unconditional (p + 1
   cannot wrap) and, with the contract's bound, keeps p * p exact. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf.

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

Definition gap (n p : int) : Z := ((φ n) + 1 - (φ p))%Z.

Lemma dec_step : forall n p : int,
  ((p <? n) && (p * p <=? n))%bool = true -> Zwf 0 (gap n (p + 1)) (gap n p).
Proof.
  intros n p H. apply andb_prop in H. destruct H as [H _].
  rewrite ltb_spec in H.
  assert (H1 : (φ (p + 1)) = ((φ p) + 1)%Z).
  { pose proof (to_Z_bounded n). sia. }
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The smallest divisor of n among p, p+1, ... below sqrt n, or n. *)
Fixpoint sd_loop (n p : int) (H : Acc (Zwf 0) (gap n p)) {struct H} : int :=
  match bdec ((p <? n) && (p * p <=? n))%bool with
  | left Hc =>
      if n mod p =? 0 then p
      else sd_loop n (p + 1) (Acc_inv H (dec_step n p Hc))
  | right _ => n
  end.

Definition pascal_impl (n : uint) : uint :=
  n - n / sd_loop n 2 (Zwf_well_founded 0 (gap n 2)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition pascal : uint -> uint := pascal_impl.
