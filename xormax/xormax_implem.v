(* Executable implementation and its required termination dependencies.
   Correctness proofs are in xormax_proofs.v. *)
(* Implementation of xormax (xormax.spec): a linear basis over GF(2).

   Code.  [xormax x] makes a flat basis [b = PArray.make 63 0], cell k
   holding 0 or a vector whose leading bit is k.  One pass over x inserts
   every number ([reduce]: from bit 62 down, a set bit k is cleared by
   xoring b.[k], or the number is stored in b.[k] when that cell is empty),
   then [greedy] walks the basis from bit 62 down and keeps r lxor b.[k]
   whenever it is larger than r.  All values are 63-bit [int]s; x is only
   read and b is threaded linearly.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (template/polymul1), on the measure gap n j for
   the pass over x and on to_Z i for the two downward loops over the bits.

   Proof.  The math side has two spans: [inspan l] (the xor-sums of
   sublists of l, equivalent to the spec's [subset_xor]) and [cspan f n]
   (the xor-sums of subsets of f 0, ..., f (n-1)); both are the smallest
   xor-closed sets containing their generators ([*_closed], [*_min]).  The
   basis invariant [binv] says that each cell is in the span of the prefix
   read so far and each element of the prefix in the span of the cells,
   and that every nonzero cell k lies in [2^k, 2^(k+1)).  The greedy pass
   is the function [gm]; [gm_in] puts its result in the span and
   [gm_max] bounds every element of the span by it (comparison through
   the quotients by 2^k). *)

From Xormax.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

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

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall m i : int,
  (i <? m)%uint63 = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : to_Z (i + 1)%uint63 = (to_Z i + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall i : int,
  (0 <? i)%uint63 = true -> Zwf 0 (to_Z (i - 1)%uint63) (to_Z i).
Proof.
  intros i H. rewrite ltb_spec in H. change (to_Z 0%uint63) with 0%Z in H.
  assert (H1 : to_Z (i - 1)%uint63 = (to_Z i - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Section Code.
Local Open Scope uint63_scope.

(* Insert c, whose bits at i and above are clear, into the basis b. *)
Fixpoint reduce (b : array int) (c i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H}
    : array int :=
  match bdec (0 <? i) with
  | left Hi =>
      if (c >> (i - 1)) =? 0 then reduce b c (i - 1) (Acc_inv H (dec_down i Hi))
      else
        let bk := b.[i - 1] in
        if bk =? 0 then b.[i - 1 <- c]
        else reduce b (c lxor bk) (i - 1) (Acc_inv H (dec_down i Hi))
  | right _ => b
  end.

(* Insert x.[j], ..., x.[n-1]. *)
Fixpoint build (x : array uint) (n j : int) (b : array int)
    (H : Acc (Zwf 0) (gap n j)) {struct H} : array int :=
  match bdec (j <? n) with
  | left Hj =>
      build x n (j + 1) (reduce b x.[j] 63 (Zwf_well_founded 0 _))
        (Acc_inv H (dec_step n j Hj))
  | right _ => b
  end.

(* Greedy maximum over the cells i-1, ..., 0, starting from r. *)
Fixpoint greedy (b : array int) (r i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H}
    : int :=
  match bdec (0 <? i) with
  | left Hi =>
      let r' := r lxor b.[i - 1] in
      greedy b (if r <? r' then r' else r) (i - 1) (Acc_inv H (dec_down i Hi))
  | right _ => r
  end.

Definition xormax_impl (x : array uint) : uint :=
  let b := build x (PArray.length x) 0 (PArray.make 63 0)
             (Zwf_well_founded 0 _) in
  greedy b 0 63 (Zwf_well_founded 0 _).

End Code.

(* ------------------------------------------------------------------ *)
(* Math side: spans                                                    *)
(* ------------------------------------------------------------------ *)

Open Scope N_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition xormax : array uint -> uint := xormax_impl.
