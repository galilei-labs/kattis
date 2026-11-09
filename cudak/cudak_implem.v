(* Executable implementation and its required termination dependencies.
   Correctness proofs are in cudak_proofs.v. *)
(* Implementation of cudak (cudak.spec): digit DP.

   Code.  [cudak a b s] computes D, the number of decimal digits of b
   (b < 10^D, D <= 15), and one flat table T of D rows of s+1 cells,
   T[k*(s+1) + u] = g k u = #{ y < 10^k : digit sum of y = u }, built row
   by row from g 0 u = [u = 0] and g (k+1) u = sum_{c <= 9, c <= u}
   g k (u - c).  The count is f(b) - f(a-1), f(X) = #{ y <= X : digit sum
   s }, computed by a top-down walk over the D digits of X.  The smallest
   qualifying integer is the (f(a-1)+1)-th integer of digit sum s, built
   greedily digit by digit from the top, each digit chosen by subtracting
   the table counts of the smaller digits from the remaining rank.  All
   values are Uint63 words (no value exceeds 10^15 + 1).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (the template's device). *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import FinFun.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ================================================================== *)
(* The termination device                                              *)
(* ================================================================== *)

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

Lemma dec_pred : forall j : int,
  (0 <? j) = true -> Zwf 0 (φ (j - 1)) (φ j).
Proof.
  intros j H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
  unfold Zwf. pose proof (to_Z_bounded (j - 1)). lia.
Qed.

Lemma andb_l : forall a b : bool, a && b = true -> a = true.
Proof. intros a b H. destruct a; [reflexivity | discriminate]. Qed.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

(* the table count of the integers below 10^k (row k, at [base]) whose
   digit sum is t - c, or 0 when c > t *)
Definition vcell (T : array int) (base t c : int) : int :=
  if c <=? t then T.[base + (t - c)] else 0.

(* acc + sum of the vcells for the digits d .. c-1 *)
Fixpoint rowsum (T : array int) (base t c d acc : int)
    (H : Acc (Zwf 0) (gap c d)) {struct H} : int :=
  match bdec (d <? c) with
  | left Hd =>
      rowsum T base t c (d + 1) (acc + vcell T base t d)
        (Acc_inv H (dec_step c d Hd))
  | right _ => acc
  end.

(* cells idx .. n-1 of the table; idx = k * S1 + u, row k >= 1 computed
   from row k - 1 *)
Fixpoint fill (T : array int) (s S1 n idx k u : int)
    (H : Acc (Zwf 0) (gap n idx)) {struct H} : array int :=
  match bdec (idx <? n) with
  | left Hi =>
      fill T.[idx <- rowsum T ((k - 1) * S1) u 10 0 0
                        (Zwf_well_founded 0 (gap 10 0))]
        s S1 n (idx + 1)
        (if u =? s then k + 1 else k) (if u =? s then 0 else u + 1)
        (Acc_inv H (dec_step n idx Hi))
  | right _ => T
  end.

(* the number d of decimal digits of b, with q = 10^(d-1) *)
Fixpoint digits (b d q : int) (H : Acc (Zwf 0) (gap 15 d)) {struct H}
    : int * int :=
  match bdec ((d <? 15) && (q * 10 <=? b)) with
  | left Hc => digits b (d + 1) (q * 10) (Acc_inv H (dec_step 15 d (andb_l _ _ Hc)))
  | right _ => (d, q)
  end.

(* acc + #{ y <= R : digit sum t }, R having j digits, p = 10^(j-1) *)
Fixpoint walk (T : array int) (S1 j p R t acc : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : int :=
  match bdec (0 <? j) with
  | left Hj =>
      let c := R / p in
      let acc' := rowsum T ((j - 1) * S1) t c 0 acc
                    (Zwf_well_founded 0 (gap c 0)) in
      if t <? c then acc'
      else walk T S1 (j - 1) (p / 10) (R mod p) (t - c) acc'
             (Acc_inv H (dec_pred j Hj))
  | right _ => if t =? 0 then acc + 1 else acc
  end.

(* the digit c (from c on) at which the rank r falls, and the rank left *)
Fixpoint pick (T : array int) (base t c r : int)
    (H : Acc (Zwf 0) (gap 9 c)) {struct H} : int * int :=
  match bdec ((c <? 9) && (vcell T base t c <? r)) with
  | left Hc =>
      pick T base t (c + 1) (r - vcell T base t c)
        (Acc_inv H (dec_step 9 c (andb_l _ _ Hc)))
  | right _ => (c, r)
  end.

(* the greedy construction: prefix x, j digits left, sum t left, rank r *)
Fixpoint minwalk (T : array int) (S1 j t r x : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : int :=
  match bdec (0 <? j) with
  | left Hj =>
      let cr := pick T ((j - 1) * S1) t 0 r (Zwf_well_founded 0 (gap 9 0)) in
      minwalk T S1 (j - 1) (t - fst cr) (snd cr) (x * 10 + fst cr)
        (Acc_inv H (dec_pred j Hj))
  | right _ => x
  end.

Definition cudak_impl (a b s : uint) : uint * uint :=
  let S1 := s + 1 in
  let dq := digits b 1 1 (Zwf_well_founded 0 (gap 15 1)) in
  let D := fst dq in
  let q := snd dq in
  let n := D * S1 in
  let T := fill (PArray.make n 0).[0 <- 1] s S1 n S1 1 0
             (Zwf_well_founded 0 (gap n S1)) in
  let cb := walk T S1 D q b s 0 (Zwf_well_founded 0 (φ D)) in
  let ca := walk T S1 D q (a - 1) s 0 (Zwf_well_founded 0 (φ D)) in
  (cb - ca, minwalk T S1 D s (ca + 1) 0 (Zwf_well_founded 0 (φ D))).

(* ================================================================== *)
(* The spec's items, at top level                                      *)
(* ================================================================== *)

Definition cudak : uint -> uint -> uint -> uint * uint := cudak_impl.
