(* Executable implementation and its required termination dependencies.
   Correctness proofs are in cardhand_proofs.v. *)
(* Implementation of cardhand (cardhand.spec). *)

From Cardhand.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import PrimString String Ascii Sorted Permutation.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Unset Lia Cache.

(* ================================================================== *)
(* Part 4. Target orders and keys                                      *)
(* ================================================================== *)

Open Scope Z_scope.

(* ================================================================== *)
(* Part 7. The program                                                 *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope Z_scope.
Open Scope array_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := (φ m) - (φ j).

Lemma dec_step : forall m i : int,
  (i <? m)%uint63 = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = (φ i) + 1) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall q : int, (0 <? q)%uint63 = true -> Zwf 0 (φ (q - 1)) (φ q).
Proof.
  intros q H. rewrite ltb_spec in H. change (φ 0) with 0 in H.
  assert ((φ (q - 1)) = (φ q) - 1) by sia. unfold Zwf. lia.
Qed.

Section Program.
Local Open Scope uint63_scope.

Definition imax (a b : int) : int := if a <? b then b else a.

(* index of a suit character in "shdc" *)
Definition sidx_m (c : int) : int :=
  if c =? 115 then 0 else if c =? 104 then 1 else if c =? 100 then 2 else 3.

(* index of a rank character in "23456789TJQKA" *)
Definition rank_m (c : int) : int :=
  if c <=? 57 then c - 50
  else if c =? 84 then 8 else if c =? 74 then 9 else if c =? 81 then 10
  else if c =? 75 then 11 else 12.

Definition pw4 (s : int) : int :=
  if s =? 0 then 1 else if s =? 1 then 4 else if s =? 2 then 16 else 64.
Definition pw2 (s : int) : int :=
  if s =? 0 then 256 else if s =? 1 then 512 else if s =? 2 then 1024 else 2048.

(* target t: block of suit s, and its direction (1: ascending) *)
Definition sg_m (t s : int) : int := (t / pw4 s) mod 4.
Definition dr_m (t s : int) : int := (t / pw2 s) mod 2.
Definition key_m (t s r : int) : int :=
  sg_m t s * 13 + (if dr_m t s =? 1 then r else 12 - r).

(* the four blocks are distinct: t is one of the 4! x 2^4 targets *)
Definition inj_m (t : int) : bool :=
  let a := sg_m t 0 in let b := sg_m t 1 in let c := sg_m t 2 in let d := sg_m t 3 in
  negb (a =? b) && negb (a =? c) && negb (a =? d) &&
  negb (b =? c) && negb (b =? d) && negb (c =? d).

(* suit and rank index of every card *)
Fixpoint prep (x : array PrimString.string) (n i : int) (SU RK : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let w := x.[i] in
      prep x n (i + 1) SU.[i <- sidx_m (PrimString.get w 1)]
        RK.[i <- rank_m (PrimString.get w 0)] (Acc_inv H (dec_step n i Hi))
  | right _ => (SU, RK)
  end.

(* the key of every card under target t, and the set of keys present *)
Fixpoint keys (t : int) (SU RK : array int) (n i : int) (K P : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let k := key_m t SU.[i] RK.[i] in
      keys t SU RK n (i + 1) K.[i <- k] P.[k <- 1] (Acc_inv H (dec_step n i Hi))
  | right _ => (K, P)
  end.

(* the keys present, in increasing order: the hand sorted in target order *)
Fixpoint compact (P : array int) (k : int) (B : array int) (m : int)
    (H : Acc (Zwf 0) (gap 52 k)) {struct H} : array int * int :=
  match bdec (k <? 52) with
  | left Hk =>
      if P.[k] =? 1
      then compact P (k + 1) B.[m <- k] (m + 1) (Acc_inv H (dec_step 52 k Hk))
      else compact P (k + 1) B m (Acc_inv H (dec_step 52 k Hk))
  | right _ => (B, m)
  end.

(* the LCS table, flat, row width w = m + 1, filled from the last cell
   (i, j) = (n-1, m-1) back to (0, 0); row n and column m stay 0 *)
Fixpoint dp (K B : array int) (m w q : int) (T : array int)
    (H : Acc (Zwf 0) (φ q)) {struct H} : array int :=
  match bdec (0 <? q) with
  | left Hq =>
      let q' := q - 1 in
      let i := q' / m in
      let j := q' mod m in
      let c := if K.[i] =? B.[j] then T.[(i + 1) * w + (j + 1)] + 1
               else imax T.[(i + 1) * w + j] T.[i * w + (j + 1)] in
      dp K B m w q' T.[i * w + j <- c] (Acc_inv H (dec_down q Hq))
  | right _ => T
  end.

Definition lcs_for (t : int) (SU RK : array int) (n : int) : int :=
  let (K, P) := keys t SU RK n 0 (PArray.make n 0) (PArray.make 52 0)
                  (Zwf_well_founded 0 (gap n 0)) in
  let (B, m) := compact P 0 (PArray.make 52 0) 0 (Zwf_well_founded 0 (gap 52 0)) in
  let w := m + 1 in
  let T := dp K B m w (n * m) (PArray.make ((n + 1) * w) 0)
             (Zwf_well_founded 0 (φ (n * m))) in
  T.[0].

(* the best LCS over the targets t, t+1, ..., 4095 *)
Fixpoint search (SU RK : array int) (n t best : int)
    (H : Acc (Zwf 0) (gap 4096 t)) {struct H} : int :=
  match bdec (t <? 4096) with
  | left Ht =>
      search SU RK n (t + 1)
        (if inj_m t then imax best (lcs_for t SU RK n) else best)
        (Acc_inv H (dec_step 4096 t Ht))
  | right _ => best
  end.

Definition min_moves_impl (x : array PrimString.string) : uint :=
  let n := PArray.length x in
  let (SU, RK) := prep x n 0 (PArray.make n 0) (PArray.make n 0)
                    (Zwf_well_founded 0 (gap n 0)) in
  n - search SU RK n 0 0 (Zwf_well_founded 0 (gap 4096 0)).

Lemma prep_eq : forall x n i SU RK H, prep x n i SU RK H =
  match bdec (i <? n)%uint63 with
  | left Hi =>
      let w := x.[i] in
      prep x n (i + 1) SU.[i <- sidx_m (PrimString.get w 1)]
        RK.[i <- rank_m (PrimString.get w 0)] (Acc_inv H (dec_step n i Hi))
  | right _ => (SU, RK)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma keys_eq : forall t SU RK n i K P H, keys t SU RK n i K P H =
  match bdec (i <? n)%uint63 with
  | left Hi =>
      let k := key_m t SU.[i] RK.[i] in
      keys t SU RK n (i + 1) K.[i <- k] P.[k <- 1] (Acc_inv H (dec_step n i Hi))
  | right _ => (K, P)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma compact_eq : forall P k B m H, compact P k B m H =
  match bdec (k <? 52)%uint63 with
  | left Hk =>
      if (P.[k] =? 1)%uint63
      then compact P (k + 1) B.[m <- k] (m + 1) (Acc_inv H (dec_step 52 k Hk))
      else compact P (k + 1) B m (Acc_inv H (dec_step 52 k Hk))
  | right _ => (B, m)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma dp_eq : forall K B m w q T H, dp K B m w q T H =
  match bdec (0 <? q)%uint63 with
  | left Hq =>
      let q' := (q - 1)%uint63 in
      let i := (q' / m)%uint63 in
      let j := (q' mod m)%uint63 in
      let c := if (K.[i] =? B.[j])%uint63 then (T.[(i + 1) * w + (j + 1)] + 1)%uint63
               else imax T.[(i + 1) * w + j] T.[i * w + (j + 1)] in
      dp K B m w q' T.[i * w + j <- c] (Acc_inv H (dec_down q Hq))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma search_eq : forall SU RK n t best H, search SU RK n t best H =
  match bdec (t <? 4096)%uint63 with
  | left Ht =>
      search SU RK n (t + 1)
        (if inj_m t then imax best (lcs_for t SU RK n) else best)
        (Acc_inv H (dec_step 4096 t Ht))
  | right _ => best
  end.
Proof. intros. destruct H. reflexivity. Qed.

End Program.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition min_moves : array PrimString.string -> uint := min_moves_impl.
