(* Executable implementation and its required termination dependencies.
   Correctness proofs are in addemup_proofs.v. *)
(* Implementation of addemup (addemup.spec): sort, then binary search.

   Code.  Every card c (index i) shows its face value c and, when it can be
   turned, its upside-down reading [alt c] (computed on the int, digit by
   digit with div/mod 10; a card that cannot be turned gets [alt c = c], a
   harmless duplicate).  The shown values are tagged with their card in one
   int key  v * K + i  (K = 2^17 > 100 000 >= the number of cards), stored
   in one flat table T of 2n cells (T[2i] face, T[2i+1] reading), sorted
   once by a top-down merge sort with one auxiliary buffer.  Then, for each
   card i and each of its shown values v <= s, the complement w = s - v is
   looked up by binary search (lower bound) in the sorted table: a card
   j < i showing w is a key in [w*K, w*K + i), a card j > i a key in
   [w*K + i + 1, (w+1)*K); one lower-bound search per range.  No Z, no nat,
   no list in the code.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof, as in template/polymul1. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorted Permutation Orders Mergesort.
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

Lemma dec_lo : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof. intros lo hi H. rewrite ltb_spec in H. unfold Zwf, gap. sia. Qed.

Lemma dec_hi : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap hi (lo + (hi - lo) / 2 + 1)) (gap hi lo).
Proof. intros lo hi H. rewrite ltb_spec in H. unfold Zwf, gap. sia. Qed.

Lemma dec_mid : forall lo hi : int,
  (lo <? hi) = true -> (1 <? hi - lo) = true ->
  Zwf 0 (gap hi (lo + (hi - lo) / 2)) (gap hi lo).
Proof.
  intros lo hi H H'. rewrite ltb_spec in H, H'. unfold Zwf, gap. sia.
Qed.

Lemma dec_div : forall x : int, (0 <? x) = true -> Zwf 0 (φ (x / 10)) (φ x).
Proof. intros x H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* A digit read upside down, if it reads as a digit. *)
Definition rotd (d : int) : option int :=
  if d =? 0 then Some 0 else if d =? 1 then Some 1 else
  if d =? 2 then Some 2 else if d =? 5 then Some 5 else
  if d =? 6 then Some 9 else if d =? 8 then Some 8 else
  if d =? 9 then Some 6 else None.

(* The digits of x, least significant first, rotated and appended to r. *)
Fixpoint rloop (x r : int) (H : Acc (Zwf 0) (φ x)) {struct H} : option int :=
  match bdec (0 <? x) with
  | left Hx =>
      match rotd (x mod 10) with
      | Some e => rloop (x / 10) (r * 10 + e) (Acc_inv H (dec_div x Hx))
      | None => None
      end
  | right _ => Some r
  end.

(* The upside-down reading of c, or c itself when c cannot be turned. *)
Definition alt (c : int) : int :=
  match rloop c 0 (Zwf_well_founded 0 (φ c)) with
  | Some r => r
  | None => c
  end.

Definition K : int := 131072.

(* T[2j] := c_j * K + j and T[2j+1] := alt c_j * K + j, for j = i .. n-1. *)
Fixpoint build (y T : array int) (n i : int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let c := y.[i] in
      build y (T.[2 * i <- c * K + i].[2 * i + 1 <- alt c * K + i]) n (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.

(* Merge src[i..mid) and src[j..hi) into dst[k..hi). *)
Fixpoint merge_loop (src dst : array int) (i mid j hi k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if i <? mid then
        if j <? hi then
          if src.[i] <=? src.[j] then
            merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
              (Acc_inv H (dec_step hi k Hk))
          else
            merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
              (Acc_inv H (dec_step hi k Hk))
        else
          merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
            (Acc_inv H (dec_step hi k Hk))
      else
        merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* dst[k..hi) := src[k..hi). *)
Fixpoint copy_loop (src dst : array int) (hi k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      copy_loop src dst.[k <- src.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* Top-down merge sort of a[lo..hi), with the buffer b; returns both. *)
Fixpoint msort (a b : array int) (lo hi : int) (H : Acc (Zwf 0) (gap hi lo))
    {struct H} : array int * array int :=
  match bdec (lo <? hi) with
  | left H1 =>
      match bdec (1 <? hi - lo) with
      | left H2 =>
          let mid := lo + (hi - lo) / 2 in
          let (a1, b1) := msort a b lo mid (Acc_inv H (dec_lo lo hi H1)) in
          let (a2, b2) := msort a1 b1 mid hi (Acc_inv H (dec_mid lo hi H1 H2)) in
          let b3 := merge_loop a2 b2 lo mid mid hi lo
                      (Zwf_well_founded 0 (gap hi lo)) in
          (copy_loop b3 a2 hi lo (Zwf_well_founded 0 (gap hi lo)), b3)
      | right _ => (a, b)
      end
  | right _ => (a, b)
  end.

(* Lower bound: the first position p in [lo, hi) with S[p] >= x (or hi). *)
Fixpoint lbloop (S : array int) (x lo hi : int) (H : Acc (Zwf 0) (gap hi lo))
    {struct H} : int :=
  match bdec (lo <? hi) with
  | left Hlt =>
      if S.[lo + (hi - lo) / 2] <? x
      then lbloop S x (lo + (hi - lo) / 2 + 1) hi (Acc_inv H (dec_hi lo hi Hlt))
      else lbloop S x lo (lo + (hi - lo) / 2) (Acc_inv H (dec_lo lo hi Hlt))
  | right _ => lo
  end.

(* Some key of the sorted S[0..m) lies in [lo, hi). *)
Definition inrange (S : array int) (m lo hi : int) : bool :=
  let p := lbloop S lo 0 m (Zwf_well_founded 0 (gap m 0)) in
  if p <? m then S.[p] <? hi else false.

(* Some card other than i shows w. *)
Definition found (S : array int) (m w i : int) : bool :=
  if inrange S m (w * K) (w * K + i) then true
  else inrange S m (w * K + i + 1) ((w + 1) * K).

(* Card i shows v, and some other card shows s - v. *)
Definition okv (S : array int) (m s v i : int) : bool :=
  if v <=? s then found S m (s - v) i else false.

(* Some card i' in [i, n) completes a winning pair. *)
Fixpoint scan (y S : array int) (s m n i : int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : bool :=
  match bdec (i <? n) with
  | left Hi =>
      let c := y.[i] in
      if okv S m s c i then true
      else if okv S m s (alt c) i then true
      else scan y S s m n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => false
  end.

Definition addemup_impl (s : uint) (y : array uint) : bool :=
  let n := PArray.length y in
  let m := 2 * n in
  let T := build y (PArray.make m 0) n 0 (Zwf_well_founded 0 (gap n 0)) in
  let S := fst (msort T (PArray.make m 0) 0 m (Zwf_well_founded 0 (gap m 0))) in
  scan y S s m n 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* The upside-down reading                                             *)
(* ------------------------------------------------------------------ *)

Open Scope N_scope.

Close Scope N_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition addemup : uint -> array uint -> bool := addemup_impl.
