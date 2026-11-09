(* Executable implementation and its required termination dependencies.
   Correctness proofs are in knigsoftheforest_proofs.v. *)
From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import FinFun.
From Stdlib Require Import Permutation.
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

Lemma dec_up : forall i : int,
  (0 <? i) = true -> Zwf 0 (φ ((i - 1) / 2)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

(* The larger child of the node whose left child is l, in a heap of size s. *)
Definition pick (h : array int) (s l : int) : int :=
  if l + 1 <? s then (if h.[l] <? h.[l + 1] then l + 1 else l) else l.

Lemma dec_down : forall (h : array int) (s i : int),
  (i <? s / 2) = true -> Zwf 0 ((φ s) - (φ (pick h s (2 * i + 1))))%Z ((φ s) - (φ i))%Z.
Proof.
  intros h s i H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded i).
  assert (Hs2 : (φ (s / 2)) = ((φ s) / 2)%Z) by sia.
  assert (Hl : (φ (2 * i + 1)) = (2 * (φ i) + 1)%Z) by sia.
  unfold pick, Zwf.
  destruct (2 * i + 1 + 1 <? s) eqn:E1; [destruct (h.[2 * i + 1] <? h.[2 * i + 1 + 1])|];
    rewrite ?ltb_spec in E1; sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* CLRS max-heap on the first s cells of h, keyed on the values. *)
Fixpoint sift_up (h : array int) (i : int) (H : Acc (Zwf 0) (φ i)) {struct H}
    : array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let q := (i - 1) / 2 in
      let vi := h.[i] in
      let vq := h.[q] in
      match bdec (vq <? vi) with
      | left _ => sift_up h.[i <- vq].[q <- vi] q (Acc_inv H (dec_up i Hi))
      | right _ => h
      end
  | right _ => h
  end.

Fixpoint sift_down (h : array int) (s i : int) (H : Acc (Zwf 0) ((φ s) - (φ i))%Z)
    {struct H} : array int :=
  match bdec (i <? s / 2) with
  | left Hi =>
      let c := pick h s (2 * i + 1) in
      let vi := h.[i] in
      let vc := h.[c] in
      match bdec (vi <? vc) with
      | left _ => sift_down h.[i <- vc].[c <- vi] s c (Acc_inv H (dec_down h s i Hi))
      | right _ => h
      end
  | right _ => h
  end.

(* Insert v into the heap of size s (the new size is s + 1). *)
Definition insert (h : array int) (s v : int) : array int :=
  sift_up h.[s <- v] s (Zwf_well_founded 0 (φ s)).

(* Remove the maximum h.[0] of the heap of size s >= 1 (new size s - 1). *)
Definition extract (h : array int) (s : int) : array int :=
  let s1 := s - 1 in
  sift_down h.[0 <- h.[s1]] s1 0 (Zwf_well_founded 0 ((φ s1) - (φ 0))%Z).

(* One moose: in the pool of 2011 (the heap), or the newcomer of its year
   (the table, indexed by year - 2011). *)
Definition step (st : array int * int * array int) (yr sv : int)
    : array int * int * array int :=
  let '(h, s, t) := st in
  if yr =? 2011 then (insert h s sv, s + 1, t)
  else (h, s, t.[yr - 2011 <- sv]).

Fixpoint fill (ys ps : array int) (m i : int) (st : array int * int * array int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int * int * array int :=
  match bdec (i <? m) with
  | left Hi => fill ys ps m (i + 1) (step st ys.[i] ps.[i]) (Acc_inv H (dec_step m i Hi))
  | right _ => st
  end.

(* Year 2011 + d: the strongest moose of the pool wins. *)
Fixpoint sim (t h : array int) (n p s d : int) (H : Acc (Zwf 0) (gap n d)) {struct H}
    : option int :=
  match bdec (d <? n) with
  | left Hd =>
      if s =? 0 then None else
      let top := h.[0] in
      if top =? p then Some (2011 + d)
      else if d + 1 <? n then
        sim t (insert (extract h s) (s - 1) t.[d + 1]) n p s (d + 1)
          (Acc_inv H (dec_step n d Hd))
      else None
  | right _ => None
  end.

Definition knigs_impl (k n y p : uint) (ys ps : array uint) : option uint :=
  let m := PArray.length ys in
  let st0 := step (PArray.make (m + 1) 0, 0, PArray.make n 0) y p in
  let '(h, s, t) := fill ys ps m 0 st0 (Zwf_well_founded 0 (gap m 0)) in
  sim t h n p s 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Heaps as functions on Z                                             *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition knigsoftheforest :
  uint -> uint -> uint -> uint -> array uint -> array uint -> option uint := knigs_impl.
