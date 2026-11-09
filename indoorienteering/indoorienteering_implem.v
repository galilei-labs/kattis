(* Executable implementation and its required termination dependencies.
   Correctness proofs are in indoorienteering_proofs.v. *)
From Indoorienteering.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool Permutation.
From Stdlib Require Import FinFun.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Termination devices                                                 *)
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

(* The measure of a search node: remaining depth r, next candidate v. *)
Definition meas (n r v : int) : Z := ((φ r) * ((φ n) + 1) + ((φ n) - (φ v)))%Z.

Lemma dec_sib : forall n r v : int,
  (r =? 0) = false -> (v <? n) = true -> Zwf 0 (meas n r (v + 1)) (meas n r v).
Proof.
  intros n r v Hr Hv. rewrite ltb_spec in Hv.
  assert (H1 : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
  pose proof (to_Z_bounded r). pose proof (to_Z_bounded n).
  unfold Zwf, meas. rewrite H1. nia.
Qed.

Lemma dec_child : forall n r v : int,
  (r =? 0) = false -> (v <? n) = true -> Zwf 0 (meas n (r - 1) 0) (meas n r v).
Proof.
  intros n r v Hr Hv. rewrite ltb_spec in Hv.
  rewrite eqb_false_spec in Hr.
  assert (Hr' : (φ r) <> 0%Z) by (intro E; apply Hr; apply to_Z_inj; exact E).
  assert (H1 : (φ (r - 1)) = ((φ r) - 1)%Z) by (pose proof (to_Z_bounded r); sia).
  pose proof (to_Z_bounded r). pose proof (to_Z_bounded n). pose proof (to_Z_bounded v).
  unfold Zwf, meas. rewrite H1. change (φ 0) with 0%Z. nia.
Qed.

(* ------------------------------------------------------------------ *)
(* The hash table: one flat int array, 0 = empty slot, linear probing  *)
(* without wrap-around (a probe that runs off the end fails).          *)
(* ------------------------------------------------------------------ *)

Definition hmul : int := 7046029254386353131.

(* multiplicative hashing: the top bits of k * hmul *)
Definition hidx (sh k : int) : int := (k * hmul) >> sh.

(* the first slot from i on that is empty or holds k; PArray.length t
   when there is none *)
Fixpoint find (t : array int) (k i : int)
    (H : Acc (Zwf 0) (gap (PArray.length t) i)) {struct H} : int :=
  match bdec (i <? PArray.length t) with
  | left Hi =>
      let x := t.[i] in
      if (x =? 0) || (x =? k) then i
      else find t k (i + 1) (Acc_inv H (dec_step _ _ Hi))
  | right _ => i
  end.

Definition find0 (sh : int) (t : array int) (k : int) : int :=
  find t k (hidx sh k) (Zwf_well_founded 0 _).

Definition lookup (sh : int) (t : array int) (k : int) : bool :=
  let j := find0 sh t k in
  (j <? PArray.length t) && (t.[j] =? k).

(* the table with k in it, and true; or t unchanged and false when the
   probe ran off the end *)
Definition insert (sh : int) (t : array int) (k : int) : array int * bool :=
  let j := find0 sh t k in
  if j <? PArray.length t then
    (if t.[j] =? 0 then (t.[j <- k], true) else (t, true))
  else (t, false).

(* ------------------------------------------------------------------ *)
(* The two half-path searches for one middle point m                   *)
(* ------------------------------------------------------------------ *)

(* the packed key of (set S, length l): S * 2^50 + l + 1, never 0 *)
Definition key (S l : int) : int := ((S << 50) + l) + 1.

Section Search.

(* D: the flat n x n distance matrix; a: the anchor (n - 1); m: the middle
   point; fp: the mask of the n - 2 other points; need: the mask the first
   side's sets must contain (the symmetry); fr2 = fp minus need: the points
   of the second side; base2 = need; k2: the second side's depth; sh: the
   hash shift; size: the table length. *)
Variables (D : array int) (n L a m fp need fr2 base2 k2 sh size : int).

(* Second side: from the current point c, with the free points free, the
   length so far len and r points still to choose, candidates from v on:
   is there a completion back to the anchor whose probe key is in t? *)
Fixpoint pdfs (t : array int) (c free len r v : int)
    (H : Acc (Zwf 0) (meas n r v)) {struct H} : bool :=
  match bdec (r =? 0) with
  | left _ =>
      let l := len + D.[c * n + a] in
      if l <=? L then lookup sh t (key (base2 lxor free) (L - l)) else false
  | right Hr =>
      match bdec (v <? n) with
      | left Hv =>
          let bv := 1 << v in
          if (free land bv) =? 0 then
            pdfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
          else
            let l := len + D.[c * n + v] in
            if l <=? L then
              if pdfs t v (free lxor bv) l (r - 1) 0 (Acc_inv H (dec_child n r v Hr Hv))
              then true
              else pdfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
            else pdfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
      | right _ => false
      end
  end.

(* A first-side half-path of key k reaches the table: inserted, or, when
   the probe runs off the end, the table is first probed by the whole
   second side ("flush") and k goes into a fresh one. *)
Definition leafins (t : array int) (k : int) : array int * bool :=
  match insert sh t k with
  | (t1, true) => (t1, false)
  | (t1, false) =>
      if pdfs t1 m fr2 0 k2 0 (Zwf_well_founded 0 _) then (t1, true)
      else (fst (insert sh (PArray.make size 0) k), false)
  end.

(* First side: from the anchor to m; returns the table and "found". *)
Fixpoint idfs (t : array int) (c free len r v : int)
    (H : Acc (Zwf 0) (meas n r v)) {struct H} : array int * bool :=
  match bdec (r =? 0) with
  | left _ =>
      let l := len + D.[c * n + m] in
      if l <=? L then leafins t (key (fp lxor free) l) else (t, false)
  | right Hr =>
      match bdec (v <? n) with
      | left Hv =>
          let bv := 1 << v in
          if (free land bv) =? 0 then
            idfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
          else if (r =? 1) && negb ((need land (free lxor bv)) =? 0) then
            idfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
          else
            let l := len + D.[c * n + v] in
            if l <=? L then
              match idfs t v (free lxor bv) l (r - 1) 0
                      (Acc_inv H (dec_child n r v Hr Hv)) with
              | (t1, true) => (t1, true)
              | (t1, false) =>
                  idfs t1 c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
              end
            else idfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
      | right _ => (t, false)
      end
  end.

End Search.

(* One middle point m: build the table of the first side, then probe it. *)
Definition search_m (D : array int) (n L a k1 k2 sh size m : int) : bool :=
  let fp := ((1 << a) - 1) lxor (1 << m) in
  let need := if ((n land 1) =? 0) && (4 <=? n)
              then 1 << (if m =? 0 then 1 else 0) else 0 in
  let fr2 := fp lxor need in
  match idfs D n L a m fp need fr2 need k2 sh size (PArray.make size 0)
          a fp 0 k1 0 (Zwf_well_founded 0 _) with
  | (_, true) => true
  | (t, false) => pdfs D n L a need sh t m fr2 0 k2 0 (Zwf_well_founded 0 _)
  end.

Fixpoint mloop (D : array int) (n L a k1 k2 sh size m : int)
    (H : Acc (Zwf 0) (gap a m)) {struct H} : bool :=
  match bdec (m <? a) with
  | left Hm =>
      if search_m D n L a k1 k2 sh size m then true
      else mloop D n L a k1 k2 sh size (m + 1) (Acc_inv H (dec_step a m Hm))
  | right _ => false
  end.

(* The input matrix, flattened: cell i holds x.[i / n].[i mod n]. *)
Fixpoint fill (x : array (array int)) (n N i : int) (D : array int)
    (H : Acc (Zwf 0) (gap N i)) {struct H} : array int :=
  match bdec (i <? N) with
  | left Hi => fill x n N (i + 1) D.[i <- x.[i / n].[i mod n]] (Acc_inv H (dec_step N i Hi))
  | right _ => D
  end.

(* log2 of the table capacity: at least twice the first side's half-paths *)
Definition logcap (n : int) : int :=
  if n <=? 8 then 7 else if n =? 9 then 9 else if n =? 10 then 11
  else if n =? 11 then 13 else if n =? 12 then 15 else if n =? 13 then 17
  else 20.

Definition indoor (x : array (array uint)) (L : uint) : bool :=
  let n := PArray.length x in
  let N := n * n in
  let D := fill x n N 0 (PArray.make N 0) (Zwf_well_founded 0 _) in
  let a := n - 1 in
  let k1 := (n - 2) / 2 in
  let k2 := n - 2 - k1 in
  let b := logcap n in
  mloop D n L a k1 k2 (63 - b) ((1 << b) + 256) 0 (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition indoorienteering : array (array uint) -> uint -> bool := indoor.
