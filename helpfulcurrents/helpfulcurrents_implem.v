(* Executable implementation and its required termination dependencies.
   Correctness proofs are in helpfulcurrents_proofs.v. *)
(* Implementation of helpfulcurrents (helpfulcurrents.spec): forward
   path counting, row by row, from the bottom row northwards.

   Code.  W(y,x), the number of move sequences taking the ship from its
   start (Y-1, xinit) to (y, x), satisfies
     W(y,x) = [start] + [north] W(y+1,x) + [cell(y,x-1) = '>'] W(y,x-1)
                                         + [cell(y,x+1) = '<'] W(y,x+1)
   (north: the cell below is not the castle and (y,x) is not '#').  One
   array holds a row of counts modulo 1000003, a second one a flag "the
   count is non-zero"; both are updated in place, row y over row y+1.
   Pass 1, west to east, adds the start, the north and the west
   contributions (A); pass 2, east to west, adds the east contribution
   (B = W).  This is exact because a '>' cell has no '<' east of it and a
   '<' cell no '>' west of it.  When pass 2 meets the castle it records
   its (count, flag), the answer.

   Proof.  [counted S n]: the set S of move lists has exactly n elements
   (a NoDup list); [rep S v f]: v is n mod 1000003, f is 0 iff n = 0.
   [pref_decomp] is the recurrence on the sets of prefixes; the loop
   invariants say each cell [rep]s its set.  A route is a prefix ending
   at the castle.

   Termination: erased [Acc (Zwf 0)] on a Z measure, as in polymul1. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString.
Import ListNotations.

Open Scope bool_scope.
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

Lemma dec_down : forall x : int, (0 <? x) = true -> Zwf 0 (φ (x - 1)) (φ x).
Proof.
  intros x H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (x - 1)) = ((φ x) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition P : int := 1000003.

(* (a + b) mod P, for a, b < P *)
Definition addm (a b : int) : int :=
  let s := a + b in if s <? P then s else s - P.

(* the flag of a union: zero iff both are *)
Definition orf (a b : int) : int := if a =? 0 then b else a.

(* Pass 1 over row y (string s, the row below sb), west to east: cell x
   receives start + north + west, where (wv, wf) is the west
   contribution (the value of cell x-1 when it is '>'). *)
Fixpoint pass1 (s sb : PrimString.string) (Ym Xm xim y : int)
    (x wv wf : int) (cv cf : array int) (H : Acc (Zwf 0) (gap Xm x)) {struct H}
    : array int * array int :=
  match bdec (x <? Xm) with
  | left Hx =>
      let c := PrimString.get s x in
      let st := (y + 1 =? Ym) && (x =? xim) in
      let sv := if st then 1 else 0 in
      let north := (y + 1 <? Ym) && negb (PrimString.get sb x =? 64)
                   && negb (c =? 35) in
      let nv := if north then cv.[x] else 0 in
      let nf := if north then cf.[x] else 0 in
      let av := addm (addm sv nv) wv in
      let af := orf (orf sv nf) wf in
      let w := c =? 62 in
      pass1 s sb Ym Xm xim y (x + 1) (if w then av else 0) (if w then af else 0)
        cv.[x <- av] cf.[x <- af] (Acc_inv H (dec_step Xm x Hx))
  | right _ => (cv, cf)
  end.

(* Pass 2 over row y, east to west: cell x-1 receives the east
   contribution (ev, ef) (the value of cell x when it is '<'); the
   castle's final value is recorded in (av, af). *)
Fixpoint pass2 (s : PrimString.string) (x ev ef : int) (cv cf : array int)
    (av af : int) (H : Acc (Zwf 0) (φ x)) {struct H}
    : (array int * array int) * (int * int) :=
  match bdec (0 <? x) with
  | left Hx =>
      let x' := x - 1 in
      let c := PrimString.get s x' in
      let bv := addm cv.[x'] ev in
      let bf := orf cf.[x'] ef in
      let e := c =? 60 in
      let k := c =? 64 in
      pass2 s x' (if e then bv else 0) (if e then bf else 0)
        cv.[x' <- bv] cf.[x' <- bf]
        (if k then bv else av) (if k then bf else af) (Acc_inv H (dec_down x Hx))
  | right _ => ((cv, cf), (av, af))
  end.

(* Rows k-1, k-2, ..., 0; the arrays hold row k. *)
Fixpoint rows (m : array PrimString.string) (Ym Xm xim : int) (k : int)
    (cv cf : array int) (av af : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : int * int :=
  match bdec (0 <? k) with
  | left Hk =>
      let y := k - 1 in
      let s := m.[y] in
      let r1 := pass1 s m.[k] Ym Xm xim y 0 0 0 cv cf
                  (Zwf_well_founded 0 (gap Xm 0)) in
      let r2 := pass2 s Xm 0 0 (fst r1) (snd r1) av af
                  (Zwf_well_founded 0 (φ Xm)) in
      rows m Ym Xm xim y (fst (fst r2)) (snd (fst r2)) (fst (snd r2))
        (snd (snd r2)) (Acc_inv H (dec_down k Hk))
  | right _ => (av, af)
  end.

Definition helpfulcurrents_impl (Ym Xm xim : uint) (m : array PrimString.string)
    : option uint :=
  let r := rows m Ym Xm xim Ym (PArray.make Xm 0) (PArray.make Xm 0) 0 0
             (Zwf_well_founded 0 (φ Ym)) in
  if snd r =? 0 then None else Some (fst r).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition helpfulcurrents : uint -> uint -> uint -> array PrimString.string -> option uint
  := helpfulcurrents_impl.
