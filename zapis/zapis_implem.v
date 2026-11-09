(* Executable implementation and its required termination dependencies.
   Correctness proofs are in zapis_proofs.v. *)
From Zapis.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray PrimString ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
Import ListNotations.

(* ================================================================== *)
(* Math side: words as lists of characters                             *)
(* ================================================================== *)

Local Open Scope list_scope.

(* ================================================================== *)
(* Uint63 / PArray plumbing                                            *)
(* ================================================================== *)

Local Open Scope uint63_scope.
Local Open Scope array_scope.

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

Lemma dec_down : forall t : int,
  (0 <? t) = true -> Zwf 0 (φ (t - 1)) (φ t).
Proof.
  intros t H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (t - 1)) = ((φ t) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

Definition MOD : int := 100000.

(* min v MOD *)
Definition capm (v : int) : int := if v <? MOD then v else MOD.

(* the character a may be o, and the character b may be c *)
Definition okp (a b o c : int) : bool :=
  ((a =? o) || (a =? 63)) && ((b =? c) || (b =? 63)).

(* the number of bracket kinds (o, c) such that a can be o and b can be c *)
Definition pcode (a b : int) : int :=
  (if okp a b 40 41 then 1 else 0) + (if okp a b 91 93 then 1 else 0)
  + (if okp a b 123 125 then 1 else 0).

(* the residue of the interval [a, b) sits at ixi W a b, its capped count
   at the next cell *)
Definition ixi (W a b : int) : int := 2 * (a * W + b).

(* Sum over k = kk, kk + 2, ... (t terms) of the products, the residue in
   r and the count capped at MOD in c. *)
Fixpoint inner (x : PrimString.string) (tb : array int) (W ci ii j kk t r c : int)
    (H : Acc (Zwf 0) (φ t)) {struct H} : int * int :=
  match bdec (0 <? t) with
  | left Ht =>
      let p := pcode ci (PrimString.get x kk) in
      let ia := ixi W (ii + 1) kk in
      let ib := ixi W (kk + 1) j in
      let ra := tb.[ia] in
      let ca := tb.[ia + 1] in
      let rb := tb.[ib] in
      let cb := tb.[ib + 1] in
      inner x tb W ci ii j (kk + 2) (t - 1)
        ((r + ((p * ra) mod MOD) * rb) mod MOD)
        (capm (c + capm (capm (p * ca) * cb)))
        (Acc_inv H (dec_down t Ht))
  | right _ => (r, c)
  end.

(* The intervals [ii, ii + L) for ii = ii .. m - 1 (L = 2h). *)
Fixpoint middle (x : PrimString.string) (W h L m ii : int) (tb : array int)
    (H : Acc (Zwf 0) (gap m ii)) {struct H} : array int :=
  match bdec (ii <? m) with
  | left Hi =>
      let j := ii + L in
      let b0 := if h =? 0 then 1 else 0 in
      let rc := inner x tb W (PrimString.get x ii) ii j (ii + 1) h b0 b0
                  (Zwf_well_founded 0 (φ h)) in
      let p := ixi W ii j in
      middle x W h L m (ii + 1) (tb.[p <- fst rc].[p + 1 <- snd rc])
        (Acc_inv H (dec_step m ii Hi))
  | right _ => tb
  end.

(* The even interval lengths 2h, 2h + 2, ..., up to n. *)
Fixpoint outer (x : PrimString.string) (n W hm h : int) (tb : array int)
    (H : Acc (Zwf 0) (gap hm h)) {struct H} : array int :=
  match bdec (h <? hm) with
  | left Hh =>
      let L := 2 * h in
      outer x n W hm (h + 1)
        (middle x W h L (n - L + 1) 0 tb (Zwf_well_founded 0 (gap (n - L + 1) 0)))
        (Acc_inv H (dec_step hm h Hh))
  | right _ => tb
  end.

Definition zapis_impl (x : PrimString.string) : uint * bool :=
  let n := PrimString.length x in
  let W := n + 1 in
  let tb := outer x n W (n / 2 + 1) 0 (PArray.make (2 * (W * W)) 0)
              (Zwf_well_founded 0 (gap (n / 2 + 1) 0)) in
  let p := ixi W 0 n in
  (tb.[p], MOD <=? tb.[p + 1]).

(* ================================================================== *)
(* The spec's items, at top level                                      *)
(* ================================================================== *)

Definition zapis : PrimString.string -> uint * bool := zapis_impl.
