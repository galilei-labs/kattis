(* Executable implementation and its required termination dependencies.
   Correctness proofs are in antiarithmetic_proofs.v. *)
(* Implementation of antiarithmetic (antiarithmetic.spec), steering v2:
   bitset scan over positions, the steps of a middle value tested 63 at a
   time (W = 63, every bit of a Uint63 word).

   Code.  n = |x|.  Two flat bitsets S and R of n/63 + 1 words each (bit v
   of a bitset is bit v mod 63 of word v / 63).  Scanning the positions
   left to right, with m = x.[pos] the value there: bit v of S is set iff
   value v was seen at an earlier position, and bit n-1-v of R likewise
   (R is S mirrored).  With L = min(m, n-1-m), a progression with middle m
   exists iff some step e in [1, L] has exactly one of m-e, m+e seen; bit
   S[m+e] is bit e-1 of S read from offset m+1, bit S[m-e] = R[n-1-m+e] is
   bit e-1 of R read from offset n-m.  [inner] reads both 63-bit slices
   from those offsets (offset 63a + r: (w[a] >> r) lor (w[a+1] << (63-r)),
   the r = 0 case giving w[a+1] << 63 = 0), XORs them, masks the last one
   to its rem <= 63 valid steps with (1 << rem) - 1 (= all ones for
   rem = 63), and stops on the first nonzero word.  Otherwise bit m of S
   and bit n-1-m of R are set ([setbit], one read-modify-write each on the
   latest version) and the scan goes on; true after the last position.

   Termination: both loops recurse on an erased [Acc (Zwf 0) _] proof (the
   template's device): [scan] on n - pos, [inner] on rem.  No nat, no Z
   in the code. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
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

Lemma rem_dec : forall rem : int,
  (rem <=? 63) = false -> Zwf 0 (φ (rem - 63)) (φ rem).
Proof.
  intros rem H. rewrite <- not_true_iff_false, leb_spec in H.
  change (φ 63) with 63%Z in H.
  assert (H1 : (φ (rem - 63)) = ((φ rem) - 63)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* true iff some j < rem has bit (63 aS + rS + j) of S different from bit
   (63 aR + rR + j) of R; lS = 63 - rS, lR = 63 - rR. *)
Fixpoint inner (S R : array int) (rS lS rR lR : int) (aS aR rem : int)
    (H : Acc (Zwf 0) (φ rem)) {struct H} : bool :=
  let w := ((S.[aS] >> rS) lor (S.[aS + 1] << lS))
           lxor ((R.[aR] >> rR) lor (R.[aR + 1] << lR)) in
  match bdec (rem <=? 63) with
  | left _ => negb ((w land ((1 << rem) - 1)) =? 0)
  | right Hr =>
      if w =? 0
      then inner S R rS lS rR lR (aS + 1) (aR + 1) (rem - 63)
             (Acc_inv H (rem_dec rem Hr))
      else true
  end.

(* Set bit v of the bitset t. *)
Definition setbit (t : array int) (v : int) : array int :=
  let a := v / 63 in t.[a <- t.[a] lor (1 << (v mod 63))].

Fixpoint scan (x : array uint) (n : int) (S R : array int) (pos : int)
    (H : Acc (Zwf 0) (gap n pos)) {struct H} : bool :=
  match bdec (pos <? n) with
  | left Hp =>
      let m : int := x.[pos] in
      let c := n - 1 - m in
      let L := if m <? c then m else c in
      let oS := m + 1 in
      let oR := n - m in
      let rS := oS mod 63 in
      let rR := oR mod 63 in
      if inner S R rS (63 - rS) rR (63 - rR) (oS / 63) (oR / 63) L
           (Zwf_well_founded 0 (φ L))
      then false
      else scan x n (setbit S m) (setbit R c) (pos + 1)
             (Acc_inv H (dec_step n pos Hp))
  | right _ => true
  end.

Definition antiarithmetic_impl (x : array uint) : bool :=
  let n := PArray.length x in
  let k := n / 63 + 1 in
  scan x n (PArray.make k 0) (PArray.make k 0) 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition antiarithmetic : array uint -> bool := antiarithmetic_impl.
