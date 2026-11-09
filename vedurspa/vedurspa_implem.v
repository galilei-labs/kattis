(* Executable implementation and its required termination dependencies.
   Correctness proofs are in vedurspa_proofs.v. *)
(* Implementation of vedurspa.spec: least-squares line per column, exact.

   Code.  Each of the four columns is read once ([col_sums], one pass):
   the present cells give the exact sums
     P = #present, SK = sum k, SKK = sum k^2, SY = sum y_k, SKY = sum k y_k
   over Z, the y_k being scaled by a common power of two 2^g: a float is
   the dyadic m * 2^e of its normalised mantissa and exponent ([fex],
   [frshiftexp] / [normfr_mantissa], turned into Z by [zofi], binary
   digits, no nat), an integer is (v, 0); g is the least exponent met so
   far and the running SY, SKY are shifted left when it decreases.  The
   normal equations of the line a + b t give, with D = P SKK - SK^2 and
   B = P SKY - SK SY,
     a + b t = ((SY D - B SK) + B P t) / (P D) * 2^g,
   an affine numerator over a fixed denominator ([fit], once per column).
   Each forecast cell rounds that rational (scaled by 2^20 for a float
   column, by 1 for an integer column) to the nearest integer by one Z
   division ([rnd_at]), clamps it to the column's range ([clampZ]) and
   converts it back: an int, or a float as (that integer) * 2^-20, both
   steps exact.  The four output arrays are filled in one pass over the m
   cells, every [set] on the latest version.  Every loop is the combinator
   [loop] (erased Acc on hi - i).

   Exact arithmetic: the sums, the line and the rounding are computed in
   Z (bignums, as the steering file's @forbid allows for the outputs);
   indices, lengths and the loop counters stay Uint63 ints.

   Proof.  [lsq_of_normal]: a line satisfying the normal equations
   minimises sse (the excess is a sum of squares).  [D_ge]: D >= P - 1,
   so D > 0 as soon as two values are present.  [sums_spec]: the loop
   computes the sums over the reals ([sumf]).  [fit_spec]: the fit is a
   least-squares line.  [round_err], [clamp_lip]: the output is within
   1/2 (integers) or 2^-21 (floats) of the clamped line. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Respeced Require Import Repr ReprFloat.
From Flocq Require Core.Core IEEE754.BinarySingleNaN IEEE754.PrimFloat.
Import ListNotations.

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

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

(* The one loop combinator: for i = lo, lo+1, ... while i < hi and
   [cont i s], s := f i s. *)
Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.

Definition loop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) : St :=
  wloop hi cont f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Lemma dec_half : forall i : int, (i =? 0) = false -> Zwf 0 (to_Z (i / 2)) (to_Z i).
Proof.
  intros i H. assert (to_Z i <> 0%Z).
  { intros E. assert (i = 0) by (apply to_Z_inj; exact E). subst i. discriminate. }
  pose proof (to_Z_bounded i). unfold Zwf. sia.
Qed.

(* the integer a machine word denotes, by binary digits (no nat) *)
Fixpoint zofi_rec (i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H} : Z :=
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.

Definition zofi (i : int) : Z := zofi_rec i (Zwf_well_founded 0 (to_Z i)).

(* the machine word of a positive below 2^63, by binary digits (no nat) *)
Fixpoint pos2int (p : positive) : int :=
  match p with
  | xH => 1
  | xO q => 2 * pos2int q
  | xI q => 2 * pos2int q + 1
  end.

Definition z2int (z : Z) : int :=
  match z with
  | Zpos p => pos2int p
  | _ => 0
  end.

(* the exact value of a finite float, from its normalised mantissa and
   exponent: f = m * 2^(e - 2101 - 53) *)
Definition fex (f : float) : Z * Z :=
  let (z, e) := frshiftexp f in
  let m := zofi (normfr_mantissa z) in
  ((if (f <? 0)%float then - m else m)%Z, (zofi e - 2154)%Z).

(* a cell of a column, as a dyadic (m, e) = m * 2^e *)
Definition fconv (o : option float) : option (Z * Z) :=
  match o with Some f => Some (fex f) | None => None end.

Definition iconv (o : option uint) : option (Z * Z) :=
  match o with Some v => Some (zofi v, 0%Z) | None => None end.

(* The exact sums of a column; sY and sKY are in units of 2^sG. *)
Record sums := mksums { sP : Z; sK : Z; sKK : Z; sY : Z; sKY : Z; sG : Z }.

Definition sums0 : sums := mksums 0 0 0 0 0 0.

Definition acc_step {A : Type} (conv : A -> option (Z * Z)) (x : array A)
    (i : int) (s : sums) : sums :=
  match conv x.[i] with
  | None => s
  | Some d =>
      let M := fst d in
      let E := snd d in
      let K := zofi i in
      let P := (sP s + 1)%Z in
      let SK := (sK s + K)%Z in
      let SKK := (sKK s + K * K)%Z in
      if Z.eqb M 0 then mksums P SK SKK (sY s) (sKY s) (sG s)
      else
        let g := Z.min (sG s) E in
        let Y := Z.shiftl M (E - g) in
        let sh := (sG s - g)%Z in
        mksums P SK SKK (Z.shiftl (sY s) sh + Y) (Z.shiftl (sKY s) sh + K * Y) g
  end.

Definition col_sums {A : Type} (conv : A -> option (Z * Z)) (x : array A) : sums :=
  loop (PArray.length x) (fun _ _ => true) (acc_step conv x) 0 sums0.

(* The least-squares line, scaled by 2^sc, at hour T is (c0 + c1 T) / den. *)
Record fitr := mkfit { fc0 : Z; fc1 : Z; fden : Z }.

Definition fit (s : sums) (sc : Z) : option fitr :=
  let P := sP s in
  let SK := sK s in
  if Z.ltb P 2 then None
  else
    let D := (P * sKK s - SK * SK)%Z in
    let B := (P * sKY s - SK * sY s)%Z in
    let n0 := (sY s * D - B * SK)%Z in
    let n1 := (B * P)%Z in
    let den := (P * D)%Z in
    let e := (sG s + sc)%Z in
    if Z.leb 0 e then Some (mkfit (Z.shiftl n0 e) (Z.shiftl n1 e) den)
    else Some (mkfit n0 n1 (Z.shiftl den (- e))).

(* the nearest integer (ties up) to the line at hour T *)
Definition rnd_at (f : fitr) (T : Z) : Z :=
  ((2 * (fc0 f + fc1 f * T) + fden f) / (2 * fden f))%Z.

Definition clampZ (lo hi v : Z) : Z := Z.max lo (Z.min hi v).

Definition fl_of_Z (z : Z) : float :=
  if Z.ltb z 0 then (- of_uint63 (z2int (- z)))%float else of_uint63 (z2int z).

Definition c20 : float := (of_uint63 1 / of_uint63 1048576)%float.

(* a float forecast cell: the clamped line to within 2^-21 *)
Definition fout (fo : option fitr) (lo hi : Z) (T : Z) : option float :=
  match fo with
  | None => None
  | Some f => Some (fl_of_Z (clampZ (lo * 1048576) (hi * 1048576) (rnd_at f T)) * c20)%float
  end.

(* an integer forecast cell: the nearest integer of the clamped line *)
Definition iout (fo : option fitr) (lo hi : Z) (T : Z) : option uint :=
  match fo with
  | None => None
  | Some f => Some (z2int (clampZ lo hi (rnd_at f T)))
  end.

Definition Out : Type :=
  (array (option float) * array (option uint) * array (option float) * array (option uint))%type.

Definition out_step (ft fd fs fh : option fitr) (nt nd ns nh : Z) (i : int) (o : Out) : Out :=
  let '(a, b, c, d) := o in
  let j := zofi i in
  (a.[i <- fout ft (-50) 50 (nt + j)],
   b.[i <- iout fd 0 360 (nd + j)],
   c.[i <- fout fs 0 80 (ns + j)],
   d.[i <- iout fh 0 110 (nh + j)]).

Definition vedurspa_impl (xt : array (option float)) (xd : array (option uint))
    (xs : array (option float)) (xh : array (option uint)) (m : uint) : Out :=
  let ft := fit (col_sums fconv xt) 20 in
  let fd := fit (col_sums iconv xd) 0 in
  let fs := fit (col_sums fconv xs) 20 in
  let fh := fit (col_sums iconv xh) 0 in
  let L := if m <=? max_length then m else max_length in
  loop L (fun _ _ => true)
    (out_step ft fd fs fh (zofi (PArray.length xt)) (zofi (PArray.length xd))
       (zofi (PArray.length xs)) (zofi (PArray.length xh)))
    0 (PArray.make L None, PArray.make L None, PArray.make L None, PArray.make L None).

Local Notation bp := (Raux.bpow Zaux.radix2).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition vedurspa :
  array (option float) -> array (option uint) ->
  array (option float) -> array (option uint) -> uint ->
  array (option float) * array (option uint) *
  array (option float) * array (option uint) := vedurspa_impl.
