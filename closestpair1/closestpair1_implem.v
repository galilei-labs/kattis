(* Executable implementation and its required termination dependencies.
   Correctness proofs are in closestpair1_proofs.v. *)
(* Implementation of closestpair1.spec: closest pair of points, bucket
   sort and a sweep over the buckets, exact over the reals.

   Code.  n buckets by abscissa.  The bucket of a coordinate f is
   min(n-1, u - 2^52) where u = (f + 10^5) * (n / 200001) + 2^52 in binary64
   is an integer-valued float of [2^52, 2^53), read off as the mantissa of
   its normalised fraction ([frshiftexp], [normfr_mantissa]); it is
   non-decreasing in f, which is all the proof uses.  Counting sort of the
   point indices by bucket (count, prefix sums, placement: flat [array int]s
   of length n), and the least abscissa of every bucket (one flat
   [array float]).  The sweep: for each position a of the bucket order,
   compare point p = P[a] with P[a+1], P[a+2], ... and stop at the first
   position c whose bucket is after p's and whose least abscissa m has
   float (m - x_p)^2 > best + tol: every later point is in that bucket or
   a later one, so at least that far from p.
   A candidate is rejected when its float squared distance is above the
   best's by more than tol = 2^-10 (the float error is below 4e-5 on the
   statement's range), and otherwise compared EXACTLY: [fex] reads a float
   as m * 2^e with m, e in Z (mantissa and exponent from [frshiftexp] and
   [normfr_mantissa], turned into Z by [zofi], binary digits, no nat), and
   [dex] is the exact squared distance as a dyadic m * 2^e (Z operations
   only).  Every loop is the combinator [loop] (erased Acc on hi - i).

   Proof.  [fex_val]: the dyadic is the real the float denotes (Flocq's
   Bfrexp_correct / Bnormfr_mantissa_correct).  [Kf_mono]: buckets are
   monotone.  [PA_*]: the placement puts point i at position
   pos i = #{keys < key i} + #{j < i with key j = key i}, a bijection onto
   [0, n) sorted by key (pigeonhole for surjectivity).  [cand_spec],
   [cont_spec], [inner_spec], [sweep_spec]: after the sweep, the best pair
   is no farther, exactly, than any pair of positions a < c. *)

From Closestpair1.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
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

(* -- Exact arithmetic, used only to settle close comparisons. -------- *)

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

(* A dyadic number (m, e) denotes m * 2^e. *)
Definition dal (d : Z * Z) (e : Z) : Z := Z.shiftl (fst d) (snd d - e).
Definition dadd (a b : Z * Z) : Z * Z :=
  let e := Z.min (snd a) (snd b) in (dal a e + dal b e, e)%Z.
Definition dsub (a b : Z * Z) : Z * Z :=
  let e := Z.min (snd a) (snd b) in (dal a e - dal b e, e)%Z.
Definition dmul (a b : Z * Z) : Z * Z := (fst a * fst b, snd a + snd b)%Z.
Definition dlt (a b : Z * Z) : bool :=
  let e := Z.min (snd a) (snd b) in Z.ltb (dal a e) (dal b e).

(* the exact value of a finite float, from its normalised mantissa and
   exponent: f = m * 2^(e - 2101 - 53) *)
Definition fex (f : float) : Z * Z :=
  let (z, e) := frshiftexp f in
  let m := zofi (normfr_mantissa z) in
  ((if (f <? 0)%float then - m else m)%Z, (zofi e - 2154)%Z).

(* the exact squared distance between points a and b *)
Definition dex (x y : array float) (a b : int) : Z * Z :=
  let dx := dsub (fex x.[a]) (fex x.[b]) in
  let dy := dsub (fex y.[a]) (fex y.[b]) in
  dadd (dmul dx dx) (dmul dy dy).

(* -- Floats. ---------------------------------------------------------- *)

(* The squared distance between points a and b, in binary64. *)
Definition fd (x y : array float) (a b : int) : float :=
  let dx := (x.[a] - x.[b])%float in
  let dy := (y.[a] - y.[b])%float in
  (dx * dx + dy * dy)%float.

(* the float square of a float difference *)
Definition gx (m p : float) : float := let d := (m - p)%float in (d * d)%float.

Definition c1e5 : float := of_uint63 100000.
Definition c52 : float := of_uint63 4503599627370496.
Definition cinit : float := of_uint63 200001.
(* the margin under which two float squared distances are compared exactly *)
Definition tol : float := (of_uint63 1 / of_uint63 1024)%float.

(* The bucket of a coordinate f, in [0, n1], non-decreasing in f:
   u = (f + 10^5) * s + 2^52 is an integer-valued float in [2^52, 2^53),
   its integer is the mantissa of its normalised fraction. *)
Definition key (s : float) (n1 : int) (f : float) : int :=
  let u := ((f + c1e5) * s + c52)%float in
  let k := normfr_mantissa (fst (frshiftexp u)) - 4503599627370496 in
  if k <? n1 then k else n1.

(* -- The bucket sort. ------------------------------------------------- *)

Definition key_step (x : array float) (s : float) (n1 : int) (i : int) (K : array int)
    : array int := K.[i <- key s n1 x.[i]].

Definition count_step (K : array int) (i : int) (C : array int) : array int :=
  let b := K.[i] in let v := C.[b] in C.[b <- v + 1].

Definition prefix_step (b : int) (st : array int * int) : array int * int :=
  let '(C, acc) := st in let v := C.[b] in (C.[b <- acc], acc + v).

Definition place_step (K : array int) (i : int) (st : array int * array int)
    : array int * array int :=
  let '(P, C) := st in
  let b := K.[i] in let v := C.[b] in (P.[v <- i], C.[b <- v + 1]).

(* the least abscissa of each bucket (cinit for an empty one) *)
Definition min_step (x : array float) (K : array int) (i : int) (M : array float)
    : array float :=
  let b := K.[i] in let xi := x.[i] in
  if (xi <? M.[b])%float then M.[b <- xi] else M.

(* -- The sweep. ------------------------------------------------------- *)

(* the candidate pair (p, P[c]) against the best (bf, bi, bj) *)
Definition cand_step (x y : array float) (P : array int) (p : int)
    (c : int) (st : float * int * int) : float * int * int :=
  let '(bf, bi, bj) := st in
  let q := P.[c] in
  let f := fd x y p q in
  if (bf + tol <? f)%float then st
  else if dlt (dex x y p q) (dex x y bi bj) then (f, p, q) else st.

(* go on unless every point from position c on is, by its bucket's least
   abscissa, certainly farther from p than the best *)
Definition cand_cont (x : array float) (K : array int) (M : array float)
    (P : array int) (p kp : int) (c : int) (st : float * int * int) : bool :=
  let '(bf, _, _) := st in
  let kq := K.[P.[c]] in
  if kp <? kq then negb (bf + tol <? gx M.[kq] x.[p])%float else true.

Definition sweep_step (x y : array float) (K : array int) (M : array float)
    (P : array int) (n : int) (a : int) (st : float * int * int) : float * int * int :=
  let p := P.[a] in
  loop n (cand_cont x K M P p K.[p]) (cand_step x y P p) (a + 1) st.

Definition closestpair (x y : array float) : uint * uint :=
  let n := PArray.length x in
  if 2 <=? n then
    let s := (of_uint63 n / cinit)%float in
    let n1 := n - 1 in
    let K := loop n (fun _ _ => true) (key_step x s n1) 0 (PArray.make n 0) in
    let C := loop n (fun _ _ => true) (count_step K) 0 (PArray.make n 0) in
    let '(C, _) := loop n (fun _ _ => true) prefix_step 0 (C, 0) in
    let '(P, _) := loop n (fun _ _ => true) (place_step K) 0 (PArray.make n 0, C) in
    let M := loop n (fun _ _ => true) (min_step x K) 0 (PArray.make n cinit) in
    let '(_, i, j) := loop n (fun _ _ => true) (sweep_step x y K M P n) 0 (fd x y 0 1, 0, 1) in
    (i, j)
  else (0, 1).

(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Reals: the float squared distance and its rounding                  *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Local Instance prec53' : FLX.Prec_gt_0 53 := eq_refl _.
Local Instance fexp64_valid' : Generic_fmt.Valid_exp fexp64 := FLT.FLT_exp_valid _ _.

Local Close Scope R_scope.

Local Notation bp := (Raux.bpow Zaux.radix2).

Local Open Scope R_scope.

Local Close Scope R_scope.

(* ------------------------------------------------------------------ *)
(* The float filters against the exact squared distances               *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Local Close Scope R_scope.
