(* Executable implementation and its required termination dependencies.
   Correctness proofs are in polymul2_proofs.v. *)
(* Implementation of polymul2 (polymul2.spec): exact polynomial product by
   a binary64 complex FFT on split coefficients.

   Code.  Every coefficient c (a signed 32-bit integer) is split into SIX
   balanced 6-bit limbs, c = sum_{i<6} (d_i - 32) 64^i with d_i the base-64
   digits of c + KOFF (Uint63 shifts and masks).  N = 2^lg is the smallest
   power of two >= |a| + |b| - 1.  The 12 limb polynomials are transformed
   by a radix-2 Stockham FFT (natural order in and out, two pairs of flat
   float buffers used in ping-pong, all threaded linearly); the twiddles of
   stage s, w^k = exp(2 i pi k / 2^(s+1)), are built once per call from the
   stage s-1 table (even k: copy, odd k: one complex product by the base
   exp(2 i pi / 2^(s+1))), the bases by the sqrt half-angle recursion
   c' = sqrt((1 + c)/2), s' = s / (2 c').  For each g < 6 the pointwise sum
   P = sum_{i+j=2g} A_i B_j + I sum_{i+j=2g+1} A_i B_j is inverse-transformed
   (one complex inverse transform for two weights), scaled by 1/N, rounded
   to the nearest integer with the 1.5 * 2^52 trick and read back through
   frshiftexp / normfr_mantissa; the result cell accumulates
   D_2g 64^2g + D_(2g+1) 64^(2g+1) in wrapping Uint63 arithmetic.  No nat,
   no Z, no list in the code; loops terminate by an erased Acc on a Z gap.

   Proof.  Exact side (Parts A-C): complex numbers as pairs of reals, the
   stage map, its isometry (|.|^2 doubles), the composition of the lg stages
   is the DFT, orthogonality of the roots of unity, the Cauchy product.
   Rounded side (Parts D-E): the code is mirrored by functions over R built
   from rnd (ReprFloat); a butterfly errs by (5.43 eps + delta)(|u| + |v|),
   a stage by 2 alpha ||x|| in the 2-norm, the whole transform by
   sqrt(2)^lg (||x|| + 1) 0.78 sum_s alpha_s; the half-angle bases err by
   at most 4 eps (cos) and 7 eps (sin), the stage-s twiddles by 15.1 s eps.
   The final bound (FinalErr) is 0.2465 per output before scaling, with
   forward errors bounded through Cauchy-Schwarz in l1; the scaling and the
   rounding step keep it below 1/2.  Part G relates every loop to its
   mirror (repr on every cell), Part IntId reassembles the limbs into
   prod_coeff, the convolution formula, and the 63-bit word read as a
   signed integer is the exact coefficient by vi_product.  The spec states
   the product by evaluation (p(x) = a(x) * b(x) at every integer x, with
   the length); Part 0 states the convolution formula (the former spec's
   model) and proves that the list it defines is that product. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Sint63.
From Respeced Require Import Repr ReprFloat.
From Flocq Require Core.Core IEEE754.BinarySingleNaN IEEE754.PrimFloat.
Import ListNotations.

Unset Lia Cache.

(* ====================================================================== *)
(* Part F.  The program                                                   *)
(* ====================================================================== *)

Local Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

(* the one loop: for i = lo .. hi - 1, s := f i s *)
Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (f : int -> St -> St) (i : int) (s : St)
    (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.

Definition loop (hi : int) (f : int -> St -> St) (i : int) (s : St) : St :=
  wloop hi f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* the smallest k with L <= 2^k (k < 63) *)
Fixpoint lg_find (L k : int) (H : Acc (Zwf 0) (gap 62 k)) {struct H} : int :=
  match bdec (k <? 62) with
  | left Hk => if L <=? (1 << k) then k else lg_find L (k + 1) (Acc_inv H (dec_step 62 k Hk))
  | right _ => k
  end.

Definition log2up (L : int) : int := lg_find L 0 (Zwf_well_founded 0 (gap 62 0)).

(* --- twiddles: stage s (s < lg) at offsets 2^s .. 2^(s+1) - 1 --- *)

Definition tw_cell (m hm : int) (bc bs : float) (k : int) (st : array float * array float)
    : array float * array float :=
  let '(tre, tim) := st in
  let src := hm + (k >> 1) in
  let ar := tre.[src] in
  let ai := tim.[src] in
  if (k land 1) =? 0 then (tre.[m + k <- ar], tim.[m + k <- ai])
  else (tre.[m + k <- (ar * bc - ai * bs)%float], tim.[m + k <- (ar * bs + ai * bc)%float]).

Definition tw_stage (s : int) (st : array float * array float * float * float)
    : array float * array float * float * float :=
  let '(tre, tim, bc, bs) := st in
  let m := 1 << s in
  let '(tre, tim) := loop m (tw_cell m (1 << (s - 1)) bc bs) 0 (tre, tim) in
  let c' := PrimFloat.sqrt ((1 + bc) * 0.5)%float in
  (tre, tim, c', (bs / (2 * c'))%float).

Definition build_tw (lg N : int) : array float * array float :=
  let tre := (PArray.make N 0%float).[1 <- 1%float] in
  let tim := PArray.make N 0%float in
  let '(tre, tim, _, _) := loop lg tw_stage 1 (tre, tim, 0%float, 1%float) in
  (tre, tim).

(* --- one stage of the transform: span r = 2^sh, twiddles at m + q --- *)

Definition bfly (sh m half : int) (neg : bool) (sre sim tre tim : array float)
    (j : int) (st : array float * array float) : array float * array float :=
  let '(dre, dim) := st in
  let q := j >> sh in
  let i1 := j + (q << sh) in
  let i2 := i1 + (1 << sh) in
  let wr := tre.[m + q] in
  let wi := if neg then (- tim.[m + q])%float else tim.[m + q] in
  let ur := sre.[i1] in
  let ui := sim.[i1] in
  let vr := sre.[i2] in
  let vi := sim.[i2] in
  let tr := (wr * vr - wi * vi)%float in
  let ti := (wr * vi + wi * vr)%float in
  (dre.[j <- (ur + tr)%float].[j + half <- (ur - tr)%float],
   dim.[j <- (ui + ti)%float].[j + half <- (ui - ti)%float]).

Definition fft_stage (lg half : int) (neg : bool) (tre tim : array float) (s : int)
    (st : array float * array float * array float * array float)
    : array float * array float * array float * array float :=
  let '(sre, sim, dre, dim) := st in
  let '(dre, dim) := loop half (bfly (lg - 1 - s) (1 << s) half neg sre sim tre tim) 0 (dre, dim) in
  (dre, dim, sre, sim).

Definition fft (lg half : int) (neg : bool) (tre tim : array float) (re im : array float)
    : array float * array float :=
  let N := half + half in
  let '(re, im, _, _) := loop lg (fft_stage lg half neg tre tim) 0
                            (re, im, PArray.make N 0%float, PArray.make N 0%float) in
  (re, im).

(* --- limbs: c = sum_i (d_i - 32) 64^i, d_i the base-64 digits of c + KOFF --- *)

Definition KOFF : int := 34905131040.

Definition limb (c i : int) : float :=
  (of_uint63 (((c + KOFF) >> (6 * i)) land 63) - 32)%float.

Definition load (x : array sint) (n N i : int) : array float :=
  loop n (fun t a => a.[t <- limb x.[t] i]) 0 (PArray.make N 0%float).

Definition copy_out (N off : int) (yr yi : array float) (st : array float * array float)
    : array float * array float :=
  loop N (fun k st => let '(BR, BI) := st in (BR.[off + k <- yr.[k]], BI.[off + k <- yi.[k]])) 0 st.

Definition NL : int := 6.

Definition fwd_all (x : array sint) (n lg half : int) (tre tim : array float)
    : array float * array float :=
  let N := half + half in
  loop NL (fun i st =>
      let '(yr, yi) := fft lg half false tre tim (load x n N i) (PArray.make N 0%float) in
      copy_out N (i * N) yr yi st) 0 (PArray.make (NL * N) 0%float, PArray.make (NL * N) 0%float).

(* --- pointwise products: P = sum_{i+j=w} A_i B_j + I * sum_{i+j=w+1} A_i B_j, w = 2g --- *)

Definition cacc (ar ai br bi : float) (st : float * float) : float * float :=
  let '(qr, qi) := st in ((qr + (ar * br - ai * bi))%float, (qi + (ar * bi + ai * br))%float).

Definition pterm (w N k : int) (AR AI BR BI : array float) (i : int) (st : float * float) : float * float :=
  if andb (i <=? w) (w - i <? NL) then
    cacc AR.[i * N + k] AI.[i * N + k] BR.[(w - i) * N + k] BI.[(w - i) * N + k] st
  else st.

Definition pcell (g N : int) (AR AI BR BI : array float) (k : int) (st : array float * array float)
    : array float * array float :=
  let '(pr, pim) := st in
  let '(q0r, q0i) := loop NL (pterm (g + g) N k AR AI BR BI) 0 (0%float, 0%float) in
  let '(q1r, q1i) := loop NL (pterm (g + g + 1) N k AR AI BR BI) 0 (0%float, 0%float) in
  (pr.[k <- (q0r - q1i)%float], pim.[k <- (q0i + q1r)%float]).

Definition products (g N : int) (AR AI BR BI : array float) : array float * array float :=
  loop N (pcell g N AR AI BR BI) 0 (PArray.make N 0%float, PArray.make N 0%float).

(* --- reading back: nearest integer of z (|z| < 2^51) as a 63-bit word --- *)

Definition MAGIC : float := 6755399441055744%float.
Definition MAGICI : int := 6755399441055744.

Definition toint (z : float) : int :=
  let (f, _) := frshiftexp (z + MAGIC)%float in normfr_mantissa f - MAGICI.

Definition accum (g L : int) (invN : float) (yr yi : array float) (R : array int) : array int :=
  loop L (fun q R =>
      let d0 := toint (yr.[q] * invN)%float in
      let d1 := toint (yi.[q] * invN)%float in
      R.[q <- R.[q] + (d0 << (12 * g)) + (d1 << (12 * g + 6))]) 0 R.

Definition polymul_impl (x y : array sint) : array sint :=
  let na := PArray.length x in
  let nb := PArray.length y in
  let L := na + nb - 1 in
  let lg := log2up L in
  let half := 1 << (lg - 1) in
  let N := half + half in
  let '(tre, tim) := build_tw lg N in
  let '(AR, AI) := fwd_all x na lg half tre tim in
  let '(BR, BI) := fwd_all y nb lg half tre tim in
  let invN := (1 / of_uint63 N)%float in
  loop NL (fun g R =>
      let '(pr, pim) := products g N AR AI BR BI in
      let '(yr, yi) := fft lg half true tre tim pr pim in
      accum g L invN yr yi R) 0 (PArray.make L 0).

(* ---------------------------------------------------------------------- *)
(* The spec's items, at top level                                         *)
(* ---------------------------------------------------------------------- *)

Definition polymul : array sint -> array sint -> array sint := polymul_impl.
