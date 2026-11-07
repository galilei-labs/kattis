(* Implementation of equationsolver_exact.spec under steering v4.

   v4 = ../implem-bens-3 (steering v3), pasted, with the singular branch
   (float rank r < n) extended : the k = n - r dropped rows of Q, rounded,
   are checked exactly as reduced left-null vectors (any of them proving
   the system inconsistent gives Inconsistent) ; the padded n x n matrix B
   (rows outside D copied from A with the free columns C zeroed, row d_t
   the unit row of its paired free column c_t ; a nested array, the one
   nested table the steering allows) is certified injective by the
   eps < 1 half of the certificate ([certify_inj]), which decides
   Multiple ; otherwise v3's witness pair, then the exact fallback.
   The Prop side : [exact_exists_arr] (injective => surjective, for any
   float matrix), [lnull_extend] and [padded_math].

   v3 =../implem-bens-2 (steering v2) with the float decode [dec] made
   constant time : frshiftexp + normfr_mantissa + Uint63.to_Z, no copy of
   Prim2SF (no shr_fexp / Zdigits2), and i2z / z2i the primitives
   Uint63.to_Z / of_Z instead of bit loops.  Everything else is v2's.

   Part 1 (from ../implem-bens-1, the exact Gauss-Jordan over Z) : the
   fallback [solve_exact] and its proof, plus the elimination theory
   generalised to every scale of the right-hand side, which gives
   [exact_exists] (an injective system has a solution).
   Part 2 : the float path -- unverified Gaussian elimination with partial
   pivoting giving x~ and R ~ A^-1, the certificate ||I - RA|| < 1 and the
   residual bound (float dot products with a proven forward error bound,
   norm arithmetic exact on dyadics), the Multiple / Inconsistent witness
   checks (exact), and [solve]. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Respeced Require Import Repr.
From Respeced Require Import ZBig.
Import ListNotations.

Open Scope uint63_scope.
Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device and the loop combinator                      *)
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
(* Conversions int <-> Z : the primitives, constant time (steering v3) *)
(* ------------------------------------------------------------------ *)

(* Uint63.to_Z / of_Z, called directly; on the arrays_bigint route
   Respeced.ExtrZBigint maps them to Bigint.of_uint63 / to_uint63 *)
Definition i2z (x : int) : Z := to_Z x.
Definition z2i (z : Z) : int := of_Z z.

(* ------------------------------------------------------------------ *)
(* SF2Prim, for the fallback's output rounding only                    *)
(* ------------------------------------------------------------------ *)

Definition ldexp' (f : float) (e : Z) : float :=
  let e' := Z.max (Z.min e (Z.sub emax emin)) (Z.sub (Z.sub emin emax) (Zpos 1)) in
  ldshiftexp f (z2i (Z.add e' shift)).

Definition SF2Prim' (ef : spec_float) : float :=
  match ef with
  | S754_nan => nan
  | S754_zero false => zero
  | S754_zero true => neg_zero
  | S754_infinity false => infinity
  | S754_infinity true => neg_infinity
  | S754_finite s m e =>
    let pm := of_uint63 (z2i (Zpos m)) in
    let f := ldexp' pm e in
    if s then (-f)%float else f
  end.

(* a float, read exactly, in constant time : signed mantissa and exponent,
   (0, 0) when not finite or zero.  For a subnormal the mantissa is padded
   with trailing zeros (a non-canonical pair, the same value). *)
Definition dec (f : float) : Z * Z :=
  if is_nan f then (0%Z, 0%Z)
  else if is_zero f then (0%Z, 0%Z)
  else if is_infinity f then (0%Z, 0%Z)
  else
    let (r, e) := frshiftexp f in
    let m := to_Z (normfr_mantissa r) in
    ((if get_sign f then (- m)%Z else m), (to_Z e - shift - prec)%Z).

(* the integer f * 2^-E, for E at most the exponent of f *)
Definition scale (f : float) (E : Z) : Z := Z.shiftl (fst (dec f)) (snd (dec f) - E).

(* the rounding of a rational to the nearest binary64 (zero on overflow) *)
Definition qr (sx : bool) (mx : positive) (sy : bool) (my : positive) : float :=
  let '(mz, ez, lz) := SFdiv_core_binary prec emax (Zpos mx) 0 (Zpos my) 0 in
  match SpecFloat.binary_round_aux prec emax (xorb sx sy) mz ez lz with
  | S754_finite s m e => SF2Prim' (S754_finite s m e)
  | _ => zero
  end.

Definition qround (num den : Z) : float :=
  match num, den with
  | Zpos mx, Zpos my => qr false mx false my
  | Zpos mx, Zneg my => qr false mx true my
  | Zneg mx, Zpos my => qr true mx false my
  | Zneg mx, Zneg my => qr true mx true my
  | _, _ => zero
  end.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The table T : n rows of w = n + 1 integers, row-major, the last
   column being the right-hand side. *)

(* the least exponent of a row (and 0) *)
Definition row_exp (n : int) (row : array float) (bi : float) : Z :=
  loop n (fun _ _ => true) (fun j E => Z.min E (snd (dec row.[j]))) 0
       (Z.min 0 (snd (dec bi))).

Definition fill_row (n w i : int) (row : array float) (E : Z) (T : array Z) : array Z :=
  loop n (fun _ _ => true) (fun j T => T.[i * w + j <- scale row.[j] E]) 0 T.

Definition build_step (a : array (array float)) (b : array float) (n w : int)
    (i : int) (T : array Z) : array Z :=
  let row := a.[i] in
  let bi := b.[i] in
  let E := row_exp n row bi in
  let T := fill_row n w i row E T in
  T.[i * w + n <- scale bi E].

Definition build (a : array (array float)) (b : array float) (n w : int) : array Z :=
  loop n (fun _ _ => true) (build_step a b n w) 0 (PArray.make (n * w) 0%Z).

(* the first row q in [r, n) with T[q][c] <> 0, n if none *)
Definition find_piv (T : array Z) (n w c r : int) : int :=
  loop n (fun _ _ => true)
    (fun i s => if s =? n then (if Z.eqb T.[i * w + c] 0 then s else i) else s) r n.

Definition swap_rows (T : array Z) (w q r : int) : array Z :=
  loop w (fun _ _ => true)
    (fun j T => let x := T.[r * w + j] in let y := T.[q * w + j] in
                T.[r * w + j <- y].[q * w + j <- x]) 0 T.

(* row i := a * row i - b * row r *)
Definition upd_row (T : array Z) (w i r : int) (a b : Z) : array Z :=
  loop w (fun _ _ => true)
    (fun j T => T.[i * w + j <- (a * T.[i * w + j] - b * T.[r * w + j])%Z]) 0 T.

Definition row_gcd (T : array Z) (w i : int) : Z :=
  loop w (fun _ _ => true) (fun j g => zgcd g T.[i * w + j]) 0 0%Z.

Definition div_row (T : array Z) (w i : int) (g : Z) : array Z :=
  loop w (fun _ _ => true) (fun j T => T.[i * w + j <- (T.[i * w + j] / g)%Z]) 0 T.

(* clear column c of row i with the pivot row r (pivot a), then divide
   the row by the gcd of its entries *)
Definition elim_row (w c r : int) (a : Z) (i : int) (T : array Z) : array Z :=
  if i =? r then T else
  let b := T.[i * w + c] in
  if Z.eqb b 0 then T else
  let T := upd_row T w i r a b in
  let g := row_gcd T w i in
  if Z.ltb 1 g then div_row T w i g else T.

(* Gauss-Jordan step on column c, r pivots so far *)
Definition col_step (n w : int) (c : int) (st : array Z * int) : array Z * int :=
  let (T, r) := st in
  let q := find_piv T n w c r in
  if q =? n then (T, r) else
  let T := swap_rows T w q r in
  let a := T.[r * w + c] in
  (loop n (fun _ _ => true) (elim_row w c r a) 0 T, r + 1).

Definition eliminate (n w : int) (T : array Z) : array Z * int :=
  loop n (fun _ _ => true) (col_step n w) 0 (T, 0).

Definition inconsistent (T : array Z) (n w r : int) : bool :=
  loop n (fun _ _ => true) (fun i fl => orb fl (negb (Z.eqb T.[i * w + n] 0))) r false.

Definition output (T : array Z) (n w : int) : array float :=
  loop n (fun _ _ => true)
    (fun i out => out.[i <- qround T.[i * w + n] T.[i * w + i]]) 0 (PArray.make n zero).

Definition solve_exact (n : uint) (a : array (array float)) (b : array float) : outcome (array float) :=
  let w := n + 1 in
  let T := build a b n w in
  let (T, r) := eliminate n w T in
  if inconsistent T n w r then Inconsistent
  else if r <? n then Multiple
  else Unique (output T n w).

(* ================================================================== *)
(* Proofs                                                             *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* The loop combinator                                                 *)
(* ------------------------------------------------------------------ *)

Section LoopProof.
Context {St : Type}.

Lemma wloop_eq : forall (hi : int) cont (f : int -> St -> St) i s H,
  wloop hi cont f i s H =
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma loop_inv : forall (P : int -> St -> Prop) (hi lo : int) cont f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> cont j t = true ->
     P (j + 1) (f j t)) ->
  exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (loop hi cont f lo s) /\
    (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (loop hi cont f lo s) = false)).
Proof.
  intros P hi lo cont f s Hle Hp Hstep. unfold loop.
  assert (G : forall n i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = n ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t ->
     exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (wloop hi cont f i t H) /\
       (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (wloop hi cont f i t H) = false))).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H En Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      destruct (cont i t) eqn:Ec.
      + apply (IH (gap hi (i + 1))).
        * rewrite <- En. apply dec_step; exact Hlt.
        * reflexivity.
        * pose proof (to_Z_bounded hi).
          assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
        * apply Hstep; auto; lia.
      + exists i. split; [lia |]. split; [exact Pt | right; split; [lia | exact Ec]].
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      exists i. split; [lia |]. split; [exact Pt | left; lia]. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi (fun _ _ => true) f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep.
  destruct (loop_inv P hi lo (fun _ _ => true) f s Hle Hp) as (j & _ & Pj & [E | [_ E]]).
  - intros j t Hj Pt _. apply Hstep; auto.
  - apply to_Z_inj in E. subst j. exact Pj.
  - discriminate.
Qed.

End LoopProof.

(* ------------------------------------------------------------------ *)
(* The conversions are the stock ones                                  *)
(* ------------------------------------------------------------------ *)

Lemma i2z_spec : forall x, i2z x = to_Z x.
Proof. reflexivity. Qed.

Lemma z2i_spec : forall z, z2i z = of_Z z.
Proof. reflexivity. Qed.

Lemma SF2Prim'_eq : forall z, SF2Prim' z = SF2Prim z.
Proof.
  intros [[]|[]| |s m e]; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Floats, exactly                                                     *)
(* ------------------------------------------------------------------ *)

From Flocq Require Import Core IEEE754.BinarySingleNaN.
From Flocq Require IEEE754.PrimFloat.
From Respeced Require Import ReprFloat.
Notation float := PrimFloat.float.
Local Instance prec53' : Prec_gt_0 53 := eq_refl _.
Local Instance fexp64_valid' : Valid_exp fexp64 := FLT_exp_valid _ _.

Lemma IZR_pow2 : forall k, (0 <= k)%Z -> IZR (2 ^ k) = powerRZ 2 k.
Proof.
  intros k Hk. rewrite <- (Z2Nat.id k) by lia. rewrite <- pow_IZR, pow_powerRZ. reflexivity.
Qed.

(* the constant-time decode against FloatAxioms' frshiftexp_spec and
   normfr_mantissa_spec, through SpecFloat's SFfrexp / SFnormfr_mantissa *)
Lemma iter_xO : forall k m, Zpos (Pos.iter xO m k) = (Zpos m * 2 ^ Zpos k)%Z.
Proof.
  induction k as [| k IH] using Pos.peano_ind; intros m.
  - simpl. lia.
  - rewrite Pos.iter_succ, Pos2Z.inj_succ, Z.pow_succ_r by lia.
    change (Zpos (xO (Pos.iter xO m k))) with (2 * Zpos (Pos.iter xO m k))%Z. rewrite IH. ring.
Qed.

Lemma Prim2SF_sign : forall f s m e, PrimFloat.is_nan f = false -> PrimFloat.is_zero f = false -> PrimFloat.is_infinity f = false ->
  Prim2SF f = S754_finite s m e -> s = get_sign f.
Proof.
  intros f s m e H1 H2 H3. unfold Prim2SF. rewrite H1, H2, H3.
  destruct (FloatOps.Z.frexp f) as [r ex]. cbv zeta.
  destruct (shr_fexp prec emax (to_Z (normfr_mantissa r)) (ex - prec) loc_Exact) as [shr e'].
  destruct (shr_m shr); intros E; inversion E; reflexivity.
Qed.

Lemma dec_val : forall f, (IZR (fst (dec f)) * powerRZ 2 (snd (dec f)))%R = fval f.
Proof.
  intros f. unfold dec, fval.
  destruct (PrimFloat.is_nan f) eqn:H1.
  { unfold Prim2SF. rewrite H1. simpl. ring. }
  destruct (PrimFloat.is_zero f) eqn:H2.
  { unfold Prim2SF. rewrite H1, H2. simpl. ring. }
  destruct (PrimFloat.is_infinity f) eqn:H3.
  { unfold Prim2SF. rewrite H1, H2, H3. simpl. ring. }
  pose proof (frshiftexp_spec f) as HF.
  destruct (frshiftexp f) as [r e]. cbv zeta.
  pose proof (normfr_mantissa_spec r) as HN.
  destruct (Prim2SF f) as [s|s| |s m ex] eqn:HP.
  - injection HF as Hr He. rewrite Hr in HN. simpl in HN. rewrite HN.
    destruct (get_sign f); simpl; ring.
  - injection HF as Hr He. rewrite Hr in HN. simpl in HN. rewrite HN.
    destruct (get_sign f); simpl; ring.
  - injection HF as Hr He. rewrite Hr in HN. simpl in HN. rewrite HN.
    destruct (get_sign f); simpl; ring.
  - pose proof (Prim2SF_sign f s m ex H1 H2 H3 HP) as Hs. subst s.
    unfold SFfrexp in HF. destruct (Z.leb prec (Zpos (digits2_pos m))) eqn:Hd.
    + injection HF as Hr He. rewrite Hr in HN. unfold SFnormfr_mantissa in HN.
      rewrite Z.eqb_refl in HN. rewrite HN. cbn [fst snd Z.of_N].
      replace (to_Z e - shift - prec)%Z with ex by lia.
      destruct (get_sign f); rewrite ?opp_IZR; ring.
    + apply Z.leb_gt in Hd.
      set (d := (prec - Zpos (digits2_pos m))%Z) in HF.
      assert (Hd' : (0 < d)%Z) by (unfold d; lia).
      injection HF as Hr He. rewrite Hr in HN. unfold SFnormfr_mantissa in HN.
      rewrite Z.eqb_refl in HN. rewrite HN. cbn [fst snd Z.of_N].
      rewrite iter_xO, Z2Pos.id by exact Hd'.
      replace (to_Z e - shift - prec)%Z with (ex - d)%Z by lia.
      assert (Hv : (IZR (Zpos m * 2 ^ d) * powerRZ 2 (ex - d) = IZR (Zpos m) * powerRZ 2 ex)%R).
      { rewrite mult_IZR, IZR_pow2 by lia. rewrite Rmult_assoc, <- powerRZ_add by lra.
        replace (d + (ex - d))%Z with ex by ring. reflexivity. }
      destruct (get_sign f); rewrite ?opp_IZR; [rewrite Ropp_mult_distr_l_reverse, Hv |]; auto.
Qed.

(* a represented real is its signed mantissa times 2^exponent *)
Lemma fval_dec : forall (f : float) r, repr f r ->
  r = (IZR (fst (dec f)) * powerRZ 2 (snd (dec f)))%R.
Proof.
  intros f r [_ <-]. symmetry. apply dec_val.
Qed.

Lemma scale_spec : forall (f : float) E, (E <= snd (dec f))%Z ->
  (IZR (scale f E) * powerRZ 2 E = IZR (fst (dec f)) * powerRZ 2 (snd (dec f)))%R.
Proof.
  intros f E HE. unfold scale. rewrite Z.shiftl_mul_pow2 by lia. rewrite mult_IZR.
  rewrite IZR_pow2 by lia. rewrite Rmult_assoc, <- powerRZ_add by lra.
  replace (snd (dec f) - E + E)%Z with (snd (dec f)) by ring. reflexivity.
Qed.

Lemma repr_zero : repr zero 0%R.
Proof. split; reflexivity. Qed.

Lemma repr_SF : forall z, SpecFloat.valid_binary 53%Z 1024%Z z = true -> is_finite_SF z = true ->
  repr (SF2Prim z) (SF2R radix2 z).
Proof.
  intros z Hv Hf. apply repr_float_iff.
  assert (H : B2SF (Flocq.IEEE754.PrimFloat.Prim2B (SF2Prim z)) = z).
  { rewrite Flocq.IEEE754.PrimFloat.B2SF_Prim2B. apply Prim2SF_SF2Prim. exact Hv. }
  split.
  - rewrite <- is_finite_SF_B2SF, H. exact Hf.
  - rewrite <- SF2R_B2SF, H. reflexivity.
Qed.

Lemma qr_correct : forall sx mx sy my,
  let q := (IZR (cond_Zopp sx (Zpos mx)) / IZR (cond_Zopp sy (Zpos my)))%R in
  exists v, repr (qr sx mx sy my) v /\ (Rabs (rnd q) < bpow radix2 1024 -> v = rnd q)%R.
Proof.
  intros sx mx sy my q.
  pose proof (Bdiv_correct_aux 53 1024 Flocq.IEEE754.PrimFloat.Hprec Flocq.IEEE754.PrimFloat.Hmax
                mode_NE sx mx 0 sy my 0) as H.
  cbv zeta in H.
  unfold qr. destruct (SFdiv_core_binary prec emax (Zpos mx) 0 (Zpos my) 0) as [[mz ez] lz] eqn:Ed.
  change prec with 53%Z in Ed. change emax with 1024%Z in Ed. rewrite Ed in H. cbv iota in H.
  rewrite Flocq.IEEE754.PrimFloat.binary_round_aux_equiv.
  change prec with 53%Z. change emax with 1024%Z.
  replace (F2R (Float radix2 (cond_Zopp sx (Zpos mx)) 0)) with (IZR (cond_Zopp sx (Zpos mx))) in H
    by (unfold F2R; simpl; ring).
  replace (F2R (Float radix2 (cond_Zopp sy (Zpos my)) 0)) with (IZR (cond_Zopp sy (Zpos my))) in H
    by (unfold F2R; simpl; ring).
  fold q in H.
  destruct H as [Hv H]. revert H. case Rlt_bool_spec; intros Hlt H.
  - destruct H as [H1 [H2 _]].
    destruct (binary_round_aux 53 1024 mode_NE (xorb sx sy) mz ez lz) as [s|s| |s m e] eqn:Ez;
      try discriminate.
    + exists 0%R. split; [exact repr_zero |]. intros _. exact H1.
    + exists (SF2R radix2 (S754_finite s m e)). split.
      * rewrite SF2Prim'_eq. apply repr_SF; assumption.
      * intros _. exact H1.
  - rewrite H. simpl. exists 0%R. split; [exact repr_zero |]. intros Hlt'. exfalso.
    assert (E : rnd q = round radix2 (fexp 53 1024) (round_mode mode_NE) q) by reflexivity.
    rewrite E in Hlt'. change (IZR (Z.pow_pos 2 1024)) with (bpow radix2 1024) in Hlt'. lra.
Qed.

Lemma near_ok : forall q v, (Rabs (rnd q) < bpow radix2 1024 -> v = rnd q)%R ->
  attainable q -> (Rabs (v - q) <= 1 / 1000)%R.
Proof.
  intros q v Hv [f [[x Hx] Hf]].
  pose proof (repr_float_format x f Hx) as Ff. pose proof (repr_float_bounded x f Hx) as Bf.
  assert (HN : Rnd_N_pt (generic_format radix2 fexp64) q (rnd q)).
  { unfold rnd. apply round_N_pt. exact _. }
  destruct HN as [Fr HN]. specialize (HN f Ff).
  assert (Hlt : (Rabs (rnd q) < bpow radix2 1024)%R).
  { destruct (Rlt_or_le (Rabs (rnd q)) (bpow radix2 1024)) as [| Hge]; [assumption | exfalso].
    assert (Fa : generic_format radix2 fexp64 (Rabs f)) by (apply generic_format_abs; exact Ff).
    assert (Fb : generic_format radix2 fexp64 (bpow radix2 1024)).
    { apply generic_format_bpow. unfold fexp64, FLT_exp. cbn. lia. }
    pose proof (pred_ge_gt radix2 fexp64 (Rabs f) (bpow radix2 1024) Fa Fb Bf) as Hp.
    rewrite pred_bpow in Hp. change (fexp64 1024) with 971%Z in Hp.
    pose proof (Rabs_triang_inv (rnd q) f) as T1.
    pose proof (Rabs_triang (rnd q - q) (q - f)) as T2.
    replace (rnd q - q + (q - f))%R with (rnd q - f)%R in T2 by ring.
    rewrite (Rabs_minus_sym q f) in T2.
    pose proof (bpow_le radix2 0 971 ltac:(lia)) as B0. change (bpow radix2 0) with 1%R in B0.
    lra. }
  rewrite (Hv Hlt). lra.
Qed.

Lemma qround_spec : forall num den, den <> 0%Z ->
  exists v, repr (qround num den) v /\
    (attainable (IZR num / IZR den) -> Rabs (v - IZR num / IZR den) <= 1 / 1000)%R.
Proof.
  intros num den Hd.
  destruct num as [| mx | mx]; [| destruct den as [| my | my]; [easy | |] ..].
  - exists 0%R. split; [destruct den; exact repr_zero |].
    intros _. unfold Rdiv. rewrite Rmult_0_l, Rminus_0_r, Rabs_R0. lra.
  - destruct (qr_correct false mx false my) as (v & Hr & Hv). exists v. split; [exact Hr |].
    apply near_ok. exact Hv.
  - destruct (qr_correct false mx true my) as (v & Hr & Hv). exists v. split; [exact Hr |].
    apply near_ok. exact Hv.
  - destruct (qr_correct true mx false my) as (v & Hr & Hv). exists v. split; [exact Hr |].
    apply near_ok. exact Hv.
  - destruct (qr_correct true mx true my) as (v & Hr & Hv). exists v. split; [exact Hr |].
    apply near_ok. exact Hv.
Qed.

(* ------------------------------------------------------------------ *)
(* Linear systems over integer tables, Prop side                       *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

Fixpoint sumR (f : nat -> R) (k : nat) : R :=
  match k with
  | O => 0
  | S k => sumR f k + f k
  end.

Lemma sumR_ext : forall f g k, (forall j, (j < k)%nat -> f j = g j) -> sumR f k = sumR g k.
Proof.
  intros f g k H. induction k as [| k IH]; simpl; [reflexivity |].
  rewrite IH by (intros; apply H; lia). rewrite (H k) by lia. reflexivity.
Qed.

Lemma sumR_lin : forall f g c1 c2 k,
  sumR (fun j => c1 * f j + c2 * g j) k = c1 * sumR f k + c2 * sumR g k.
Proof. intros f g c1 c2 k. induction k as [| k IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma sumR_plus : forall f g k, sumR (fun j => f j + g j) k = sumR f k + sumR g k.
Proof. intros f g k. induction k as [| k IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma sumR_zero : forall f k, (forall j, (j < k)%nat -> f j = 0) -> sumR f k = 0.
Proof.
  intros f k H. induction k as [| k IH]; simpl; [reflexivity |].
  rewrite IH by (intros; apply H; lia). rewrite (H k) by lia. ring.
Qed.

Lemma sumR_delta : forall a v k, (a < k)%nat ->
  sumR (fun j => if Nat.eqb j a then v else 0) k = v.
Proof.
  intros a v k. induction k as [| k IH]; intros H; [lia |]. simpl.
  destruct (Nat.eqb_spec k a) as [-> | Hne].
  - rewrite sumR_zero; [ring |]. intros j Hj. destruct (Nat.eqb_spec j a); [lia | reflexivity].
  - rewrite IH by lia. ring.
Qed.

Lemma sumR_scal : forall f c k, sumR (fun j => c * f j) k = c * sumR f k.
Proof. intros f c k. induction k as [| k IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma sumR_scal_r : forall f c k, sumR (fun j => f j * c) k = sumR f k * c.
Proof. intros f c k. induction k as [| k IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma sumR_shift : forall f k, sumR f (S k) = f O + sumR (fun j => f (S j)) k.
Proof.
  intros f k. induction k as [| k IH]; [simpl; ring |].
  change (sumR f (S (S k))) with (sumR f (S k) + f (S k)). rewrite IH. simpl. ring.
Qed.

Section Systems.
Variable N : nat.

Definition rowsum (V : nat -> nat -> Z) (i : nat) (x : nat -> R) : R :=
  sumR (fun j => IZR (V i j) * x j) N.

Definition roweq (V : nat -> nat -> Z) (i : nat) (x : nat -> R) : Prop :=
  rowsum V i x = IZR (V i N).

Definition sol (V : nat -> nat -> Z) (x : nat -> R) : Prop :=
  forall i, (i < N)%nat -> roweq V i x.

Definition equiv (V V' : nat -> nat -> Z) : Prop := forall x, sol V x <-> sol V' x.

Lemma equiv_refl : forall V, equiv V V.
Proof. intros V x. tauto. Qed.

Lemma equiv_trans : forall V1 V2 V3, equiv V1 V2 -> equiv V2 V3 -> equiv V1 V3.
Proof. intros V1 V2 V3 H1 H2 x. specialize (H1 x). specialize (H2 x). tauto. Qed.

Lemma rowsum_ext : forall V V' i i' x, (forall j, (j < N)%nat -> V' i' j = V i j) ->
  rowsum V' i' x = rowsum V i x.
Proof. intros V V' i i' x H. apply sumR_ext. intros j Hj. rewrite H by exact Hj. reflexivity. Qed.

(* row i := (a * row i - b * row r) / g, the other rows unchanged *)
Definition rowop (V V' : nat -> nat -> Z) (i r : nat) (a b : Z) : Prop :=
  (forall k j, k <> i -> (k < N)%nat -> (j <= N)%nat -> V' k j = V k j) /\
  exists g, g <> 0%Z /\ forall j, (j <= N)%nat -> (g * V' i j = a * V i j - b * V r j)%Z.

Lemma rowop_equiv : forall V V' i r a b, (i < N)%nat -> (r < N)%nat -> i <> r -> a <> 0%Z ->
  rowop V V' i r a b -> equiv V V'.
Proof.
  intros V V' i r a b Hi Hr Hir Ha [HV (g & Hg & Hrow)] x.
  assert (Ks : forall k, k <> i -> (k < N)%nat -> rowsum V' k x = rowsum V k x /\ V' k N = V k N).
  { intros k Hki HkN. split; [apply rowsum_ext; intros j Hj; apply HV; lia | apply HV; lia]. }
  assert (Si : IZR g * rowsum V' i x = IZR a * rowsum V i x + - IZR b * rowsum V r x).
  { unfold rowsum. rewrite <- sumR_scal, <- sumR_lin. apply sumR_ext. intros j Hj.
    rewrite <- Rmult_assoc, <- mult_IZR, Hrow by lia. rewrite minus_IZR, !mult_IZR. ring. }
  assert (Ni : IZR g * IZR (V' i N) = IZR a * IZR (V i N) + - IZR b * IZR (V r N)).
  { rewrite <- mult_IZR, Hrow by lia. rewrite minus_IZR, !mult_IZR. ring. }
  assert (Hg' : IZR g <> 0) by (apply not_0_IZR; exact Hg).
  assert (Ha' : IZR a <> 0) by (apply not_0_IZR; exact Ha).
  unfold sol, roweq. split; intros H k Hk.
  - destruct (Nat.eq_dec k i) as [-> | Hne].
    + apply (Rmult_eq_reg_l (IZR g)); [| exact Hg']. rewrite Si, Ni, (H i Hi), (H r Hr). ring.
    + destruct (Ks k Hne Hk) as [-> ->]. apply H; exact Hk.
  - assert (Er : rowsum V r x = IZR (V r N)).
    { destruct (Ks r (not_eq_sym Hir) Hr) as [<- <-]. apply H; exact Hr. }
    destruct (Nat.eq_dec k i) as [-> | Hne].
    + apply (Rmult_eq_reg_l (IZR a)); [| exact Ha'].
      assert (E1 : IZR g * rowsum V' i x = IZR g * IZR (V' i N)) by (rewrite (H i Hi); reflexivity).
      rewrite Si, Ni, Er in E1. lra.
    + destruct (Ks k Hne Hk) as [<- <-]. apply H; exact Hk.
Qed.

(* swapping rows p and r *)
Definition sw (p r k : nat) : nat := if Nat.eqb k p then r else if Nat.eqb k r then p else k.

Lemma sw_lt : forall p r k, (p < N)%nat -> (r < N)%nat -> (k < N)%nat -> (sw p r k < N)%nat.
Proof. intros p r k Hp Hr Hk. unfold sw. destruct (Nat.eqb k p), (Nat.eqb k r); lia. Qed.

Lemma sw_sw : forall p r k, sw p r (sw r p k) = k.
Proof.
  intros p r k. unfold sw.
  destruct (Nat.eqb_spec k r) as [E1 | E1]; destruct (Nat.eqb_spec k p) as [E2 | E2];
    repeat (rewrite ?Nat.eqb_refl; simpl);
    repeat match goal with |- context [PeanoNat.Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end; lia.
Qed.

Lemma swap_equiv : forall V V' p r, (p < N)%nat -> (r < N)%nat ->
  (forall k j, (k < N)%nat -> (j <= N)%nat -> V' k j = V (sw p r k) j) -> equiv V V'.
Proof.
  intros V V' p r Hp Hr HV x. unfold sol, roweq.
  assert (E : forall k, (k < N)%nat -> rowsum V' k x = rowsum V (sw p r k) x /\ V' k N = V (sw p r k) N).
  { intros k Hk. split; [apply rowsum_ext; intros j Hj; apply HV; lia | apply HV; lia]. }
  split; intros H k Hk.
  - destruct (E k Hk) as [-> ->]. apply H, sw_lt; assumption.
  - pose proof (sw_sw p r k) as Hs. rewrite <- Hs.
    assert (Hk' : (sw r p k < N)%nat) by (apply sw_lt; assumption).
    destruct (E _ Hk') as [<- <-]. apply H; exact Hk'.
Qed.

(* the same table with its right-hand side multiplied by t : t = 1 is the
   system itself, t = 0 its homogeneous system *)
Definition sc (t : Z) (V : nat -> nat -> Z) (i j : nat) : Z :=
  if Nat.eqb j N then (t * V i j)%Z else V i j.

(* equivalence of the systems for every scale of the right-hand side *)
Definition equivG (V V' : nat -> nat -> Z) : Prop :=
  forall t x, sol (sc t V) x <-> sol (sc t V') x.

Definition hsol (V : nat -> nat -> Z) (x : nat -> R) : Prop :=
  forall i, (i < N)%nat -> rowsum V i x = 0.

Lemma equivG_refl : forall V, equivG V V.
Proof. intros V t x. tauto. Qed.

Lemma equivG_trans : forall V1 V2 V3, equivG V1 V2 -> equivG V2 V3 -> equivG V1 V3.
Proof. intros V1 V2 V3 H1 H2 t x. specialize (H1 t x). specialize (H2 t x). tauto. Qed.

Lemma sol_extV : forall V V' x, (forall i j, (i < N)%nat -> (j <= N)%nat -> V' i j = V i j) ->
  sol V x -> sol V' x.
Proof.
  intros V V' x H Hs i Hi. unfold roweq. rewrite (rowsum_ext V V' i i x) by (intros; apply H; lia).
  rewrite H by lia. apply Hs, Hi.
Qed.

Lemma sol_sc1 : forall V x, sol (sc 1 V) x <-> sol V x.
Proof.
  intros V x. split; apply sol_extV; intros i j Hi Hj; unfold sc;
    destruct (Nat.eqb j N); try reflexivity; ring.
Qed.

Lemma sol_sc0 : forall V x, sol (sc 0 V) x <-> hsol V x.
Proof.
  intros V x. unfold sol, roweq, hsol. split; intros H i Hi; specialize (H i Hi).
  - rewrite (rowsum_ext V (sc 0 V) i i x) in H; [rewrite H; unfold sc; rewrite Nat.eqb_refl; reflexivity |].
    intros j Hj. unfold sc. destruct (Nat.eqb_spec j N); [lia | reflexivity].
  - rewrite (rowsum_ext V (sc 0 V) i i x); [rewrite H; unfold sc; rewrite Nat.eqb_refl; reflexivity |].
    intros j Hj. unfold sc. destruct (Nat.eqb_spec j N); [lia | reflexivity].
Qed.

Lemma equivG_sol : forall V V', equivG V V' -> forall x, sol V x <-> sol V' x.
Proof.
  intros V V' H x. split; intros Hx; apply sol_sc1; apply (H 1%Z x); apply sol_sc1; exact Hx.
Qed.

Lemma equivG_hsol : forall V V', equivG V V' -> forall x, hsol V x <-> hsol V' x.
Proof.
  intros V V' H x. split; intros Hx; apply sol_sc0; apply (H 0%Z x); apply sol_sc0; exact Hx.
Qed.

Lemma rowop_equivG : forall V V' i r a b, (i < N)%nat -> (r < N)%nat -> i <> r -> a <> 0%Z ->
  rowop V V' i r a b -> equivG V V'.
Proof.
  intros V V' i r a b Hi Hr Hir Ha [HK (g & Hg & HG)] t.
  apply (rowop_equiv (sc t V) (sc t V') i r a b); auto.
  split.
  - intros k j Hk HkN Hj. unfold sc. rewrite HK by assumption. reflexivity.
  - exists g. split; [exact Hg |]. intros j Hj. unfold sc.
    destruct (Nat.eqb j N); [| apply HG; exact Hj].
    replace (g * (t * V' i j))%Z with (t * (g * V' i j))%Z by ring. rewrite HG by exact Hj. ring.
Qed.

Lemma swap_equivG : forall V V' p r, (p < N)%nat -> (r < N)%nat ->
  (forall k j, (k < N)%nat -> (j <= N)%nat -> V' k j = V (sw p r k) j) -> equivG V V'.
Proof.
  intros V V' p r Hp Hr HV t. apply (swap_equiv (sc t V) (sc t V') p r Hp Hr).
  intros k j Hk Hj. unfold sc. rewrite HV by assumption. reflexivity.
Qed.

End Systems.

(* ------------------------------------------------------------------ *)
(* Gauss-Jordan, Prop side : the invariant of the column loop          *)
(* ------------------------------------------------------------------ *)

Section Elim.
Variable N : nat.

(* after columns [0, c), r pivots : row k < r has its pivot in column p k,
   alone in its column ; rows r.. are zero on columns [0, c) ; a free
   column exists when r < c ; the pivots are diagonal when r = c *)
Definition INV (V0 V : nat -> nat -> Z) (c r : nat) : Prop :=
  equivG N V0 V /\ (r <= c <= N)%nat /\
  exists p : nat -> nat,
    (forall k, (k < r)%nat -> (p k < c)%nat /\ V k (p k) <> 0%Z /\
        forall i, (i < N)%nat -> i <> k -> V i (p k) = 0%Z) /\
    (forall i j, (r <= i < N)%nat -> (j < c)%nat -> V i j = 0%Z) /\
    ((r < c)%nat -> exists f, (f < c)%nat /\ forall k, (k < r)%nat -> p k <> f) /\
    (r = c -> forall k, (k < r)%nat -> p k = k).

Lemma INV_init : forall V0, INV V0 V0 0 0.
Proof.
  intros V0. split; [apply equivG_refl |]. split; [lia |]. exists (fun k => k).
  split; [intros; lia |]. split; [intros; lia |]. split; intros; lia.
Qed.

Lemma INV_nopiv : forall V0 V c r, INV V0 V c r -> (c < N)%nat ->
  (forall i, (r <= i < N)%nat -> V i c = 0%Z) -> INV V0 V (S c) r.
Proof.
  intros V0 V c r [He [Hrc (p & H3 & H4 & H5 & H6)]] Hc Hz.
  split; [exact He |]. split; [lia |]. exists p. split; [| split; [| split]].
  - intros k Hk. destruct (H3 k Hk) as (A & B & C). split; [lia | split; assumption].
  - intros i j Hi Hj. destruct (Nat.eq_dec j c) as [-> | Hne]; [apply Hz; lia | apply H4; lia].
  - intros _. exists c. split; [lia |]. intros k Hk. destruct (H3 k Hk) as (A & _). lia.
  - intros E. lia.
Qed.

(* the row loop of a pivot step : rows [0, i0) cleared in column c *)
Definition EL (V0 V1 : nat -> nat -> Z) (p : nat -> nat) (c r i0 : nat) (V : nat -> nat -> Z) : Prop :=
  equivG N V0 V /\ (forall j, (j <= N)%nat -> V r j = V1 r j) /\
  (forall k, (k < r)%nat -> V k (p k) <> 0%Z /\ forall i, (i < N)%nat -> i <> k -> V i (p k) = 0%Z) /\
  (forall i j, (r < i < N)%nat -> (j < c)%nat -> V i j = 0%Z) /\
  (forall i, (i < i0)%nat -> (i < N)%nat -> i <> r -> V i c = 0%Z).

(* what the pivot step knows of the swapped table V1 and of p *)
Definition PIV (V1 : nat -> nat -> Z) (p : nat -> nat) (c r : nat) : Prop :=
  (r < N)%nat /\ (c < N)%nat /\ (r <= c)%nat /\ V1 r c <> 0%Z /\ (forall j, (j < c)%nat -> V1 r j = 0%Z) /\
  (forall k, (k < r)%nat -> (p k < c)%nat) /\
  ((r < c)%nat -> exists f, (f < c)%nat /\ forall k, (k < r)%nat -> p k <> f) /\
  (r = c -> forall k, (k < r)%nat -> p k = k).

Lemma mul_eq_0_r : forall g x : Z, g <> 0%Z -> (g * x = 0)%Z -> x = 0%Z.
Proof. intros g x Hg H. apply Z.mul_eq_0 in H. lia. Qed.

Lemma EL_step : forall V0 V1 p c r i0 V V', PIV V1 p c r -> EL V0 V1 p c r i0 V -> (i0 < N)%nat ->
  ((i0 = r /\ V' = V) \/ (i0 <> r /\ rowop N V V' i0 r (V1 r c) (V i0 c))) ->
  EL V0 V1 p c r (S i0) V'.
Proof.
  intros V0 V1 p c r i0 V V' (Hr & Hc & Hrc & Ha & Hz & Hp & _ & _) (He & Hrow & H3 & H4 & H5) Hi0 [[-> ->] | [Hne Hop]].
  - split; [exact He |]. split; [exact Hrow |]. split; [exact H3 |]. split; [exact H4 |].
    intros i Hi HiN Hir. apply H5; lia.
  - pose proof Hop as [HK (g & Hg & HG)].
    assert (Ex : forall j, (j <= N)%nat -> (V i0 j = 0%Z) -> (V r j = 0%Z) -> V' i0 j = 0%Z).
    { intros j Hj E1 E2. apply (mul_eq_0_r g); [exact Hg |]. rewrite HG by exact Hj. rewrite E1, E2. ring. }
    split; [| split; [| split; [| split]]].
    + apply (equivG_trans N _ V); [exact He |]. apply (rowop_equivG N V V' i0 r (V1 r c) (V i0 c)); auto.
    + intros j Hj. rewrite HK by lia. apply Hrow; exact Hj.
    + intros k Hk. assert (Hpk := Hp k Hk). destruct (H3 k Hk) as [Nk Zk].
      assert (Vrk : V r (p k) = 0%Z) by (apply Zk; lia). split.
      * destruct (Nat.eq_dec k i0) as [-> | Hki].
        -- intros E. apply Nk. assert (E' := HG (p i0) ltac:(lia)). rewrite E, Vrk in E'.
           assert (E'' : (V1 r c * V i0 (p i0) = 0)%Z) by lia. apply Z.mul_eq_0 in E''. lia.
        -- rewrite HK by lia. exact Nk.
      * intros i Hi Hik. destruct (Nat.eq_dec i i0) as [-> | Hii].
        -- apply Ex; [lia | apply Zk; lia | exact Vrk].
        -- rewrite HK by lia. apply Zk; assumption.
    + intros i j Hi Hj. destruct (Nat.eq_dec i i0) as [-> | Hii].
      * apply Ex; [lia | apply H4; lia | rewrite Hrow by lia; apply Hz; exact Hj].
      * rewrite HK by lia. apply H4; assumption.
    + intros i Hi HiN Hir. destruct (Nat.eq_dec i i0) as [-> | Hii].
      * apply (mul_eq_0_r g); [exact Hg |]. rewrite HG by lia. rewrite (Hrow c) by lia. ring.
      * rewrite HK by lia. apply H5; lia.
Qed.

Lemma EL_init : forall V0 V V1 c r q, INV V0 V c r -> (c < N)%nat -> (r <= q < N)%nat ->
  V q c <> 0%Z ->
  (forall k j, (k < N)%nat -> (j <= N)%nat -> V1 k j = V (sw q r k) j) ->
  exists p, PIV V1 p c r /\ EL V0 V1 p c r 0 V1.
Proof.
  intros V0 V V1 c r q [He [Hrc (p & H3 & H4 & H5 & H6)]] Hc Hq Hqc HV1.
  assert (Hr : (r < N)%nat) by lia.
  assert (S1 : forall j, (j <= N)%nat -> V1 r j = V q j).
  { intros j Hj. rewrite HV1 by lia. unfold sw.
    destruct (Nat.eqb_spec r q) as [-> | Hne]; [reflexivity | rewrite Nat.eqb_refl; reflexivity]. }
  assert (Ssw : forall k, (k < N)%nat -> (r <= k)%nat -> (r <= sw q r k < N)%nat).
  { intros k Hk Hrk. unfold sw. destruct (Nat.eqb k q), (Nat.eqb k r); lia. }
  assert (Slo : forall k, (k < r)%nat -> sw q r k = k).
  { intros k Hk. unfold sw. destruct (Nat.eqb_spec k q); [lia |]. destruct (Nat.eqb_spec k r); [lia | reflexivity]. }
  assert (Sne : forall i k, (k < r)%nat -> i <> k -> sw q r i <> k).
  { intros i k Hk Hik. unfold sw. destruct (Nat.eqb_spec i q); [lia |]. destruct (Nat.eqb_spec i r); [lia | exact Hik]. }
  exists p. split.
  - split; [exact Hr |]. split; [exact Hc |]. split; [lia |]. split; [rewrite S1 by lia; exact Hqc |].
    split; [intros j Hj; rewrite S1 by lia; apply H4; lia |].
    split; [intros k Hk; apply H3; exact Hk |]. split; assumption.
  - split; [| split; [| split; [| split]]].
    + apply (equivG_trans N _ V); [exact He |]. apply (swap_equivG N V V1 q r); [lia | lia | exact HV1].
    + intros; reflexivity.
    + intros k Hk. destruct (H3 k Hk) as (A & B & C). split.
      * rewrite HV1 by lia. rewrite Slo by exact Hk. exact B.
      * intros i Hi Hik. rewrite HV1 by lia. apply C; [apply sw_lt; lia | apply Sne; assumption].
    + intros i j Hi Hj. rewrite HV1 by lia. apply H4; [apply Ssw; lia | exact Hj].
    + intros i Hi. lia.
Qed.

Lemma EL_fin : forall V0 V1 p c r V, PIV V1 p c r -> EL V0 V1 p c r N V -> INV V0 V (S c) (S r).
Proof.
  intros V0 V1 p c r V (Hr & Hc & Hrc & Ha & Hz & Hp & H5 & H6) (He & Hrow & H3 & H4 & Hcol).
  split; [exact He |]. split; [lia |].
  exists (fun k => if Nat.eqb k r then c else p k). split; [| split; [| split]].
  - intros k Hk. destruct (Nat.eqb_spec k r) as [-> | Hne].
    + split; [lia |]. split; [rewrite Hrow by lia; exact Ha |].
      intros i Hi Hir. apply Hcol; assumption.
    + assert (Hk' : (k < r)%nat) by lia. destruct (H3 k Hk') as [A B].
      split; [specialize (Hp k Hk'); lia | split; assumption].
  - intros i j Hi Hj. destruct (Nat.eq_dec j c) as [-> | Hne].
    + apply Hcol; lia.
    + apply H4; lia.
  - intros Hlt. destruct (H5 ltac:(lia)) as (f & Hf & Hfp). exists f. split; [lia |].
    intros k Hk. destruct (Nat.eqb_spec k r); [lia | apply Hfp; lia].
  - intros E k Hk. destruct (Nat.eqb_spec k r) as [-> | Hne]; [lia |]. apply H6; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the answer off the final table                              *)
(* ------------------------------------------------------------------ *)

Lemma fin_inconsistent : forall V0 V r i, INV V0 V N r -> (r <= i < N)%nat -> V i N <> 0%Z ->
  forall x, ~ sol N V0 x.
Proof.
  intros V0 V r i [He [_ (p & _ & H4 & _)]] Hi Hne x Hx. apply (equivG_sol _ _ _ He) in Hx.
  specialize (Hx i ltac:(lia)). unfold roweq, rowsum in Hx.
  rewrite sumR_zero in Hx; [| intros j Hj; rewrite H4 by lia; simpl; ring].
  apply Hne. apply eq_IZR. rewrite <- Hx. reflexivity.
Qed.

Fixpoint findk (p : nat -> nat) (j r : nat) : option nat :=
  match r with
  | O => None
  | S r' => if Nat.eqb (p r') j then Some r' else findk p j r'
  end.

Lemma findk_some : forall p j r k, findk p j r = Some k -> (k < r)%nat /\ p k = j.
Proof.
  intros p j r. induction r as [| r IH]; simpl; intros k H; [discriminate |].
  destruct (Nat.eqb_spec (p r) j) as [E | E].
  - injection H as <-. split; [lia | exact E].
  - destruct (IH k H). split; [lia | assumption].
Qed.

Lemma findk_none : forall p j r, findk p j r = None -> forall k, (k < r)%nat -> p k <> j.
Proof.
  intros p j r. induction r as [| r IH]; simpl; intros H k Hk; [lia |].
  destruct (Nat.eqb_spec (p r) j) as [E | E]; [discriminate |].
  destruct (Nat.eq_dec k r) as [-> | Hne]; [exact E | apply IH; [exact H | lia]].
Qed.

(* the solution with free column f set to t, the other free columns to 0 *)
Definition xsol (V : nat -> nat -> Z) (p : nat -> nat) (r f : nat) (t : R) (j : nat) : R :=
  match findk p j r with
  | Some k => (IZR (V k N) - IZR (V k f) * t) / IZR (V k (p k))
  | None => if Nat.eqb j f then t else 0
  end.

Lemma fin_multiple : forall V0 V r, INV V0 V N r -> (r < N)%nat ->
  (forall i, (r <= i < N)%nat -> V i N = 0%Z) ->
  exists x y : nat -> R, sol N V0 x /\ sol N V0 y /\ exists f, (f < N)%nat /\ x f <> y f.
Proof.
  intros V0 V r [He [Hrc (p & H3 & H4 & H5 & _)]] Hr Hcons.
  destruct (H5 Hr) as (f & Hf & Hfp).
  assert (Hinj : forall k k', (k < r)%nat -> (k' < r)%nat -> p k = p k' -> k = k').
  { intros k k' Hk Hk' E. destruct (Nat.eq_dec k k') as [| Hne]; [assumption | exfalso].
    destruct (H3 k Hk) as (_ & Nk & _). destruct (H3 k' Hk') as (_ & _ & Zk').
    apply Nk. rewrite E. apply Zk'; lia. }
  assert (Hs : forall t, sol N V (xsol V p r f t)).
  { intros t i Hi. unfold roweq, rowsum.
    destruct (Nat.lt_ge_cases i r) as [Hir | Hir].
    - destruct (H3 i Hir) as (Hpi & Ni & Zi).
      rewrite (sumR_ext _ (fun j => (if Nat.eqb j (p i) then IZR (V i N) - IZR (V i f) * t else 0)
                                 + (if Nat.eqb j f then IZR (V i f) * t else 0))).
      + rewrite sumR_plus, !sumR_delta by lia. ring.
      + intros j Hj. unfold xsol. destruct (findk p j r) as [k |] eqn:Ek.
        * destruct (findk_some p j r k Ek) as [Hk <-].
          assert (Hkf : p k <> f) by (apply Hfp; exact Hk).
          destruct (Nat.eqb_spec (p k) f) as [| _]; [contradiction |].
          destruct (Nat.eq_dec k i) as [-> | Hki].
          -- rewrite Nat.eqb_refl. field. apply not_0_IZR. exact Ni.
          -- destruct (Nat.eqb_spec (p k) (p i)) as [E | _].
             ++ apply Hinj in E; [lia | exact Hk | exact Hir].
             ++ destruct (H3 k Hk) as (_ & _ & Zk). rewrite (Zk i) by lia. simpl. ring.
        * pose proof (findk_none p j r Ek) as Hn.
          destruct (Nat.eqb_spec j (p i)) as [E | _]; [exfalso; apply (Hn i Hir); auto |].
          destruct (Nat.eqb_spec j f) as [-> | _]; ring.
    - rewrite sumR_zero; [rewrite Hcons by lia; reflexivity |].
      intros j Hj. rewrite H4 by lia. simpl. ring. }
  exists (xsol V p r f 0), (xsol V p r f 1). split; [apply (equivG_sol _ _ _ He), Hs |]. split; [apply (equivG_sol _ _ _ He), Hs |].
  exists f. split; [exact Hf |]. unfold xsol.
  destruct (findk p f r) as [k |] eqn:Ek.
  - destruct (findk_some p f r k Ek) as [Hk E]. exfalso. apply (Hfp k Hk E).
  - rewrite Nat.eqb_refl. lra.
Qed.

(* a kernel vector : free column f at 1, the other free columns at 0 *)
Definition xker (V : nat -> nat -> Z) (p : nat -> nat) (r f : nat) (j : nat) : R :=
  match findk p j r with
  | Some k => - IZR (V k f) / IZR (V k (p k))
  | None => if Nat.eqb j f then 1 else 0
  end.

Lemma fin_kernel : forall V0 V r, INV V0 V N r -> (r < N)%nat ->
  exists d : nat -> R, hsol N V0 d /\ exists f, (f < N)%nat /\ d f <> 0.
Proof.
  intros V0 V r [He [Hrc (p & H3 & H4 & H5 & _)]] Hr.
  destruct (H5 Hr) as (f & Hf & Hfp).
  assert (Hinj : forall k k', (k < r)%nat -> (k' < r)%nat -> p k = p k' -> k = k').
  { intros k k' Hk Hk' E. destruct (Nat.eq_dec k k') as [| Hne]; [assumption | exfalso].
    destruct (H3 k Hk) as (_ & Nk & _). destruct (H3 k' Hk') as (_ & _ & Zk').
    apply Nk. rewrite E. apply Zk'; lia. }
  exists (xker V p r f). split.
  - apply (equivG_hsol N _ _ He). intros i Hi. unfold rowsum.
    destruct (Nat.lt_ge_cases i r) as [Hir | Hir].
    + destruct (H3 i Hir) as (Hpi & Ni & Zi).
      rewrite (sumR_ext _ (fun j => (if Nat.eqb j (p i) then - IZR (V i f) else 0)
                                 + (if Nat.eqb j f then IZR (V i f) else 0))).
      * rewrite sumR_plus, !sumR_delta by lia. ring.
      * intros j Hj. unfold xker. destruct (findk p j r) as [k |] eqn:Ek.
        -- destruct (findk_some p j r k Ek) as [Hk <-].
           assert (Hkf : p k <> f) by (apply Hfp; exact Hk).
           destruct (Nat.eqb_spec (p k) f) as [| _]; [contradiction |].
           destruct (Nat.eq_dec k i) as [-> | Hki].
           ++ rewrite Nat.eqb_refl. field. apply not_0_IZR. exact Ni.
           ++ destruct (Nat.eqb_spec (p k) (p i)) as [E | _].
              ** apply Hinj in E; [lia | exact Hk | exact Hir].
              ** destruct (H3 k Hk) as (_ & _ & Zk). rewrite (Zk i) by lia. simpl. ring.
        -- pose proof (findk_none p j r Ek) as Hn.
           destruct (Nat.eqb_spec j (p i)) as [E | _]; [exfalso; apply (Hn i Hir); auto |].
           destruct (Nat.eqb_spec j f) as [-> | _]; ring.
    + rewrite sumR_zero; [reflexivity |].
      intros j Hj. rewrite H4 by lia. simpl. ring.
  - exists f. split; [exact Hf |]. unfold xker.
    destruct (findk p f r) as [k |] eqn:Ek.
    + destruct (findk_some p f r k Ek) as [Hk E]. exfalso. apply (Hfp k Hk E).
    + rewrite Nat.eqb_refl. lra.
Qed.

Lemma fin_unique : forall V0 V, INV V0 V N N ->
  (forall k, (k < N)%nat -> V k k <> 0%Z) /\
  sol N V0 (fun k => IZR (V k N) / IZR (V k k)) /\
  forall y, sol N V0 y -> forall k, (k < N)%nat -> y k = IZR (V k N) / IZR (V k k).
Proof.
  intros V0 V [He [_ (p & H3 & _ & _ & H6)]].
  assert (Hd : forall k, (k < N)%nat -> V k k <> 0%Z).
  { intros k Hk. destruct (H3 k Hk) as (_ & Nk & _). rewrite (H6 eq_refl k Hk) in Nk. exact Nk. }
  assert (Hz : forall k j, (k < N)%nat -> (j < N)%nat -> j <> k -> V k j = 0%Z).
  { intros k j Hk Hj Hjk. destruct (H3 j Hj) as (_ & _ & Zj). rewrite (H6 eq_refl j Hj) in Zj. apply Zj; auto. }
  assert (Hrow : forall y k, (k < N)%nat -> rowsum N V k y = IZR (V k k) * y k).
  { intros y k Hk. unfold rowsum.
    rewrite (sumR_ext _ (fun j => if Nat.eqb j k then IZR (V k k) * y k else 0)).
    - apply sumR_delta; exact Hk.
    - intros j Hj. destruct (Nat.eqb_spec j k) as [-> | Hne]; [reflexivity |].
      rewrite Hz by assumption. simpl. ring. }
  split; [exact Hd |]. split.
  - apply (equivG_sol _ _ _ He). intros k Hk. unfold roweq. rewrite Hrow by exact Hk. field. apply not_0_IZR, Hd, Hk.
  - intros y Hy k Hk. apply (equivG_sol _ _ _ He) in Hy. specialize (Hy k Hk). unfold roweq in Hy.
    rewrite Hrow in Hy by exact Hk. rewrite <- Hy. field. apply not_0_IZR, Hd, Hk.
Qed.

End Elim.

(* ------------------------------------------------------------------ *)
(* The table, machine side                                             *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.

Definition toN (x : int) : nat := Z.to_nat (to_Z x).

(* cell (i, j) of the table T of an n-equation system *)
Definition V (n : int) (T : array Z) (i j : nat) : Z :=
  T.[of_Z (Z.of_nat (i * S (toN n) + j))].

Ltac nlia := unfold toN in *; sia.

Ltac bdes := repeat match goal with
  | |- context [PeanoNat.Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b)
  | |- context [PeanoNat.Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b)
  end; simpl.

Lemma zget_set_same : forall (t : array Z) (i : int) (v : Z),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same Z t i v H). Qed.

Lemma zget_set_other : forall (t : array Z) (i j : int) (v : Z),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other Z t i j v H). Qed.

Lemma zlength_set : forall (t : array Z) (i : int) (v : Z),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set Z t i v). Qed.

Lemma fget_set_same : forall (t : array float) (i : int) (v : float),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same float t i v H). Qed.

Lemma fget_set_other : forall (t : array float) (i j : int) (v : float),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other float t i j v H). Qed.

Lemma flength_set : forall (t : array float) (i : int) (v : float),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set float t i v). Qed.

Lemma zlength_make : forall (k : int) (v : Z),
  PArray.length (PArray.make k v) = if k <=? max_length then k else max_length.
Proof. intros k v. exact (length_make Z k v). Qed.

Lemma flength_make : forall (k : int) (v : float),
  PArray.length (PArray.make k v) = if k <=? max_length then k else max_length.
Proof. intros k v. exact (length_make float k v). Qed.

Lemma toN_Z : forall x, Z.of_nat (toN x) = to_Z x.
Proof. intros x. unfold toN. pose proof (to_Z_bounded x). lia. Qed.

Lemma of_toN : forall x, of_Z (Z.of_nat (toN x)) = x.
Proof. intros x. rewrite toN_Z. apply of_to_Z. Qed.

Lemma toN_inj : forall x y, toN x = toN y -> x = y.
Proof. intros x y H. apply to_Z_inj. rewrite <- !toN_Z, H. reflexivity. Qed.

Lemma idx_inj : forall i j i' j' W : nat, (j < W)%nat -> (j' < W)%nat ->
  (i * W + j = i' * W + j')%nat -> i = i' /\ j = j'.
Proof.
  intros i j i' j' W Hj Hj' E.
  assert (i = i') by (destruct (Nat.lt_trichotomy i i') as [H | [H | H]]; [nia | exact H | nia]).
  subst. split; [reflexivity | lia].
Qed.

Section Table.
Variable n : int.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.

Definition LEN (T : array Z) : Prop := to_Z (PArray.length T) = (to_Z n * (to_Z n + 1))%Z.

Lemma w_spec : to_Z (n + 1) = (to_Z n + 1)%Z.
Proof. sia. Qed.

Lemma idx_eq : forall i j : int, (to_Z i <= to_Z n)%Z -> (to_Z j <= to_Z n)%Z ->
  i * (n + 1) + j = of_Z (Z.of_nat (toN i * S (toN n) + toN j)).
Proof.
  intros i j Hi Hj. apply to_Z_inj. rewrite of_Z_spec.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_succ, !toN_Z.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  assert (Hm : to_Z (i * (n + 1)) = (to_Z i * (to_Z n + 1))%Z).
  { rewrite Uint63.mul_spec, w_spec. apply Z.mod_small. change wB with 9223372036854775808%Z. nia. }
  rewrite Uint63.add_spec, Hm. rewrite (Z.mod_small (to_Z i * (to_Z n + 1) + to_Z j));
    [| change wB with 9223372036854775808%Z; nia].
  rewrite Z.mod_small; [ring | change wB with 9223372036854775808%Z; nia].
Qed.

Lemma get_V : forall T (i j : int), (to_Z i <= to_Z n)%Z -> (to_Z j <= to_Z n)%Z ->
  T.[i * (n + 1) + j] = V n T (toN i) (toN j).
Proof. intros T i j Hi Hj. unfold V. rewrite idx_eq by assumption. reflexivity. Qed.

Lemma toNn : (1 <= toN n <= 100)%nat.
Proof. nlia. Qed.

Lemma idx_small : forall i j, (i <= toN n)%nat -> (j <= toN n)%nat ->
  to_Z (of_Z (Z.of_nat (i * S (toN n) + j))) = Z.of_nat (i * S (toN n) + j).
Proof.
  intros i j Hi Hj. pose proof toNn as HnN. rewrite of_Z_spec. apply Z.mod_small.
  assert (i * S (toN n) + j <= 100 * 101 + 100)%nat by nia.
  change wB with 9223372036854775808%Z. lia.
Qed.

Lemma V_set : forall T (i0 j0 : int) v i j, LEN T -> (to_Z i0 < to_Z n)%Z -> (to_Z j0 <= to_Z n)%Z ->
  (i < toN n)%nat -> (j <= toN n)%nat ->
  V n (T.[i0 * (n + 1) + j0 <- v]) i j =
  if (Nat.eqb i (toN i0) && Nat.eqb j (toN j0))%bool then v else V n T i j.
Proof.
  intros T i0 j0 v i j HL Hi0 Hj0 Hi Hj. unfold V. rewrite idx_eq by lia.
  assert (Hi0' : (toN i0 < toN n)%nat) by nlia. assert (Hj0' : (toN j0 <= toN n)%nat) by nlia.
  pose proof toNn as HnN.
  destruct (Nat.eqb_spec i (toN i0)) as [-> | Hne1]; destruct (Nat.eqb_spec j (toN j0)) as [-> | Hne2]; simpl.
  - apply zget_set_same. rewrite Uint63.ltb_spec, idx_small, HL by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_succ, !toN_Z. nia.
  - apply zget_set_other. intros E. apply (f_equal to_Z) in E. rewrite !idx_small in E by lia.
    apply Nat2Z.inj in E. apply idx_inj in E; lia.
  - apply zget_set_other. intros E. apply (f_equal to_Z) in E. rewrite !idx_small in E by lia.
    apply Nat2Z.inj in E. apply idx_inj in E; lia.
  - apply zget_set_other. intros E. apply (f_equal to_Z) in E. rewrite !idx_small in E by lia.
    apply Nat2Z.inj in E. apply idx_inj in E; lia.
Qed.

Lemma LEN_set : forall T k v, LEN T -> LEN (T.[k <- v]).
Proof. intros T k v H. unfold LEN. rewrite zlength_set. exact H. Qed.

Lemma toN_succ : forall j hi : int, (to_Z j < to_Z hi)%Z -> toN (j + 1) = S (toN j).
Proof. intros j hi H. pose proof (to_Z_bounded hi). nlia. Qed.

Lemma upd_row_spec : forall T i r a b, LEN T -> (to_Z i < to_Z n)%Z -> (to_Z r < to_Z n)%Z -> i <> r ->
  LEN (upd_row T (n + 1) i r a b) /\
  forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
    V n (upd_row T (n + 1) i r a b) k j =
    if Nat.eqb k (toN i) then (a * V n T k j - b * V n T (toN r) j)%Z else V n T k j.
Proof.
  intros T i r a b HL Hi Hr Hir. unfold upd_row.
  assert (Hir' : toN r <> toN i) by (intros E; apply Hir, toN_inj; auto).
  pose proof toNn as HnN.
  match goal with |- context [loop ?hi ?c ?f ?lo ?s] =>
    assert (H : LEN (loop hi c f lo s) /\ forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
      V n (loop hi c f lo s) k j = if (Nat.eqb k (toN i) && Nat.ltb j (toN hi))%bool
                   then (a * V n T k j - b * V n T (toN r) j)%Z else V n T k j) end.
  { apply (for_inv (fun jj T' => LEN T' /\
      forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
        V n T' k j = if (Nat.eqb k (toN i) && Nat.ltb j (toN jj))%bool
                     then (a * V n T k j - b * V n T (toN r) j)%Z else V n T k j)).
    - nlia.
    - split; [exact HL |]. intros k j Hk Hj. change (toN 0) with 0%nat. bdes; try lia; reflexivity.
    - intros jj T' Hjj [HL' HV]. split; [apply LEN_set, HL' |].
      intros k j Hk Hj. rewrite V_set by (auto; nlia).
      rewrite (get_V T' i jj), (get_V T' r jj) by nlia.
      rewrite (HV (toN i) (toN jj)), (HV (toN r) (toN jj)) by nlia.
      rewrite (HV k j) by assumption. rewrite (toN_succ jj (n + 1)) by lia.
      bdes; subst; try lia; reflexivity. }
  destruct H as [HL' HV]. split; [exact HL' |]. intros k j Hk Hj. rewrite HV by assumption.
  assert (Hw : (j < toN (n + 1))%nat) by nlia. bdes; try lia; reflexivity.
Qed.

Lemma div_row_spec : forall T i g, LEN T -> (to_Z i < to_Z n)%Z ->
  LEN (div_row T (n + 1) i g) /\
  forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
    V n (div_row T (n + 1) i g) k j = if Nat.eqb k (toN i) then (V n T k j / g)%Z else V n T k j.
Proof.
  intros T i g HL Hi. unfold div_row. pose proof toNn as HnN.
  match goal with |- context [loop ?hi ?c ?f ?lo ?s] =>
    assert (H : LEN (loop hi c f lo s) /\ forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
      V n (loop hi c f lo s) k j = if (Nat.eqb k (toN i) && Nat.ltb j (toN hi))%bool
                   then (V n T k j / g)%Z else V n T k j) end.
  { apply (for_inv (fun jj T' => LEN T' /\
      forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
        V n T' k j = if (Nat.eqb k (toN i) && Nat.ltb j (toN jj))%bool
                     then (V n T k j / g)%Z else V n T k j)).
    - nlia.
    - split; [exact HL |]. intros k j Hk Hj. change (toN 0) with 0%nat. bdes; try lia; reflexivity.
    - intros jj T' Hjj [HL' HV]. split; [apply LEN_set, HL' |].
      intros k j Hk Hj. rewrite V_set by (auto; nlia).
      rewrite (get_V T' i jj) by nlia. rewrite (HV (toN i) (toN jj)) by nlia.
      rewrite (HV k j) by assumption. rewrite (toN_succ jj (n + 1)) by lia.
      bdes; subst; try lia; reflexivity. }
  destruct H as [HL' HV]. split; [exact HL' |]. intros k j Hk Hj. rewrite HV by assumption.
  assert (Hw : (j < toN (n + 1))%nat) by nlia. bdes; try lia; reflexivity.
Qed.

Lemma row_gcd_spec : forall T i, (to_Z i < to_Z n)%Z ->
  forall j, (j <= toN n)%nat -> Z.divide (row_gcd T (n + 1) i) (V n T (toN i) j).
Proof.
  intros T i Hi. unfold row_gcd. pose proof toNn as HnN.
  match goal with |- context [loop ?hi ?c ?f ?lo ?s] =>
    assert (H : forall j, (j < toN hi)%nat -> Z.divide (loop hi c f lo s) (V n T (toN i) j)) end.
  { apply (for_inv (fun jj g => forall j, (j < toN jj)%nat -> Z.divide g (V n T (toN i) j))).
    - nlia.
    - intros j Hj. change (toN 0) with 0%nat in Hj. lia.
    - intros jj g Hjj HV j Hj. rewrite (toN_succ jj (n + 1)) in Hj by lia.
      rewrite zgcd_spec, (get_V T i jj) by nlia.
      destruct (Nat.eq_dec j (toN jj)) as [-> | Hne].
      + apply Z.gcd_divide_r.
      + eapply Z.divide_trans; [apply Z.gcd_divide_l | apply HV; lia]. }
  intros j Hj. apply H. nlia.
Qed.

Lemma swap_rows_spec : forall T q r, LEN T -> (to_Z q < to_Z n)%Z -> (to_Z r < to_Z n)%Z ->
  LEN (swap_rows T (n + 1) q r) /\
  forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
    V n (swap_rows T (n + 1) q r) k j = V n T (sw (toN q) (toN r) k) j.
Proof.
  intros T q r HL Hq Hr. unfold swap_rows. pose proof toNn as HnN.
  match goal with |- context [loop ?hi ?c ?f ?lo ?s] =>
    assert (H : LEN (loop hi c f lo s) /\ forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
      V n (loop hi c f lo s) k j = if Nat.ltb j (toN hi)
                   then V n T (sw (toN q) (toN r) k) j else V n T k j) end.
  { apply (for_inv (fun jj T' => LEN T' /\
      forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
        V n T' k j = if Nat.ltb j (toN jj) then V n T (sw (toN q) (toN r) k) j else V n T k j)).
    - nlia.
    - split; [exact HL |]. intros k j Hk Hj. change (toN 0) with 0%nat. bdes; try lia; reflexivity.
    - intros jj T' Hjj [HL' HV]. cbv beta zeta. split; [apply LEN_set, LEN_set, HL' |].
      intros k j Hk Hj. rewrite V_set by (auto using LEN_set; nlia).
      rewrite V_set by (auto; nlia).
      rewrite (get_V T' r jj), (get_V T' q jj) by nlia.
      rewrite (HV (toN r) (toN jj)), (HV (toN q) (toN jj)) by nlia.
      rewrite (HV k j) by assumption. rewrite (toN_succ jj (n + 1)) by lia.
      rewrite Nat.ltb_irrefl.
      destruct (Nat.eqb_spec j (toN jj)) as [-> | Hne].
      + rewrite !Bool.andb_true_r, ?Nat.ltb_irrefl.
        replace (Nat.ltb (toN jj) (S (toN jj))) with true by (symmetry; apply Nat.ltb_lt; lia).
        unfold sw. destruct (Nat.eqb_spec k (toN q)) as [-> | Hkq]; [reflexivity |].
        destruct (Nat.eqb_spec k (toN r)) as [-> | Hkr]; reflexivity.
      + rewrite !Bool.andb_false_r.
        destruct (Nat.ltb_spec j (toN jj)), (Nat.ltb_spec j (S (toN jj))); try lia; reflexivity. }
  destruct H as [HL' HV]. split; [exact HL' |]. intros k j Hk Hj. rewrite HV by assumption.
  assert (Hw : (j < toN (n + 1))%nat) by nlia. bdes; try lia; reflexivity.
Qed.

Lemma find_piv_spec : forall T c r, (to_Z c < to_Z n)%Z -> (to_Z r <= to_Z n)%Z ->
  (find_piv T n (n + 1) c r = n /\ forall k, (toN r <= k < toN n)%nat -> V n T k (toN c) = 0%Z) \/
  ((to_Z r <= to_Z (find_piv T n (n + 1) c r) < to_Z n)%Z /\
   V n T (toN (find_piv T n (n + 1) c r)) (toN c) <> 0%Z).
Proof.
  intros T c r Hc Hr. unfold find_piv. pose proof toNn as HnN.
  apply (for_inv (fun i s => (s = n /\ forall k, (toN r <= k < toN i)%nat -> V n T k (toN c) = 0%Z) \/
    ((to_Z r <= to_Z s < to_Z i)%Z /\ V n T (toN s) (toN c) <> 0%Z))).
  - exact Hr.
  - left. split; [reflexivity | intros; lia].
  - intros i s Hi [[-> Hz] | [Hs Hnz]].
    + rewrite eqb_refl. rewrite (get_V T i c) by nlia.
      destruct (Z.eqb_spec (V n T (toN i) (toN c)) 0) as [E | E].
      * left. split; [reflexivity |]. intros k Hk. rewrite (toN_succ i n) in Hk by lia.
        destruct (Nat.eq_dec k (toN i)) as [-> | Hne]; [exact E | apply Hz; lia].
      * right. split; [sia | exact E].
    + assert (Hsn : (s =? n) = false) by (rewrite eqb_false_spec; intros ->; lia).
      rewrite Hsn. right. split; [sia | exact Hnz].
Qed.

Lemma elim_row_spec : forall c r a i T, LEN T -> (to_Z c < to_Z n)%Z -> (to_Z r < to_Z n)%Z ->
  (to_Z i < to_Z n)%Z -> a <> 0%Z ->
  LEN (elim_row (n + 1) c r a i T) /\
  ((toN i = toN r /\ V n (elim_row (n + 1) c r a i T) = V n T) \/
   (toN i <> toN r /\ rowop (toN n) (V n T) (V n (elim_row (n + 1) c r a i T)) (toN i) (toN r) a
                                (V n T (toN i) (toN c)))).
Proof.
  intros c r a i T HL Hc Hr Hi Ha. pose proof toNn as HnN. unfold elim_row.
  destruct (i =? r) eqn:E.
  - apply eqb_correct in E. subst. split; [exact HL | left; auto].
  - rewrite eqb_false_spec in E. assert (Hne : toN i <> toN r) by (intro; apply E, toN_inj; auto).
    rewrite (get_V T i c) by lia.
    destruct (Z.eqb_spec (V n T (toN i) (toN c)) 0) as [Eb | Eb].
    + split; [exact HL |]. right. split; [assumption |]. split; [intros; reflexivity |].
      exists a. split; [exact Ha |]. intros j Hj. rewrite Eb. ring.
    + destruct (upd_row_spec T i r a (V n T (toN i) (toN c)) HL Hi Hr E) as [HL1 HV1].
      pose proof (row_gcd_spec (upd_row T (n + 1) i r a (V n T (toN i) (toN c))) i Hi) as Hg.
      destruct (Z.ltb_spec 1 (row_gcd (upd_row T (n + 1) i r a (V n T (toN i) (toN c))) (n + 1) i))
        as [Hg1 | Hg1].
      * destruct (div_row_spec (upd_row T (n + 1) i r a (V n T (toN i) (toN c))) i
                   (row_gcd (upd_row T (n + 1) i r a (V n T (toN i) (toN c))) (n + 1) i) HL1 Hi)
          as [HL2 HV2].
        split; [exact HL2 |]. right. split; [assumption |]. split.
        -- intros k j Hk HkN Hj. rewrite HV2, HV1 by assumption.
           destruct (Nat.eqb_spec k (toN i)); [contradiction | reflexivity].
        -- exists (row_gcd (upd_row T (n + 1) i r a (V n T (toN i) (toN c))) (n + 1) i).
           split; [lia |]. intros j Hj. rewrite HV2 by nlia. rewrite Nat.eqb_refl.
           destruct (Hg j Hj) as [m Hm]. rewrite Hm. rewrite Z.div_mul by lia.
           rewrite HV1 in Hm by nlia. rewrite Nat.eqb_refl in Hm. rewrite Z.mul_comm. exact (eq_sym Hm).
      * split; [exact HL1 |]. right. split; [assumption |]. split.
        -- intros k j Hk HkN Hj. rewrite HV1 by assumption.
           destruct (Nat.eqb_spec k (toN i)); [contradiction | reflexivity].
        -- exists 1%Z. split; [lia |]. intros j Hj. rewrite HV1 by nlia. rewrite Nat.eqb_refl. ring.
Qed.

Lemma eliminate_spec : forall T, LEN T ->
  LEN (fst (eliminate n (n + 1) T)) /\ (to_Z (snd (eliminate n (n + 1) T)) <= to_Z n)%Z /\
  INV (toN n) (V n T) (V n (fst (eliminate n (n + 1) T))) (toN n) (toN (snd (eliminate n (n + 1) T))).
Proof.
  intros T HL. pose proof toNn as HnN. unfold eliminate.
  apply (for_inv (fun c st => LEN (fst st) /\ (to_Z (snd st) <= to_Z c)%Z /\
           INV (toN n) (V n T) (V n (fst st)) (toN c) (toN (snd st)))).
  - nlia.
  - split; [exact HL |]. split; [simpl; lia |]. change (toN 0) with 0%nat. apply INV_init.
  - intros c [T' r] Hc (HL' & Hrc & HI). simpl in HL', Hrc, HI. unfold col_step.
    assert (Hc' : (to_Z c < to_Z n)%Z) by lia.
    destruct (find_piv_spec T' c r Hc' ltac:(lia)) as [[Eq Hz] | [Hq Hnz]].
    + rewrite Eq, eqb_refl. simpl. split; [exact HL' |]. split; [sia |].
      rewrite (toN_succ c n) by lia. apply INV_nopiv; [exact HI | nlia | exact Hz].
    + assert (En : (find_piv T' n (n + 1) c r =? n) = false) by (rewrite eqb_false_spec; intros E; lia).
      rewrite En. cbv zeta.
      assert (Hq' : (to_Z (find_piv T' n (n + 1) c r) < to_Z n)%Z) by lia.
      assert (Hr' : (to_Z r < to_Z n)%Z) by lia.
      destruct (swap_rows_spec T' (find_piv T' n (n + 1) c r) r HL' Hq' Hr') as [HL1 HV1].
      destruct (EL_init (toN n) (V n T) (V n T') (V n (swap_rows T' (n + 1) (find_piv T' n (n + 1) c r) r))
                  (toN c) (toN r) (toN (find_piv T' n (n + 1) c r)) HI ltac:(nlia) ltac:(nlia) Hnz HV1)
        as (p & HP & HE0).
      rewrite (get_V _ r c) by lia.
      assert (Ha : V n (swap_rows T' (n + 1) (find_piv T' n (n + 1) c r) r) (toN r) (toN c) <> 0%Z)
        by (destruct HP as (_ & _ & _ & Ha & _); exact Ha).
      match goal with |- context [loop n ?cc ?ff 0 ?ss] =>
        assert (HL2 : LEN (loop n cc ff 0 ss) /\
                EL (toN n) (V n T) (V n ss) p (toN c) (toN r) (toN n) (V n (loop n cc ff 0 ss))) end.
      { apply (for_inv (fun i T'' => LEN T'' /\
                EL (toN n) (V n T) (V n (swap_rows T' (n + 1) (find_piv T' n (n + 1) c r) r))
                   p (toN c) (toN r) (toN i) (V n T''))).
        - lia.
        - split; [exact HL1 |]. change (toN 0) with 0%nat. exact HE0.
        - intros i T'' Hi [HL3 HE3].
          destruct (elim_row_spec c r _ i T'' HL3 Hc' Hr' ltac:(lia) Ha) as [HL4 Hop].
          split; [exact HL4 |]. rewrite (toN_succ i n) by lia.
          apply (EL_step (toN n) _ _ p (toN c) (toN r) (toN i) (V n T'')); [exact HP | exact HE3 | nlia |].
          destruct Hop as [[E1 E2] | [E1 E2]]; [left; auto | right; split; [exact E1 |]].
          exact E2. }
      destruct HL2 as [HL2 HE2]. simpl. split; [exact HL2 |]. split; [sia |].
      rewrite (toN_succ c n), (toN_succ r n) by lia.
      eapply EL_fin; [exact HP | exact HE2].
Qed.

Lemma inconsistent_spec : forall T r, (to_Z r <= to_Z n)%Z ->
  (inconsistent T n (n + 1) r = true <->
   exists i, (toN r <= i < toN n)%nat /\ V n T i (toN n) <> 0%Z).
Proof.
  intros T r Hr. unfold inconsistent.
  apply (for_inv (fun i fl => (fl = true <-> exists k, (toN r <= k < toN i)%nat /\ V n T k (toN n) <> 0%Z))).
  - exact Hr.
  - split; [discriminate | intros (k & Hk & _); lia].
  - intros i fl Hi IH. rewrite (get_V T i n) by nlia. rewrite (toN_succ i n) by lia. split.
    + intros H. apply Bool.orb_true_iff in H. destruct H as [H | H].
      * apply IH in H. destruct H as (k & Hk & Hv). exists k. split; [lia | exact Hv].
      * exists (toN i). split; [nlia |]. intros E. rewrite E in H. discriminate.
    + intros (k & Hk & Hv). apply Bool.orb_true_iff. destruct (Nat.eq_dec k (toN i)) as [-> | Hne].
      * right. rewrite (proj2 (Z.eqb_neq _ _) Hv). reflexivity.
      * left. apply IH. exists k. split; [lia | exact Hv].
Qed.

Lemma output_spec : forall T,
  PArray.length (output T n (n + 1)) = n /\
  forall k, (k < toN n)%nat -> (output T n (n + 1)).[of_Z (Z.of_nat k)] = qround (V n T k (toN n)) (V n T k k).
Proof.
  intros T. unfold output. pose proof toNn as HnN.
  match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
    assert (H : PArray.length (loop hi cc ff lo ss) = n /\
      forall k, (k < toN hi)%nat -> (loop hi cc ff lo ss).[of_Z (Z.of_nat k)] = qround (V n T k (toN n)) (V n T k k)) end.
  { apply (for_inv (fun i out => PArray.length out = n /\
      forall k, (k < toN i)%nat -> out.[of_Z (Z.of_nat k)] = qround (V n T k (toN n)) (V n T k k))).
    - nlia.
    - split.
      + rewrite flength_make. replace (n <=? max_length) with true; [reflexivity |].
        symmetry. rewrite Uint63.leb_spec. change (to_Z max_length) with 4194303%Z. lia.
      + intros k Hk. change (toN 0) with 0%nat in Hk. lia.
    - intros i out Hi [HLo Ho]. split; [rewrite flength_set; exact HLo |].
      intros k Hk. rewrite (toN_succ i n) in Hk by lia.
      rewrite (get_V T i n), (get_V T i i) by nlia.
      destruct (Nat.eq_dec k (toN i)) as [-> | Hne].
      + rewrite of_toN. apply fget_set_same. rewrite HLo. apply Uint63.ltb_spec. lia.
      + rewrite fget_set_other; [apply Ho; lia |]. intros E. apply Hne.
        apply (f_equal to_Z) in E. rewrite of_Z_spec, Z.mod_small in E; [| change wB with 9223372036854775808%Z; nlia].
        nlia. }
  exact H.
Qed.

Lemma row_exp_spec : forall row bi, (row_exp n row bi <= snd (dec bi))%Z /\
  forall j, (to_Z j < to_Z n)%Z -> (row_exp n row bi <= snd (dec row.[j]))%Z.
Proof.
  intros row bi. unfold row_exp.
  apply (for_inv (fun jj E => (E <= snd (dec bi))%Z /\
    forall j, (to_Z j < to_Z jj)%Z -> (E <= snd (dec row.[j]))%Z)).
  - change (to_Z 0) with 0%Z. lia.
  - split; [lia | intros j Hj; pose proof (to_Z_bounded j); change (to_Z 0) with 0%Z in Hj; lia].
  - intros jj E Hjj [H1 H2]. split; [lia |]. intros j Hj.
    destruct (Z.eq_dec (to_Z j) (to_Z jj)) as [Ej | Ej].
    + apply to_Z_inj in Ej. subst. lia.
    + assert (to_Z j < to_Z jj)%Z by sia. specialize (H2 j ltac:(assumption)). lia.
Qed.

Lemma fill_row_spec : forall i row E T, LEN T -> (to_Z i < to_Z n)%Z ->
  LEN (fill_row n (n + 1) i row E T) /\
  forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
    V n (fill_row n (n + 1) i row E T) k j =
    if (Nat.eqb k (toN i) && Nat.ltb j (toN n))%bool then scale row.[of_Z (Z.of_nat j)] E else V n T k j.
Proof.
  intros i row E T HL Hi. unfold fill_row. pose proof toNn as HnN.
  apply (for_inv (fun jj T' => LEN T' /\
      forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
        V n T' k j = if (Nat.eqb k (toN i) && Nat.ltb j (toN jj))%bool
                     then scale row.[of_Z (Z.of_nat j)] E else V n T k j)).
  - nlia.
  - split; [exact HL |]. intros k j Hk Hj. change (toN 0) with 0%nat. bdes; try lia; reflexivity.
  - intros jj T' Hjj [HL' HV]. split; [apply LEN_set, HL' |].
    intros k j Hk Hj. rewrite V_set by (auto; nlia).
    rewrite (HV k j) by assumption. rewrite (toN_succ jj n) by lia.
    destruct (Nat.eqb_spec k (toN i)) as [-> | Hki]; simpl; [| reflexivity].
    destruct (Nat.eqb_spec j (toN jj)) as [-> | Hjj']; simpl.
    + rewrite of_toN. replace (Nat.ltb (toN jj) (S (toN jj))) with true by (symmetry; apply Nat.ltb_lt; lia).
      reflexivity.
    + destruct (Nat.ltb_spec j (toN jj)), (Nat.ltb_spec j (S (toN jj))); try lia; reflexivity.
Qed.

Lemma build_spec : forall a b, LEN (build a b n (n + 1)) /\
  forall k j, (k < toN n)%nat -> (j <= toN n)%nat ->
    V n (build a b n (n + 1)) k j =
      (if Nat.ltb j (toN n)
       then scale a.[of_Z (Z.of_nat k)].[of_Z (Z.of_nat j)] (row_exp n a.[of_Z (Z.of_nat k)] b.[of_Z (Z.of_nat k)])
       else scale b.[of_Z (Z.of_nat k)] (row_exp n a.[of_Z (Z.of_nat k)] b.[of_Z (Z.of_nat k)])).
Proof.
  intros a b. unfold build. pose proof toNn as HnN.
  match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
    assert (H : LEN (loop hi cc ff lo ss) /\ forall k j, (k < toN hi)%nat -> (j <= toN n)%nat ->
      V n (loop hi cc ff lo ss) k j =
      (if Nat.ltb j (toN n)
       then scale a.[of_Z (Z.of_nat k)].[of_Z (Z.of_nat j)] (row_exp n a.[of_Z (Z.of_nat k)] b.[of_Z (Z.of_nat k)])
       else scale b.[of_Z (Z.of_nat k)] (row_exp n a.[of_Z (Z.of_nat k)] b.[of_Z (Z.of_nat k)]))) end.
  { apply (for_inv (fun i T => LEN T /\ forall k j, (k < toN i)%nat -> (j <= toN n)%nat ->
      V n T k j =
      (if Nat.ltb j (toN n)
       then scale a.[of_Z (Z.of_nat k)].[of_Z (Z.of_nat j)] (row_exp n a.[of_Z (Z.of_nat k)] b.[of_Z (Z.of_nat k)])
       else scale b.[of_Z (Z.of_nat k)] (row_exp n a.[of_Z (Z.of_nat k)] b.[of_Z (Z.of_nat k)])))).
    - nlia.
    - split.
      + unfold LEN. rewrite zlength_make.
        assert (Hm : to_Z (n * (n + 1)) = (to_Z n * (to_Z n + 1))%Z).
        { assert (Hb : (to_Z n * (to_Z n + 1) <= 100 * 101)%Z) by (apply Z.mul_le_mono_nonneg; lia).
          rewrite Uint63.mul_spec, w_spec. apply Z.mod_small. change wB with 9223372036854775808%Z. lia. }
        assert (Hb : (to_Z n * (to_Z n + 1) <= 100 * 101)%Z) by (apply Z.mul_le_mono_nonneg; lia).
        replace (n * (n + 1) <=? max_length) with true; [exact Hm |].
        symmetry. rewrite Uint63.leb_spec, Hm. change (to_Z max_length) with 4194303%Z. lia.
      + intros k j Hk. change (toN 0) with 0%nat in Hk. lia.
    - intros i T Hi [HL HV]. unfold build_step. cbv zeta.
      destruct (fill_row_spec i a.[i] (row_exp n a.[i] b.[i]) T HL ltac:(lia)) as [HL1 HV1].
      split; [apply LEN_set, HL1 |].
      intros k j Hk Hj. rewrite (toN_succ i n) in Hk by lia.
      rewrite V_set by (auto; nlia). rewrite HV1 by nlia.
      destruct (Nat.eq_dec k (toN i)) as [-> | Hne].
      + rewrite Nat.eqb_refl. simpl. rewrite of_toN.
        destruct (Nat.eqb_spec j (toN n)) as [-> | Hjn].
        * rewrite Nat.ltb_irrefl. reflexivity.
        * replace (Nat.ltb j (toN n)) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
      + destruct (Nat.eqb_spec k (toN i)); [contradiction |]. simpl. apply HV; lia. }
  destruct H as [HL HV]. split; [exact HL |]. intros k j Hk Hj. apply HV; assumption.
Qed.

End Table.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma dot_sumR : forall row xs, List.length row = List.length xs ->
  dot row xs = sumR (fun j => (nth j row 0 * nth j xs 0)%R) (List.length row).
Proof.
  induction row as [| r row IH]; intros xs Hl; [reflexivity |].
  destruct xs as [| v xs]; [discriminate |]. simpl in Hl. injection Hl as Hl.
  change (List.length (r :: row)) with (S (List.length row)). rewrite sumR_shift. simpl.
  rewrite IH by exact Hl. reflexivity.
Qed.

Lemma Forall2_iff : forall {A B} (P : A -> B -> Prop) l1 l2 d1 d2, List.length l1 = List.length l2 ->
  (Forall2 P l1 l2 <-> forall i, (i < List.length l1)%nat -> P (nth i l1 d1) (nth i l2 d2)).
Proof.
  intros A B P l1. induction l1 as [| x l1 IH]; intros l2 d1 d2 Hl.
  - destruct l2; [| discriminate]. split; [intros _ i Hi; simpl in Hi; lia | intros _; constructor].
  - destruct l2 as [| y l2]; [discriminate |]. simpl in Hl. injection Hl as Hl. split.
    + intros H i Hi. inversion H as [| ? ? ? ? Hxy Hrest]; subst.
      destruct i as [| i]; [exact Hxy |]. simpl. apply (IH l2 d1 d2 Hl); [exact Hrest | simpl in Hi; lia].
    + intros H. constructor; [apply (H 0%nat); simpl; lia |].
      apply (IH l2 d1 d2 Hl). intros i Hi. apply (H (S i)). simpl. lia.
Qed.

Lemma repr_nth_float : forall (x : array float) (l : list R) k, repr x l -> (k < List.length l)%nat ->
  repr x.[of_Z (Z.of_nat k)] (nth k l 0%R).
Proof.
  intros x l k [_ H] Hk. destruct (H k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth l k 0%R Hm). exact Hr.
Qed.

Lemma repr_nth_row : forall (x : array (array float)) (l : list (list R)) k, repr x l -> (k < List.length l)%nat ->
  repr x.[of_Z (Z.of_nat k)] (nth k l []).
Proof.
  intros x l k [_ H] Hk. destruct (H k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth l k [] Hm). exact Hr.
Qed.

Lemma sol_ext : forall N V x y, (forall j, (j < N)%nat -> x j = y j) -> sol N V x -> sol N V y.
Proof.
  intros N V0 x y Hxy H i Hi. unfold roweq, rowsum in *. rewrite <- (H i Hi).
  apply sumR_ext. intros j Hj. rewrite Hxy by exact Hj. reflexivity.
Qed.

Lemma nth_map_seq : forall (f : nat -> R) N j, (j < N)%nat -> nth j (map f (seq 0 N)) 0%R = f j.
Proof.
  intros f N j Hj. rewrite (nth_indep _ _ (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Theorem solve_exact_correct :
  forall (n : N) (a : list (list R)) (b : list R)
         (xn : uint) (xa : array (array float)) (xb : array float),
  valid_input n a b -> repr xn n -> repr xa a -> repr xb b ->
  exists o : outcome (list R), repr (solve_exact xn xa xb) o /\ solve_spec n a b o.
Proof.
  intros n a b xn xa xb [Hvn Hrows Hrow Hvb] Hxn Ha Hb.
  unfold repr, repr_uint in Hxn.
  assert (Hn : (1 <= to_Z xn <= 100)%Z) by lia.
  pose proof (toNn xn Hn) as HnN.
  assert (Hlen : forall {X} (l : list X), len l = n -> List.length l = toN xn).
  { intros X l Hl. unfold len in Hl. unfold toN. lia. }
  assert (La : List.length a = toN xn) by (apply Hlen; exact Hrows).
  assert (Lb : List.length b = toN xn) by (apply Hlen; exact Hvb).
  assert (Lrow : forall i, (i < toN xn)%nat -> List.length (nth i a []) = toN xn).
  { intros i Hi. apply Hlen. rewrite Forall_nth in Hrow. apply Hrow. lia. }
  (* the integer table of the system *)
  destruct (build_spec xn Hn xa xb) as [HL0 HV0].
  set (T0 := build xa xb xn (xn + 1)) in *.
  set (E := fun i : nat => row_exp xn xa.[of_Z (Z.of_nat i)] xb.[of_Z (Z.of_nat i)]).
  assert (HA : forall i j, (i < toN xn)%nat -> (j < toN xn)%nat ->
    nth j (nth i a []) 0%R = (IZR (V xn T0 i j) * powerRZ 2 (E i))%R).
  { intros i j Hi Hj. rewrite HV0 by lia.
    replace (Nat.ltb j (toN xn)) with true by (symmetry; apply Nat.ltb_lt; exact Hj).
    assert (Hr : repr (xa.[of_Z (Z.of_nat i)]).[of_Z (Z.of_nat j)] (nth j (nth i a []) 0%R)).
    { apply repr_nth_float; [apply repr_nth_row; [exact Ha | lia] | rewrite Lrow; assumption]. }
    unfold E. rewrite scale_spec; [apply fval_dec; exact Hr |].
    apply (row_exp_spec xn Hn). rewrite of_Z_spec, Z.mod_small; [nlia | change wB with 9223372036854775808%Z; lia]. }
  assert (HB : forall i, (i < toN xn)%nat -> nth i b 0%R = (IZR (V xn T0 i (toN xn)) * powerRZ 2 (E i))%R).
  { intros i Hi. rewrite HV0 by lia. rewrite Nat.ltb_irrefl.
    assert (Hr : repr xb.[of_Z (Z.of_nat i)] (nth i b 0%R)) by (apply repr_nth_float; [exact Hb | lia]).
    unfold E. rewrite scale_spec; [apply fval_dec; exact Hr |]. apply (row_exp_spec xn Hn). }
  assert (Key : forall xs, solves n a b xs <-> List.length xs = toN xn /\ sol (toN xn) (V xn T0) (fun j => nth j xs 0%R)).
  { intros xs. unfold solves. split.
    - intros [Hl HF]. assert (Hl' : List.length xs = toN xn) by (apply Hlen; exact Hl). split; [exact Hl' |].
      rewrite (Forall2_iff _ a b [] 0%R) in HF by lia.
      intros i Hi. unfold roweq, rowsum. specialize (HF i ltac:(lia)).
      rewrite dot_sumR in HF by (rewrite Lrow, Hl'; lia). rewrite Lrow in HF by exact Hi.
      rewrite HB in HF by exact Hi.
      apply (Rmult_eq_reg_r (powerRZ 2 (E i))); [| apply powerRZ_NOR; lra].
      rewrite <- HF, <- sumR_scal_r. apply sumR_ext. intros j Hj. rewrite HA by assumption. ring.
    - intros [Hl Hs]. split; [unfold len; rewrite Hl; unfold toN; lia |].
      rewrite (Forall2_iff _ a b [] 0%R) by lia. intros i Hi. rewrite La in Hi.
      rewrite dot_sumR by (rewrite Lrow, Hl; lia). rewrite Lrow by exact Hi. rewrite HB by exact Hi.
      specialize (Hs i Hi). unfold roweq, rowsum in Hs. rewrite <- Hs, <- sumR_scal_r.
      apply sumR_ext. intros j Hj. rewrite HA by assumption. ring. }
  destruct (eliminate_spec xn Hn T0 HL0) as (HL & Hr & HI).
  unfold solve_exact. cbv zeta. change (build xa xb xn (xn + 1)) with T0.
  destruct (eliminate xn (xn + 1) T0) as [T r] eqn:Ee. simpl in HL, Hr, HI.
  destruct (inconsistent T xn (xn + 1) r) eqn:Ei.
  - exists Inconsistent. split; [exact I |].
    intros xs Hs. apply Key in Hs. destruct Hs as [_ Hs].
    apply (inconsistent_spec xn Hn T r Hr) in Ei. destruct Ei as (i & Hi & Hv).
    exact (fin_inconsistent (toN xn) (V xn T0) (V xn T) (toN r) i HI Hi Hv _ Hs).
  - assert (Hcons : forall i, (toN r <= i < toN xn)%nat -> V xn T i (toN xn) = 0%Z).
    { intros i Hi. destruct (Z.eq_dec (V xn T i (toN xn)) 0) as [| Hne]; [assumption | exfalso].
      assert (inconsistent T xn (xn + 1) r = true)
        by (apply (inconsistent_spec xn Hn T r Hr); exists i; auto).
      congruence. }
    destruct (r <? xn) eqn:Er.
    + exists Multiple. split; [exact I |].
      rewrite Uint63.ltb_spec in Er.
      destruct (fin_multiple (toN xn) (V xn T0) (V xn T) (toN r) HI ltac:(nlia) Hcons)
        as (x & y & Hx & Hy & f & Hf & Hxy).
      exists (map x (seq 0 (toN xn))), (map y (seq 0 (toN xn))).
      split; [| split].
      * apply Key. split; [rewrite length_map, length_seq; reflexivity |].
        apply (sol_ext _ _ x); [intros j Hj; symmetry; apply nth_map_seq; exact Hj | exact Hx].
      * apply Key. split; [rewrite length_map, length_seq; reflexivity |].
        apply (sol_ext _ _ y); [intros j Hj; symmetry; apply nth_map_seq; exact Hj | exact Hy].
      * intros Exy. apply Hxy. rewrite <- (nth_map_seq x (toN xn) f Hf), <- (nth_map_seq y (toN xn) f Hf), Exy.
        reflexivity.
    + assert (Hge : ~ (to_Z r < to_Z xn)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      assert (Er' : toN r = toN xn) by nlia. rewrite Er' in HI.
      destruct (fin_unique (toN xn) (V xn T0) (V xn T) HI) as (Hd & Hsol & Huniq).
      destruct (output_spec xn Hn T) as [Lo Ho].
      assert (Hq : forall k, (k < toN xn)%nat ->
        repr (output T xn (xn + 1)).[of_Z (Z.of_nat k)] (fval (output T xn (xn + 1)).[of_Z (Z.of_nat k)]) /\
        (attainable (IZR (V xn T k (toN xn)) / IZR (V xn T k k)) ->
         Rabs (fval (output T xn (xn + 1)).[of_Z (Z.of_nat k)] - IZR (V xn T k (toN xn)) / IZR (V xn T k k))
           <= 1 / 1000)%R).
      { intros k Hk. rewrite Ho by exact Hk.
        destruct (qround_spec (V xn T k (toN xn)) (V xn T k k) (Hd k Hk)) as (v & Hrv & Hv).
        assert (Ev : fval (qround (V xn T k (toN xn)) (V xn T k k)) = v) by (destruct Hrv as [_ Ev]; exact Ev).
        rewrite Ev. split; assumption. }
      exists (Unique (map (fun k => fval (output T xn (xn + 1)).[of_Z (Z.of_nat k)]) (seq 0 (toN xn)))).
      split.
      * split.
        -- rewrite length_map, length_seq, toN_Z. exact (f_equal to_Z (eq_sym Lo)).
        -- intros k Hk. rewrite length_map, length_seq in Hk.
           exists (fval (output T xn (xn + 1)).[of_Z (Z.of_nat k)]). split.
           ++ rewrite (nth_error_nth' _ 0%R) by (rewrite length_map, length_seq; exact Hk).
              rewrite nth_map_seq by exact Hk. reflexivity.
           ++ exact (proj1 (Hq k Hk)).
      * exists (map (fun k => IZR (V xn T k (toN xn)) / IZR (V xn T k k))%R (seq 0 (toN xn))).
        split; [| split].
        -- apply Key. split; [rewrite length_map, length_seq; reflexivity |].
           apply (sol_ext _ _ (fun k => IZR (V xn T k (toN xn)) / IZR (V xn T k k))%R);
             [intros j Hj; symmetry; apply nth_map_seq; exact Hj | exact Hsol].
        -- intros ys Hys. apply Key in Hys. destruct Hys as [Hly Hsy].
           apply (nth_ext _ _ 0%R 0%R); [rewrite length_map, length_seq; exact Hly |].
           intros k Hk. rewrite Hly in Hk. rewrite nth_map_seq by exact Hk. exact (Huniq (fun j => nth j ys 0%R) Hsy k Hk).
        -- unfold approximates. apply (Forall2_iff _ _ _ 0%R 0%R); [rewrite !length_map, !length_seq; reflexivity |].
           intros k Hk. rewrite length_map, length_seq in Hk. rewrite !nth_map_seq by exact Hk.
           exact (proj2 (Hq k Hk)).
Qed.


(* An injective system has a solution : the elimination theory above, run on
   the scaled integer table in the proof only (the program never runs it on
   this path). *)
Lemma exact_exists :
  forall (n : N) (a : list (list R)) (b : list R) (xn : uint) (xa : array (array float)) (xb : array float),
  valid_input n a b -> repr xn n -> repr xa a -> repr xb b ->
  (forall d : nat -> R,
     (forall i, (i < toN xn)%nat -> sumR (fun j => nth j (nth i a []) 0%R * d j)%R (toN xn) = 0%R) ->
     forall j, (j < toN xn)%nat -> d j = 0%R) ->
  exists x : nat -> R,
    forall i, (i < toN xn)%nat -> sumR (fun j => nth j (nth i a []) 0%R * x j)%R (toN xn) = nth i b 0%R.
Proof.
  intros n a b xn xa xb [Hvn Hrows Hrow Hvb] Hxn Ha Hb Hinj.
  unfold repr, repr_uint in Hxn.
  assert (Hn : (1 <= to_Z xn <= 100)%Z) by lia.
  pose proof (toNn xn Hn) as HnN.
  assert (Hlen : forall {X} (l : list X), len l = n -> List.length l = toN xn).
  { intros X l Hl. unfold len in Hl. unfold toN. lia. }
  assert (La : List.length a = toN xn) by (apply Hlen; exact Hrows).
  assert (Lb : List.length b = toN xn) by (apply Hlen; exact Hvb).
  assert (Lrow : forall i, (i < toN xn)%nat -> List.length (nth i a []) = toN xn).
  { intros i Hi. apply Hlen. rewrite Forall_nth in Hrow. apply Hrow. lia. }
  destruct (build_spec xn Hn xa xb) as [HL0 HV0].
  set (T0 := build xa xb xn (xn + 1)) in *.
  set (E := fun i : nat => row_exp xn xa.[of_Z (Z.of_nat i)] xb.[of_Z (Z.of_nat i)]).
  assert (HA : forall i j, (i < toN xn)%nat -> (j < toN xn)%nat ->
    nth j (nth i a []) 0%R = (IZR (V xn T0 i j) * powerRZ 2 (E i))%R).
  { intros i j Hi Hj. rewrite HV0 by lia.
    replace (Nat.ltb j (toN xn)) with true by (symmetry; apply Nat.ltb_lt; exact Hj).
    assert (Hr : repr (xa.[of_Z (Z.of_nat i)]).[of_Z (Z.of_nat j)] (nth j (nth i a []) 0%R)).
    { apply repr_nth_float; [apply repr_nth_row; [exact Ha | lia] | rewrite Lrow; assumption]. }
    unfold E. rewrite scale_spec; [apply fval_dec; exact Hr |].
    apply (row_exp_spec xn Hn). rewrite of_Z_spec, Z.mod_small; [nlia | change wB with 9223372036854775808%Z; lia]. }
  assert (HB : forall i, (i < toN xn)%nat -> nth i b 0%R = (IZR (V xn T0 i (toN xn)) * powerRZ 2 (E i))%R).
  { intros i Hi. rewrite HV0 by lia. rewrite Nat.ltb_irrefl.
    assert (Hr : repr xb.[of_Z (Z.of_nat i)] (nth i b 0%R)) by (apply repr_nth_float; [exact Hb | lia]).
    unfold E. rewrite scale_spec; [apply fval_dec; exact Hr |]. apply (row_exp_spec xn Hn). }
  assert (Hrs : forall i x, (i < toN xn)%nat ->
    sumR (fun j => nth j (nth i a []) 0%R * x j)%R (toN xn) = (rowsum (toN xn) (V xn T0) i x * powerRZ 2 (E i))%R).
  { intros i x Hi. unfold rowsum. rewrite <- sumR_scal_r. apply sumR_ext. intros j Hj.
    rewrite HA by assumption. ring. }
  destruct (eliminate_spec xn Hn T0 HL0) as (HL & Hr & HI).
  destruct (Nat.lt_ge_cases (toN (snd (eliminate xn (xn + 1) T0))) (toN xn)) as [Hlt | Hge].
  - destruct (fin_kernel (toN xn) _ _ _ HI Hlt) as (d & Hd & f & Hf & Hdf).
    exfalso. apply Hdf. apply Hinj; [| exact Hf].
    intros i Hi. rewrite Hrs by exact Hi. rewrite (Hd i Hi). ring.
  - assert (Er : toN (snd (eliminate xn (xn + 1) T0)) = toN xn) by nlia. rewrite Er in HI.
    destruct (fin_unique (toN xn) _ _ HI) as (_ & Hsol & _).
    eexists. intros i Hi. rewrite Hrs by exact Hi. rewrite (Hsol i Hi). rewrite HB by exact Hi. reflexivity.
Qed.

(* ================================================================== *)
(* Part 2 : the float path                                            *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Floats : finiteness and the transport lemmas under a finiteness    *)
(* check instead of a magnitude bound                                 *)
(* ------------------------------------------------------------------ *)

Module FP := Flocq.IEEE754.PrimFloat.

Lemma fin_mul : forall a b : float, PrimFloat.is_finite (a * b)%float = true ->
  PrimFloat.is_finite a = true /\ PrimFloat.is_finite b = true.
Proof.
  intros a b. rewrite !FP.is_finite_equiv, FP.mul_equiv.
  destruct (FP.Prim2B a), (FP.Prim2B b); intros H; simpl in H; first [discriminate | split; reflexivity].
Qed.

Lemma fin_add : forall a b : float, PrimFloat.is_finite (a + b)%float = true ->
  PrimFloat.is_finite a = true /\ PrimFloat.is_finite b = true.
Proof.
  intros a b. rewrite !FP.is_finite_equiv, FP.add_equiv.
  destruct (FP.Prim2B a) as [sa|sa| |sa ma ea Ha], (FP.Prim2B b) as [sb|sb| |sb mb eb Hb];
    intros H; simpl in H; try discriminate; try (split; reflexivity);
    destruct sa, sb; simpl in H; discriminate.
Qed.

Lemma fin_sub : forall a b : float, PrimFloat.is_finite (a - b)%float = true ->
  PrimFloat.is_finite a = true /\ PrimFloat.is_finite b = true.
Proof.
  intros a b. rewrite !FP.is_finite_equiv, FP.sub_equiv.
  destruct (FP.Prim2B a) as [sa|sa| |sa ma ea Ha], (FP.Prim2B b) as [sb|sb| |sb mb eb Hb];
    intros H; simpl in H; try discriminate; try (split; reflexivity);
    destruct sa, sb; simpl in H; discriminate.
Qed.

Lemma repr_mul_fin : forall (a b : float) x y, repr a x -> repr b y ->
  PrimFloat.is_finite (a * b)%float = true -> repr (a * b)%float (rnd (x * y)).
Proof.
  intros a b x y Ha Hb Hf.
  destruct (Rlt_bool_spec (Rabs (rnd (x * y))) (bpow radix2 1024)) as [Hlt | Hge];
    [apply repr_mul; assumption | exfalso].
  apply repr_float_iff in Ha, Hb; destruct Ha as [Fa Ea]; destruct Hb as [Fb Eb].
  pose proof (Bmult_correct _ _ FP.Hprec FP.Hmax mode_NE (FP.Prim2B a) (FP.Prim2B b)) as H.
  prim_correct H. rewrite Ea, Eb, Rlt_bool_false in H by exact Hge.
  pose proof (f_equal is_finite_SF H) as E. rewrite is_finite_SF_B2SF in E.
  rewrite FP.is_finite_equiv, FP.mul_equiv in Hf.
  pose proof (eq_trans (eq_sym Hf) E) as X. discriminate X.
Qed.

Lemma repr_add_fin : forall (a b : float) x y, repr a x -> repr b y ->
  PrimFloat.is_finite (a + b)%float = true -> repr (a + b)%float (rnd (x + y)).
Proof.
  intros a b x y Ha Hb Hf.
  destruct (Rlt_bool_spec (Rabs (rnd (x + y))) (bpow radix2 1024)) as [Hlt | Hge];
    [apply repr_add; assumption | exfalso].
  apply repr_float_iff in Ha, Hb; destruct Ha as [Fa Ea]; destruct Hb as [Fb Eb].
  pose proof (Bplus_correct _ _ FP.Hprec FP.Hmax mode_NE (FP.Prim2B a) (FP.Prim2B b) Fa Fb) as H.
  prim_correct H. rewrite Ea, Eb, Rlt_bool_false in H by exact Hge.
  destruct H as [H _].
  pose proof (f_equal is_finite_SF H) as E. rewrite is_finite_SF_B2SF in E.
  rewrite FP.is_finite_equiv, FP.add_equiv in Hf.
  pose proof (eq_trans (eq_sym Hf) E) as X. discriminate X.
Qed.

(* ------------------------------------------------------------------ *)
(* The forward error of a float dot product                           *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

Definition nu : R := u / 2.             (* 2^-53, the unit roundoff *)
Definition lamR : R := 3 * nu.
Definition muR : R := 3 * eta_max.

Lemma nu_val : nu = / 9007199254740992.
Proof. unfold nu. rewrite u_val. field. Qed.

(* one step of the sequential dot product : a product rounded, then a sum *)
Lemma dot_step : forall K S P A x y,
  0 <= K <= 1048576 -> Rabs P <= A ->
  Rabs (S - P) <= K * lamR * A + K * muR ->
  Rabs (rnd (S + rnd (x * y)) - (P + x * y)) <= (K + 1) * lamR * (A + Rabs (x * y)) + (K + 1) * muR.
Proof.
  intros K S P A x y HK HP HS.
  destruct (rnd_model (x * y)) as (e1 & h1 & He1 & Hh1 & _ & Em).
  set (m := rnd (x * y)) in *.
  destruct (rnd_model (S + m)) as (e2 & h2 & He2 & Hh2 & _ & Es).
  rewrite Es. set (T := Rabs (x * y)).
  pose proof eta_max_pos as Hpos. pose proof (Rabs_pos (x * y)) as HT. fold T in HT.
  pose proof (Rabs_pos P). fold nu in He1, He2. pose proof nu_val as Hnu.
  assert (F1 : Rabs (x * y * e1) <= T * nu).
  { rewrite Rabs_mult. apply Rmult_le_compat_l; [exact HT | exact He1]. }
  assert (Fm : Rabs m <= T + T * nu + eta_max).
  { rewrite Em. eapply Rle_trans; [apply Rabs_triang |].
    replace (x * y * (1 + e1)) with (x * y + x * y * e1) by ring.
    eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang |]. fold T. lra. }
  assert (F3 : Rabs (S + m) <= Rabs (S - P) + A + T + T * nu + eta_max).
  { replace (S + m) with ((S - P) + P + m) by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang |]. lra. }
  assert (F2 : Rabs ((S + m) * e2) <= (K * lamR * A + K * muR + A + T + T * nu + eta_max) * nu).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [| exact He2]. lra. }
  assert (F5 : K * A <= 1048576 * A) by (apply Rmult_le_compat_r; lra).
  assert (F6 : 0 <= K * T) by (apply Rmult_le_pos; lra).
  assert (F7 : 0 <= K * eta_max) by (apply Rmult_le_pos; lra).
  assert (F8 : 0 <= K * A) by (apply Rmult_le_pos; lra).
  assert (F9 : K * eta_max <= 1048576 * eta_max) by (apply Rmult_le_compat_r; lra).
  replace ((S + m) * (1 + e2) + h2 - (P + x * y))
    with ((S - P) + (x * y * e1 + h1) + (S + m) * e2 + h2)
    by (rewrite Em; ring).
  eapply Rle_trans; [apply Rabs_triang |].
  eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang |].
  eapply Rle_trans; [apply Rplus_le_compat_r, Rplus_le_compat_r, Rabs_triang |].
  eapply Rle_trans; [apply Rplus_le_compat_r, Rplus_le_compat_r, Rplus_le_compat_l, Rabs_triang |].
  unfold lamR, muR in *. rewrite Hnu in *. lra.
Qed.

Open Scope uint63_scope.

(* the sequential float dot product of X[ox ..] and Y[oy ..] over len terms *)
Definition fdot (X : array float) (ox : int) (Y : array float) (oy : int) (len : int) : float :=
  loop len (fun _ _ => true) (fun k s => (s + X.[ox + k] * Y.[oy + k])%float) 0 zero.

Definition ix (k : nat) : int := of_Z (Z.of_nat k).

Definition fin (f : float) : Prop := PrimFloat.is_finite f = true.

Definition prodsum (X : array float) (ox : int) (Y : array float) (oy : int) (k : nat) : R :=
  sumR (fun j => fval X.[ox + ix j] * fval Y.[oy + ix j])%R k.

Definition abssum (X : array float) (ox : int) (Y : array float) (oy : int) (k : nat) : R :=
  sumR (fun j => Rabs (fval X.[ox + ix j] * fval Y.[oy + ix j]))%R k.

Lemma abssum_ge : forall X ox Y oy k, (Rabs (prodsum X ox Y oy k) <= abssum X ox Y oy k)%R.
Proof.
  intros X ox Y oy k. unfold prodsum, abssum. induction k as [| k IH]; simpl.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma toN_S : forall j hi : int, (to_Z j < to_Z hi)%Z -> toN (j + 1) = S (toN j).
Proof. intros j hi H. pose proof (to_Z_bounded hi). unfold toN. sia. Qed.

Lemma ix_toN : forall k, ix (toN k) = k.
Proof. intros k. apply of_toN. Qed.

Lemma fval_repr : forall f, fin f -> repr f (fval f).
Proof. intros f H. split; [exact H | reflexivity]. Qed.

Lemma fdot_spec : forall X ox Y oy len, (to_Z len <= 1048576)%Z ->
  fin (fdot X ox Y oy len) ->
  (forall k, (k < toN len)%nat -> fin X.[ox + ix k] /\ fin Y.[oy + ix k]) /\
  (Rabs (fval (fdot X ox Y oy len) - prodsum X ox Y oy (toN len))
     <= INR (toN len) * lamR * abssum X ox Y oy (toN len) + INR (toN len) * muR)%R.
Proof.
  intros X ox Y oy len Hlen. unfold fdot.
  apply (for_inv (fun k s => fin s ->
    (forall j, (j < toN k)%nat -> fin X.[ox + ix j] /\ fin Y.[oy + ix j]) /\
    (Rabs (fval s - prodsum X ox Y oy (toN k))
       <= INR (toN k) * lamR * abssum X ox Y oy (toN k) + INR (toN k) * muR)%R)).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded len). lia.
  - intros _. change (toN 0) with 0%nat. split; [intros j Hj; lia |].
    unfold prodsum, abssum. simpl. change (fval zero) with 0%R.
    rewrite Rminus_0_r, Rabs_R0. lra.
  - intros k s Hk IH Hf. cbv beta in Hf.
    destruct (fin_add _ _ Hf) as [Fs Fp]. destruct (fin_mul _ _ Fp) as [Fx Fy].
    destruct (IH Fs) as [IHf IHb].
    rewrite (toN_S k len) by lia.
    split.
    + intros j Hj. destruct (Nat.eq_dec j (toN k)) as [-> | Hne]; [rewrite ix_toN; split; assumption |].
      apply IHf. lia.
    + pose proof (repr_mul_fin _ _ _ _ (fval_repr _ Fx) (fval_repr _ Fy) Fp) as Rm.
      pose proof (repr_add_fin _ _ _ _ (fval_repr _ Fs) Rm Hf) as Ra.
      destruct Ra as [_ ->].
      unfold prodsum, abssum. simpl sumR. fold (prodsum X ox Y oy (toN k)). fold (abssum X ox Y oy (toN k)).
      rewrite ix_toN, S_INR.
      apply dot_step; [| apply abssum_ge | exact IHb].
      split; [apply pos_INR |]. rewrite INR_IZR_INZ. unfold toN. rewrite Z2Nat.id by (pose proof (to_Z_bounded k); lia).
      replace 1048576%R with (IZR 1048576) by reflexivity. apply IZR_le. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact dyadic numbers m * 2^e (Z mantissa and exponent) : the        *)
(* certificate's O(n^2) norm and bound arithmetic and the witness      *)
(* checks                                                             *)
(* ------------------------------------------------------------------ *)

Definition dy := (Z * Z)%type.

Definition dval (d : dy) : R := (IZR (fst d) * powerRZ 2 (snd d))%R.

Definition dadd (x y : dy) : dy :=
  let (m1, e1) := x in let (m2, e2) := y in
  if Z.leb e1 e2 then ((m1 + Z.shiftl m2 (e2 - e1))%Z, e1)
  else ((Z.shiftl m1 (e1 - e2) + m2)%Z, e2).

Definition dmul (x y : dy) : dy := ((fst x * fst y)%Z, (snd x + snd y)%Z).
Definition dabs (x : dy) : dy := (Z.abs (fst x), snd x).
Definition dneg (x : dy) : dy := ((- fst x)%Z, snd x).
Definition dleb (x y : dy) : bool := Z.leb 0 (fst (dadd y (dneg x))).
Definition dltb (x y : dy) : bool := Z.ltb 0 (fst (dadd y (dneg x))).
Definition dzero (x : dy) : bool := Z.eqb (fst x) 0.
Definition dmax (x y : dy) : dy := if dleb x y then y else x.
Definition d0 : dy := (0%Z, 0%Z).
Definition dint (z : Z) : dy := (z, 0%Z).

Lemma pow2_pos : forall e, (0 < powerRZ 2 e)%R.
Proof. intros e. apply powerRZ_lt. lra. Qed.

Lemma shiftl_val : forall m k e, (0 <= k)%Z ->
  (IZR (Z.shiftl m k) * powerRZ 2 e = IZR m * powerRZ 2 (e + k))%R.
Proof.
  intros m k e Hk. rewrite Z.shiftl_mul_pow2 by exact Hk. rewrite mult_IZR, IZR_pow2 by exact Hk.
  rewrite powerRZ_add by lra. ring.
Qed.

Lemma dval_add : forall x y, dval (dadd x y) = (dval x + dval y)%R.
Proof.
  intros [m1 e1] [m2 e2]. unfold dadd, dval; simpl.
  destruct (Z.leb_spec e1 e2) as [H | H]; simpl.
  - rewrite plus_IZR, Rmult_plus_distr_r, shiftl_val by lia.
    replace (e1 + (e2 - e1))%Z with e2 by ring. reflexivity.
  - rewrite plus_IZR, Rmult_plus_distr_r, shiftl_val by lia.
    replace (e2 + (e1 - e2))%Z with e1 by ring. reflexivity.
Qed.

Lemma dval_mul : forall x y, dval (dmul x y) = (dval x * dval y)%R.
Proof.
  intros [m1 e1] [m2 e2]. unfold dmul, dval; simpl. rewrite mult_IZR, powerRZ_add by lra. ring.
Qed.

Lemma dval_abs : forall x, dval (dabs x) = Rabs (dval x).
Proof.
  intros [m e]. unfold dabs, dval; simpl. rewrite Rabs_mult, abs_IZR.
  rewrite (Rabs_right (powerRZ 2 e)) by (apply Rle_ge, Rlt_le, pow2_pos). reflexivity.
Qed.

Lemma dval_neg : forall x, dval (dneg x) = (- dval x)%R.
Proof. intros [m e]. unfold dneg, dval; simpl. rewrite opp_IZR. ring. Qed.

Lemma dval_int : forall z, dval (dint z) = IZR z.
Proof. intros z. unfold dval, dint. simpl. ring. Qed.

Lemma dval_0 : dval d0 = 0%R.
Proof. unfold dval, d0. simpl. ring. Qed.

Lemma dsign_le : forall x, (0 <= fst x)%Z <-> (0 <= dval x)%R.
Proof.
  intros [m e]. unfold dval; simpl. pose proof (pow2_pos e). split; intros H'.
  - apply Rmult_le_pos; [apply IZR_le; exact H' | lra].
  - destruct (Z.le_gt_cases 0 m) as [| Hlt]; [assumption | exfalso].
    apply IZR_lt in Hlt. assert (IZR m * powerRZ 2 e < 0)%R by (apply Rmult_neg_pos; lra). lra.
Qed.

Lemma dsign_lt : forall x, (0 < fst x)%Z <-> (0 < dval x)%R.
Proof.
  intros [m e]. unfold dval; simpl. pose proof (pow2_pos e). split; intros H'.
  - apply Rmult_lt_0_compat; [apply IZR_lt; exact H' | lra].
  - destruct (Z.lt_ge_cases 0 m) as [| Hlt]; [assumption | exfalso].
    apply IZR_le in Hlt. assert (0 <= - IZR m * powerRZ 2 e)%R by (apply Rmult_le_pos; lra). nra.
Qed.

Lemma dzero_spec : forall x, dzero x = true <-> dval x = 0%R.
Proof.
  intros [m e]. unfold dzero, dval; simpl. pose proof (pow2_pos e). rewrite Z.eqb_eq. split; intros H'.
  - subst. ring.
  - apply Rmult_integral in H'. destruct H' as [H' | H']; [apply eq_IZR; exact H' | lra].
Qed.

Lemma dleb_spec : forall x y, dleb x y = true <-> (dval x <= dval y)%R.
Proof.
  intros x y. unfold dleb. rewrite Z.leb_le, dsign_le, dval_add, dval_neg. lra.
Qed.

Lemma dltb_spec : forall x y, dltb x y = true <-> (dval x < dval y)%R.
Proof.
  intros x y. unfold dltb. rewrite Z.ltb_lt, dsign_lt, dval_add, dval_neg. lra.
Qed.

Lemma dmax_l : forall x y, (dval x <= dval (dmax x y))%R.
Proof.
  intros x y. unfold dmax. destruct (dleb x y) eqn:E; [apply dleb_spec; exact E | lra].
Qed.

Lemma dmax_r : forall x y, (dval y <= dval (dmax x y))%R.
Proof.
  intros x y. unfold dmax. destruct (dleb x y) eqn:E; [lra |].
  assert (~ (dval x <= dval y)%R) by (rewrite <- dleb_spec; congruence). lra.
Qed.

(* a float, read exactly *)
Lemma dval_dec : forall f, dval (dec f) = fval f.
Proof.
  intros f. unfold dval. apply dec_val.
Qed.

(* ------------------------------------------------------------------ *)
(* The certificate, on real matrices                                  *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

Lemma sumR_le : forall f g k, (forall j, (j < k)%nat -> f j <= g j) -> sumR f k <= sumR g k.
Proof.
  intros f g k H. induction k as [| k IH]; simpl; [lra |].
  pose proof (H k ltac:(lia)). assert (sumR f k <= sumR g k) by (apply IH; intros; apply H; lia). lra.
Qed.

Lemma sumR_abs : forall f k, Rabs (sumR f k) <= sumR (fun j => Rabs (f j)) k.
Proof.
  intros f k. induction k as [| k IH]; simpl; [rewrite Rabs_R0; lra |].
  eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma sumR_nonneg : forall f k, (forall j, (j < k)%nat -> 0 <= f j) -> 0 <= sumR f k.
Proof.
  intros f k H. induction k as [| k IH]; simpl; [lra |].
  pose proof (H k ltac:(lia)). assert (0 <= sumR f k) by (apply IH; intros; apply H; lia). lra.
Qed.

Lemma sumR_swap : forall (f : nat -> nat -> R) n m,
  sumR (fun j => sumR (fun k => f k j) m) n = sumR (fun k => sumR (fun j => f k j) n) m.
Proof.
  intros f n m. induction n as [| n IH]; simpl.
  - rewrite sumR_zero; [reflexivity | intros; reflexivity].
  - rewrite IH, <- sumR_plus. reflexivity.
Qed.

Lemma max_idx : forall (f : nat -> R) k, (0 < k)%nat ->
  exists j0, (j0 < k)%nat /\ forall j, (j < k)%nat -> f j <= f j0.
Proof.
  intros f k Hk. induction k as [| k IH]; [lia |].
  destruct (Nat.eq_dec k 0) as [-> | Hne].
  - exists 0%nat. split; [lia |]. intros j Hj. assert (j = 0%nat) by lia. subst. lra.
  - destruct (IH ltac:(lia)) as (j0 & Hj0 & Hm).
    destruct (Rle_lt_dec (f k) (f j0)) as [Hle | Hlt].
    + exists j0. split; [lia |]. intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hjk]; [exact Hle | apply Hm; lia].
    + exists k. split; [lia |]. intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hjk]; [lra |].
      pose proof (Hm j ltac:(lia)). lra.
Qed.

Section Cert.
Variable N : nat.
Variables Am Rm : nat -> nat -> R.

Definition delta (i j : nat) : R := if Nat.eqb i j then 1 else 0.

Definition Emat (i j : nat) : R := delta i j - sumR (fun k => Rm i k * Am k j) N.

Definition matvec (M : nat -> nat -> R) (i : nat) (x : nat -> R) : R := sumR (fun j => M i j * x j) N.

Lemma decomp : forall e i, (i < N)%nat ->
  e i = sumR (fun k => Rm i k * matvec Am k e) N + sumR (fun j => Emat i j * e j) N.
Proof.
  intros e i Hi. unfold Emat, matvec.
  rewrite (sumR_ext (fun j => (delta i j - sumR (fun k => Rm i k * Am k j) N) * e j)
                    (fun j => 1 * (if Nat.eqb j i then e i else 0) + (-1) * sumR (fun k => Rm i k * Am k j * e j) N))
    by (intros j Hj; rewrite sumR_scal_r; unfold delta;
        destruct (Nat.eqb_spec i j), (Nat.eqb_spec j i); subst; try lia; ring).
  rewrite sumR_lin, sumR_delta by exact Hi.
  rewrite (sumR_ext (fun k => Rm i k * sumR (fun j => Am k j * e j) N)
                    (fun k => sumR (fun j => Rm i k * Am k j * e j) N))
    by (intros k Hk; rewrite <- sumR_scal; apply sumR_ext; intros; ring).
  rewrite <- (sumR_swap (fun k j => Rm i k * Am k j * e j)). ring.
Qed.

Lemma cert_bound : forall eps rho sigma (e : nat -> R),
  (forall i, (i < N)%nat -> sumR (fun j => Rabs (Emat i j)) N <= eps) ->
  (forall i, (i < N)%nat -> sumR (fun k => Rabs (Rm i k)) N <= rho) ->
  (forall i, (i < N)%nat -> Rabs (matvec Am i e) <= sigma) ->
  forall j, (j < N)%nat -> Rabs (e j) * (1 - eps) <= rho * sigma.
Proof.
  intros eps rho sigma e HE HR HS j Hj.
  assert (HN : (0 < N)%nat) by lia.
  assert (Hrho : 0 <= rho).
  { eapply Rle_trans; [| apply (HR 0%nat HN)]. apply sumR_nonneg. intros; apply Rabs_pos. }
  assert (Hsig : 0 <= sigma) by (eapply Rle_trans; [apply Rabs_pos | apply (HS 0%nat HN)]).
  destruct (max_idx (fun j => Rabs (e j)) N HN) as (j0 & Hj0 & Hm). cbv beta in Hm.
  set (M := Rabs (e j0)) in *.
  assert (Hi : forall i, (i < N)%nat -> Rabs (e i) <= rho * sigma + eps * M).
  { intros i Hi. rewrite (decomp e i Hi).
    eapply Rle_trans; [apply Rabs_triang |]. apply Rplus_le_compat.
    - eapply Rle_trans; [apply sumR_abs |].
      apply Rle_trans with (sumR (fun k => Rabs (Rm i k) * sigma) N).
      + apply sumR_le. intros k Hk. rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | apply HS; exact Hk].
      + rewrite sumR_scal_r. apply Rmult_le_compat_r; [exact Hsig | apply HR; exact Hi].
    - eapply Rle_trans; [apply sumR_abs |].
      apply Rle_trans with (sumR (fun k => Rabs (Emat i k) * M) N).
      + apply sumR_le. intros k Hk. rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | apply Hm; exact Hk].
      + rewrite sumR_scal_r. rewrite (Rmult_comm eps M), Rmult_comm. apply Rmult_le_compat_l; [apply Rabs_pos | apply HE; exact Hi]. }
  pose proof (Hi j0 Hj0) as H0. fold M in H0. pose proof (Hm j Hj) as Hjm.
  assert (0 <= rho * sigma) by (apply Rmult_le_pos; assumption).
  destruct (Rle_lt_dec eps 1) as [Hle | Hlt].
  - apply Rle_trans with (M * (1 - eps)); [apply Rmult_le_compat_r; lra | lra].
  - assert (0 <= Rabs (e j) * (eps - 1)) by (apply Rmult_le_pos; [apply Rabs_pos | lra]). lra.
Qed.

End Cert.

(* ================================================================== *)
(* The program of the float path                                      *)
(* ================================================================== *)

Open Scope uint63_scope.

(* ------------------------------------------------------------------ *)
(* Unverified numerics : Gaussian elimination with partial pivoting   *)
(* (CLRS ch. 28) on M = [A | b] (n x (n + 1), flat) and on Q = I       *)
(* (n x n, flat), back substitution giving the candidate x~ and the    *)
(* approximate inverse R (in Q).  Nothing is proven of them : the      *)
(* certificate below checks what they produce.                         *)
(* ------------------------------------------------------------------ *)

Definition init_M (xa : array (array float)) (xb : array float) (n w : int) : array float :=
  loop n (fun _ _ => true)
    (fun i M => let row := xa.[i] in
       let M := loop n (fun _ _ => true) (fun j M => M.[i * w + j <- row.[j]]) 0 M in
       M.[i * w + n <- xb.[i]]) 0 (PArray.make (n * w) zero).

Definition init_Q (n : int) : array float :=
  loop n (fun _ _ => true) (fun i Q => Q.[i * n + i <- one]) 0 (PArray.make (n * n) zero).

(* the pivot threshold of each column : 2^-40 times its largest magnitude
   in A ; it only steers the candidates (which column looks free), it
   decides nothing *)
Definition thr_scale : float := 0x1p-40%float.

Definition col_thr (xa : array (array float)) (n : int) : array float :=
  loop n (fun _ _ => true)
    (fun j T => let m := loop n (fun _ _ => true)
                   (fun i m => let v := PrimFloat.abs (xa.[i].[j]) in if (m <? v)%float then v else m) 0 zero in
                T.[j <- (m * thr_scale)%float]) 0 (PArray.make n zero).

Definition swap_f (T : array float) (w p r : int) : array float :=
  loop w (fun _ _ => true)
    (fun j T => let x := T.[r * w + j] in let y := T.[p * w + j] in
                T.[r * w + j <- y].[p * w + j <- x]) 0 T.

(* row i -= f * row r, columns [lo, w) *)
Definition axpy_row (T : array float) (w i r lo : int) (f : float) : array float :=
  loop w (fun _ _ => true)
    (fun j T => T.[i * w + j <- (T.[i * w + j] - f * T.[r * w + j])%float]) lo T.

Definition scale_row (T : array float) (w i : int) (piv : float) : array float :=
  loop w (fun _ _ => true) (fun j T => T.[i * w + j <- (T.[i * w + j] / piv)%float]) 0 T.

(* a fresh array of length n, cell i = f i (v4 : the padded matrix, the
   row permutation's start) *)
Definition tab {T : Type} (n : int) (d : T) (f : int -> T) : array T :=
  loop n (fun _ _ => true) (fun i t => t.[i <- f i]) 0 (PArray.make n d).

(* v4 : fs_perm, the original index of the row now at each position
   (unverified, validated by the left-null check) *)
Record fstate := FS { fs_M : array float; fs_Q : array float; fs_r : int; fs_pc : array int;
                      fs_perm : array int }.

Definition fwd_col (n w : int) (thr : array float) (c : int) (st : fstate) : fstate :=
  let r := fs_r st in
  if r <? n then
    let M := fs_M st in
    let '(p, mx) := loop n (fun _ _ => true)
        (fun i pm => let v := PrimFloat.abs M.[i * w + c] in
                     if (snd pm <? v)%float then (i, v) else pm) r (r, zero) in
    if (mx <=? thr.[c])%float then st
    else
      let M := swap_f M w p r in
      let Q := swap_f (fs_Q st) n p r in
      let piv := M.[r * w + c] in
      let '(M, Q) := loop n (fun _ _ => true)
          (fun i mq => let '(M, Q) := mq in
             let f := (M.[i * w + c] / piv)%float in
             let M := axpy_row M w i r (c + 1) f in
             (M.[i * w + c <- zero], axpy_row Q n i r 0 f)) (r + 1) (M, Q) in
      let pm := fs_perm st in
      let x := pm.[p] in let y := pm.[r] in
      FS M Q (r + 1) (fs_pc st).[r <- c] pm.[p <- y].[r <- x]
  else st.

Definition forward (n w : int) (thr : array float) (M Q : array float) : fstate :=
  loop n (fun _ _ => true) (fwd_col n w thr) 0 (FS M Q 0 (PArray.make n 0) (tab n 0 (fun i => i))).

(* back substitution on the triangular M (rank n), the same operations on Q *)
Definition backsub (n w : int) (M Q : array float) : array float * array float :=
  loop n (fun _ _ => true)
    (fun t mq => let '(M, Q) := mq in
       let i := n - 1 - t in
       let piv := M.[i * w + i] in
       let xi := (M.[i * w + n] / piv)%float in
       let M := M.[i * w + n <- xi] in
       let Q := scale_row Q n i piv in
       loop i (fun _ _ => true)
         (fun i' mq => let '(M, Q) := mq in
            let f := M.[i' * w + i] in
            (M.[i' * w + n <- (M.[i' * w + n] - f * xi)%float], axpy_row Q n i' i 0 f)) 0 (M, Q))
    0 (M, Q).

Definition get_col (M : array float) (n w c : int) : array float :=
  loop n (fun _ _ => true) (fun i x => x.[i <- M.[i * w + c]]) 0 (PArray.make n zero).

Definition get_row (Q : array float) (n i : int) : array float :=
  loop n (fun _ _ => true) (fun k x => x.[k <- Q.[i * n + k]]) 0 (PArray.make n zero).

(* witness candidates on the echelon form of rank r < n *)
Definition free_col (pc : array int) (n r : int) : int :=
  let isp := loop r (fun _ _ => true) (fun t isp => isp.[pc.[t] <- true]) 0 (PArray.make n false) in
  loop n (fun _ _ => true) (fun c f => if andb (f =? n) (negb isp.[c]) then c else f) 0 n.

(* v4 : the k free columns, those not in pc[0..r), in increasing order
   (cells k .. n-1 unused) *)
Definition free_cols (pc : array int) (n r : int) : array int :=
  let isp := loop r (fun _ _ => true) (fun t isp => isp.[pc.[t] <- true]) 0 (PArray.make n false) in
  fst (loop n (fun _ _ => true)
         (fun c st => let '(fc, cnt) := st in
            if isp.[c] then (fc, cnt) else (fc.[cnt <- c], cnt + 1)) 0 (PArray.make n 0, 0)).

(* x[pc t] := (rhs t - sum_{j > pc t} M[t][j] x[j]) / M[t][pc t], t = r-1 .. 0 *)
Definition echelon_solve (M : array float) (pc : array int) (n w r : int) (homog : bool)
    (x : array float) : array float :=
  loop r (fun _ _ => true)
    (fun s x => let t := r - 1 - s in let c := pc.[t] in
       let s0 := if homog then zero else M.[t * w + n] in
       let acc := loop n (fun _ _ => true)
                    (fun j acc => (acc - M.[t * w + j] * x.[j])%float) (c + 1) s0 in
       x.[c <- (acc / M.[t * w + c])%float]) 0 x.

Definition argmax_rhs (M : array float) (n w r : int) : int :=
  fst (loop n (fun _ _ => true)
         (fun i pm => let v := PrimFloat.abs M.[i * w + n] in
                      if (snd pm <? v)%float then (i, v) else pm) r (r, zero)).

(* a float, read exactly, rounded to a fraction h / k with k <= 2^30 by
   continued fractions (stops at relative distance 2^-40) *)
Definition rat1 (f : float) : Z * Z :=
  let (m, e) := dec f in
  if Z.leb 0 e then (Z.shiftl m e, 1%Z) else
  let den := Z.shiftl 1 (- e) in
  let st := loop 64 (fun _ st => negb (snd st))
    (fun _ st => let '(an, ad, h1, h0, k1, k0) := fst st in
       let q := (an / ad)%Z in
       let h := (q * h1 + h0)%Z in let k := (q * k1 + k0)%Z in
       if Z.ltb 1073741824 k then (fst st, true)
       else let rem := (an - q * ad)%Z in
            let close := Z.leb (Z.shiftl (Z.abs (m * k - h * den)) 40) (Z.abs m * k) in
            ((ad, rem, h, h1, k, k1), orb (Z.eqb rem 0) close))
    0 ((m, den, 1%Z, 0%Z, 0%Z, 1%Z), false) in
  let '(_, _, h1, _, k1, _) := fst st in
  if Z.ltb 0 k1 then (h1, k1) else (0%Z, 1%Z).

(* a float vector rounded to fractions, over a common denominator L :
   the integer numerators and L *)
Definition ratvec (x : array float) (n : int) : array Z * Z :=
  let '(H, K, L) := loop n (fun _ _ => true)
      (fun j st => let '(H, K, L) := st in let (h, k) := rat1 x.[j] in
         (H.[j <- h], K.[j <- k], (L / zgcd L k * k)%Z)) 0
      (PArray.make n 0%Z, PArray.make n 1%Z, 1%Z) in
  (loop n (fun _ _ => true) (fun j P => P.[j <- (H.[j] * (L / K.[j]))%Z]) 0 (PArray.make n 0%Z), L).

(* ------------------------------------------------------------------ *)
(* Verified : the certificate and the witness checks                  *)
(* ------------------------------------------------------------------ *)

Definition dsumf (len : int) (f : int -> dy) : dy :=
  loop len (fun _ _ => true) (fun k acc => dadd acc (f k)) 0 d0.

Definition allf (len : int) (p : int -> bool) : bool :=
  loop len (fun _ _ => true) (fun k b => andb b (p k)) 0 true.

(* sum of f k d_k, with d_k := g k, and whether every d_k is finite *)
Definition dsumb (len : int) (g : int -> float) (f : int -> float -> dy) : dy * bool :=
  loop len (fun _ _ => true)
    (fun k st => let d := g k in (dadd (fst st) (f k d), andb (snd st) (PrimFloat.is_finite d))) 0 (d0, true).

(* the largest first component of h i, and whether every second one holds *)
Definition maxb (len : int) (h : int -> dy * bool) : dy * bool :=
  loop len (fun _ _ => true)
    (fun i st => let r := h i in (dmax (fst st) (fst r), andb (snd st) (snd r))) 0 (d0, true).

Definition dsub (x y : dy) : dy := dadd x (dneg y).
Definition d1 : dy := (1%Z, 0%Z).

Definition transpose (xa : array (array float)) (n : int) : array float :=
  loop n (fun _ _ => true)
    (fun i T => let row := xa.[i] in
       loop n (fun _ _ => true) (fun j T => T.[j * n + i <- row.[j]]) 0 T) 0 (PArray.make (n * n) zero).

(* S[k] = sum_j |A[k][j]| *)
Definition rowabs (xa : array (array float)) (n : int) : array dy :=
  loop n (fun _ _ => true)
    (fun k S => let row := xa.[k] in S.[k <- dsumf n (fun j => dabs (dec row.[j]))]) 0 (PArray.make n d0).

(* row i of E = I - R A : sum_j |delta_ij - fl(R_i . A_.j)| plus the error
   bound of the n dot products ; every dot product checked finite *)
Definition erow (n : int) (Q AT : array float) (S : array dy) (lamd mud2 : dy) (i : int) : dy * bool :=
  let e := dsumb n (fun j => fdot Q (i * n) AT (j * n) n)
             (fun j d => dabs (dsub (dint (if i =? j then 1%Z else 0%Z)) (dec d))) in
  let rr := dsumf n (fun k => dmul (dabs (dec Q.[i * n + k])) S.[k]) in
  (dadd (dadd (fst e) (dmul lamd rr)) mud2, snd e).

Definition rowR (n : int) (Q : array float) (i : int) : dy * bool :=
  (dsumf n (fun k => dabs (dec Q.[i * n + k])), true).

(* |b_i - fl(A_i . x~)| plus its error bound *)
Definition resid (n : int) (xa : array (array float)) (xb xt : array float) (lamd mud1 : dy) (i : int) : dy * bool :=
  let row := xa.[i] in
  let d := fdot row 0 xt 0 n in
  (dadd (dadd (dabs (dsub (dec xb.[i]) (dec d)))
              (dmul lamd (dsumf n (fun j => dabs (dmul (dec row.[j]) (dec xt.[j]))))))
        mud1,
   PrimFloat.is_finite d).

Definition certify (n : int) (xa : array (array float)) (xb : array float) (AT Q xt : array float) : bool :=
  let nz := i2z n in
  let lamd := ((3 * nz)%Z, (-53)%Z) in
  let mud1 := ((3 * nz)%Z, (-1075)%Z) in
  let mud2 := ((3 * nz * nz)%Z, (-1075)%Z) in
  let S := rowabs xa n in
  let '(eps, ok1) := maxb n (erow n Q AT S lamd mud2) in
  let '(rho, _) := maxb n (rowR n Q) in
  let '(sig, ok2) := maxb n (resid n xa xb xt lamd mud1) in
  andb (andb (andb ok1 ok2) (PArray.length xt =? n))
       (andb (dltb eps d1) (dleb (dadd (dmul (1000%Z, 0%Z) (dmul rho sig)) eps) d1)).

(* exact dot product of floats X[o ..] with integers Y[0 ..] *)
Definition zdot (X : array float) (o : int) (Y : array Z) (len : int) : dy :=
  dsumf len (fun k => dmul (dec X.[o + k]) (dint Y.[k])).

(* y^T A = 0 and y^T b <> 0 *)
Definition chk_incons (AT : array float) (xb : array float) (n : int) (y : array Z) : bool :=
  andb (allf n (fun j => dzero (zdot AT (j * n) y n))) (negb (dzero (zdot xb 0 y n))).

(* A p = q b, A v = 0, q <> 0, v <> 0 *)
Definition chk_mult (xa : array (array float)) (xb : array float) (n : int) (p : array Z) (q : Z)
    (v : array Z) : bool :=
  andb (andb (negb (Z.eqb q 0)) (negb (allf n (fun j => Z.eqb v.[j] 0))))
       (allf n (fun i => let row := xa.[i] in
                         andb (dzero (dsub (zdot row 0 p n) (dmul (dint q) (dec xb.[i]))))
                              (dzero (zdot row 0 v n)))).

(* ------------------------------------------------------------------ *)
(* v4 : the padded certificate of the singular branch                 *)
(* ------------------------------------------------------------------ *)

(* the candidate left-null vector of dropped row t : row r + t of Q,
   rounded to integers over a common denominator *)
Definition yv (Q : array float) (n r t : int) : array Z := fst (ratvec (get_row Q n (r + t)) n).

(* D : flag of every d_t = perm[r + t], t < k, and tix[d_t] := t (the last
   t written) *)
Definition mark_D (perm : array int) (n r k : int) : array bool * array int :=
  loop k (fun _ _ => true)
    (fun t st => let d := perm.[r + t] in ((fst st).[d <- true], (snd st).[d <- t]))
    0 (PArray.make n false, PArray.make n 0).

(* C : flag of every c_t = fc[t], t < k *)
Definition mark_C (fc : array int) (n k : int) : array bool :=
  loop k (fun _ _ => true) (fun t C => C.[fc.[t] <- true]) 0 (PArray.make n false).

(* y is a reduced left-null vector of row d : y^T A = 0, y^T b = 0,
   y_d <> 0, y_i = 0 for every other i in D *)
Definition chk_red (AT xb : array float) (n : int) (y : array Z) (d : int) (Df : array bool) : bool :=
  andb (andb (allf n (fun j => dzero (zdot AT (j * n) y n))) (dzero (zdot xb 0 y n)))
       (andb (negb (Z.eqb y.[d] 0))
             (allf n (fun i => orb (negb Df.[i]) (orb (i =? d) (Z.eqb y.[i] 0))))).

(* over the k dropped rows : does one of them prove the system
   inconsistent, and are all of them reduced left-null vectors (with r < n,
   d_t < n and c_t < n) *)
Definition scan_null (AT xb Q : array float) (perm fc : array int) (Df : array bool) (n r k : int)
    : bool * bool :=
  loop k (fun _ _ => true)
    (fun t s => let y := yv Q n r t in let d := perm.[r + t] in
       (orb (fst s) (chk_incons AT xb n y),
        andb (snd s) (andb (andb (d <? n) (fc.[t] <? n)) (chk_red AT xb n y d Df))))
    0 (false, r <? n).

(* the padded matrix B, entry (i, j) *)
Definition bentry (xa : array (array float)) (Df : array bool) (tix fc : array int) (Cf : array bool)
    (i j : int) : float :=
  if Df.[i] then (if j =? fc.[tix.[i]] then one else zero)
  else if Cf.[j] then zero else xa.[i].[j].

(* B as fresh rows : the one nested table besides the input (steering v4) *)
Definition padB (xa : array (array float)) (n : int) (Df : array bool) (tix fc : array int)
    (Cf : array bool) : array (array float) :=
  tab n (PArray.make 0 zero) (fun i => tab n zero (fun j => bentry xa Df tix fc Cf i j)).

(* the eps < 1 half of [certify] : ||I - Q A||_inf < 1, rigorously *)
Definition certify_inj (n : int) (xa : array (array float)) (AT Q : array float) : bool :=
  let nz := i2z n in
  let lamd := ((3 * nz)%Z, (-53)%Z) in
  let mud2 := ((3 * nz * nz)%Z, (-1075)%Z) in
  let S := rowabs xa n in
  let '(eps, ok1) := maxb n (erow n Q AT S lamd mud2) in
  andb ok1 (dltb eps d1).

(* unverified elimination on B for an approximate inverse, then the
   verified injectivity certificate *)
Definition padded_ok (xa : array (array float)) (n : int) (Df : array bool) (tix fc : array int)
    (Cf : array bool) : bool :=
  let B := padB xa n Df tix fc Cf in
  let w := n + 1 in
  let st := forward n w (col_thr B n) (init_M B (PArray.make n zero) n w) (init_Q n) in
  if fs_r st =? n then
    certify_inj n B (transpose B n) (snd (backsub n w (fs_M st) (fs_Q st)))
  else false.

Definition solve (n : uint) (xa : array (array float)) (xb : array float) : outcome (array float) :=
  let w := n + 1 in
  let st := forward n w (col_thr xa n) (init_M xa xb n w) (init_Q n) in
  let AT := transpose xa n in
  if fs_r st =? n then
    let '(M, Q) := backsub n w (fs_M st) (fs_Q st) in
    let xt := get_col M n w n in
    if certify n xa xb AT Q xt then Unique xt else solve_exact n xa xb
  else
    let M := fs_M st in
    let r := fs_r st in
    let k := if r <? n then n - r else 0 in
    let fc := free_cols (fs_pc st) n r in
    let mD := mark_D (fs_perm st) n r k in
    let Df := fst mD in
    let tix := snd mD in
    let Cf := mark_C fc n k in
    let sc := scan_null AT xb (fs_Q st) (fs_perm st) fc Df n r k in
    if fst sc then Inconsistent
    else if (if snd sc then padded_ok xa n Df tix fc Cf else false) then Multiple
    else
      let f := free_col (fs_pc st) n r in
      let x0 := echelon_solve M (fs_pc st) n w r false (PArray.make n zero) in
      let v := echelon_solve M (fs_pc st) n w r true (PArray.make n zero).[f <- one] in
      let '(p, q) := ratvec x0 n in
      if chk_mult xa xb n p q (fst (ratvec v n)) then Multiple else solve_exact n xa xb.

(* ================================================================== *)
(* Proofs of the float path                                           *)
(* ================================================================== *)

Lemma to_Z_0_le : forall x : int, (to_Z 0 <= to_Z x)%Z.
Proof. intros x. change (to_Z 0) with 0%Z. pose proof (to_Z_bounded x). lia. Qed.

Lemma dsumf_spec : forall len f,
  dval (dsumf len f) = sumR (fun k => dval (f (ix k))) (toN len).
Proof.
  intros len f. unfold dsumf.
  apply (for_inv (fun k acc => dval acc = sumR (fun j => dval (f (ix j))) (toN k))).
  - apply to_Z_0_le.
  - apply dval_0.
  - intros k acc Hk IH. rewrite (toN_S k len) by lia. simpl. rewrite dval_add, IH, ix_toN. reflexivity.
Qed.

Lemma allf_spec : forall len p,
  allf len p = true <-> forall k, (k < toN len)%nat -> p (ix k) = true.
Proof.
  intros len p. unfold allf.
  apply (for_inv (fun k b => b = true <-> forall j, (j < toN k)%nat -> p (ix j) = true)).
  - apply to_Z_0_le.
  - split; [intros _ j Hj; change (toN 0) with 0%nat in Hj; lia | reflexivity].
  - intros k b Hk IH. rewrite (toN_S k len) by lia. rewrite Bool.andb_true_iff, IH. split.
    + intros [H1 H2] j Hj. destruct (Nat.eq_dec j (toN k)) as [-> | Hne]; [rewrite ix_toN; exact H2 | apply H1; lia].
    + intros H. split; [intros j Hj; apply H; lia | rewrite <- (ix_toN k); apply H; lia].
Qed.

Lemma dsumb_spec : forall len g f, snd (dsumb len g f) = true ->
  (forall k, (k < toN len)%nat -> fin (g (ix k))) /\
  dval (fst (dsumb len g f)) = sumR (fun k => dval (f (ix k) (g (ix k)))) (toN len).
Proof.
  intros len g f. unfold dsumb.
  apply (for_inv (fun k st => snd st = true ->
    (forall j, (j < toN k)%nat -> fin (g (ix j))) /\
    dval (fst st) = sumR (fun j => dval (f (ix j) (g (ix j)))) (toN k))).
  - apply to_Z_0_le.
  - intros _. split; [intros j Hj; change (toN 0) with 0%nat in Hj; lia | apply dval_0].
  - intros k st Hk IH Hs. simpl in Hs. apply Bool.andb_true_iff in Hs. destruct Hs as [Hs Hg].
    destruct (IH Hs) as [IH1 IH2]. rewrite (toN_S k len) by lia. split.
    + intros j Hj. destruct (Nat.eq_dec j (toN k)) as [-> | Hne]; [rewrite ix_toN; exact Hg | apply IH1; lia].
    + simpl. rewrite dval_add, IH2, ix_toN. reflexivity.
Qed.

Lemma maxb_le : forall len h i, (i < toN len)%nat ->
  (dval (fst (h (ix i))) <= dval (fst (maxb len h)))%R.
Proof.
  intros len h. unfold maxb.
  apply (for_inv (fun k st => forall i, (i < toN k)%nat -> (dval (fst (h (ix i))) <= dval (fst st))%R)).
  - apply to_Z_0_le.
  - intros i Hi. change (toN 0) with 0%nat in Hi. lia.
  - intros k st Hk IH i Hi. rewrite (toN_S k len) in Hi by lia. simpl.
    destruct (Nat.eq_dec i (toN k)) as [-> | Hne].
    + rewrite ix_toN. apply dmax_r.
    + eapply Rle_trans; [apply IH; lia | apply dmax_l].
Qed.

Lemma maxb_ok : forall len h, snd (maxb len h) = true ->
  forall i, (i < toN len)%nat -> snd (h (ix i)) = true.
Proof.
  intros len h. unfold maxb.
  apply (for_inv (fun k st => snd st = true -> forall i, (i < toN k)%nat -> snd (h (ix i)) = true)).
  - apply to_Z_0_le.
  - intros _ i Hi. change (toN 0) with 0%nat in Hi. lia.
  - intros k st Hk IH Hs i Hi. simpl in Hs. apply Bool.andb_true_iff in Hs. destruct Hs as [Hs Hh].
    rewrite (toN_S k len) in Hi by lia.
    destruct (Nat.eq_dec i (toN k)) as [-> | Hne]; [rewrite ix_toN; exact Hh | apply IH; [exact Hs | lia]].
Qed.

Section Tables.
Variable n : int.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.

Lemma ix_lt : forall a, (a < toN n)%nat -> to_Z (ix a) = Z.of_nat a.
Proof.
  intros a Ha. unfold ix. rewrite of_Z_spec. apply Z.mod_small.
  unfold toN in Ha. change wB with 9223372036854775808%Z. lia.
Qed.

Lemma idx2 : forall a b, (a < toN n)%nat -> (b < toN n)%nat ->
  to_Z (ix a * n + ix b) = (Z.of_nat a * to_Z n + Z.of_nat b)%Z.
Proof.
  intros a b Ha Hb. pose proof (ix_lt a Ha) as Ea. pose proof (ix_lt b Hb) as Eb.
  assert (Ha' : (Z.of_nat a < to_Z n)%Z) by (unfold toN in Ha; lia).
  assert (Hb' : (Z.of_nat b < to_Z n)%Z) by (unfold toN in Hb; lia).
  rewrite Uint63.add_spec, Uint63.mul_spec, Ea, Eb.
  rewrite (Z.mod_small (Z.of_nat a * to_Z n)) by (change wB with 9223372036854775808%Z; nia).
  apply Z.mod_small. change wB with 9223372036854775808%Z. nia.
Qed.

Lemma idx2_lt : forall a b, (a < toN n)%nat -> (b < toN n)%nat ->
  (to_Z (ix a * n + ix b) < to_Z n * to_Z n)%Z.
Proof.
  intros a b Ha Hb. rewrite idx2 by assumption.
  assert (Ha' : (Z.of_nat a < to_Z n)%Z) by (unfold toN in Ha; lia).
  assert (Hb' : (Z.of_nat b < to_Z n)%Z) by (unfold toN in Hb; lia). nia.
Qed.

Lemma idx2_inj : forall a b c d, (a < toN n)%nat -> (b < toN n)%nat -> (c < toN n)%nat -> (d < toN n)%nat ->
  ix a * n + ix b = ix c * n + ix d -> a = c /\ b = d.
Proof.
  intros a b c d Ha Hb Hc Hd E. apply (f_equal to_Z) in E. rewrite !idx2 in E by assumption.
  apply (idx_inj a b c d (toN n)); [exact Hb | exact Hd |].
  apply Nat2Z.inj. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, toN_Z. lia.
Qed.

Lemma nn_spec : to_Z (n * n) = (to_Z n * to_Z n)%Z.
Proof. rewrite Uint63.mul_spec. apply Z.mod_small. change wB with 9223372036854775808%Z. nia. Qed.

Lemma flen_make_nn : forall (d : float), PArray.length (PArray.make (n * n) d) = n * n.
Proof.
  intros d. rewrite flength_make. replace (n * n <=? max_length) with true; [reflexivity |].
  symmetry. rewrite Uint63.leb_spec, nn_spec. change (to_Z max_length) with 4194303%Z. nia.
Qed.

Lemma n_le_max : (n <=? max_length) = true.
Proof. rewrite Uint63.leb_spec. change (to_Z max_length) with 4194303%Z. lia. Qed.

Lemma toN_lt : forall k : int, (to_Z k < to_Z n)%Z -> (toN k < toN n)%nat.
Proof. intros k Hk. unfold toN. pose proof (to_Z_bounded k). lia. Qed.

Lemma transpose_spec : forall xa a b, (a < toN n)%nat -> (b < toN n)%nat ->
  (transpose xa n).[ix b * n + ix a] = xa.[ix a].[ix b].
Proof.
  intros xa. unfold transpose.
  match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
    assert (H : PArray.length (loop hi cc ff lo ss) = n * n /\
       forall a b, (a < toN n)%nat -> (b < toN n)%nat -> (loop hi cc ff lo ss).[ix b * n + ix a] = xa.[ix a].[ix b]) end.
  2: { intros a b Ha Hb. apply H; assumption. }
  apply (for_inv (fun i T => PArray.length T = n * n /\
      forall a b, (a < toN i)%nat -> (b < toN n)%nat -> T.[ix b * n + ix a] = xa.[ix a].[ix b])).
  - apply to_Z_0_le.
  - split; [apply flen_make_nn | intros a b Ha; change (toN 0) with 0%nat in Ha; lia].
  - intros i T Hi [HL HT]. rewrite (toN_S i n) by lia.
    assert (Hi' : (toN i < toN n)%nat) by (apply toN_lt; lia).
    cbv zeta.
    match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
      assert (H : PArray.length (loop hi cc ff lo ss) = n * n /\
        forall a b, ((a < toN i)%nat \/ (a = toN i /\ (b < toN n)%nat)) -> (b < toN n)%nat ->
          (loop hi cc ff lo ss).[ix b * n + ix a] = xa.[ix a].[ix b]) end.
    2: { destruct H as [HL' HT']. split; [exact HL' |]. intros a b Ha Hb.
         apply HT'; [| exact Hb]. destruct (Nat.eq_dec a (toN i)) as [-> | Hne];
           [right; split; [reflexivity | exact Hb] | left; lia]. }
    apply (for_inv (fun j T' => PArray.length T' = n * n /\
      forall a b, ((a < toN i)%nat \/ (a = toN i /\ (b < toN j)%nat)) -> (b < toN n)%nat ->
        T'.[ix b * n + ix a] = xa.[ix a].[ix b])).
    + apply to_Z_0_le.
    + split; [exact HL |]. intros a b [Ha | [_ Hb']] Hb; [apply HT; assumption | change (toN 0) with 0%nat in Hb'; lia].
    + intros j T' Hj [HL' HT']. rewrite (toN_S j n) by lia.
      assert (Hj' : (toN j < toN n)%nat) by (apply toN_lt; lia).
      split; [rewrite flength_set; exact HL' |].
      intros a b Hab Hb.
      assert (Han : (a < toN n)%nat) by (destruct Hab as [| [-> _]]; lia).
      rewrite <- (ix_toN j), <- (ix_toN i).
      destruct (Nat.eq_dec a (toN i)) as [-> | Hai]; [destruct (Nat.eq_dec b (toN j)) as [-> | Hbj] |].
      * rewrite fget_set_same; [reflexivity |]. rewrite HL', Uint63.ltb_spec, nn_spec. apply idx2_lt; assumption.
      * rewrite fget_set_other; [apply HT'; [right; split; [reflexivity | lia] | exact Hb] |].
        intros E. apply idx2_inj in E; [lia | assumption ..].
      * rewrite fget_set_other; [apply HT'; [lia | exact Hb] |].
        intros E. apply idx2_inj in E; [| assumption ..]. destruct Hab as [Hab | [Hab _]]; lia.
Qed.

End Tables.

Lemma dget_set_same : forall (t : array dy) (i : int) (v : dy),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same dy t i v H). Qed.

Lemma dget_set_other : forall (t : array dy) (i j : int) (v : dy),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other dy t i j v H). Qed.

Lemma dlength_set : forall (t : array dy) (i : int) (v : dy),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set dy t i v). Qed.

Lemma dlength_make : forall (k : int) (v : dy),
  PArray.length (PArray.make k v) = if k <=? max_length then k else max_length.
Proof. intros k v. exact (length_make dy k v). Qed.

Lemma ix_inj : forall n a b, (to_Z n <= 100)%Z -> (a < toN n)%nat -> (b < toN n)%nat -> ix a = ix b -> a = b.
Proof.
  intros n a b Hn Ha Hb E. apply (f_equal to_Z) in E. unfold ix in E. rewrite !of_Z_spec, !Z.mod_small in E;
    [lia | unfold toN in *; change wB with 9223372036854775808%Z; lia ..].
Qed.

Lemma rowabs_spec : forall n xa k, (1 <= to_Z n <= 100)%Z -> (k < toN n)%nat ->
  dval (rowabs xa n).[ix k] = sumR (fun j => Rabs (fval xa.[ix k].[ix j])) (toN n).
Proof.
  intros n xa k Hn Hk. unfold rowabs.
  match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
    assert (H : PArray.length (loop hi cc ff lo ss) = n /\
      forall a, (a < toN n)%nat -> (loop hi cc ff lo ss).[ix a] = dsumf n (fun j => dabs (dec xa.[ix a].[j]))) end.
  { apply (for_inv (fun i S => PArray.length S = n /\
      forall a, (a < toN i)%nat -> S.[ix a] = dsumf n (fun j => dabs (dec xa.[ix a].[j])))).
    - apply to_Z_0_le.
    - split; [rewrite dlength_make, (n_le_max n Hn); reflexivity | intros a Ha; change (toN 0) with 0%nat in Ha; lia].
    - intros i S Hi [HL HS]. rewrite (toN_S i n) by lia. cbv zeta.
      split; [rewrite dlength_set; exact HL |]. intros a Ha.
      destruct (Nat.eq_dec a (toN i)) as [-> | Hne].
      + rewrite ix_toN. apply dget_set_same. rewrite HL, Uint63.ltb_spec. lia.
      + rewrite dget_set_other; [apply HS; lia |]. intros E. rewrite <- (ix_toN i) in E.
        assert (Hin : (toN i < toN n)%nat) by (apply toN_lt; lia).
        apply (ix_inj n) in E; lia. }
  destruct H as [_ H]. rewrite H by exact Hk. rewrite dsumf_spec. apply sumR_ext. intros j Hj.
  rewrite dval_abs, dval_dec. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The certificate, machine side                                      *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

Lemma pow_nu : powerRZ 2 (-53) = nu.
Proof.
  unfold nu, u. rewrite bpow_powerRZ. change (IZR radix2) with 2.
  replace (-53)%Z with (-52 + -1)%Z by reflexivity. rewrite powerRZ_add by lra.
  simpl (powerRZ 2 (-1)). field.
Qed.

Lemma pow_eta : powerRZ 2 (-1075) = eta_max.
Proof. unfold eta_max. rewrite bpow_powerRZ. reflexivity. Qed.

Lemma INR_toN : forall x : int, INR (toN x) = IZR (to_Z x).
Proof. intros x. rewrite INR_IZR_INZ, toN_Z. reflexivity. Qed.

Lemma dval_lam : forall n : int, dval ((3 * i2z n)%Z, (-53)%Z) = INR (toN n) * lamR.
Proof.
  intros n. unfold dval, lamR. cbn [fst snd]. rewrite i2z_spec, mult_IZR, pow_nu, INR_toN. ring.
Qed.

Lemma dval_mu1 : forall n : int, dval ((3 * i2z n)%Z, (-1075)%Z) = INR (toN n) * muR.
Proof.
  intros n. unfold dval, muR. cbn [fst snd]. rewrite i2z_spec, mult_IZR, pow_eta, INR_toN. ring.
Qed.

Lemma dval_mu2 : forall n : int, dval ((3 * i2z n * i2z n)%Z, (-1075)%Z) = INR (toN n) * (INR (toN n) * muR).
Proof.
  intros n. unfold dval, muR. cbn [fst snd]. rewrite i2z_spec, !mult_IZR, pow_eta, INR_toN. ring.
Qed.

Lemma sumR_const : forall c k, sumR (fun _ => c) k = INR k * c.
Proof. intros c k. induction k as [| k IH]; simpl sumR; [simpl; ring | rewrite IH, S_INR; ring]. Qed.

Lemma row_err : forall N (d P Ab dl : nat -> R) c1 c2,
  (forall j, (j < N)%nat -> Rabs (d j - P j) <= c1 * Ab j + c2) ->
  sumR (fun j => Rabs (dl j - P j)) N
    <= sumR (fun j => Rabs (dl j - d j)) N + c1 * sumR Ab N + INR N * c2.
Proof.
  intros N d P Ab dl c1 c2 H.
  rewrite <- sumR_scal, <- sumR_const, <- !sumR_plus. apply sumR_le. intros j Hj.
  pose proof (H j Hj). pose proof (Rabs_triang (dl j - d j) (d j - P j)).
  replace (dl j - d j + (d j - P j)) with (dl j - P j) in * by ring. lra.
Qed.

Lemma ix_eqb : forall n i j, (to_Z n <= 100)%Z -> (i < toN n)%nat -> (j < toN n)%nat ->
  (ix i =? ix j)%uint63 = Nat.eqb i j.
Proof.
  intros n i j Hn Hi Hj. destruct (Nat.eqb_spec i j) as [-> | Hne]; [apply Uint63.eqb_refl |].
  apply eqb_false_spec. intros E. apply Hne. apply (ix_inj n); assumption.
Qed.

Lemma add0_ix : forall k, (0 + ix k)%uint63 = ix k.
Proof. intros k. apply to_Z_inj. rewrite Uint63.add_spec. change (to_Z 0) with 0%Z. rewrite Z.add_0_l. apply Z.mod_small, to_Z_bounded. Qed.

Section CertMachine.
Variable n : int.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.
Variables (xa : array (array float)) (xb Q xt : array float).

Let N := toN n.
Definition Am (k j : nat) : R := fval xa.[ix k].[ix j].
Definition Rm (i k : nat) : R := fval Q.[(ix i * n)%uint63 + ix k].

Lemma HN100 : (to_Z n <= 1048576)%Z.
Proof. lia. Qed.

Lemma erow_spec : forall i, (i < N)%nat ->
  snd (erow n Q (transpose xa n) (rowabs xa n) ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n * i2z n)%Z, (-1075)%Z) (ix i)) = true ->
  sumR (fun j => Rabs (Emat N Am Rm i j)) N
    <= dval (fst (erow n Q (transpose xa n) (rowabs xa n) ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n * i2z n)%Z, (-1075)%Z) (ix i))).
Proof.
  intros i Hi Hok. unfold erow in *. cbv zeta in Hok |- *. cbn [fst snd] in Hok |- *.
  match type of Hok with snd (dsumb ?l ?g ?f) = true => destruct (dsumb_spec l g f Hok) as [Hfin Hval] end.
  rewrite !dval_add, dval_mul, Hval, dsumf_spec, dval_lam, dval_mu2.
  unfold Emat.
  assert (HT : forall k j, (k < N)%nat -> (j < N)%nat -> fval (transpose xa n).[ix j * n + ix k] = Am k j).
  { intros k j Hk Hj. rewrite transpose_spec by (try exact Hn; assumption). reflexivity. }
  eapply Rle_trans.
  - apply (row_err N (fun j => fval (fdot Q (ix i * n) (transpose xa n) (ix j * n) n))
              (fun j => sumR (fun k => Rm i k * Am k j) N)
              (fun j => sumR (fun k => Rabs (Rm i k * Am k j)) N) (delta i)
              (INR N * lamR) (INR N * muR)).
    intros j Hj. destruct (fdot_spec Q (ix i * n) (transpose xa n) (ix j * n) n HN100 (Hfin j Hj)) as [_ Hb].
    unfold prodsum, abssum in Hb.
    rewrite (sumR_ext (fun k => Rm i k * Am k j) (fun k => fval Q.[ix i * n + ix k] * fval (transpose xa n).[ix j * n + ix k]))
      by (intros k Hk; unfold Rm; rewrite HT by assumption; reflexivity).
    rewrite (sumR_ext (fun k => Rabs (Rm i k * Am k j)) (fun k => Rabs (fval Q.[ix i * n + ix k] * fval (transpose xa n).[ix j * n + ix k])))
      by (intros k Hk; unfold Rm; rewrite HT by assumption; reflexivity).
    exact Hb.
  - apply Rplus_le_compat; [apply Rplus_le_compat |].
    + apply Req_le. apply sumR_ext. intros j Hj. unfold dsub.
      rewrite dval_abs, dval_add, dval_neg, dval_int, dval_dec.
      rewrite (ix_eqb n i j) by (try lia; assumption). unfold delta.
      destruct (Nat.eqb i j); reflexivity.
    + rewrite !Rmult_assoc. apply Rmult_le_compat_l; [apply pos_INR |].
      apply Rmult_le_compat_l; [unfold lamR, nu; pose proof u_pos; lra |].
      apply Req_le. rewrite sumR_swap. apply sumR_ext. intros k Hk.
      rewrite dval_mul, dval_abs, dval_dec, rowabs_spec by (try exact Hn; assumption).
      rewrite <- sumR_scal. apply sumR_ext. intros j Hj. rewrite Rabs_mult. reflexivity.
    + apply Req_le. reflexivity.
Qed.

Lemma resid_spec : forall i, (i < N)%nat ->
  snd (resid n xa xb xt ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n)%Z, (-1075)%Z) (ix i)) = true ->
  (forall j, (j < N)%nat -> fin xt.[ix j]) /\
  Rabs (fval xb.[ix i] - sumR (fun j => Am i j * fval xt.[ix j]) N)
    <= dval (fst (resid n xa xb xt ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n)%Z, (-1075)%Z) (ix i))).
Proof.
  intros i Hi Hok. unfold resid in *. cbv zeta in Hok |- *. cbn [fst snd] in Hok |- *.
  destruct (fdot_spec xa.[ix i] 0 xt 0 n HN100 Hok) as [Hf Hb].
  unfold prodsum, abssum in Hb.
  rewrite (sumR_ext (fun j => fval xa.[ix i].[0 + ix j] * fval xt.[0 + ix j]) (fun j => Am i j * fval xt.[ix j])) in Hb
    by (intros j Hj; rewrite !add0_ix; reflexivity).
  rewrite (sumR_ext (fun j => Rabs (fval xa.[ix i].[0 + ix j] * fval xt.[0 + ix j])) (fun j => Rabs (Am i j * fval xt.[ix j]))) in Hb
    by (intros j Hj; rewrite !add0_ix; reflexivity).
  split; [intros j Hj; destruct (Hf j Hj) as [_ H]; rewrite add0_ix in H; exact H |].
  rewrite !dval_add, dval_mul, dval_lam, dval_mu1, dsumf_spec. unfold dsub.
  rewrite dval_abs, dval_add, dval_neg, !dval_dec.
  rewrite (sumR_ext (fun k => dval (dabs (dmul (dec xa.[ix i].[ix k]) (dec xt.[ix k])))) (fun j => Rabs (Am i j * fval xt.[ix j])))
    by (intros j Hj; rewrite dval_abs, dval_mul, !dval_dec; reflexivity).
  pose proof (Rabs_triang (fval xb.[ix i] - fval (fdot xa.[ix i] 0 xt 0 n))
                          (fval (fdot xa.[ix i] 0 xt 0 n) - sumR (fun j => Am i j * fval xt.[ix j]) N)) as T.
  replace (fval xb.[ix i] - fval (fdot xa.[ix i] 0 xt 0 n) + (fval (fdot xa.[ix i] 0 xt 0 n) - sumR (fun j => Am i j * fval xt.[ix j]) N))
    with (fval xb.[ix i] - sumR (fun j => Am i j * fval xt.[ix j]) N) in T by ring.
  unfold N, Rminus in *. lra.
Qed.

Lemma rowR_spec : forall i, dval (fst (rowR n Q (ix i))) = sumR (fun k => Rabs (Rm i k)) N.
Proof.
  intros i. unfold rowR. cbn [fst]. rewrite dsumf_spec. apply sumR_ext. intros k Hk.
  rewrite dval_abs, dval_dec. reflexivity.
Qed.

Lemma certify_spec : certify n xa xb (transpose xa n) Q xt = true ->
  exists eps rho sig : R, eps < 1 /\ 1000 * (rho * sig) + eps <= 1 /\
    (forall i, (i < N)%nat -> sumR (fun j => Rabs (Emat N Am Rm i j)) N <= eps) /\
    (forall i, (i < N)%nat -> sumR (fun k => Rabs (Rm i k)) N <= rho) /\
    (forall i, (i < N)%nat -> Rabs (fval xb.[ix i] - sumR (fun j => Am i j * fval xt.[ix j]) N) <= sig) /\
    PArray.length xt = n /\ (forall j, (j < N)%nat -> fin xt.[ix j]).
Proof.
  unfold certify. cbv zeta.
  destruct (maxb n (erow n Q (transpose xa n) (rowabs xa n) ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n * i2z n)%Z, (-1075)%Z)))
    as [eps ok1] eqn:E1.
  destruct (maxb n (rowR n Q)) as [rho ok3] eqn:E3.
  destruct (maxb n (resid n xa xb xt ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n)%Z, (-1075)%Z))) as [sig ok2] eqn:E2.
  intros H. rewrite !Bool.andb_true_iff in H. destruct H as [[[Ho1 Ho2] HL] [Hlt Hle]].
  apply dltb_spec in Hlt. apply dleb_spec in Hle. apply Uint63.eqb_correct in HL.
  rewrite dval_add, !dval_mul in Hle.
  assert (D1 : dval d1 = 1) by (unfold dval, d1; simpl; ring).
  assert (D2 : dval (1000%Z, 0%Z) = 1000) by (unfold dval; simpl; ring).
  rewrite D1 in Hlt, Hle. rewrite D2 in Hle.
  assert (HN0 : (0 < N)%nat) by (unfold N, toN; lia).
  exists (dval eps), (dval rho), (dval sig). split; [exact Hlt |]. split; [exact Hle |].
  split; [| split; [| split; [| split]]].
  - intros i Hi. eapply Rle_trans; [apply erow_spec; [exact Hi |] |].
    + pose proof (f_equal snd E1) as K0. cbn [snd] in K0. rewrite Ho1 in K0.
      exact (maxb_ok _ _ K0 i Hi).
    + pose proof (maxb_le n (erow n Q (transpose xa n) (rowabs xa n) ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n * i2z n)%Z, (-1075)%Z)) i Hi) as K.
      rewrite E1 in K. exact K.
  - intros i Hi. rewrite <- rowR_spec. pose proof (maxb_le n (rowR n Q) i Hi) as K. rewrite E3 in K. exact K.
  - intros i Hi. eapply Rle_trans; [apply resid_spec; [exact Hi |] |].
    + pose proof (f_equal snd E2) as K0. cbn [snd] in K0. rewrite Ho2 in K0.
      exact (maxb_ok _ _ K0 i Hi).
    + pose proof (maxb_le n (resid n xa xb xt ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n)%Z, (-1075)%Z)) i Hi) as K.
      rewrite E2 in K. exact K.
  - exact HL.
  - apply (resid_spec 0%nat HN0).
    pose proof (f_equal snd E2) as K0. cbn [snd] in K0. rewrite Ho2 in K0.
    exact (maxb_ok _ _ K0 0%nat HN0).
Qed.

(* v4 : the eps < 1 half alone *)
Lemma certify_inj_spec : certify_inj n xa (transpose xa n) Q = true ->
  exists eps : R, eps < 1 /\
    (forall i, (i < N)%nat -> sumR (fun j => Rabs (Emat N Am Rm i j)) N <= eps).
Proof.
  unfold certify_inj. cbv zeta.
  destruct (maxb n (erow n Q (transpose xa n) (rowabs xa n) ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n * i2z n)%Z, (-1075)%Z)))
    as [eps ok1] eqn:E1.
  intros H. apply Bool.andb_true_iff in H. destruct H as [Ho1 Hlt].
  apply dltb_spec in Hlt.
  assert (D1 : dval d1 = 1) by (unfold dval, d1; simpl; ring).
  rewrite D1 in Hlt.
  exists (dval eps). split; [exact Hlt |].
  intros i Hi. eapply Rle_trans; [apply erow_spec; [exact Hi |] |].
  - pose proof (f_equal snd E1) as K0. cbn [snd] in K0. rewrite Ho1 in K0.
    exact (maxb_ok _ _ K0 i Hi).
  - pose proof (maxb_le n (erow n Q (transpose xa n) (rowabs xa n) ((3 * i2z n)%Z, (-53)%Z) ((3 * i2z n * i2z n)%Z, (-1075)%Z)) i Hi) as K.
    rewrite E1 in K. exact K.
Qed.

End CertMachine.

(* ------------------------------------------------------------------ *)
(* The witness checks                                                 *)
(* ------------------------------------------------------------------ *)

Lemma zdot_spec : forall X o Y len,
  dval (zdot X o Y len) = sumR (fun k => fval X.[(o + ix k)%uint63] * IZR Y.[ix k]) (toN len).
Proof.
  intros X o Y len. unfold zdot. rewrite dsumf_spec. apply sumR_ext. intros k Hk.
  rewrite dval_mul, dval_dec, dval_int. reflexivity.
Qed.

Lemma chk_incons_spec : forall n xa xb y, (1 <= to_Z n <= 100)%Z ->
  chk_incons (transpose xa n) xb n y = true ->
  (forall j, (j < toN n)%nat -> sumR (fun i => Am xa i j * IZR y.[ix i]) (toN n) = 0) /\
  sumR (fun i => fval xb.[ix i] * IZR y.[ix i]) (toN n) <> 0.
Proof.
  intros n xa xb y Hn H. unfold chk_incons in H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  rewrite allf_spec in H1. split.
  - intros j Hj. specialize (H1 j Hj). apply dzero_spec in H1. rewrite zdot_spec in H1.
    rewrite <- H1. apply sumR_ext. intros i Hi. unfold Am. rewrite transpose_spec by assumption. reflexivity.
  - intros E. apply Bool.negb_true_iff in H2. apply Bool.not_true_iff_false in H2. apply H2.
    apply dzero_spec. rewrite zdot_spec. rewrite <- E. apply sumR_ext. intros i Hi. rewrite add0_ix. reflexivity.
Qed.

Lemma chk_mult_spec : forall n xa xb p q v,
  chk_mult xa xb n p q v = true ->
  q <> 0%Z /\ ~ (forall j, (j < toN n)%nat -> v.[ix j] = 0%Z) /\
  forall i, (i < toN n)%nat ->
    sumR (fun j => Am xa i j * IZR p.[ix j]) (toN n) = IZR q * fval xb.[ix i] /\
    sumR (fun j => Am xa i j * IZR v.[ix j]) (toN n) = 0.
Proof.
  intros n xa xb p q v H. unfold chk_mult in H. rewrite !Bool.andb_true_iff in H.
  destruct H as [[Hq Hv] H]. split; [| split].
  - apply Bool.negb_true_iff, Z.eqb_neq in Hq. exact Hq.
  - intros Hall. apply Bool.negb_true_iff in Hv. apply Bool.not_true_iff_false in Hv. apply Hv.
    apply allf_spec. intros k Hk. apply Z.eqb_eq, Hall, Hk.
  - rewrite allf_spec in H. intros i Hi. specialize (H i Hi). cbv zeta in H.
    apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    apply dzero_spec in H1, H2. unfold dsub in H1. rewrite dval_add, dval_neg, dval_mul, dval_int, dval_dec, zdot_spec in H1.
    rewrite zdot_spec in H2. split.
    + apply (Rplus_eq_reg_r (- (IZR q * fval xb.[ix i]))). rewrite Rplus_opp_r. rewrite <- H1.
      f_equal. apply sumR_ext. intros j Hj. rewrite add0_ix. reflexivity.
    + rewrite <- H2. apply sumR_ext. intros j Hj. rewrite add0_ix. reflexivity.
Qed.

(* y^T A = 0 and y^T b <> 0 : no solution *)
Lemma incons_math : forall N (A : nat -> nat -> R) (bv y x : nat -> R),
  (forall j, (j < N)%nat -> sumR (fun i => A i j * y i) N = 0) ->
  sumR (fun i => bv i * y i) N <> 0 ->
  ~ (forall i, (i < N)%nat -> sumR (fun j => A i j * x j) N = bv i).
Proof.
  intros N A bv y x Hy Hb Hx. apply Hb.
  rewrite (sumR_ext _ (fun i => sumR (fun j => A i j * x j * y i) N))
    by (intros i Hi; rewrite <- (Hx i Hi), sumR_scal_r; reflexivity).
  rewrite <- (sumR_swap (fun i j => A i j * x j * y i)).
  apply sumR_zero. intros j Hj.
  rewrite (sumR_ext _ (fun i => x j * (A i j * y i))) by (intros; ring).
  rewrite sumR_scal, Hy by exact Hj. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                       *)
(* ------------------------------------------------------------------ *)

Lemma sumR_sub : forall f g k, sumR (fun j => f j - g j) k = sumR f k - sumR g k.
Proof. intros f g k. induction k as [| k IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma abs_le_0 : forall e eps, eps < 1 -> Rabs e * (1 - eps) <= 0 -> e = 0.
Proof.
  intros e eps He H. pose proof (Rabs_pos e).
  assert (Rabs e <= 0).
  { destruct (Rle_lt_dec (Rabs e) 0) as [| Hlt]; [assumption | exfalso].
    assert (0 < Rabs e * (1 - eps)) by (apply Rmult_lt_0_compat; lra). lra. }
  unfold Rabs in *. destruct (Rcase_abs e); lra.
Qed.

Lemma abs_le_tol : forall e eps rho sig, eps < 1 -> 1000 * (rho * sig) + eps <= 1 ->
  Rabs e * (1 - eps) <= rho * sig -> Rabs e <= 1 / 1000.
Proof.
  intros e eps rho sig He Hc H.
  destruct (Rle_lt_dec (Rabs e) (1 / 1000)) as [| Hlt]; [assumption | exfalso].
  assert (1 / 1000 * (1 - eps) < Rabs e * (1 - eps)) by (apply Rmult_lt_compat_r; lra). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* v4 : the padded certificate, machine side                          *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.

(* the PArray lemmas on bool and int arrays, at this file's universe instances *)
Lemma blength_make : forall (k : int) (v : bool),
  PArray.length (PArray.make k v) = if k <=? max_length then k else max_length.
Proof. intros k v. exact (length_make bool k v). Qed.
Lemma blength_set : forall (t : array bool) (i : int) (v : bool),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set bool t i v). Qed.
Lemma bget_set_same : forall (t : array bool) (i : int) (v : bool),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same bool t i v H). Qed.
Lemma bget_set_other : forall (t : array bool) (i j : int) (v : bool),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other bool t i j v H). Qed.
Lemma bget_make : forall (k i : int) (v : bool), (PArray.make k v).[i] = v.
Proof. intros k i v. exact (get_make bool v k i). Qed.
Lemma ilength_make : forall (k : int) (v : int),
  PArray.length (PArray.make k v) = if k <=? max_length then k else max_length.
Proof. intros k v. exact (length_make int k v). Qed.
Lemma ilength_set : forall (t : array int) (i : int) (v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.
Lemma iget_set_same : forall (t : array int) (i : int) (v : int),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same int t i v H). Qed.
Lemma iget_set_other : forall (t : array int) (i j : int) (v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.
Lemma iget_make : forall (k i : int) (v : int), (PArray.make k v).[i] = v.
Proof. intros k i v. exact (get_make int v k i). Qed.

Lemma tab_spec : forall {T : Type} (n : int) (d : T) (f : int -> T), (1 <= to_Z n <= 100)%Z ->
  PArray.length (tab n d f) = n /\ forall k, (k < toN n)%nat -> (tab n d f).[ix k] = f (ix k).
Proof.
  intros T n d f Hn. unfold tab.
  apply (for_inv (fun i t => PArray.length t = n /\ forall k, (k < toN i)%nat -> t.[ix k] = f (ix k))).
  - apply to_Z_0_le.
  - split; [rewrite length_make, (n_le_max n Hn); reflexivity |].
    intros k Hk. change (toN 0) with 0%nat in Hk. lia.
  - intros i t Hi [HL HT]. rewrite (toN_S i n) by lia. split; [rewrite length_set; exact HL |].
    intros k Hk. destruct (Nat.eq_dec k (toN i)) as [-> | Hne].
    + rewrite ix_toN. apply get_set_same. rewrite HL, Uint63.ltb_spec. lia.
    + rewrite get_set_other; [apply HT; lia |]. intros E. rewrite <- (ix_toN i) in E.
      assert (Hin : (toN i < toN n)%nat) by (unfold toN; pose proof (to_Z_bounded i); lia).
      pose proof (ix_inj n (toN i) k ltac:(lia) Hin ltac:(lia) E). lia.
Qed.

(* the float instance, for right-hand sides built in the proof only *)
Definition ftab (n : int) (d : float) (f : int -> float) : array float :=
  loop n (fun _ _ => true) (fun i t => t.[i <- f i]) 0 (PArray.make n d).

Lemma ftab_spec : forall (n : int) (d : float) (f : int -> float), (1 <= to_Z n <= 100)%Z ->
  forall k, (k < toN n)%nat -> (ftab n d f).[ix k] = f (ix k).
Proof.
  intros n d f Hn. unfold ftab.
  match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
    assert (H : PArray.length (loop hi cc ff lo ss) = n /\
      forall k, (k < toN n)%nat -> (loop hi cc ff lo ss).[ix k] = f (ix k)) end.
  2: exact (proj2 H).
  apply (for_inv (fun i t => PArray.length t = n /\ forall k, (k < toN i)%nat -> t.[ix k] = f (ix k))).
  - apply to_Z_0_le.
  - split; [rewrite flength_make, (n_le_max n Hn); reflexivity |].
    intros k Hk. change (toN 0) with 0%nat in Hk. lia.
  - intros i t Hi [HL HT]. rewrite (toN_S i n) by lia. split; [rewrite flength_set; exact HL |].
    intros k Hk. destruct (Nat.eq_dec k (toN i)) as [-> | Hne].
    + rewrite ix_toN. apply fget_set_same. rewrite HL, Uint63.ltb_spec. lia.
    + rewrite fget_set_other; [apply HT; lia |]. intros E. rewrite <- (ix_toN i) in E.
      assert (Hin : (toN i < toN n)%nat) by (unfold toN; pose proof (to_Z_bounded i); lia).
      pose proof (ix_inj n (toN i) k ltac:(lia) Hin ltac:(lia) E). lia.
Qed.

Lemma padB_spec : forall xa n Df tix fc Cf, (1 <= to_Z n <= 100)%Z ->
  forall i j, (i < toN n)%nat -> (j < toN n)%nat ->
  (padB xa n Df tix fc Cf).[ix i].[ix j] = bentry xa Df tix fc Cf (ix i) (ix j).
Proof.
  intros xa n Df tix fc Cf Hn i j Hi Hj. unfold padB.
  rewrite (proj2 (tab_spec n _ _ Hn) i Hi). cbv beta.
  exact (proj2 (tab_spec n zero (fun j0 => bentry xa Df tix fc Cf (ix i) j0) Hn) j Hj).
Qed.

Lemma mark_D_spec : forall perm n r k, (1 <= to_Z n <= 100)%Z ->
  forall i, (i < toN n)%nat -> (fst (mark_D perm n r k)).[ix i] = true ->
  (to_Z (snd (mark_D perm n r k)).[ix i] < to_Z k)%Z /\ perm.[r + (snd (mark_D perm n r k)).[ix i]] = ix i.
Proof.
  intros perm n r k Hn. unfold mark_D.
  match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
    assert (H : PArray.length (fst (loop hi cc ff lo ss)) = n /\ PArray.length (snd (loop hi cc ff lo ss)) = n /\
      forall i, (i < toN n)%nat -> (fst (loop hi cc ff lo ss)).[ix i] = true ->
        (to_Z (snd (loop hi cc ff lo ss)).[ix i] < to_Z k)%Z /\ perm.[r + (snd (loop hi cc ff lo ss)).[ix i]] = ix i) end.
  2: { destruct H as (_ & _ & H). exact H. }
  apply (for_inv (fun t st => PArray.length (fst st) = n /\ PArray.length (snd st) = n /\
      forall i, (i < toN n)%nat -> (fst st).[ix i] = true ->
        (to_Z (snd st).[ix i] < to_Z t)%Z /\ perm.[r + (snd st).[ix i]] = ix i)).
  - apply to_Z_0_le.
  - cbn [fst snd]. rewrite blength_make, ilength_make, (n_le_max n Hn). split; [reflexivity | split; [reflexivity |]].
    intros i Hi. rewrite bget_make. discriminate.
  - intros t st Ht (HL1 & HL2 & HI). cbv beta zeta. cbn [fst snd]. rewrite blength_set, ilength_set.
    split; [exact HL1 | split; [exact HL2 |]].
    intros i Hi. assert (Ht1 : to_Z (t + 1) = (to_Z t + 1)%Z) by sia.
    assert (Hix : (ix i <? n) = true) by (rewrite Uint63.ltb_spec, (ix_lt n Hn i Hi); unfold toN in Hi; lia).
    destruct (Uint63.eqb perm.[r + t] (ix i)) eqn:E.
    + apply Uint63.eqb_correct in E. rewrite E. rewrite bget_set_same by (rewrite HL1; exact Hix).
      rewrite iget_set_same by (rewrite HL2; exact Hix). intros _. split; [lia | exact E].
    + apply eqb_false_spec in E. rewrite bget_set_other, iget_set_other by exact E.
      intros H. destruct (HI i Hi H) as [H1 H2]. split; [lia | exact H2].
Qed.

Lemma mark_C_spec : forall fc n k, (1 <= to_Z n <= 100)%Z ->
  forall t, (to_Z t < to_Z k)%Z -> (fc.[t] <? n) = true -> (mark_C fc n k).[fc.[t]] = true.
Proof.
  intros fc n k Hn. unfold mark_C.
  match goal with |- context [loop ?hi ?cc ?ff ?lo ?ss] =>
    assert (H : PArray.length (loop hi cc ff lo ss) = n /\
      forall t, (to_Z t < to_Z k)%Z -> (fc.[t] <? n) = true -> (loop hi cc ff lo ss).[fc.[t]] = true) end.
  2: exact (proj2 H).
  apply (for_inv (fun t0 C => PArray.length C = n /\
      forall t, (to_Z t < to_Z t0)%Z -> (fc.[t] <? n) = true -> C.[fc.[t]] = true)).
  - apply to_Z_0_le.
  - rewrite blength_make, (n_le_max n Hn). split; [reflexivity |].
    intros t Ht. change (to_Z 0) with 0%Z in Ht. pose proof (to_Z_bounded t). lia.
  - intros t0 C Ht0 [HL HC]. rewrite blength_set. split; [exact HL |]. intros t Ht Hf.
    assert (Ht1 : to_Z (t0 + 1) = (to_Z t0 + 1)%Z) by sia.
    destruct (Uint63.eqb fc.[t0] fc.[t]) eqn:E.
    + apply Uint63.eqb_correct in E. rewrite <- E. apply bget_set_same. rewrite HL, E. exact Hf.
    + apply eqb_false_spec in E. rewrite bget_set_other by exact E. apply HC; [| exact Hf].
      destruct (Z.eq_dec (to_Z t) (to_Z t0)) as [Et | Et]; [apply to_Z_inj in Et; subst; congruence | lia].
Qed.

Lemma chk_red_spec : forall n xa xb y d Df, (1 <= to_Z n <= 100)%Z ->
  chk_red (transpose xa n) xb n y d Df = true ->
  (forall j, (j < toN n)%nat -> sumR (fun i => Am xa i j * IZR y.[ix i])%R (toN n) = 0%R) /\
  sumR (fun i => fval xb.[ix i] * IZR y.[ix i])%R (toN n) = 0%R /\ y.[d] <> 0%Z /\
  (forall i, (i < toN n)%nat -> Df.[ix i] = true -> ix i <> d -> y.[ix i] = 0%Z).
Proof.
  intros n xa xb y d Df Hn H. unfold chk_red in H. rewrite !Bool.andb_true_iff in H.
  destruct H as [[H1 H2] [H3 H4]]. rewrite allf_spec in H1, H4. split; [| split; [| split]].
  - intros j Hj. specialize (H1 j Hj). apply dzero_spec in H1. rewrite zdot_spec in H1.
    rewrite <- H1. apply sumR_ext. intros i Hi. unfold Am. rewrite transpose_spec by assumption. reflexivity.
  - apply dzero_spec in H2. rewrite zdot_spec in H2. rewrite <- H2. apply sumR_ext. intros i Hi.
    rewrite add0_ix. reflexivity.
  - apply Bool.negb_true_iff, Z.eqb_neq in H3. exact H3.
  - intros i Hi HD Hne. specialize (H4 i Hi). rewrite HD in H4. cbn [negb orb] in H4.
    apply Bool.orb_true_iff in H4. destruct H4 as [E | E].
    + apply Uint63.eqb_correct in E. contradiction.
    + apply Z.eqb_eq in E. exact E.
Qed.

Lemma scan_null_spec : forall AT xb Q perm fc Df n r k,
  (fst (scan_null AT xb Q perm fc Df n r k) = true -> exists t, chk_incons AT xb n (yv Q n r t) = true) /\
  (snd (scan_null AT xb Q perm fc Df n r k) = true -> (r <? n) = true /\
     forall t, (to_Z t < to_Z k)%Z -> (perm.[r + t] <? n) = true /\ (fc.[t] <? n) = true /\
       chk_red AT xb n (yv Q n r t) perm.[r + t] Df = true).
Proof.
  intros AT xb Q perm fc Df n r k. unfold scan_null.
  apply (for_inv (fun t0 s => (fst s = true -> exists t, chk_incons AT xb n (yv Q n r t) = true) /\
     (snd s = true -> (r <? n) = true /\
        forall t, (to_Z t < to_Z t0)%Z -> (perm.[r + t] <? n) = true /\ (fc.[t] <? n) = true /\
          chk_red AT xb n (yv Q n r t) perm.[r + t] Df = true))).
  - apply to_Z_0_le.
  - cbn [fst snd]. split; [discriminate |]. intros H. split; [exact H |].
    intros t Ht. change (to_Z 0) with 0%Z in Ht. pose proof (to_Z_bounded t). lia.
  - intros t0 s Ht0 [IH1 IH2]. cbv beta zeta. cbn [fst snd]. split.
    + intros H. apply Bool.orb_true_iff in H. destruct H as [H | H]; [exact (IH1 H) | exists t0; exact H].
    + intros H. rewrite !Bool.andb_true_iff in H. destruct H as [Hs [[Hd Hc] Hr]].
      destruct (IH2 Hs) as [Hrn IH]. split; [exact Hrn |]. intros t Ht.
      assert (Ht1 : to_Z (t0 + 1) = (to_Z t0 + 1)%Z) by sia.
      destruct (Z.eq_dec (to_Z t) (to_Z t0)) as [Et | Et].
      * apply to_Z_inj in Et. subst t. auto.
      * apply IH. lia.
Qed.

(* an injective square float matrix is surjective onto float right-hand
   sides : exact_exists for any pair of arrays (scale_spec + dec_val in
   place of fval_dec) *)
Lemma exact_exists_arr : forall (xn : int) (xa : array (array float)) (xb : array float),
  (1 <= to_Z xn <= 100)%Z ->
  (forall d : nat -> R, (forall i, (i < toN xn)%nat -> sumR (fun j => Am xa i j * d j)%R (toN xn) = 0%R) ->
     forall j, (j < toN xn)%nat -> d j = 0%R) ->
  exists x : nat -> R, forall i, (i < toN xn)%nat ->
    sumR (fun j => Am xa i j * x j)%R (toN xn) = fval xb.[ix i].
Proof.
  intros xn xa xb Hn Hinj.
  pose proof (toNn xn Hn) as HnN.
  destruct (build_spec xn Hn xa xb) as [HL0 HV0].
  set (T0 := build xa xb xn (xn + 1)) in *.
  set (E := fun i : nat => row_exp xn xa.[of_Z (Z.of_nat i)] xb.[of_Z (Z.of_nat i)]).
  assert (HA : forall i j, (i < toN xn)%nat -> (j < toN xn)%nat ->
    Am xa i j = (IZR (V xn T0 i j) * powerRZ 2 (E i))%R).
  { intros i j Hi Hj. rewrite HV0 by lia.
    replace (Nat.ltb j (toN xn)) with true by (symmetry; apply Nat.ltb_lt; exact Hj).
    unfold E. rewrite scale_spec; [unfold Am, ix; symmetry; apply dec_val |].
    apply (row_exp_spec xn Hn). rewrite of_Z_spec, Z.mod_small; [nlia | change wB with 9223372036854775808%Z; lia]. }
  assert (HB : forall i, (i < toN xn)%nat -> fval xb.[ix i] = (IZR (V xn T0 i (toN xn)) * powerRZ 2 (E i))%R).
  { intros i Hi. rewrite HV0 by lia. rewrite Nat.ltb_irrefl.
    unfold E. rewrite scale_spec; [unfold ix; symmetry; apply dec_val |]. apply (row_exp_spec xn Hn). }
  assert (Hrs : forall i x, (i < toN xn)%nat ->
    sumR (fun j => Am xa i j * x j)%R (toN xn) = (rowsum (toN xn) (V xn T0) i x * powerRZ 2 (E i))%R).
  { intros i x Hi. unfold rowsum. rewrite <- sumR_scal_r. apply sumR_ext. intros j Hj.
    rewrite HA by assumption. ring. }
  destruct (eliminate_spec xn Hn T0 HL0) as (HL & Hr & HI).
  destruct (Nat.lt_ge_cases (toN (snd (eliminate xn (xn + 1) T0))) (toN xn)) as [Hlt | Hge].
  - destruct (fin_kernel (toN xn) _ _ _ HI Hlt) as (d & Hd & f & Hf & Hdf).
    exfalso. apply Hdf. apply Hinj; [| exact Hf].
    intros i Hi. rewrite Hrs by exact Hi. rewrite (Hd i Hi). ring.
  - assert (Er : toN (snd (eliminate xn (xn + 1) T0)) = toN xn) by nlia. rewrite Er in HI.
    destruct (fin_unique (toN xn) _ _ HI) as (_ & Hsol & _).
    eexists. intros i Hi. rewrite Hrs by exact Hi. rewrite (Hsol i Hi). rewrite HB by exact Hi. reflexivity.
Qed.

Open Scope R_scope.

(* eps < 1 makes the matrix injective : cert_bound with sigma = 0 *)
Lemma inj_of_cert : forall n xa Q, (1 <= to_Z n <= 100)%Z ->
  certify_inj n xa (transpose xa n) Q = true ->
  forall d : nat -> R, (forall i, (i < toN n)%nat -> sumR (fun j => Am xa i j * d j) (toN n) = 0) ->
  forall j, (j < toN n)%nat -> d j = 0.
Proof.
  intros n xa Q Hn Hc d Hd j Hj.
  destruct (certify_inj_spec n Hn xa Q Hc) as (eps & Heps & HE).
  assert (HN0 : (0 < toN n)%nat) by (unfold toN; lia).
  destruct (max_idx (fun i => sumR (fun k => Rabs (Rm n Q i k)) (toN n)) (toN n) HN0) as (i0 & _ & Hm).
  apply (abs_le_0 _ eps Heps).
  replace 0 with (sumR (fun k => Rabs (Rm n Q i0 k)) (toN n) * 0) by ring.
  apply (cert_bound (toN n) (Am xa) (Rm n Q) eps _ 0 d HE Hm); [| exact Hj].
  intros i Hi. unfold matvec. rewrite Hd by exact Hi. rewrite Rabs_R0. lra.
Qed.

(* the reduced left-null vectors carry the rows of D : if every row
   outside D holds, every row holds *)
Lemma lnull_extend : forall N (A : nat -> nat -> R) (bv x : nat -> R) (Dm : nat -> bool) (Y : nat -> nat -> R),
  (forall d, (d < N)%nat -> Dm d = true ->
     (forall j, (j < N)%nat -> sumR (fun i => A i j * Y d i) N = 0) /\ Y d d <> 0 /\
     (forall i, (i < N)%nat -> Dm i = true -> i <> d -> Y d i = 0)) ->
  (forall d, (d < N)%nat -> Dm d = true -> sumR (fun i => bv i * Y d i) N = 0) ->
  (forall i, (i < N)%nat -> Dm i = false -> sumR (fun j => A i j * x j) N = bv i) ->
  forall i, (i < N)%nat -> sumR (fun j => A i j * x j) N = bv i.
Proof.
  intros N A bv x Dm Y Hy Hb Hx d Hd.
  destruct (Dm d) eqn:ED; [| exact (Hx d Hd ED)].
  destruct (Hy d Hd ED) as (HyA & Hyd & Hy0).
  set (f := fun i => Y d i * (sumR (fun j => A i j * x j) N - bv i)).
  assert (S0 : sumR f N = 0).
  { unfold f. rewrite (sumR_ext _ (fun i => sumR (fun j => A i j * x j * Y d i) N - bv i * Y d i))
      by (intros i Hi; rewrite sumR_scal_r; ring).
    rewrite sumR_sub, (Hb d Hd ED).
    rewrite <- (sumR_swap (fun i j => A i j * x j * Y d i)).
    rewrite sumR_zero; [ring |]. intros j Hj.
    rewrite (sumR_ext _ (fun i => x j * (A i j * Y d i))) by (intros; ring).
    rewrite sumR_scal, HyA by exact Hj. ring. }
  assert (S1 : sumR f N = f d).
  { rewrite (sumR_ext f (fun i => if Nat.eqb i d then f d else 0)); [apply sumR_delta; exact Hd |].
    intros i Hi. destruct (Nat.eqb_spec i d) as [-> | Hne]; [reflexivity |].
    unfold f. destruct (Dm i) eqn:Ei.
    - rewrite (Hy0 i Hi Ei Hne). ring.
    - rewrite (Hx i Hi Ei). ring. }
  rewrite S1 in S0. unfold f in S0. apply Rmult_integral in S0.
  destruct S0 as [H | H]; [contradiction | lra].
Qed.

(* the padded matrix B, injective and surjective, gives a solution x of
   A x = b and a kernel vector v of A with v_c0 <> 0 *)
Lemma padded_math : forall N (A Bm : nat -> nat -> R) (bv : nat -> R) (Dm Cm : nat -> bool) (cm : nat -> nat)
    (Y : nat -> nat -> R) (c0 : nat),
  (forall i j, (i < N)%nat -> (j < N)%nat ->
     Bm i j = if Dm i then (if Nat.eqb j (cm i) then 1 else 0) else (if Cm j then 0 else A i j)) ->
  (forall i, (i < N)%nat -> Dm i = true -> (cm i < N)%nat /\ Cm (cm i) = true) ->
  (c0 < N)%nat -> Cm c0 = true ->
  (forall d : nat -> R, (forall i, (i < N)%nat -> sumR (fun j => Bm i j * d j) N = 0) ->
     forall j, (j < N)%nat -> d j = 0) ->
  (exists x, forall i, (i < N)%nat -> sumR (fun j => Bm i j * x j) N = if Dm i then 0 else bv i) ->
  (exists v, forall i, (i < N)%nat -> sumR (fun j => Bm i j * v j) N =
     if Dm i then (if Nat.eqb (cm i) c0 then 1 else 0) else - A i c0) ->
  (forall d, (d < N)%nat -> Dm d = true ->
     (forall j, (j < N)%nat -> sumR (fun i => A i j * Y d i) N = 0) /\ Y d d <> 0 /\
     (forall i, (i < N)%nat -> Dm i = true -> i <> d -> Y d i = 0)) ->
  (forall d, (d < N)%nat -> Dm d = true -> sumR (fun i => bv i * Y d i) N = 0) ->
  exists x v, (forall i, (i < N)%nat -> sumR (fun j => A i j * x j) N = bv i) /\
              (forall i, (i < N)%nat -> sumR (fun j => A i j * v j) N = 0) /\ v c0 <> 0.
Proof.
  intros N A Bm bv Dm Cm cm Y c0 HB HDC Hc0 Hc0C Inj [x Hx] [v Hv] Hy Hb.
  assert (HrowD : forall i z, (i < N)%nat -> Dm i = true -> sumR (fun j => Bm i j * z j) N = z (cm i)).
  { intros i z Hi HDi. destruct (HDC i Hi HDi) as [Hci _].
    rewrite (sumR_ext _ (fun j => if Nat.eqb j (cm i) then z (cm i) else 0));
      [apply sumR_delta; exact Hci |].
    intros j Hj. rewrite HB by assumption. rewrite HDi.
    destruct (Nat.eqb_spec j (cm i)) as [-> | _]; ring. }
  assert (HrowN : forall i z z', (i < N)%nat -> Dm i = false ->
     (forall j, (j < N)%nat -> Cm j = false -> z j = z' j) ->
     sumR (fun j => Bm i j * z j) N = sumR (fun j => Bm i j * z' j) N).
  { intros i z z' Hi HDi Hz. apply sumR_ext. intros j Hj. rewrite HB by assumption. rewrite HDi.
    destruct (Cm j) eqn:ECj; [ring | rewrite (Hz j Hj ECj); reflexivity]. }
  (* x vanishes on C *)
  set (xh := fun j => if Cm j then 0 else x j).
  assert (Exh : forall j, (j < N)%nat -> x j = xh j).
  { intros j Hj. assert (D0 : x j - xh j = 0); [| lra].
    apply (Inj (fun j => x j - xh j)); [| exact Hj].
    intros i Hi. rewrite (sumR_ext _ (fun j => Bm i j * x j - Bm i j * xh j)) by (intros; ring).
    rewrite sumR_sub. destruct (Dm i) eqn:HDi.
    - pose proof (Hx i Hi) as Hxi. rewrite HDi, (HrowD i x Hi HDi) in Hxi.
      rewrite (HrowD i x Hi HDi), (HrowD i xh Hi HDi). unfold xh.
      destruct (HDC i Hi HDi) as [_ ->]. rewrite Hxi. ring.
    - rewrite (HrowN i x xh Hi HDi); [ring |]. intros j' Hj' ECj. unfold xh. rewrite ECj. reflexivity. }
  assert (HxC : forall j, (j < N)%nat -> Cm j = true -> x j = 0).
  { intros j Hj ECj. rewrite (Exh j Hj). unfold xh. rewrite ECj. reflexivity. }
  assert (HAx : forall i, (i < N)%nat -> sumR (fun j => A i j * x j) N = bv i).
  { apply (lnull_extend N A bv x Dm Y Hy Hb).
    intros i Hi HDi. pose proof (Hx i Hi) as Hxi. rewrite HDi in Hxi. rewrite <- Hxi.
    apply sumR_ext. intros j Hj. rewrite HB by assumption. rewrite HDi.
    destruct (Cm j) eqn:ECj; [rewrite (HxC j Hj ECj); ring | reflexivity]. }
  (* v is the unit vector of c0 on C *)
  set (vh := fun j => if Cm j then (if Nat.eqb j c0 then 1 else 0) else v j).
  assert (Evh : forall j, (j < N)%nat -> v j = vh j).
  { intros j Hj. assert (D0 : v j - vh j = 0); [| lra].
    apply (Inj (fun j => v j - vh j)); [| exact Hj].
    intros i Hi. rewrite (sumR_ext _ (fun j => Bm i j * v j - Bm i j * vh j)) by (intros; ring).
    rewrite sumR_sub. destruct (Dm i) eqn:HDi.
    - pose proof (Hv i Hi) as Hvi. rewrite HDi, (HrowD i v Hi HDi) in Hvi.
      rewrite (HrowD i v Hi HDi), (HrowD i vh Hi HDi). unfold vh.
      destruct (HDC i Hi HDi) as [_ ->]. rewrite Hvi. ring.
    - rewrite (HrowN i v vh Hi HDi); [ring |]. intros j' Hj' ECj. unfold vh. rewrite ECj. reflexivity. }
  assert (HvC : forall j, (j < N)%nat -> Cm j = true -> v j = if Nat.eqb j c0 then 1 else 0).
  { intros j Hj ECj. rewrite (Evh j Hj). unfold vh. rewrite ECj. reflexivity. }
  assert (HAv : forall i, (i < N)%nat -> sumR (fun j => A i j * v j) N = 0).
  { apply (lnull_extend N A (fun _ => 0) v Dm Y Hy).
    - intros d Hd HDd. apply sumR_zero. intros; ring.
    - intros i Hi HDi. pose proof (Hv i Hi) as Hvi. rewrite HDi in Hvi.
      rewrite (sumR_ext _ (fun j => Bm i j * v j + (if Nat.eqb j c0 then A i c0 else 0))).
      + rewrite sumR_plus, Hvi, sumR_delta by exact Hc0. ring.
      + intros j Hj. rewrite HB by assumption. rewrite HDi. destruct (Cm j) eqn:ECj.
        * rewrite (HvC j Hj ECj). destruct (Nat.eqb_spec j c0) as [-> | _]; ring.
        * destruct (Nat.eqb_spec j c0) as [-> | _]; [congruence | ring]. }
  exists x, v. split; [exact HAx | split; [exact HAv |]].
  rewrite (HvC c0 Hc0 Hc0C), Nat.eqb_refl. lra.
Qed.

Theorem solve_correct_main :
  forall (n : N) (a : list (list R)) (b : list R)
         (xn : uint) (xa : array (array float)) (xb : array float),
  valid_input n a b -> repr xn n -> repr xa a -> repr xb b ->
  exists o : outcome (list R), repr (solve xn xa xb) o /\ solve_spec n a b o.
Proof.
  intros n a b xn xa xb Hvi Hxn Ha Hb.
  pose proof Hvi as [Hvn Hrows Hrow Hvb].
  pose proof Hxn as Hxn'. unfold repr, repr_uint in Hxn'.
  assert (Hn : (1 <= to_Z xn <= 100)%Z) by lia.
  pose proof (toNn xn Hn) as HnN.
  set (N0 := toN xn) in *.
  assert (Hlen : forall {X} (l : list X), len l = n -> List.length l = N0).
  { intros X l Hl. unfold len in Hl. unfold N0, toN. lia. }
  assert (La : List.length a = N0) by (apply Hlen; exact Hrows).
  assert (Lb : List.length b = N0) by (apply Hlen; exact Hvb).
  assert (Lrow : forall i, (i < N0)%nat -> List.length (nth i a []) = N0).
  { intros i Hi. apply Hlen. rewrite Forall_nth in Hrow. apply Hrow. lia. }
  assert (HAm : forall i j, (i < N0)%nat -> (j < N0)%nat -> Am xa i j = nth j (nth i a []) 0).
  { intros i j Hi Hj. unfold Am.
    assert (Hr : repr (xa.[ix i]).[ix j] (nth j (nth i a []) 0%R)).
    { apply repr_nth_float; [apply repr_nth_row; [exact Ha | lia] | rewrite Lrow; assumption]. }
    destruct Hr as [_ Hr]. exact Hr. }
  assert (HBm : forall i, (i < N0)%nat -> fval xb.[ix i] = nth i b 0).
  { intros i Hi. assert (Hr : repr xb.[ix i] (nth i b 0%R)) by (apply repr_nth_float; [exact Hb | lia]).
    destruct Hr as [_ Hr]. exact Hr. }
  assert (Bridge : forall xs, solves n a b xs <-> List.length xs = N0 /\
            forall i, (i < N0)%nat -> sumR (fun j => Am xa i j * nth j xs 0) N0 = fval xb.[ix i]).
  { intros xs. unfold solves. split.
    - intros [Hl HF]. assert (Hl' : List.length xs = N0) by (apply Hlen; exact Hl). split; [exact Hl' |].
      rewrite (Forall2_iff _ a b [] 0%R) in HF by lia.
      intros i Hi. specialize (HF i ltac:(lia)).
      rewrite dot_sumR in HF by (rewrite Lrow, Hl'; lia). rewrite Lrow in HF by exact Hi.
      rewrite HBm by exact Hi. rewrite <- HF. apply sumR_ext. intros j Hj. rewrite HAm by assumption. reflexivity.
    - intros [Hl Hs]. split; [unfold len; rewrite Hl; unfold N0, toN; lia |].
      rewrite (Forall2_iff _ a b [] 0%R) by lia. intros i Hi. rewrite La in Hi.
      rewrite dot_sumR by (rewrite Lrow, Hl; lia). rewrite Lrow by exact Hi.
      rewrite <- HBm by exact Hi. rewrite <- (Hs i Hi). apply sumR_ext. intros j Hj. rewrite HAm by assumption. reflexivity. }
  assert (Lmap : forall f : nat -> R, List.length (map f (seq 0 N0)) = N0)
    by (intros f; rewrite length_map, length_seq; reflexivity).
  assert (Nmap : forall (f : nat -> R) j, (j < N0)%nat -> nth j (map f (seq 0 N0)) 0 = f j)
    by (intros f j Hj; apply nth_map_seq; exact Hj).
  unfold solve. cbv zeta.
  destruct (fs_r (forward xn (xn + 1) (col_thr xa xn) (init_M xa xb xn (xn + 1)) (init_Q xn)) =? xn).
  - destruct (backsub xn (xn + 1) _ _) as [M Q].
    destruct (certify xn xa xb (transpose xa xn) Q (get_col M xn (xn + 1) xn)) eqn:Ec;
      [| exact (solve_exact_correct n a b xn xa xb Hvi Hxn Ha Hb)].
    set (xt := get_col M xn (xn + 1) xn) in *.
    destruct (certify_spec xn Hn xa xb Q xt Ec)
      as (eps & rho & sig & Heps & Hc & HE & HR & HS & HL & Hfin).
    fold N0 in HE, HR, HS, Hfin.
    assert (Inj : forall d : nat -> R, (forall i, (i < N0)%nat -> sumR (fun j => Am xa i j * d j) N0 = 0) ->
                  forall j, (j < N0)%nat -> d j = 0).
    { intros d Hd j Hj. apply (abs_le_0 _ eps Heps).
      replace 0 with (rho * 0) by ring.
      apply (cert_bound N0 (Am xa) (Rm xn Q) eps rho 0 d HE HR); [| exact Hj].
      intros i Hi. unfold matvec. rewrite Hd by exact Hi. rewrite Rabs_R0. lra. }
    destruct (exact_exists n a b xn xa xb Hvi Hxn Ha Hb) as [x Hx].
    { intros d Hd. apply Inj. intros i Hi. rewrite <- (Hd i Hi). apply sumR_ext. intros j Hj.
      rewrite HAm by assumption. reflexivity. }
    assert (Hx' : forall i, (i < N0)%nat -> sumR (fun j => Am xa i j * x j) N0 = fval xb.[ix i]).
    { intros i Hi. rewrite HBm by exact Hi. rewrite <- (Hx i Hi). apply sumR_ext. intros j Hj.
      rewrite HAm by assumption. reflexivity. }
    exists (Unique (map (fun j => fval xt.[ix j]) (seq 0 N0))). split.
    + split.
      * rewrite Lmap. unfold N0. rewrite toN_Z. exact (f_equal to_Z (eq_sym HL)).
      * intros k Hk. rewrite Lmap in Hk. exists (fval xt.[ix k]). split.
        -- rewrite (nth_error_nth' _ 0%R) by (rewrite Lmap; exact Hk). rewrite Nmap by exact Hk. reflexivity.
        -- exact (fval_repr _ (Hfin k Hk)).
    + exists (map x (seq 0 N0)). split; [| split].
      * apply Bridge. split; [apply Lmap |]. intros i Hi.
        rewrite (sumR_ext _ (fun j => Am xa i j * x j)) by (intros j Hj; rewrite Nmap by exact Hj; reflexivity).
        exact (Hx' i Hi).
      * intros ys Hys. apply Bridge in Hys. destruct Hys as [Hly Hsy].
        apply (nth_ext _ _ 0%R 0%R); [rewrite Lmap; exact Hly |].
        intros k Hk. rewrite Hly in Hk. rewrite Nmap by exact Hk.
        assert (D : nth k ys 0 - x k = 0); [| lra].
        apply (Inj (fun j => nth j ys 0 - x j)); [| exact Hk].
        intros i Hi. rewrite (sumR_ext _ (fun j => Am xa i j * nth j ys 0 - Am xa i j * x j)) by (intros; ring).
        rewrite sumR_sub, Hsy, Hx' by exact Hi. ring.
      * unfold approximates. apply (Forall2_iff _ _ _ 0%R 0%R); [rewrite !Lmap; reflexivity |].
        intros k Hk. rewrite Lmap in Hk. rewrite !Nmap by exact Hk. intros _.
        rewrite Rabs_minus_sym.
        apply (abs_le_tol _ eps rho sig Heps Hc).
        apply (cert_bound N0 (Am xa) (Rm xn Q) eps rho sig (fun j => x j - fval xt.[ix j]) HE HR); [| exact Hk].
        intros i Hi. unfold matvec.
        rewrite (sumR_ext _ (fun j => Am xa i j * x j - Am xa i j * fval xt.[ix j])) by (intros; ring).
        rewrite sumR_sub, Hx' by exact Hi. exact (HS i Hi).
  - set (st := forward xn (xn + 1) (col_thr xa xn) (init_M xa xb xn (xn + 1)) (init_Q xn)) in *.
    set (r := fs_r st) in *.
    set (k := if (r <? xn)%uint63 then (xn - r)%uint63 else 0%uint63) in *.
    set (fc := free_cols (fs_pc st) xn r) in *.
    set (Df := fst (mark_D (fs_perm st) xn r k)) in *.
    set (tix := snd (mark_D (fs_perm st) xn r k)) in *.
    set (Cf := mark_C fc xn k) in *.
    set (sc := scan_null (transpose xa xn) xb (fs_Q st) (fs_perm st) fc Df xn r k) in *.
    destruct (scan_null_spec (transpose xa xn) xb (fs_Q st) (fs_perm st) fc Df xn r k) as [Sinc Sok].
    fold sc in Sinc, Sok.
    revert Sinc Sok. destruct (fst sc) eqn:Einc; intros Sinc Sok.
    + (* Inconsistent : a dropped row is a left-null vector with y^T b <> 0 *)
      destruct (Sinc eq_refl) as [t Ei].
      exists Inconsistent. split; [exact I |].
      destruct (chk_incons_spec xn xa xb _ Hn Ei) as [Hy Hyb].
      intros xs Hs. apply Bridge in Hs. destruct Hs as [_ Hs].
      exact (incons_math N0 (Am xa) (fun i => fval xb.[ix i]) (fun i => IZR (yv (fs_Q st) xn r t).[ix i])
               (fun j => nth j xs 0) Hy Hyb Hs).
    + destruct (if snd sc then padded_ok xa xn Df tix fc Cf else false) eqn:Epad.
      { (* Multiple : the reduced left-null vectors and the padded certificate *)
        revert Sok Epad. destruct (snd sc) eqn:Eok; intros Sok Epad; [| discriminate Epad].
        destruct (Sok eq_refl) as [Hrn Hall].
        unfold padded_ok in Epad. cbv zeta in Epad.
        set (B := padB xa xn Df tix fc Cf) in *.
        destruct (fs_r (forward xn (xn + 1) (col_thr B xn) (init_M B (PArray.make xn zero) xn (xn + 1)) (init_Q xn)) =? xn)%uint63;
          [| discriminate].
        match type of Epad with certify_inj _ _ _ ?RB = true => pose proof (inj_of_cert xn B RB Hn Epad) as InjB end.
        fold N0 in InjB.
        assert (Hone : fval one = 1).
        { assert (E1 : of_uint63 1 = one) by reflexivity. rewrite <- E1.
          destruct (repr_of_uint63_exact 1 ltac:(reflexivity)) as [_ E]. rewrite E. reflexivity. }
        assert (Hzero : fval zero = 0) by (destruct repr_zero as [_ E]; exact E).
        assert (Hra : forall i j, (i < N0)%nat -> (j < N0)%nat -> repr xa.[ix i].[ix j] (Am xa i j)).
        { intros i j Hi Hj. rewrite HAm by assumption.
          apply repr_nth_float; [apply repr_nth_row; [exact Ha | lia] | rewrite Lrow; assumption]. }
        assert (Hk : (0 < to_Z k)%Z).
        { unfold k. rewrite Hrn. rewrite Uint63.ltb_spec in Hrn. pose proof (to_Z_bounded r). sia. }
        assert (HmD : forall i, (i < N0)%nat -> Df.[ix i] = true ->
                  (to_Z tix.[ix i] < to_Z k)%Z /\ (fs_perm st).[r + tix.[ix i]]%uint63 = ix i).
        { intros i Hi HD. exact (mark_D_spec (fs_perm st) xn r k Hn i Hi HD). }
        assert (HmC : forall t, (to_Z t < to_Z k)%Z -> (fc.[t] <? xn)%uint63 = true -> Cf.[fc.[t]] = true).
        { intros t Ht Hf. exact (mark_C_spec fc xn k Hn t Ht Hf). }
        assert (HltN : forall c, (c <? xn)%uint63 = true -> (toN c < N0)%nat).
        { intros c Hc. rewrite Uint63.ltb_spec in Hc. unfold N0, toN. pose proof (to_Z_bounded c). lia. }
        set (c0 := toN fc.[0%uint63]).
        destruct (Hall 0%uint63 Hk) as (_ & Hfc0 & _).
        assert (Hc0 : (c0 < N0)%nat) by (apply HltN; exact Hfc0).
        assert (Hc0C : Cf.[ix c0] = true) by (unfold c0; rewrite ix_toN; apply HmC; assumption).
        assert (Hcm : forall i, (i < N0)%nat -> Df.[ix i] = true ->
                  (toN fc.[tix.[ix i]] < N0)%nat /\ Cf.[ix (toN fc.[tix.[ix i]])] = true).
        { intros i Hi HD. destruct (HmD i Hi HD) as [Ht _]. destruct (Hall _ Ht) as (_ & Hf & _).
          split; [apply HltN; exact Hf | rewrite ix_toN; apply HmC; assumption]. }
        destruct (padded_math N0 (Am xa) (Am B) (fun i => fval xb.[ix i]) (fun i => Df.[ix i]) (fun j => Cf.[ix j])
                    (fun i => toN fc.[tix.[ix i]]) (fun d i => IZR (yv (fs_Q st) xn r tix.[ix d]).[ix i]) c0)
          as (x & v & HAx & HAv & Hvc).
        - intros i j Hi Hj. cbv beta. unfold Am at 1.
          etransitivity; [apply f_equal; exact (padB_spec xa xn Df tix fc Cf Hn i j Hi Hj) |]. unfold bentry.
          destruct (Df.[ix i]) eqn:HD.
          + destruct (Hcm i Hi HD) as [Hci _].
            rewrite <- (ix_toN fc.[tix.[ix i]]) at 1. rewrite (ix_eqb xn j _ ltac:(lia) Hj Hci).
            destruct (Nat.eqb j (toN fc.[tix.[ix i]])); assumption.
          + destruct (Cf.[ix j]); [exact Hzero | reflexivity].
        - intros i Hi HD. exact (Hcm i Hi HD).
        - exact Hc0.
        - exact Hc0C.
        - exact InjB.
        - set (Bh := ftab xn zero (fun i => if Df.[i] then zero else xb.[i])).
          destruct (exact_exists_arr xn B Bh Hn InjB) as [x Hx]. fold N0 in Hx. exists x. intros i Hi. cbv beta.
          rewrite (Hx i Hi). unfold Bh. rewrite (ftab_spec xn zero _ Hn i Hi). cbv beta.
          destruct (Df.[ix i]); [exact Hzero | reflexivity].
        - set (Gh := ftab xn zero (fun i => if Df.[i] then (if (fc.[tix.[i]] =? fc.[0%uint63])%uint63 then one else zero)
                                          else (- xa.[i].[fc.[0%uint63]])%float)).
          destruct (exact_exists_arr xn B Gh Hn InjB) as [v Hv]. fold N0 in Hv. exists v. intros i Hi. cbv beta.
          rewrite (Hv i Hi). unfold Gh. rewrite (ftab_spec xn zero _ Hn i Hi). cbv beta.
          destruct (Df.[ix i]) eqn:HD.
          + destruct (Hcm i Hi HD) as [Hci _].
            rewrite <- (ix_toN fc.[tix.[ix i]]), <- (ix_toN fc.[0%uint63]).
            rewrite (ix_eqb xn (toN fc.[tix.[ix i]]) (toN fc.[0%uint63]) ltac:(lia) Hci Hc0). unfold c0. rewrite !ix_toN.
            destruct (Nat.eqb (toN fc.[tix.[ix i]]) (toN fc.[0%uint63])); assumption.
          + rewrite <- (ix_toN fc.[0%uint63]). fold c0.
            destruct (repr_opp _ _ (Hra i c0 Hi Hc0)) as [_ E]. exact E.
        - intros d Hd HD. cbv beta. destruct (HmD d Hd HD) as [Ht Hp]. destruct (Hall _ Ht) as (_ & _ & Hred).
          rewrite Hp in Hred. destruct (chk_red_spec xn xa xb _ _ Df Hn Hred) as (H1 & _ & H3 & H4).
          split; [exact H1 | split].
          + apply not_0_IZR. exact H3.
          + intros i Hi HDi Hne. rewrite (H4 i Hi HDi); [reflexivity |].
            intros E. apply Hne. exact (ix_inj xn i d ltac:(lia) Hi Hd E).
        - intros d Hd HD. cbv beta. destruct (HmD d Hd HD) as [Ht Hp]. destruct (Hall _ Ht) as (_ & _ & Hred).
          rewrite Hp in Hred. destruct (chk_red_spec xn xa xb _ _ Df Hn Hred) as (_ & H2 & _). exact H2.
        - exists Multiple. split; [exact I |].
          exists (map x (seq 0 N0)), (map (fun j => x j + v j) (seq 0 N0)). split; [| split].
          + apply Bridge. split; [apply Lmap |]. intros i Hi.
            rewrite (sumR_ext _ (fun j => Am xa i j * x j)) by (intros j Hj; rewrite Nmap by exact Hj; reflexivity).
            exact (HAx i Hi).
          + apply Bridge. split; [apply Lmap |]. intros i Hi.
            rewrite (sumR_ext _ (fun j => 1 * (Am xa i j * x j) + 1 * (Am xa i j * v j)))
              by (intros j Hj; rewrite Nmap by exact Hj; ring).
            rewrite sumR_lin, (HAv i Hi), (HAx i Hi). ring.
          + intros E. apply Hvc.
            assert (Ej : nth c0 (map x (seq 0 N0)) 0 = nth c0 (map (fun j => x j + v j) (seq 0 N0)) 0)
              by (rewrite E; reflexivity).
            rewrite !Nmap in Ej by exact Hc0. lra. }
      destruct (ratvec (echelon_solve _ _ _ _ _ false _) xn) as [p q].
      match goal with |- context [chk_mult xa xb xn p q ?v] => set (vv := v) end.
      destruct (chk_mult xa xb xn p q vv) eqn:Em; [| exact (solve_exact_correct n a b xn xa xb Hvi Hxn Ha Hb)].
      destruct (chk_mult_spec xn xa xb p q vv Em) as (Hq & Hv & Hpv). fold N0 in Hv, Hpv.
      exists Multiple. split; [exact I |].
      assert (Hq' : IZR q <> 0) by (apply not_0_IZR; exact Hq).
      set (x0 := fun j => IZR p.[ix j] / IZR q).
      assert (H0 : forall i, (i < N0)%nat -> sumR (fun j => Am xa i j * x0 j) N0 = fval xb.[ix i]).
      { intros i Hi. unfold x0.
        rewrite (sumR_ext _ (fun j => Am xa i j * IZR p.[ix j] * / IZR q)) by (intros; unfold Rdiv; ring).
        rewrite sumR_scal_r. destruct (Hpv i Hi) as [E _]. rewrite E. field. exact Hq'. }
      exists (map x0 (seq 0 N0)), (map (fun j => x0 j + IZR vv.[ix j]) (seq 0 N0)). split; [| split].
      * apply Bridge. split; [apply Lmap |]. intros i Hi.
        rewrite (sumR_ext _ (fun j => Am xa i j * x0 j)) by (intros j Hj; rewrite Nmap by exact Hj; reflexivity).
        exact (H0 i Hi).
      * apply Bridge. split; [apply Lmap |]. intros i Hi.
        rewrite (sumR_ext _ (fun j => 1 * (Am xa i j * x0 j) + 1 * (Am xa i j * IZR vv.[ix j])))
          by (intros j Hj; rewrite Nmap by exact Hj; ring).
        rewrite sumR_lin, (proj2 (Hpv i Hi)), Rmult_0_r, Rplus_0_r, Rmult_1_l. exact (H0 i Hi).
      * intros E. apply Hv. intros j Hj.
        assert (Ej : nth j (map x0 (seq 0 N0)) 0 = nth j (map (fun j => x0 j + IZR vv.[ix j]) (seq 0 N0)) 0)
          by (rewrite E; reflexivity).
        rewrite !Nmap in Ej by exact Hj. apply eq_IZR. lra.
Qed.

Lemma solve_correct :
  forall (n : N) (a : list (list R)) (b : list R)
         (xn : uint) (xa : array (array float)) (xb : array float),
  valid_input n a b -> repr xn n -> repr xa a -> repr xb b ->
  exists o : outcome (list R), repr (solve xn xa xb) o /\ solve_spec n a b o.
Proof. exact solve_correct_main. Qed.
