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

(* ------------------------------------------------------------------ *)
(* Least squares over the reals                                        *)
(* ------------------------------------------------------------------ *)

Section LSQ.
Local Open Scope R_scope.

(* sum of f (hour, value) over the present cells of c, the first being hour t0 *)
Fixpoint sumf (f : R -> R -> R) (t0 : nat) (c : list (option R)) : R :=
  match c with
  | [] => 0
  | None :: c' => sumf f (S t0) c'
  | Some y :: c' => f (INR t0) y + sumf f (S t0) c'
  end.

Definition SP t0 c := sumf (fun _ _ => 1) t0 c.
Definition SK t0 c := sumf (fun t _ => t) t0 c.
Definition SKK t0 c := sumf (fun t _ => t * t) t0 c.
Definition SY t0 c := sumf (fun _ y => y) t0 c.
Definition SKY t0 c := sumf (fun t y => t * y) t0 c.
Definition SYY t0 c := sumf (fun _ y => y * y) t0 c.

Lemma sumf_app : forall f l1 l2 t0,
  sumf f t0 (l1 ++ l2) = sumf f t0 l1 + sumf f (t0 + List.length l1) l2.
Proof.
  intros f l1. induction l1 as [| o l1 IH]; intros l2 t0; simpl.
  - rewrite Nat.add_0_r. ring.
  - rewrite Nat.add_succ_r. destruct o; rewrite IH; simpl; ring.
Qed.

Lemma sumf_one : forall f t o,
  sumf f t [o] = match o with Some y => f (INR t) y | None => 0 end.
Proof. intros f t [y|]; simpl; ring. Qed.

Lemma SP_present : forall c t0, SP t0 c = INR (present c).
Proof.
  unfold SP. intros c. induction c as [| o c IH]; intros t0; simpl; [reflexivity|].
  destruct o; rewrite IH; [rewrite S_INR; ring | reflexivity].
Qed.

Lemma sums_absent : forall c t0, present c = 0%nat -> SK t0 c = 0 /\ SKK t0 c = 0.
Proof.
  unfold SK, SKK. intros c. induction c as [| o c IH]; intros t0 H; simpl; [split; reflexivity|].
  destruct o; simpl in H; [discriminate | apply IH; exact H].
Qed.

Lemma sse_expand : forall a b t0 c,
  sse a b t0 c = SYY t0 c - 2 * a * SY t0 c - 2 * b * SKY t0 c
                 + a * a * SP t0 c + 2 * a * b * SK t0 c + b * b * SKK t0 c.
Proof.
  unfold SYY, SY, SKY, SP, SK, SKK.
  intros a b t0 c. revert t0. induction c as [| o c IH]; intros t0; simpl; [ring|].
  destruct o; rewrite IH; ring.
Qed.

Lemma Q_expand : forall u v t0 c,
  sumf (fun t _ => (u + v * t) * (u + v * t)) t0 c
  = u * u * SP t0 c + 2 * u * v * SK t0 c + v * v * SKK t0 c.
Proof.
  unfold SP, SK, SKK.
  intros u v t0 c. revert t0. induction c as [| o c IH]; intros t0; simpl; [ring|].
  destruct o; rewrite IH; ring.
Qed.

Lemma sumf_nonneg : forall f t0 c, (forall t y, 0 <= f t y) -> 0 <= sumf f t0 c.
Proof.
  intros f t0 c Hf. revert t0. induction c as [| o c IH]; intros t0; simpl; [lra|].
  destruct o; [pose proof (Hf (INR t0) r); pose proof (IH (S t0)); lra | apply IH].
Qed.

(* a line satisfying the normal equations is a least-squares line *)
Lemma lsq_of_normal : forall c a b,
  a * SP 0 c + b * SK 0 c = SY 0 c ->
  a * SK 0 c + b * SKK 0 c = SKY 0 c ->
  lsq_line c a b.
Proof.
  intros c a b H1 H2 a' b'. rewrite !sse_expand.
  pose proof (Q_expand (a' - a) (b' - b) 0 c) as EQ.
  pose proof (sumf_nonneg (fun t _ => (a' - a + (b' - b) * t) * (a' - a + (b' - b) * t)) 0 c
                (fun t y => Rle_0_sqr _)) as NN.
  rewrite <- H1, <- H2.
  assert (E : forall X, (X - 2 * a' * (a * SP 0 c + b * SK 0 c) - 2 * b' * (a * SK 0 c + b * SKK 0 c)
           + a' * a' * SP 0 c + 2 * a' * b' * SK 0 c + b' * b' * SKK 0 c)
           - (X - 2 * a * (a * SP 0 c + b * SK 0 c) - 2 * b * (a * SK 0 c + b * SKK 0 c)
           + a * a * SP 0 c + 2 * a * b * SK 0 c + b * b * SKK 0 c)
           = (a' - a) * (a' - a) * SP 0 c + 2 * (a' - a) * (b' - b) * SK 0 c
             + (b' - b) * (b' - b) * SKK 0 c) by (intros; ring).
  specialize (E (SYY 0 c)). lra.
Qed.

(* the cells after hour s contribute at least one each to sum (t - s)^2 *)
Lemma shift_sq : forall c t0 s, (s < t0)%nat ->
  SKK t0 c - 2 * INR s * SK t0 c + INR s * INR s * SP t0 c >= INR (present c).
Proof.
  unfold SKK, SK, SP.
  intros c. induction c as [| o c IH]; intros t0 s Hs; simpl; [lra|].
  assert (Hs' : (s < S t0)%nat) by lia.
  destruct o.
  - pose proof (IH (S t0) s Hs').
    assert (INR s + 1 <= INR t0) by (rewrite <- S_INR; apply le_INR; lia).
    rewrite S_INR. nra.
  - apply IH. exact Hs'.
Qed.

Lemma D_ge : forall c t0, (1 <= present c)%nat ->
  SP t0 c * SKK t0 c - SK t0 c * SK t0 c >= INR (present c) - 1.
Proof.
  intros c. induction c as [| o c IH]; intros t0 H; simpl in H; [lia|].
  destruct o as [y|].
  - unfold SP, SK, SKK; cbn [sumf]; fold (SP (S t0) c) (SK (S t0) c) (SKK (S t0) c).
    cbn [present]. rewrite S_INR.
    destruct (Nat.eq_dec (present c) 0) as [E | E].
    + destruct (sums_absent c (S t0) E) as [E1 E2].
      rewrite E1, E2, SP_present, E. simpl. lra.
    + pose proof (IH (S t0) ltac:(lia)) as I.
      pose proof (shift_sq c (S t0) t0 ltac:(lia)) as Sq.
      rewrite SP_present in I, Sq |- *.
      assert (1 <= INR (present c)) by (change 1 with (INR 1); apply le_INR; lia).
      nra.
  - unfold SP, SK, SKK; cbn [sumf present]; fold (SP (S t0) c) (SK (S t0) c) (SKK (S t0) c).
    apply IH. exact H.
Qed.

End LSQ.

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

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi (fun _ _ => true) f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep. unfold loop.
  assert (G : forall n i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = n ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t ->
     P hi (wloop hi (fun _ _ => true) f i t H)).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H En Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      apply (IH (gap hi (i + 1))).
      + rewrite <- En. apply dec_step; exact Hlt.
      + reflexivity.
      + pose proof (to_Z_bounded hi).
        assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
      + apply Hstep; auto; lia.
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      assert (E : i = hi) by (apply to_Z_inj; lia). subst i. exact Pt. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

End LoopProof.

(* ------------------------------------------------------------------ *)
(* Exact arithmetic                                                    *)
(* ------------------------------------------------------------------ *)

Lemma zofi_rec_eq : forall i H, zofi_rec i H =
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma zofi_spec : forall i, zofi i = to_Z i.
Proof.
  assert (G : forall n i H, to_Z i = n -> zofi_rec i H = to_Z i).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i H En. rewrite zofi_rec_eq. destruct (bdec (i =? 0)) as [E | E].
    - apply Uint63.eqb_spec in E. subst i. reflexivity.
    - cbv zeta. rewrite (IH (to_Z (i / 2))); [| rewrite <- En; apply dec_half; exact E | reflexivity].
      pose proof (to_Z_bounded i).
      destruct (i mod 2 =? 0) eqn:Em.
      + apply Uint63.eqb_spec in Em. apply (f_equal to_Z) in Em. sia.
      + apply Uint63.eqb_false_spec in Em.
        assert (to_Z (i mod 2) <> 0%Z) by (intros E'; apply Em, to_Z_inj; exact E'). sia. }
  intros i. unfold zofi. apply (G _ i _ eq_refl).
Qed.

Lemma pos2int_spec : forall p, (Zpos p < wB)%Z -> to_Z (pos2int p) = Zpos p.
Proof.
  intros p. induction p as [q IH | q IH |]; intros Hp; simpl pos2int.
  - rewrite Pos2Z.inj_xI in Hp |- *. assert (E := IH ltac:(lia)). sia.
  - rewrite Pos2Z.inj_xO in Hp |- *. assert (E := IH ltac:(lia)). sia.
  - reflexivity.
Qed.

Lemma z2int_spec : forall z, (0 <= z < wB)%Z -> to_Z (z2int z) = z.
Proof.
  intros [| p | p] Hz; simpl z2int; [reflexivity | apply pos2int_spec; lia | lia].
Qed.

Local Notation bp := (Raux.bpow Zaux.radix2).

Definition dval (d : Z * Z) : R := (IZR (fst d) * bp (snd d))%R.

Lemma IZR_pow2 : forall k, (0 <= k)%Z -> IZR (2 ^ k) = bp k.
Proof. intros k Hk. destruct k as [| p | p]; [reflexivity | reflexivity | lia]. Qed.

Lemma shl_val : forall z e g, (g <= e)%Z -> (IZR (Z.shiftl z (e - g)) * bp g = IZR z * bp e)%R.
Proof.
  intros z e g He. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite mult_IZR, IZR_pow2 by lia. rewrite Rmult_assoc, <- Raux.bpow_plus.
  f_equal. f_equal. lia.
Qed.

Lemma repr_zero : repr 0%float 0%R.
Proof. split; reflexivity. Qed.

Lemma fex_val : forall (f : float) r, repr f r -> dval (fex f) = r.
Proof.
  intros f r Hf.
  assert (Hs : (f <? 0)%float = Raux.Rlt_bool r 0) by (apply repr_ltb; [exact Hf | exact repr_zero]).
  pose proof Hf as Hf'. apply repr_float_iff in Hf' as [Fin Ev].
  unfold fex. pose proof (Flocq.IEEE754.PrimFloat.frshiftexp_equiv f) as Fr.
  destruct (frshiftexp f) as [z e]. rewrite Hs. unfold dval; simpl fst; simpl snd.
  rewrite !zofi_spec, Flocq.IEEE754.PrimFloat.normfr_mantissa_equiv.
  rewrite <- Ev. clear Hs Ev Hf. revert Fr Fin.
  destruct (Flocq.IEEE754.PrimFloat.Prim2B f) as [s|s| |s m ex Hb]; intros Fr Fin; try discriminate.
  - simpl in Fr. injection Fr as Ez _. rewrite Ez. simpl.
    destruct (Raux.Rlt_bool 0 0); simpl; ring.
  - pose proof (BinarySingleNaN.Bfrexp_correct FloatOps.prec FloatOps.emax Flocq.IEEE754.PrimFloat.Hprec (BinarySingleNaN.B754_finite s m ex Hb) eq_refl) as C.
    rewrite <- Fr in C. destruct C as [E1 C]. destruct (C eq_refl) as [Hz _]. clear C.
    pose proof (BinarySingleNaN.Bnormfr_mantissa_correct FloatOps.prec FloatOps.emax Flocq.IEEE754.PrimFloat.Hmax (Flocq.IEEE754.PrimFloat.Prim2B z) Hz) as Nm.
    destruct (Flocq.IEEE754.PrimFloat.Prim2B z) as [| | |s' m' e' Hb']; try contradiction.
    destruct Nm as [Nm [_ Ee]]. rewrite Nm. subst e'. rewrite E1. clear E1 Hz Fr Nm.
    cbn [BinarySingleNaN.B2R]. unfold Defs.F2R; simpl Defs.Fnum; simpl Defs.Fexp.
    change FloatOps.shift with 2101%Z.
    replace (to_Z e - 2154)%Z with (to_Z e - 2101 + -53)%Z by lia.
    rewrite Raux.bpow_plus.
    pose proof (Raux.bpow_gt_0 Zaux.radix2 (-53)). pose proof (Raux.bpow_gt_0 Zaux.radix2 (to_Z e - 2101)).
    destruct s'; simpl Zaux.cond_Zopp; simpl Z.of_N.
    + rewrite Raux.Rlt_bool_true; [rewrite opp_IZR; change (Zneg m') with (- Zpos m')%Z; rewrite opp_IZR; ring |].
      assert (0 < IZR (Zpos m'))%R by (apply IZR_lt; lia).
      change (Zneg m') with (- Zpos m')%Z; rewrite opp_IZR.
      assert (0 < IZR (Z.pos m') * bp (-53) * bp (to_Z e - 2101))%R
        by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
      nra.
    + rewrite Raux.Rlt_bool_false; [ring |].
      assert (0 < IZR (Zpos m'))%R by (apply IZR_lt; lia).
      assert (0 < IZR (Z.pos m') * bp (-53) * bp (to_Z e - 2101))%R
        by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
      lra.
Qed.

(* ------------------------------------------------------------------ *)
(* The sums of a column                                                *)
(* ------------------------------------------------------------------ *)

Lemma firstn_snoc : forall {B} (l : list B) k d, (k < List.length l)%nat ->
  firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  intros B l. induction l as [| a l IH]; intros k d Hk; simpl in Hk; [lia|].
  destruct k as [| k]; [reflexivity|].
  change (firstn (S (S k)) (a :: l)) with (a :: firstn (S k) l).
  rewrite (IH k d ltac:(lia)). reflexivity.
Qed.

Section Col.
Context {A : Type} (conv : A -> option (Z * Z)) (x : array A) (c : list (option R)).
Hypothesis Hlen : Z.of_nat (List.length c) = to_Z (PArray.length x).
Hypothesis Hcell : forall i : int, (to_Z i < to_Z (PArray.length x))%Z ->
  match conv x.[i], nth (Z.to_nat (to_Z i)) c None with
  | Some d, Some r => dval d = r
  | None, None => True
  | _, _ => False
  end.

Definition sinv (i : int) (s : sums) : Prop :=
  let l := firstn (Z.to_nat (to_Z i)) c in
  IZR (sP s) = SP 0 l /\ IZR (sK s) = SK 0 l /\ IZR (sKK s) = SKK 0 l /\
  (IZR (sY s) * bp (sG s) = SY 0 l)%R /\ (IZR (sKY s) * bp (sG s) = SKY 0 l)%R.

Lemma acc_step_spec : forall i s, (to_Z i < to_Z (PArray.length x))%Z ->
  sinv i s -> sinv (i + 1) (acc_step conv x i s).
Proof.
  intros i s Hi (I1 & I2 & I3 & I4 & I5).
  pose proof (to_Z_bounded i) as Bi.
  assert (Hi1 : Z.to_nat (to_Z (i + 1)) = S (Z.to_nat (to_Z i))).
  { assert (to_Z (i + 1) = (to_Z i + 1)%Z) by (pose proof (to_Z_bounded (PArray.length x)); sia). lia. }
  set (k := Z.to_nat (to_Z i)) in *.
  assert (Hk : (k < List.length c)%nat) by lia.
  assert (Lk : List.length (firstn k c) = k) by (apply firstn_length_le; lia).
  assert (Kr : INR k = IZR (zofi i)) by (rewrite zofi_spec, INR_IZR_INZ; f_equal; unfold k; lia).
  unfold sinv. cbv zeta. rewrite Hi1, (firstn_snoc c k None Hk).
  unfold SP, SK, SKK, SY, SKY in *. rewrite !sumf_app, !sumf_one, Lk, Nat.add_0_l, Kr.
  set (l := firstn k c) in *.
  pose proof (Hcell i Hi) as C. fold k in C.
  unfold acc_step.
  destruct (conv x.[i]) as [d|]; destruct (nth k c None) as [r|]; try contradiction.
  - destruct d as [M E]. unfold dval in C. simpl fst in *; simpl snd in *.
    destruct (Z.eqb_spec M 0) as [HM | HM].
    + subst M. rewrite Rmult_0_l in C. subst r. simpl.
      rewrite !plus_IZR, mult_IZR, I1, I2, I3, <- I4, <- I5. repeat split; ring.
    + simpl. rewrite !plus_IZR, !mult_IZR, I1, I2, I3. repeat split; try ring.
      * rewrite Rmult_plus_distr_r, shl_val by lia. rewrite shl_val by lia.
        rewrite I4, C. ring.
      * rewrite Rmult_plus_distr_r, shl_val by lia. rewrite Rmult_assoc, shl_val by lia.
        rewrite I5, C. ring.
  - rewrite !Rplus_0_r. repeat split; assumption.
Qed.

Lemma col_sums_spec : sinv (PArray.length x) (col_sums conv x).
Proof.
  unfold col_sums. apply (for_inv sinv).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded (PArray.length x)). lia.
  - unfold sinv. simpl. unfold SP, SK, SKK, SY, SKY. simpl. repeat split; ring.
  - intros j t Hj I. apply acc_step_spec; [lia | exact I].
Qed.

Lemma col_sums_full : let s := col_sums conv x in
  IZR (sP s) = SP 0 c /\ IZR (sK s) = SK 0 c /\ IZR (sKK s) = SKK 0 c /\
  (IZR (sY s) * bp (sG s) = SY 0 c)%R /\ (IZR (sKY s) * bp (sG s) = SKY 0 c)%R.
Proof.
  pose proof col_sums_spec as H. unfold sinv in H. cbv zeta in *.
  rewrite firstn_all2 in H by lia. exact H.
Qed.

End Col.

(* ------------------------------------------------------------------ *)
(* The fit                                                             *)
(* ------------------------------------------------------------------ *)

Lemma fit_spec : forall (c : list (option R)) (s : sums) (sc : Z),
  IZR (sP s) = SP 0 c -> IZR (sK s) = SK 0 c -> IZR (sKK s) = SKK 0 c ->
  (IZR (sY s) * bp (sG s) = SY 0 c)%R -> (IZR (sKY s) * bp (sG s) = SKY 0 c)%R ->
  ((present c < 2)%nat -> fit s sc = None) /\
  ((2 <= present c)%nat -> exists f, fit s sc = Some f /\ (0 < fden f)%Z /\
     exists a b, lsq_line c a b /\
       forall T, (IZR (fc0 f + fc1 f * T) / IZR (fden f) = (a + b * IZR T) * bp sc)%R).
Proof.
  intros c s sc E1 E2 E3 E4 E5.
  assert (HP : sP s = Z.of_nat (present c)).
  { apply eq_IZR. rewrite E1, SP_present, INR_IZR_INZ. reflexivity. }
  split.
  - intros Hp. unfold fit. rewrite HP. replace (Z.of_nat (present c) <? 2)%Z with true; [reflexivity|].
    symmetry. apply Z.ltb_lt. lia.
  - intros Hp. unfold fit.
    replace (sP s <? 2)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (D_ge c 0 ltac:(lia)) as DG.
    rewrite <- E1, <- E2, <- E3 in DG.
    assert (Pp : (2 <= IZR (sP s))%R) by (apply IZR_le; lia).
    rewrite <- !mult_IZR, <- minus_IZR in DG.
    assert (Dp : (1 <= sP s * sKK s - sK s * sK s)%Z).
    { apply le_IZR. assert (INR (present c) = IZR (sP s)) by (rewrite E1, SP_present; reflexivity).
      lra. }
    set (P := sP s) in *. set (K := sK s) in *. set (KK := sKK s) in *.
    set (Y := sY s) in *. set (KY := sKY s) in *. set (g := sG s) in *.
    set (D := (P * KK - K * K)%Z) in *.
    set (B := (P * KY - K * Y)%Z).
    assert (Hden : (0 < P * D)%Z) by nia.
    assert (PR : IZR P <> 0%R) by lra.
    assert (DR : IZR D <> 0%R) by (apply not_0_IZR; lia).
    pose proof (Raux.bpow_gt_0 Zaux.radix2 g) as Gp.
    pose proof (Raux.bpow_gt_0 Zaux.radix2 sc) as Sp.
    set (bb := (IZR B / IZR D * bp g)%R).
    set (aa := ((IZR Y - IZR B / IZR D * IZR K) / IZR P * bp g)%R).
    assert (Hlsq : lsq_line c aa bb).
    { apply lsq_of_normal.
      - rewrite <- E1, <- E2, <- E4. unfold aa, bb, B. field. split; assumption.
      - rewrite <- E2, <- E3, <- E5. unfold aa, bb, B, D in *.
        rewrite !minus_IZR, !mult_IZR in *. field. split; assumption. }
    assert (Hval : forall T, (IZR ((Y * D - B * K) + B * P * T) / IZR (P * D) * bp g
                              = aa + bb * IZR T)%R).
    { intros T. unfold aa, bb. rewrite !plus_IZR, !minus_IZR, !mult_IZR.
      field. split; assumption. }
    destruct (Z.leb_spec 0 (g + sc)) as [He | He].
    + eexists. split; [reflexivity|]. simpl fden. split; [exact Hden|].
      exists aa, bb. split; [exact Hlsq|]. intros T. simpl fc0; simpl fc1.
      rewrite !Z.shiftl_mul_pow2 by lia.
      rewrite <- (Hval T), Rmult_assoc, <- Raux.bpow_plus.
      replace ((Y * D - B * K) * 2 ^ (g + sc) + B * P * 2 ^ (g + sc) * T)%Z
        with ((Y * D - B * K + B * P * T) * 2 ^ (g + sc))%Z by ring.
      rewrite mult_IZR, IZR_pow2 by lia.
      assert (IZR (P * D) <> 0%R) by (apply not_0_IZR; lia).
      field. exact H.
    + eexists. split; [reflexivity|]. simpl fden. split.
      { rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (- (g + sc)) ltac:(lia) ltac:(lia)). nia. }
      exists aa, bb. split; [exact Hlsq|]. intros T. simpl fc0; simpl fc1.
      rewrite !Z.shiftl_mul_pow2 by lia.
      rewrite <- (Hval T), Rmult_assoc, <- Raux.bpow_plus.
      rewrite mult_IZR, IZR_pow2 by lia. rewrite Raux.bpow_opp.
      pose proof (Raux.bpow_gt_0 Zaux.radix2 (g + sc)) as Ep.
      assert (IZR (P * D) <> 0%R) by (apply not_0_IZR; lia).
      field. split; [exact H | lra].
Qed.

(* ------------------------------------------------------------------ *)
(* Rounding and clamping                                               *)
(* ------------------------------------------------------------------ *)

Lemma round_err : forall X den : Z, (0 < den)%Z ->
  (Rabs (IZR ((2 * X + den) / (2 * den)) - IZR X / IZR den) <= / 2)%R.
Proof.
  intros X den Hd.
  set (q := ((2 * X + den) / (2 * den))%Z).
  pose proof (Z.div_mod (2 * X + den) (2 * den) ltac:(lia)) as Dm.
  pose proof (Z.mod_pos_bound (2 * X + den) (2 * den) ltac:(lia)) as Mb.
  fold q in Dm.
  assert (H1 : (2 * den * q <= 2 * X + den)%Z) by lia.
  assert (H2 : (2 * X + den < 2 * den * q + 2 * den)%Z) by lia.
  apply IZR_le in H1. apply IZR_lt in H2.
  rewrite !plus_IZR, !mult_IZR in H1. rewrite !plus_IZR, !mult_IZR in H2.
  rewrite ?plus_IZR, ?mult_IZR in H1. rewrite ?plus_IZR, ?mult_IZR in H2.
  assert (Dp : (0 < IZR den)%R) by (apply IZR_lt; exact Hd).
  set (w := (IZR X / IZR den)%R).
  assert (Ew : IZR X = (w * IZR den)%R) by (unfold w; field; lra).
  rewrite Ew in H1, H2.
  apply Rabs_le. split; nra.
Qed.

Lemma clamp_lip : forall lo hi x y, (lo <= hi)%R ->
  (Rabs (clamp lo hi x - clamp lo hi y) <= Rabs (x - y))%R.
Proof.
  intros lo hi x y H. unfold clamp, Rmax, Rmin.
  repeat destruct Rle_dec; unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.

Lemma clamp_range : forall lo hi x, (lo <= hi)%R -> (lo <= clamp lo hi x <= hi)%R.
Proof.
  intros lo hi x H. unfold clamp, Rmax, Rmin. repeat destruct Rle_dec; lra.
Qed.

Lemma IZR_clamp : forall lo hi v, (lo <= hi)%Z ->
  IZR (clampZ lo hi v) = clamp (IZR lo) (IZR hi) (IZR v).
Proof.
  intros lo hi v H. unfold clampZ, clamp.
  destruct (Z.le_ge_cases hi v) as [h | h].
  - rewrite Z.min_l by exact h. rewrite Rmin_left by (apply IZR_le; exact h).
    rewrite Z.max_r by exact H. rewrite Rmax_right by (apply IZR_le; exact H). reflexivity.
  - rewrite Z.min_r by lia. rewrite Rmin_right by (apply IZR_le; lia).
    destruct (Z.le_ge_cases lo v) as [h' | h'].
    + rewrite Z.max_r by exact h'. rewrite Rmax_right by (apply IZR_le; exact h'). reflexivity.
    + rewrite Z.max_l by lia. rewrite Rmax_left by (apply IZR_le; lia). reflexivity.
Qed.

Lemma clamp_scale : forall lo hi z, (lo <= hi)%R ->
  (clamp (lo * 1048576) (hi * 1048576) z / 1048576 = clamp lo hi (z / 1048576))%R.
Proof.
  intros lo hi z H. unfold clamp, Rmax, Rmin. repeat destruct Rle_dec; lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Building the output floats                                          *)
(* ------------------------------------------------------------------ *)

Lemma fmt20 : forall z : Z, (Z.abs z < 2 ^ 53)%Z ->
  rnd (IZR z * / 1048576)%R = (IZR z * / 1048576)%R.
Proof.
  intros z Hz. apply rnd_exact. apply FLT.generic_format_FLT.
  exists (Defs.Float Zaux.radix2 z (-20)); [| exact Hz | cbn; lia].
  unfold Defs.F2R; simpl. reflexivity.
Qed.

Lemma bp1000 : (1048576 <= bp 1000)%R.
Proof.
  pose proof (Raux.bpow_le Zaux.radix2 20 1000 ltac:(lia)) as H.
  change (bp 20) with 1048576%R in H. exact H.
Qed.

Lemma repr_c20 : repr c20 (/ 1048576)%R.
Proof.
  unfold c20.
  pose proof (repr_of_uint63_exact 1 eq_refl) as R1.
  pose proof (repr_of_uint63_exact 1048576 eq_refl) as R2.
  change (IZR (to_Z 1)) with 1%R in R1. change (IZR (to_Z 1048576)) with 1048576%R in R2.
  pose proof (fmt20 1 eq_refl) as F. rewrite Rmult_1_l in F.
  replace (/ 1048576)%R with (rnd (1 / 1048576))%R by (unfold Rdiv; rewrite Rmult_1_l; exact F).
  apply repr_div; [exact R1 | exact R2 | lra |].
  apply rnd_no_overflow_small. unfold Rdiv. rewrite Rmult_1_l.
  pose proof bp1000. rewrite Rabs_right; [|lra]. lra.
Qed.

Lemma repr_fl_of_Z : forall z : Z, (Z.abs z < 2 ^ 53)%Z -> repr (fl_of_Z z) (IZR z).
Proof.
  intros z Hz. unfold fl_of_Z. destruct (Z.ltb_spec z 0) as [Hn | Hn].
  - assert (E : to_Z (z2int (- z)) = (- z)%Z) by (apply z2int_spec; change wB with (2 ^ 63)%Z; lia).
    replace (IZR z) with (- IZR (to_Z (z2int (- z))))%R by (rewrite E, opp_IZR; ring).
    apply repr_opp, repr_of_uint63_exact. lia.
  - assert (E : to_Z (z2int z) = z) by (apply z2int_spec; change wB with (2 ^ 63)%Z; lia).
    rewrite <- E at 2. apply repr_of_uint63_exact. lia.
Qed.

Lemma repr_fz : forall z : Z, (Z.abs z <= 400 * 1048576)%Z ->
  repr (fl_of_Z z * c20)%float (IZR z / 1048576)%R.
Proof.
  intros z Hz.
  assert (Hz' : (Z.abs z < 2 ^ 53)%Z) by lia.
  unfold Rdiv. rewrite <- (fmt20 z Hz').
  apply repr_mul; [apply repr_fl_of_Z, Hz' | exact repr_c20 |].
  apply rnd_no_overflow_small.
  pose proof bp1000.
  assert (Rabs (IZR z) <= IZR 419430400)%R by (rewrite <- abs_IZR; apply IZR_le; lia).
  rewrite Rabs_mult, Rabs_inv, (Rabs_right 1048576) by lra.
  apply Rle_trans with (IZR 419430400 * / 1048576)%R; [| lra].
  apply Rmult_le_compat_r; [lra | exact H0].
Qed.

(* ------------------------------------------------------------------ *)
(* One forecast cell                                                   *)
(* ------------------------------------------------------------------ *)

Definition fmath (fo : option fitr) (lo hi T : Z) : option R :=
  match fo with
  | None => None
  | Some f => Some (IZR (clampZ (lo * 1048576) (hi * 1048576) (rnd_at f T)) / 1048576)%R
  end.

Definition imath (fo : option fitr) (lo hi T : Z) : option N :=
  match fo with
  | None => None
  | Some f => Some (Z.to_N (clampZ lo hi (rnd_at f T)))
  end.

Lemma repr_fout : forall fo lo hi T, (-360 <= lo <= hi)%Z -> (hi <= 360)%Z ->
  repr (fout fo lo hi T) (fmath fo lo hi T).
Proof.
  intros [f|] lo hi T H1 H2; simpl; [| exact I].
  apply repr_fz. unfold clampZ. lia.
Qed.

Lemma repr_iout : forall fo lo hi T, (0 <= lo <= hi)%Z -> (hi <= 360)%Z ->
  repr (iout fo lo hi T) (imath fo lo hi T).
Proof.
  intros [f|] lo hi T H1 H2; simpl; [| exact I].
  change (Z.to_N (to_Z (z2int (clampZ lo hi (rnd_at f T)))) = Z.to_N (clampZ lo hi (rnd_at f T))).
  f_equal. apply z2int_spec. unfold clampZ. change wB with (2 ^ 63)%Z. lia.
Qed.

Definition cell_ok (c : list (option R)) (lo hi err : R) (j : nat) (o : option R) : Prop :=
  (o = None <-> (present c < 2)%nat) /\
  forall r, o = Some r ->
    (lo <= r <= hi)%R /\
    exists a b, lsq_line c a b /\
      (Rabs (r - clamp lo hi (a + b * INR (List.length c + j))) <= err)%R.

Lemma fcell : forall (c : list (option R)) (s : sums) (lo hi : Z) (j : nat) (T : Z),
  IZR (sP s) = SP 0 c -> IZR (sK s) = SK 0 c -> IZR (sKK s) = SKK 0 c ->
  (IZR (sY s) * bp (sG s) = SY 0 c)%R -> (IZR (sKY s) * bp (sG s) = SKY 0 c)%R ->
  (lo <= hi)%Z -> IZR T = INR (List.length c + j) ->
  cell_ok c (IZR lo) (IZR hi) tol j (fmath (fit s 20) lo hi T).
Proof.
  intros c s lo hi j T E1 E2 E3 E4 E5 Hlh HT.
  destruct (fit_spec c s 20 E1 E2 E3 E4 E5) as [N S].
  destruct (Nat.lt_ge_cases (present c) 2) as [Hp | Hp].
  - rewrite (N Hp). simpl. split; [tauto | intros r Hr; discriminate].
  - destruct (S Hp) as (f & Hf & Hd & a & b & Hl & Hv). rewrite Hf. simpl.
    split; [split; [discriminate | lia] |].
    intros r Hr. injection Hr as <-.
    assert (Hlh' : (IZR lo <= IZR hi)%R) by (apply IZR_le; exact Hlh).
    rewrite IZR_clamp by lia. rewrite !mult_IZR. rewrite clamp_scale by exact Hlh'.
    split; [apply clamp_range; exact Hlh' |].
    exists a, b. split; [exact Hl |].
    eapply Rle_trans; [apply clamp_lip; exact Hlh' |].
    pose proof (round_err (fc0 f + fc1 f * T) (fden f) Hd) as Re.
    unfold rnd_at. rewrite Hv in Re. rewrite <- HT.
    change (bp 20) with 1048576%R in Re.
    set (R0 := IZR ((2 * (fc0 f + fc1 f * T) + fden f) / (2 * fden f))) in *.
    set (V := (a + b * IZR T)%R) in *.
    replace (R0 / 1048576 - V)%R with ((R0 - V * 1048576) / 1048576)%R by (field; lra).
    unfold Rdiv. rewrite Rabs_mult, (Rabs_inv 1048576), (Rabs_right 1048576) by lra.
    unfold tol. apply Rle_trans with (/ 2 * / 1048576)%R; [apply Rmult_le_compat_r; lra | lra].
Qed.

Lemma icell : forall (c : list (option R)) (s : sums) (lo hi : Z) (j : nat) (T : Z),
  IZR (sP s) = SP 0 c -> IZR (sK s) = SK 0 c -> IZR (sKK s) = SKK 0 c ->
  (IZR (sY s) * bp (sG s) = SY 0 c)%R -> (IZR (sKY s) * bp (sG s) = SKY 0 c)%R ->
  (0 <= lo <= hi)%Z -> IZR T = INR (List.length c + j) ->
  cell_ok c (IZR lo) (IZR hi) (/ 2 + tol) j
    (option_map (fun v => IZR (Z.of_N v)) (imath (fit s 0) lo hi T)).
Proof.
  intros c s lo hi j T E1 E2 E3 E4 E5 Hlh HT.
  destruct (fit_spec c s 0 E1 E2 E3 E4 E5) as [N S].
  destruct (Nat.lt_ge_cases (present c) 2) as [Hp | Hp].
  - rewrite (N Hp). simpl. split; [tauto | intros r Hr; discriminate].
  - destruct (S Hp) as (f & Hf & Hd & a & b & Hl & Hv). rewrite Hf. simpl.
    split; [split; [discriminate | lia] |].
    intros r Hr. injection Hr as <-.
    assert (Hlh' : (IZR lo <= IZR hi)%R) by (apply IZR_le; lia).
    rewrite Z2N.id by (unfold clampZ; lia).
    rewrite IZR_clamp by lia.
    split; [apply clamp_range; exact Hlh' |].
    exists a, b. split; [exact Hl |].
    eapply Rle_trans; [apply clamp_lip; exact Hlh' |].
    pose proof (round_err (fc0 f + fc1 f * T) (fden f) Hd) as Re.
    unfold rnd_at. rewrite Hv in Re. rewrite <- HT.
    change (bp 0) with 1%R in Re. rewrite Rmult_1_r in Re.
    unfold tol. lra.
Qed.

(* the cells of a forecast column *)
Lemma nth_map_seq : forall {B} (g : nat -> option B) M j, (j < M)%nat ->
  nth j (map g (seq 0 M)) None = g j.
Proof.
  intros B g M j Hj.
  rewrite (nth_indep _ None (g 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma forecast_of : forall lo hi err c (m : N) (g : nat -> option R),
  (forall j, (N.of_nat j < m)%N -> cell_ok c lo hi err j (g j)) ->
  forecast lo hi err c m (map g (seq 0 (N.to_nat m))).
Proof.
  intros lo hi err c m g H. split.
  - unfold len. rewrite length_map, length_seq. lia.
  - intros j Hj. rewrite nth_map_seq by lia. exact (H j Hj).
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the inputs                                                  *)
(* ------------------------------------------------------------------ *)

Lemma repr_cell : forall {A M} `{Repr A M} (x : array A) (l : list M) (d : M) (i : int),
  repr x l -> (to_Z i < to_Z (PArray.length x))%Z ->
  repr x.[i] (nth (Z.to_nat (to_Z i)) l d).
Proof.
  intros A M RA x l d i [Hl Hc] Hi.
  destruct (Hc (Z.to_nat (to_Z i)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in R. exact R.
Qed.

Lemma fcol_cells : forall (x : array (option float)) (c : list (option R)), repr x c ->
  forall i : int, (to_Z i < to_Z (PArray.length x))%Z ->
  match fconv x.[i], nth (Z.to_nat (to_Z i)) c None with
  | Some d, Some r => dval d = r
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros x c Hx i Hi. pose proof (repr_cell x c None i Hx Hi) as R.
  destruct (x.[i]) as [f|]; destruct (nth (Z.to_nat (to_Z i)) c None) as [r|];
    cbn in R |- *; try contradiction; [apply fex_val; exact R | exact I].
Qed.

Lemma nth_col_R : forall (d : list (option N)) k,
  nth k (col_R d) None = option_map (fun v => IZR (Z.of_N v)) (nth k d None).
Proof.
  unfold col_R. intros d. induction d as [| o d IH]; intros [| k]; simpl; auto.
Qed.

Lemma icol_cells : forall (x : array (option uint)) (d : list (option N)), repr x d ->
  forall i : int, (to_Z i < to_Z (PArray.length x))%Z ->
  match iconv x.[i], nth (Z.to_nat (to_Z i)) (col_R d) None with
  | Some e, Some r => dval e = r
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros x d Hx i Hi. pose proof (repr_cell x d None i Hx Hi) as R. rewrite nth_col_R.
  destruct (x.[i]) as [v|]; destruct (nth (Z.to_nat (to_Z i)) d None) as [w|];
    cbn in R |- *; try contradiction; [| exact I].
  unfold repr, repr_uint in R. subst w. unfold dval. simpl.
  rewrite zofi_spec, Z2N.id by (pose proof (to_Z_bounded v); lia). ring.
Qed.

Lemma len_col_R : forall d, List.length (col_R d) = List.length d.
Proof. intros d. unfold col_R. apply length_map. Qed.

(* ------------------------------------------------------------------ *)
(* The output loop                                                     *)
(* ------------------------------------------------------------------ *)

Lemma gss : forall {T : Set} (t : array T) (i : int) (v : T),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros T t i v H. exact (get_set_same T t i v H). Qed.

Lemma gso : forall {T : Set} (t : array T) (i j : int) (v : T), i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros T t i j v H. exact (get_set_other T t i j v H). Qed.

Lemma lset : forall {T : Set} (t : array T) (i : int) (v : T), PArray.length t.[i <- v] = PArray.length t.
Proof. intros T t i v. exact (length_set T t i v). Qed.

Lemma lmake : forall {T : Set} (n : int) (v : T),
  PArray.length (PArray.make n v) = if n <=? max_length then n else max_length.
Proof. intros T n v. exact (length_make T n v). Qed.

Section Output.
Variables (ft fd fs fh : option fitr) (nt nd ns nh : Z) (L : int).

Definition oinv (j : int) (o : Out) : Prop :=
  let '(a, b, c, d) := o in
  PArray.length a = L /\ PArray.length b = L /\ PArray.length c = L /\ PArray.length d = L /\
  forall i : int, (to_Z i < to_Z j)%Z ->
    a.[i] = fout ft (-50) 50 (nt + to_Z i) /\ b.[i] = iout fd 0 360 (nd + to_Z i) /\
    c.[i] = fout fs 0 80 (ns + to_Z i) /\ d.[i] = iout fh 0 110 (nh + to_Z i).

Lemma oinv_step : forall j o, (to_Z j < to_Z L)%Z -> oinv j o ->
  oinv (j + 1) (out_step ft fd fs fh nt nd ns nh j o).
Proof.
  intros j [[[a b] c] d] Hj (La & Lb & Lc & Ld & Hc). unfold out_step, oinv.
  rewrite !lset. split; [exact La|]. split; [exact Lb|]. split; [exact Lc|]. split; [exact Ld|].
  intros i Hi.
  assert (Hj1 : to_Z (j + 1) = (to_Z j + 1)%Z) by (pose proof (to_Z_bounded L); sia).
  rewrite zofi_spec.
  destruct (Z.eq_dec (to_Z i) (to_Z j)) as [E | E].
  - apply to_Z_inj in E. subst i.
    assert (Hjl : forall t : int, t = L -> (j <? t) = true) by (intros t ->; apply Uint63.ltb_spec; exact Hj).
    rewrite !gss by (apply Hjl; assumption). repeat split; reflexivity.
  - assert (N : j <> i) by (intros ->; apply E; reflexivity).
    rewrite !gso by exact N. apply Hc. lia.
Qed.

End Output.

Lemma repr_out : forall {B MB} `{Repr B MB} (a : array B) (L : int) (gm : nat -> MB) (gx : Z -> B),
  PArray.length a = L ->
  (forall i : int, (to_Z i < to_Z L)%Z -> a.[i] = gx (to_Z i)) ->
  (forall k, (Z.of_nat k < to_Z L)%Z -> repr (gx (Z.of_nat k)) (gm k)) ->
  repr a (map gm (seq 0 (Z.to_nat (to_Z L)))).
Proof.
  intros B MB RB a L gm gx HL Ha Hg.
  pose proof (to_Z_bounded L) as BL.
  split.
  - rewrite length_map, length_seq, HL. lia.
  - intros k Hk. rewrite length_map, length_seq in Hk.
    exists (gm k). split.
    + rewrite nth_error_map, nth_error_seq.
      destruct (Nat.ltb_spec k (Z.to_nat (to_Z L))); [reflexivity | lia].
    + assert (Ek : to_Z (of_Z (Z.of_nat k)) = Z.of_nat k)
        by (rewrite of_Z_spec; apply Z.mod_small; lia).
      rewrite Ha by (rewrite Ek; lia). rewrite Ek. apply Hg. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma hour_val : forall (n : int) (c : list (option R)) (j : nat),
  Z.of_nat (List.length c) = to_Z n ->
  IZR (zofi n + Z.of_nat j) = INR (List.length c + j).
Proof.
  intros n c j H. rewrite zofi_spec, <- H, <- Nat2Z.inj_add, <- INR_IZR_INZ. reflexivity.
Qed.

Lemma vedurspa_correct_main :
  forall (t : list (option R)) (d : list (option N)) (s : list (option R))
         (h : list (option N)) (m : N)
         (xt : array (option float)) (xd : array (option uint))
         (xs : array (option float)) (xh : array (option uint)) (xm : uint),
  valid_input t d s h m ->
  repr xt t -> repr xd d -> repr xs s -> repr xh h -> repr xm m ->
  exists o : list (option R) * list (option N) * list (option R) * list (option N),
    repr (vedurspa_impl xt xd xs xh xm) o /\ vedurspa_spec t d s h m o.
Proof.
  intros t d s h m xt xd xs xh xm _ Hxt Hxd Hxs Hxh Hxm.
  assert (Lt : Z.of_nat (List.length t) = to_Z (PArray.length xt)) by exact (proj1 Hxt).
  assert (Ls : Z.of_nat (List.length s) = to_Z (PArray.length xs)) by exact (proj1 Hxs).
  assert (Ld : Z.of_nat (List.length (col_R d)) = to_Z (PArray.length xd))
    by (rewrite len_col_R; exact (proj1 Hxd)).
  assert (Lh : Z.of_nat (List.length (col_R h)) = to_Z (PArray.length xh))
    by (rewrite len_col_R; exact (proj1 Hxh)).
  pose proof (col_sums_full fconv xt t Lt (fcol_cells xt t Hxt)) as (T1 & T2 & T3 & T4 & T5).
  pose proof (col_sums_full fconv xs s Ls (fcol_cells xs s Hxs)) as (S1 & S2 & S3 & S4 & S5).
  pose proof (col_sums_full iconv xd (col_R d) Ld (icol_cells xd d Hxd)) as (D1 & D2 & D3 & D4 & D5).
  pose proof (col_sums_full iconv xh (col_R h) Lh (icol_cells xh h Hxh)) as (H1 & H2 & H3 & H4 & H5).
  set (ft := fit (col_sums fconv xt) 20).
  set (fd := fit (col_sums iconv xd) 0).
  set (fs := fit (col_sums fconv xs) 20).
  set (fh := fit (col_sums iconv xh) 0).
  set (nt := zofi (PArray.length xt)). set (nd := zofi (PArray.length xd)).
  set (ns := zofi (PArray.length xs)). set (nh := zofi (PArray.length xh)).
  set (L := if xm <=? max_length then xm else max_length).
  assert (BL : (to_Z L <= 4194303)%Z).
  { unfold L. destruct (xm <=? max_length) eqn:Em; [| reflexivity].
    apply Uint63.leb_spec in Em. exact Em. }
  assert (Lm : (Z.of_N m <= 4194303)%Z -> L = xm).
  { intros Hm. unfold L. replace (xm <=? max_length) with true; [reflexivity|].
    symmetry. apply Uint63.leb_spec. unfold repr, repr_uint in Hxm.
    change (to_Z max_length) with 4194303%Z. pose proof (to_Z_bounded xm). lia. }
  assert (LM : forall {T : Set} (v : T), PArray.length (PArray.make L v) = L).
  { intros T v. rewrite lmake. replace (L <=? max_length) with true; [reflexivity|].
    symmetry. apply Uint63.leb_spec. exact BL. }
  pose proof (for_inv (oinv ft fd fs fh nt nd ns nh L) L 0
                (out_step ft fd fs fh nt nd ns nh)
                (PArray.make L None, PArray.make L None, PArray.make L None, PArray.make L None))
    as Inv.
  change (vedurspa_impl xt xd xs xh xm) with
    (loop L (fun _ _ => true) (out_step ft fd fs fh nt nd ns nh) 0
       (PArray.make L (@None float), PArray.make L (@None uint),
        PArray.make L (@None float), PArray.make L (@None uint))).
  destruct (loop L (fun _ _ => true) (out_step ft fd fs fh nt nd ns nh) 0
              (PArray.make L None, PArray.make L None, PArray.make L None, PArray.make L None))
    as [[[a b] c] e].
  destruct Inv as (La & Lb & Lc & Le & Hc).
  { change (to_Z 0) with 0%Z. pose proof (to_Z_bounded L). lia. }
  { simpl. rewrite !LM. repeat split; try reflexivity.
    all: exfalso; match goal with Hi : (to_Z ?i < to_Z 0)%Z |- _ =>
      change (to_Z 0) with 0%Z in Hi; pose proof (to_Z_bounded i); lia end. }
  { intros j o Hj I. apply oinv_step; [lia | exact I]. }
  set (M := Z.to_nat (to_Z L)).
  exists (map (fun k => fmath ft (-50) 50 (nt + Z.of_nat k)) (seq 0 M),
          map (fun k => imath fd 0 360 (nd + Z.of_nat k)) (seq 0 M),
          map (fun k => fmath fs 0 80 (ns + Z.of_nat k)) (seq 0 M),
          map (fun k => imath fh 0 110 (nh + Z.of_nat k)) (seq 0 M)).
  split.
  - split; [split; [split|]|].
    + apply (repr_out a L _ (fun z => fout ft (-50) 50 (nt + z)) La).
      * intros i Hi. exact (proj1 (Hc i Hi)).
      * intros k _. apply repr_fout; lia.
    + apply (repr_out b L _ (fun z => iout fd 0 360 (nd + z)) Lb).
      * intros i Hi. exact (proj1 (proj2 (Hc i Hi))).
      * intros k _. apply repr_iout; lia.
    + apply (repr_out c L _ (fun z => fout fs 0 80 (ns + z)) Lc).
      * intros i Hi. exact (proj1 (proj2 (proj2 (Hc i Hi)))).
      * intros k _. apply repr_fout; lia.
    + apply (repr_out e L _ (fun z => iout fh 0 110 (nh + z)) Le).
      * intros i Hi. exact (proj2 (proj2 (proj2 (Hc i Hi)))).
      * intros k _. apply repr_iout; lia.
  - unfold vedurspa_spec. intros Hm.
    assert (EM : M = N.to_nat m).
    { unfold M. rewrite (Lm ltac:(lia)). unfold repr, repr_uint in Hxm. lia. }
    rewrite EM.
    split; [| split; [| split]].
    + apply forecast_of. intros j _.
      apply (fcell t _ (-50) 50 j); auto; [lia | exact (hour_val _ t j Lt)].
    + unfold col_R at 2. rewrite map_map. apply forecast_of. intros j _.
      apply (icell (col_R d) _ 0 360 j); auto; [lia | exact (hour_val _ _ j Ld)].
    + apply forecast_of. intros j _.
      apply (fcell s _ 0 80 j); auto; [lia | exact (hour_val _ s j Ls)].
    + unfold col_R at 2. rewrite map_map. apply forecast_of. intros j _.
      apply (icell (col_R h) _ 0 110 j); auto; [lia | exact (hour_val _ _ j Lh)].
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition vedurspa :
  array (option float) -> array (option uint) ->
  array (option float) -> array (option uint) -> uint ->
  array (option float) * array (option uint) *
  array (option float) * array (option uint) := vedurspa_impl.

Lemma vedurspa_correct :
  forall (t : list (option R)) (d : list (option N)) (s : list (option R))
         (h : list (option N)) (m : N)
         (xt : array (option float)) (xd : array (option uint))
         (xs : array (option float)) (xh : array (option uint)) (xm : uint),
  valid_input t d s h m ->
  repr xt t -> repr xd d -> repr xs s -> repr xh h -> repr xm m ->
  exists o : list (option R) * list (option N) * list (option R) *
             list (option N),
    repr (vedurspa xt xd xs xh xm) o /\ vedurspa_spec t d s h m o.
Proof. exact vedurspa_correct_main. Qed.
