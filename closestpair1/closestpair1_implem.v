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

(* ================================================================== *)
(* Proofs                                                              *)
(* ================================================================== *)

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
(* PArray plumbing, restated at [array int] (universe instances)       *)
(* ------------------------------------------------------------------ *)

Lemma iget_set_same : forall (t : array int) (i v : int),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same int t i v H). Qed.

Lemma iget_set_other : forall (t : array int) (i j v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.

Lemma ilength_set : forall (t : array int) (i v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.

Lemma ilength_make : forall (n v : int),
  PArray.length (PArray.make n v) = if n <=? max_length then n else max_length.
Proof. intros n v. exact (length_make int n v). Qed.

Lemma ilength_bound : forall (t : array int), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H. rewrite Uint63.leb_spec in H.
  exact H.
Qed.

Lemma flength_bound : forall (t : array float), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length float t) as H. rewrite Uint63.leb_spec in H.
  exact H.
Qed.

Lemma to_Z_of_Z_small : forall z, (0 <= z < wB)%Z -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small; exact Hz. Qed.

Lemma wB_big : (4194304 < wB)%Z.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Reals: the float squared distance and its rounding                  *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Local Instance prec53' : FLX.Prec_gt_0 53 := eq_refl _.
Local Instance fexp64_valid' : Generic_fmt.Valid_exp fexp64 := FLT.FLT_exp_valid _ _.

Lemma rnd_opp : forall z, rnd (- z) = - rnd z.
Proof. intros z. unfold rnd. apply Round_NE.round_NE_opp. Qed.

Lemma rnd_rnd : forall z, rnd (rnd z) = rnd z.
Proof.
  intros z. apply rnd_exact. unfold rnd.
  apply Generic_fmt.generic_format_round; [exact _ | apply Generic_fmt.valid_rnd_N].
Qed.

(* the float square of the float difference d *)
Definition G (d : R) : R := rnd (rnd d * rnd d).

Lemma G_opp : forall d, G (- d) = G d.
Proof. intros d. unfold G. rewrite rnd_opp. f_equal. ring. Qed.

Lemma G_nonneg : forall d, 0 <= G d.
Proof.
  intros d. unfold G. rewrite <- rnd_0. apply rnd_le.
  pose proof (Rle_0_sqr (rnd d)). unfold Rsqr in *. lra.
Qed.

Lemma G_mono : forall d1 d2, 0 <= d1 <= d2 -> G d1 <= G d2.
Proof.
  intros d1 d2 H. unfold G. apply rnd_le.
  pose proof (rnd_le 0 d1 (proj1 H)) as H1. rewrite rnd_0 in H1.
  pose proof (rnd_le d1 d2 (proj2 H)) as H2.
  apply Rmult_le_compat; lra.
Qed.

Lemma G_abs_mono : forall d1 d2, Rabs d1 <= Rabs d2 -> G d1 <= G d2.
Proof.
  intros d1 d2 H.
  assert (E : forall d, G d = G (Rabs d)).
  { intros d. unfold Rabs. destruct (Rcase_abs d); [rewrite G_opp |]; reflexivity. }
  rewrite (E d1), (E d2). apply G_mono. split; [apply Rabs_pos | exact H].
Qed.

Definition Fd (d e : R) : R := rnd (G d + G e).

Lemma Fd_ge_l : forall d e, G d <= Fd d e.
Proof.
  intros d e. unfold Fd. pose proof (G_nonneg e).
  assert (E : G d = rnd (G d)) by (unfold G; rewrite rnd_rnd; reflexivity).
  rewrite E at 1. apply rnd_le. lra.
Qed.

Lemma Fd_ge_r : forall d e, G e <= Fd d e.
Proof.
  intros d e. unfold Fd. pose proof (G_nonneg d).
  assert (E : G e = rnd (G e)) by (unfold G; rewrite rnd_rnd; reflexivity).
  rewrite E at 1. apply rnd_le. lra.
Qed.

Lemma Fd_opp : forall d e, Fd (- d) (- e) = Fd d e.
Proof. intros d e. unfold Fd. rewrite !G_opp. reflexivity. Qed.

(* error bounds *)
Lemma abs_mul_le : forall a b A B, Rabs a <= A -> Rabs b <= B -> Rabs (a * b) <= A * B.
Proof.
  intros a b A B Ha Hb. rewrite Rabs_mult.
  apply Rmult_le_compat; auto using Rabs_pos.
Qed.

Lemma rnd_err : forall z, Rabs (rnd z - z) <= Rabs z * (u / 2) + u / 2.
Proof.
  intros z. destruct (rnd_model z) as (eps & eta & He & Ht & _ & ->).
  replace (z * (1 + eps) + eta - z) with (z * eps + eta) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_mult.
  pose proof eta_max_le_u. pose proof (Rabs_pos z).
  assert (Rabs z * Rabs eps <= Rabs z * (u / 2)) by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Lemma rnd_err_bound : forall z M, Rabs z <= M ->
  Rabs (rnd z - z) <= M * (/ 9007199254740992) + / 9007199254740992.
Proof.
  intros z M H. pose proof (rnd_err z) as E. rewrite u_val in E.
  assert (Rabs z * (/ 4503599627370496 / 2) <= M * (/ 4503599627370496 / 2))
    by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

Lemma G_err : forall d, Rabs d <= 200000 ->
  Rabs (G d - d * d) <= 138 / 10000000.
Proof.
  intros d Hd. unfold G. set (r := rnd d).
  assert (E1 : Rabs (r - d) <= 23 / 1000000000000).
  { pose proof (rnd_err_bound d 200000 Hd). unfold r. lra. }
  assert (Hr : Rabs r <= 200001).
  { replace r with ((r - d) + d) by ring.
    eapply Rle_trans; [apply Rabs_triang | lra]. }
  assert (E2 : Rabs (r * r - d * d) <= 23 / 1000000000000 * 400001).
  { replace (r * r - d * d) with ((r - d) * (r + d)) by ring. apply abs_mul_le; [exact E1 |].
    eapply Rle_trans; [apply Rabs_triang | lra]. }
  assert (E3 : Rabs (rnd (r * r) - r * r) <= 45 / 10000000).
  { pose proof (abs_mul_le r r _ _ Hr Hr) as Hrr.
    pose proof (rnd_err_bound (r * r) _ Hrr). lra. }
  replace (rnd (r * r) - d * d) with ((rnd (r * r) - r * r) + (r * r - d * d)) by ring.
  eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma Fd_err : forall d e, Rabs d <= 200000 -> Rabs e <= 200000 ->
  Rabs (Fd d e - (d * d + e * e)) <= 4 / 100000.
Proof.
  intros d e Hd He. unfold Fd. set (s := G d + G e).
  pose proof (G_err d Hd) as Gd. pose proof (G_err e He) as Ge.
  assert (Es : Rabs (s - (d * d + e * e)) <= 276 / 10000000).
  { replace (s - (d * d + e * e)) with ((G d - d * d) + (G e - e * e)) by (unfold s; ring).
    eapply Rle_trans; [apply Rabs_triang | lra]. }
  pose proof (abs_mul_le d d _ _ Hd Hd) as Hdd.
  pose proof (abs_mul_le e e _ _ He He) as Hee.
  assert (Hs : Rabs s <= 80000000001).
  { replace s with ((s - (d * d + e * e)) + (d * d + e * e)) by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    pose proof (Rabs_triang (d * d) (e * e)). lra. }
  pose proof (rnd_err_bound s _ Hs) as Er.
  replace (rnd s - (d * d + e * e)) with ((rnd s - s) + (s - (d * d + e * e))) by ring.
  eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Local Close Scope R_scope.

(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* The float computations against the reals                            *)
(* ------------------------------------------------------------------ *)

Lemma bpow_big : (1000000000000 <= Raux.bpow Zaux.radix2 1000)%R.
Proof.
  pose proof (Raux.bpow_le Zaux.radix2 40 1000 ltac:(lia)) as H.
  change (Raux.bpow Zaux.radix2 40) with 1099511627776%R in H. lra.
Qed.

Lemma no_ovf : forall z, (Rabs z <= 1000000000000)%R ->
  (Rabs (rnd z) < Raux.bpow Zaux.radix2 1024)%R.
Proof. intros z H. apply rnd_no_overflow_small. pose proof bpow_big. lra. Qed.

Lemma rnd_abs : forall z M, (Rabs z <= M)%R -> (Rabs (rnd z) <= 2 * M + 1)%R.
Proof.
  intros z M H. pose proof (rnd_err_bound z M H) as E. pose proof (Rabs_pos z).
  replace (rnd z) with ((rnd z - z) + z)%R by ring.
  eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma repr_sq_diff : forall (fa fb : float) ra rb, repr fa ra -> repr fb rb ->
  (Rabs ra <= 100000)%R -> (Rabs rb <= 100000)%R ->
  repr ((fa - fb) * (fa - fb))%float (G (ra - rb)) /\ (Rabs (G (ra - rb)) <= 400000000000)%R.
Proof.
  intros fa fb ra rb Ha Hb Ba Bb.
  assert (Hd : (Rabs (ra - rb) <= 200000)%R).
  { unfold Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
  assert (H1 : repr (fa - fb)%float (rnd (ra - rb))) by (apply repr_sub; auto; apply no_ovf; lra).
  pose proof (rnd_abs _ _ Hd) as Hr.
  pose proof (abs_mul_le _ _ _ _ Hr Hr) as Hrr.
  split.
  - apply repr_mul; auto. apply no_ovf. lra.
  - unfold G. pose proof (rnd_abs _ _ Hrr). lra.
Qed.

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

Local Notation bp := (Raux.bpow Zaux.radix2).

Definition dval (d : Z * Z) : R := (IZR (fst d) * bp (snd d))%R.

Lemma IZR_pow2 : forall k, (0 <= k)%Z -> IZR (2 ^ k) = bp k.
Proof. intros k Hk. destruct k as [| p | p]; [reflexivity | reflexivity | lia]. Qed.

Lemma dal_val : forall d e, (e <= snd d)%Z -> (IZR (dal d e) * bp e = dval d)%R.
Proof.
  intros d e He. unfold dal, dval. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite mult_IZR, IZR_pow2 by lia. rewrite Rmult_assoc, <- Raux.bpow_plus.
  f_equal. f_equal. lia.
Qed.

Lemma dval_dadd : forall a b, dval (dadd a b) = (dval a + dval b)%R.
Proof.
  intros a b. unfold dadd. cbv zeta.
  rewrite <- (dal_val a (Z.min (snd a) (snd b))) by lia.
  rewrite <- (dal_val b (Z.min (snd a) (snd b))) by lia.
  unfold dval; simpl. rewrite plus_IZR. ring.
Qed.

Lemma dval_dsub : forall a b, dval (dsub a b) = (dval a - dval b)%R.
Proof.
  intros a b. unfold dsub. cbv zeta.
  rewrite <- (dal_val a (Z.min (snd a) (snd b))) by lia.
  rewrite <- (dal_val b (Z.min (snd a) (snd b))) by lia.
  unfold dval; simpl. rewrite minus_IZR. ring.
Qed.

Lemma dval_dmul : forall a b, dval (dmul a b) = (dval a * dval b)%R.
Proof.
  intros a b. unfold dmul, dval; simpl. rewrite mult_IZR, Raux.bpow_plus. ring.
Qed.

Lemma dlt_iff : forall a b, dlt a b = true <-> (dval a < dval b)%R.
Proof.
  intros a b. unfold dlt. cbv zeta. rewrite Z.ltb_lt.
  rewrite <- (dal_val a (Z.min (snd a) (snd b))) by lia.
  rewrite <- (dal_val b (Z.min (snd a) (snd b))) by lia.
  pose proof (Raux.bpow_gt_0 Zaux.radix2 (Z.min (snd a) (snd b))).
  split; intros H'.
  - apply Rmult_lt_compat_r; [exact H | apply IZR_lt; exact H'].
  - apply lt_IZR. eapply Rmult_lt_reg_r; [exact H | exact H'].
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

Lemma dex_val4 : forall xa xb ya yb ra rb sa sb,
  repr xa ra -> repr xb rb -> repr ya sa -> repr yb sb ->
  dval (dadd (dmul (dsub (fex xa) (fex xb)) (dsub (fex xa) (fex xb)))
             (dmul (dsub (fex ya) (fex yb)) (dsub (fex ya) (fex yb)))) =
  ((ra - rb) * (ra - rb) + (sa - sb) * (sa - sb))%R.
Proof.
  intros. rewrite dval_dadd, !dval_dmul, !dval_dsub, !(fex_val _ _ H), !(fex_val _ _ H0),
    !(fex_val _ _ H1), !(fex_val _ _ H2). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The bucket key                                                      *)
(* ------------------------------------------------------------------ *)

Lemma repr_c1e5 : repr c1e5 100000%R.
Proof. exact (repr_of_uint63_exact 100000 eq_refl). Qed.

Lemma repr_c52 : repr c52 4503599627370496%R.
Proof. exact (repr_of_uint63_exact 4503599627370496 eq_refl). Qed.

Lemma repr_cinit : repr cinit 200001%R.
Proof. exact (repr_of_uint63_exact 200001 eq_refl). Qed.

(* the mantissa of an integer-valued float of [2^52, 2^53) is that integer *)
Lemma mant_val : forall (u : float) ur, repr u ur ->
  (4503599627370496 <= ur < 9007199254740992)%R ->
  IZR (to_Z (normfr_mantissa (fst (frshiftexp u)))) = ur.
Proof.
  intros f r Hf Hr.
  pose proof Hf as Hf'. apply repr_float_iff in Hf' as [Fin Ev].
  pose proof (Flocq.IEEE754.PrimFloat.frshiftexp_equiv f) as Fr.
  destruct (frshiftexp f) as [z e]. simpl fst.
  rewrite Flocq.IEEE754.PrimFloat.normfr_mantissa_equiv.
  revert Fr Fin Ev.
  destruct (Flocq.IEEE754.PrimFloat.Prim2B f) as [s|s| |s m ex Hb]; intros Fr Fin Ev; try discriminate.
  - simpl in Ev. lra.
  - pose proof (BinarySingleNaN.Bfrexp_correct FloatOps.prec FloatOps.emax Flocq.IEEE754.PrimFloat.Hprec (BinarySingleNaN.B754_finite s m ex Hb) eq_refl) as C.
    rewrite <- Fr in C. destruct C as [E1 C]. destruct (C eq_refl) as [Hz Hm]. clear C.
    rewrite Ev in E1, Hm.
    assert (Mg : Raux.mag_val Zaux.radix2 r (Raux.mag Zaux.radix2 r) = 53%Z).
    { apply Raux.mag_unique. rewrite Rabs_right by lra.
      change (bp (53 - 1)) with 4503599627370496%R. change (bp 53) with 9007199254740992%R. lra. }
    rewrite Mg in Hm. rewrite Hm in E1.
    pose proof (BinarySingleNaN.Bnormfr_mantissa_correct FloatOps.prec FloatOps.emax Flocq.IEEE754.PrimFloat.Hmax (Flocq.IEEE754.PrimFloat.Prim2B z) Hz) as Nm.
    destruct (Flocq.IEEE754.PrimFloat.Prim2B z) as [| | |s' m' e' Hb']; try contradiction.
    destruct Nm as [Nm [_ Ee]]. rewrite Nm. subst e'. clear Hz Fr Nm.
    cbn [BinarySingleNaN.B2R] in E1. unfold Defs.F2R in E1; simpl Defs.Fnum in E1; simpl Defs.Fexp in E1.
    rewrite Rmult_assoc, <- Raux.bpow_plus in E1. change (bp (-53 + 53)) with 1%R in E1.
    rewrite Rmult_1_r in E1. rewrite E1.
    destruct s'; simpl Zaux.cond_Zopp in *; [| reflexivity].
    exfalso. assert (IZR (Zneg m') < 0)%R by (apply IZR_lt; lia). lra.
Qed.

Local Open Scope R_scope.

Definition U (sr r : R) : R := rnd (rnd (rnd (r + 100000) * sr) + 4503599627370496).

Lemma U_mono : forall sr r r', 0 <= sr -> r <= r' -> U sr r <= U sr r'.
Proof.
  intros sr r r' Hs H. unfold U. apply rnd_le. apply Rplus_le_compat_r. apply rnd_le.
  apply Rmult_le_compat_r; [exact Hs |]. apply rnd_le. lra.
Qed.

Lemma U_spec : forall (s f : float) sr r, repr s sr -> 0 <= sr <= 2 -> repr f r -> Rabs r <= 100000 ->
  repr ((f + c1e5) * s + c52)%float (U sr r) /\
  4503599627370496 <= U sr r <= 4503599627370496 + 4194304.
Proof.
  intros s f sr r Hs Bs Hf Br.
  assert (B1 : Rabs (r + 100000) <= 200000) by (apply Rabs_le; apply Raux.Rabs_le_inv in Br; lra).
  assert (R1 : repr (f + c1e5)%float (rnd (r + 100000))) by (apply repr_add; auto using repr_c1e5; apply no_ovf; lra).
  pose proof (rnd_abs _ _ B1) as A1.
  assert (P1 : 0 <= rnd (r + 100000)) by (rewrite <- rnd_0; apply rnd_le; apply Raux.Rabs_le_inv in Br; lra).
  assert (B2 : Rabs (rnd (r + 100000) * sr) <= 800002).
  { rewrite Rabs_mult. rewrite (Rabs_right sr) by lra. apply Raux.Rabs_le_inv in A1.
    rewrite Rabs_right by lra. nra. }
  assert (R2 : repr ((f + c1e5) * s)%float (rnd (rnd (r + 100000) * sr))) by (apply repr_mul; auto; apply no_ovf; lra).
  pose proof (rnd_abs _ _ B2) as A2.
  assert (P2 : 0 <= rnd (rnd (r + 100000) * sr)) by (rewrite <- rnd_0; apply rnd_le; nra).
  apply Raux.Rabs_le_inv in A2.
  split.
  - apply repr_add; auto using repr_c52. apply rnd_no_overflow_small. rewrite Rabs_right by lra.
    pose proof (Raux.bpow_le Zaux.radix2 60 1000 ltac:(lia)) as H60.
    change (bp 60) with 1152921504606846976 in H60. lra.
  - unfold U. split.
    + rewrite <- (rnd_IZR 4503599627370496) at 1 by lia. apply rnd_le. lra.
    + replace (4503599627370496 + 4194304) with (IZR 4503599627370496 + IZR 4194304) by reflexivity.
      rewrite <- plus_IZR. rewrite <- (rnd_IZR (4503599627370496 + 4194304)) by lia.
      apply rnd_le. rewrite plus_IZR. lra.
Qed.

Lemma key_val : forall (s f : float) sr r (n1 : int), repr s sr -> 0 <= sr <= 2 -> repr f r ->
  Rabs r <= 100000 ->
  exists m : Z, IZR m = U sr r /\ (4503599627370496 <= m <= 4503599627370496 + 4194304)%Z /\
    to_Z (key s n1 f) = Z.min (m - 4503599627370496) (to_Z n1).
Proof.
  intros s f sr r n1 Hs Bs Hf Br.
  destruct (U_spec s f sr r Hs Bs Hf Br) as [Ru Bu].
  pose proof (mant_val _ _ Ru ltac:(lra)) as Em.
  set (M := normfr_mantissa _) in Em.
  exists (to_Z M). split; [exact Em |].
  assert (BM : (4503599627370496 <= to_Z M <= 4503599627370496 + 4194304)%Z).
  { rewrite <- Em in Bu. destruct Bu as [B1 B2]. split; [apply le_IZR; exact B1 |].
    apply le_IZR. rewrite plus_IZR. exact B2. }
  split; [exact BM |].
  unfold key. cbv zeta. fold M.
  assert (Ek : to_Z (M - 4503599627370496) = (to_Z M - 4503599627370496)%Z) by sia.
  destruct (M - 4503599627370496 <? n1)%uint63 eqn:Elt.
  - rewrite Uint63.ltb_spec in Elt. lia.
  - assert (~ (to_Z (M - 4503599627370496) < to_Z n1)%Z) by (rewrite <- Uint63.ltb_spec; congruence). lia.
Qed.

Local Close Scope R_scope.

(* ------------------------------------------------------------------ *)
(* The float filters against the exact squared distances               *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Lemma tol_spec : exists tr, repr tol tr /\ 1 / 2000 <= tr <= 1.
Proof.
  assert (H1 : repr (of_uint63 1) 1) by exact (repr_of_uint63_exact 1 eq_refl).
  assert (H2 : repr (of_uint63 1024) 1024) by exact (repr_of_uint63_exact 1024 eq_refl).
  exists (rnd (1 / 1024)). split.
  - unfold tol. apply repr_div; [exact H1 | exact H2 | lra | apply no_ovf; rewrite Rabs_right; lra].
  - assert (Rabs (1 / 1024) <= 1) by (rewrite Rabs_right; lra).
    pose proof (rnd_err_bound (1 / 1024) 1 H) as E. apply Raux.Rabs_le_inv in E. lra.
Qed.

(* bf + tol < f in floats: the candidate is strictly farther than the best *)
Lemma worse_ok : forall bfr fr Db Dc tr,
  Rabs (bfr - Db) <= 4 / 100000 -> Rabs (fr - Dc) <= 4 / 100000 ->
  1 / 2000 <= tr <= 1 -> Rabs bfr <= 100000000000 ->
  rnd (bfr + tr) < fr -> Db < Dc.
Proof.
  intros bfr fr Db Dc tr E1 E2 Bt Bb H.
  assert (Rabs (bfr + tr) <= 100000000001).
  { eapply Rle_trans; [apply Rabs_triang |]. rewrite (Rabs_right tr) by lra. lra. }
  pose proof (rnd_err_bound _ _ H0) as E. apply Raux.Rabs_le_inv in E, E1, E2. lra.
Qed.

(* bf + tol < G d in floats: d^2 is strictly more than the best *)
Lemma prune_ok : forall bfr g Db d tr,
  Rabs (bfr - Db) <= 4 / 100000 -> Rabs (g - d * d) <= 138 / 10000000 ->
  1 / 2000 <= tr <= 1 -> Rabs bfr <= 100000000000 ->
  rnd (bfr + tr) < g -> Db < d * d.
Proof.
  intros bfr g Db d tr E1 E2 Bt Bb H.
  assert (Rabs (bfr + tr) <= 100000000001).
  { eapply Rle_trans; [apply Rabs_triang |]. rewrite (Rabs_right tr) by lra. lra. }
  pose proof (rnd_err_bound _ _ H0) as E. apply Raux.Rabs_le_inv in E, E1, E2. lra.
Qed.

Local Close Scope R_scope.

(* ------------------------------------------------------------------ *)
(* The main proof                                                      *)
(* ------------------------------------------------------------------ *)

Section Main.
Variables (xs ys : list R) (x y : array float).
Hypothesis Hv : valid_input xs ys.
Hypothesis Hx : repr x xs.
Hypothesis Hy : repr y ys.

Definition X (a : int) : R := nth (Z.to_nat (to_Z a)) xs 0%R.
Definition Y (a : int) : R := nth (Z.to_nat (to_Z a)) ys 0%R.
Definition Pd (a : int) : Prop := (to_Z a < to_Z (PArray.length x))%Z.
Definition F (a b : int) : R := Fd (X a - X b) (Y a - Y b).

Lemma len_x : Z.of_nat (List.length xs) = to_Z (PArray.length x).
Proof. exact (proj1 Hx). Qed.

Lemma len_y : Z.of_nat (List.length ys) = to_Z (PArray.length x).
Proof.
  rewrite <- len_x. pose proof (vi_ys _ _ Hv) as E. unfold len in E. lia.
Qed.

Lemma n_bounds : (2 <= to_Z (PArray.length x) <= 100000)%Z.
Proof. rewrite <- len_x. pose proof (vi_n _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma length_y : PArray.length y = PArray.length x.
Proof. apply to_Z_inj. pose proof len_y. destruct Hy as [E _]. exact (eq_trans (eq_sym E) H). Qed.

Lemma repr_nth : forall (l : list R) (t : array float) (a : int), repr t l ->
  (to_Z a < Z.of_nat (List.length l))%Z -> repr t.[a] (nth (Z.to_nat (to_Z a)) l 0%R).
Proof.
  intros l t a [_ H] Ha. destruct (H (Z.to_nat (to_Z a)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded a); lia).
  rewrite of_to_Z in R. exact R.
Qed.

Lemma repr_X : forall a, Pd a -> repr x.[a] (X a).
Proof. intros a Ha. unfold X. refine (repr_nth xs x a Hx _). rewrite len_x; exact Ha. Qed.

Lemma repr_Y : forall a, Pd a -> repr y.[a] (Y a).
Proof. intros a Ha. unfold Y. refine (repr_nth ys y a Hy _). rewrite len_y; exact Ha. Qed.

Lemma bound_nth : forall (l : list R) (a : int), Forall (fun c => Rabs c <= 100000)%R l ->
  (to_Z a < Z.of_nat (List.length l))%Z -> (Rabs (nth (Z.to_nat (to_Z a)) l 0%R) <= 100000)%R.
Proof.
  intros l a H Ha. rewrite Forall_forall in H. apply H, nth_In. lia.
Qed.

Lemma X_bound : forall a, Pd a -> (Rabs (X a) <= 100000)%R.
Proof. intros a Ha. apply bound_nth; [exact (vi_x _ _ Hv) | rewrite len_x; exact Ha]. Qed.

Lemma Y_bound : forall a, Pd a -> (Rabs (Y a) <= 100000)%R.
Proof. intros a Ha. apply bound_nth; [exact (vi_y _ _ Hv) | rewrite len_y; exact Ha]. Qed.

Lemma repr_fd : forall a b, Pd a -> Pd b -> repr (fd x y a b) (F a b).
Proof.
  intros a b Ha Hb. unfold fd, F, Fd. cbv zeta.
  destruct (repr_sq_diff _ _ _ _ (repr_X a Ha) (repr_X b Hb) (X_bound a Ha) (X_bound b Hb)) as [R1 B1].
  destruct (repr_sq_diff _ _ _ _ (repr_Y a Ha) (repr_Y b Hb) (Y_bound a Ha) (Y_bound b Hb)) as [R2 B2].
  apply repr_add; auto. apply no_ovf.
  eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma F_sym : forall a b, F a b = F b a.
Proof.
  intros a b. unfold F. rewrite <- Fd_opp. f_equal; ring.
Qed.

Lemma ilength_make_n : forall v : int, PArray.length (PArray.make (PArray.length x) v) = PArray.length x.
Proof.
  intros v. rewrite ilength_make. pose proof (flength_bound x) as H.
  replace (PArray.length x <=? max_length) with true; [reflexivity |].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma flength_make_n : forall v : float, PArray.length (PArray.make (PArray.length x) v) = PArray.length x.
Proof.
  intros v. pose proof (length_make float (PArray.length x) v) as E.
  pose proof (flength_bound x) as H.
  replace (PArray.length x <=? max_length) with true in E; [exact E |].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma add1_small : forall v : int, (to_Z v < 4194304)%Z -> to_Z (v + 1) = (to_Z v + 1)%Z.
Proof. intros v H. pose proof (to_Z_bounded v). sia. Qed.

Lemma add_small : forall a b : int, (to_Z a < 4194304)%Z -> (to_Z b < 4194304)%Z ->
  to_Z (a + b) = (to_Z a + to_Z b)%Z.
Proof. intros a b H1 H2. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). sia. Qed.

Lemma iget_make : forall (m i v : int), (PArray.make m v : array int).[i] = v.
Proof. intros m i v. exact (get_make int v m i). Qed.

Lemma fget_set_same : forall (t : array float) (i : int) (v : float),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same float t i v H). Qed.

Lemma fget_set_other : forall (t : array float) (i j : int) (v : float),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other float t i j v H). Qed.

Lemma flength_set : forall (t : array float) (i : int) (v : float),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set float t i v). Qed.

Lemma fget_make : forall (m i : int) (v : float), (PArray.make m v : array float).[i] = v.
Proof. intros m i v. exact (get_make float v m i). Qed.

Lemma succ_Z : forall j : int, (to_Z j < to_Z (PArray.length x))%Z -> to_Z (j + 1) = (to_Z j + 1)%Z.
Proof. intros j H. pose proof (flength_bound x). sia. Qed.

(* -- The bucket key of point a. -- *)

Definition sf : float := (of_uint63 (PArray.length x) / cinit)%float.
Definition sr : R := rnd (IZR (to_Z (PArray.length x)) / 200001).

Lemma sr_spec : repr sf sr /\ (0 <= sr <= 2)%R.
Proof.
  pose proof n_bounds as Hn.
  assert (B : (0 <= IZR (to_Z (PArray.length x)) / 200001 <= 1)%R).
  { assert (0 <= IZR (to_Z (PArray.length x)) <= 100000)%R by (split; apply IZR_le; lia).
    split; [apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra] |].
    apply Rmult_le_reg_r with 200001%R; [lra |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  split.
  - unfold sf, sr. apply repr_div; [apply repr_of_uint63_exact; lia | exact repr_cinit | lra |].
    apply no_ovf. rewrite Rabs_right; lra.
  - assert (Rabs (IZR (to_Z (PArray.length x)) / 200001) <= 1)%R by (rewrite Rabs_right; lra).
    pose proof (rnd_err_bound _ _ H) as E. apply Raux.Rabs_le_inv in E. unfold sr. split.
    + rewrite <- rnd_0. apply rnd_le. lra.
    + lra.
Qed.

Definition n1 : int := PArray.length x - 1.

Definition Kf (a : int) : int := key sf n1 x.[a].

Lemma Kf_bound : forall a, Pd a -> (0 <= to_Z (Kf a) < to_Z (PArray.length x))%Z.
Proof.
  intros a Ha. pose proof n_bounds.
  destruct (key_val sf x.[a] sr (X a) n1 (proj1 sr_spec) (proj2 sr_spec) (repr_X a Ha) (X_bound a Ha))
    as (m & _ & Bm & E).
  unfold Kf. assert (to_Z n1 = to_Z (PArray.length x) - 1)%Z by (unfold n1; sia).
  pose proof (to_Z_bounded (key sf n1 x.[a])). lia.
Qed.

Lemma Kf_mono : forall a b, Pd a -> Pd b -> (X a <= X b)%R -> (to_Z (Kf a) <= to_Z (Kf b))%Z.
Proof.
  intros a b Ha Hb H.
  destruct (key_val sf x.[a] sr (X a) n1 (proj1 sr_spec) (proj2 sr_spec) (repr_X a Ha) (X_bound a Ha))
    as (m & Em & _ & E).
  destruct (key_val sf x.[b] sr (X b) n1 (proj1 sr_spec) (proj2 sr_spec) (repr_X b Hb) (X_bound b Hb))
    as (m' & Em' & _ & E').
  pose proof (U_mono sr (X a) (X b) (proj1 (proj2 sr_spec)) H) as U1.
  rewrite <- Em, <- Em' in U1. apply le_IZR in U1. unfold Kf. lia.
Qed.

Lemma Kf_lt : forall a b, Pd a -> Pd b -> (to_Z (Kf a) < to_Z (Kf b))%Z -> (X a < X b)%R.
Proof.
  intros a b Ha Hb H. destruct (Rlt_or_le (X a) (X b)) as [L | L]; [exact L |].
  pose proof (Kf_mono b a Hb Ha L). lia.
Qed.

(* -- Counting, on the Prop side. -- *)

Definition KZ (i : nat) : Z := to_Z (Kf (of_Z (Z.of_nat i))).

Fixpoint cnt (k : nat) (b : Z) : nat :=
  match k with O => O | S k' => (cnt k' b + if Z.eqb (KZ k') b then 1 else 0)%nat end.

Fixpoint blw (k : nat) (b : Z) : nat :=
  match k with O => O | S k' => (blw k' b + if Z.ltb (KZ k') b then 1 else 0)%nat end.

Definition NN : nat := Z.to_nat (to_Z (PArray.length x)).

Lemma KZ_int : forall j, KZ (Z.to_nat (to_Z j)) = to_Z (Kf j).
Proof.
  intros j. unfold KZ. rewrite Z2Nat.id by (pose proof (to_Z_bounded j); lia).
  rewrite of_to_Z. reflexivity.
Qed.

Lemma KZ_nonneg : forall i, (0 <= KZ i)%Z.
Proof. intros i. unfold KZ. pose proof (to_Z_bounded (Kf (of_Z (Z.of_nat i)))). lia. Qed.

Lemma cnt_le : forall k b, (cnt k b <= k)%nat.
Proof. induction k as [| k IH]; intros b; simpl; [lia |]. pose proof (IH b). destruct Z.eqb; lia. Qed.

Lemma blw_le : forall k b, (blw k b <= k)%nat.
Proof. induction k as [| k IH]; intros b; simpl; [lia |]. pose proof (IH b). destruct Z.ltb; lia. Qed.

Lemma blw_0 : forall k, blw k 0 = O.
Proof.
  induction k as [| k IH]; simpl; [reflexivity |]. rewrite IH.
  pose proof (KZ_nonneg k). destruct (Z.ltb_spec (KZ k) 0); lia.
Qed.

Lemma blw_succ : forall k b, blw k (b + 1) = (blw k b + cnt k b)%nat.
Proof.
  induction k as [| k IH]; intros b; simpl; [reflexivity |]. rewrite IH.
  destruct (Z.ltb_spec (KZ k) (b + 1)), (Z.ltb_spec (KZ k) b), (Z.eqb_spec (KZ k) b); lia.
Qed.

Lemma cnt_mono : forall k k' b, (k <= k')%nat -> (cnt k b <= cnt k' b)%nat.
Proof. intros k k' b H. induction H; simpl; [lia |]. destruct Z.eqb; lia. Qed.

Lemma blw_mono : forall k b b', (b <= b')%Z -> (blw k b <= blw k b')%nat.
Proof.
  induction k as [| k IH]; intros b b' H; simpl; [lia |]. pose proof (IH b b' H).
  destruct (Z.ltb_spec (KZ k) b), (Z.ltb_spec (KZ k) b'); lia.
Qed.

Lemma cnt_hit : forall i k, (i < k)%nat -> (cnt i (KZ i) < cnt k (KZ i))%nat.
Proof.
  intros i k H. apply Nat.lt_le_trans with (cnt (S i) (KZ i)).
  - simpl. rewrite Z.eqb_refl. lia.
  - apply cnt_mono. lia.
Qed.

(* the position of point i in the bucket order *)
Definition pos (i : nat) : nat := (blw NN (KZ i) + cnt i (KZ i))%nat.

Lemma blw_cnt_lt : forall b b', (b < b')%Z -> (blw NN b + cnt NN b <= blw NN b')%nat.
Proof. intros b b' H. rewrite <- blw_succ. apply blw_mono. lia. Qed.

Lemma pos_lt : forall i, (i < NN)%nat -> (pos i < NN)%nat.
Proof.
  intros i H. unfold pos. pose proof (cnt_hit i NN H).
  pose proof (blw_succ NN (KZ i)). pose proof (blw_le NN (KZ i + 1)). lia.
Qed.

Lemma pos_order : forall i j, (i < NN)%nat -> (KZ i < KZ j)%Z -> (pos i < pos j)%nat.
Proof.
  intros i j Hi H. unfold pos. pose proof (cnt_hit i NN Hi).
  pose proof (blw_cnt_lt (KZ i) (KZ j) H). lia.
Qed.

Lemma pos_inj : forall i j, (i < NN)%nat -> (j < NN)%nat -> pos i = pos j -> i = j.
Proof.
  intros i j Hi Hj E.
  destruct (Z.lt_trichotomy (KZ i) (KZ j)) as [L | [L | L]].
  - pose proof (pos_order i j Hi L). lia.
  - unfold pos in E. rewrite L in E.
    destruct (Nat.lt_trichotomy i j) as [l | [l | l]]; [| exact l |].
    + pose proof (cnt_hit i j l) as C. rewrite L in C. lia.
    + pose proof (cnt_hit j i l) as C. lia.
  - pose proof (pos_order j i Hj L). lia.
Qed.

Lemma pos_surj : forall c, (c < NN)%nat -> exists i, (i < NN)%nat /\ pos i = c.
Proof.
  intros c Hc. set (l := map pos (seq 0 NN)).
  assert (ND : NoDup l).
  { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
    intros a b Ha Hb E. apply in_seq in Ha, Hb. apply pos_inj; lia. }
  assert (Inc : incl l (seq 0 NN)).
  { intros a Ha. apply in_map_iff in Ha as (i & <- & Hi). apply in_seq in Hi. apply in_seq.
    pose proof (pos_lt i ltac:(lia)). lia. }
  assert (Hl : (List.length (seq 0 NN) <= List.length l)%nat) by (unfold l; rewrite length_map; lia).
  pose proof (NoDup_length_incl ND Hl Inc c ltac:(apply in_seq; lia)) as G.
  apply in_map_iff in G as (i & E & Hi). apply in_seq in Hi. exists i. split; [lia | exact E].
Qed.

(* -- The four passes of the bucket sort. -- *)

Definition KY : array int :=
  loop (PArray.length x) (fun _ _ => true) (key_step x sf n1) 0 (PArray.make (PArray.length x) 0).

Lemma KY_spec : PArray.length KY = PArray.length x /\ forall i, Pd i -> KY.[i] = Kf i.
Proof.
  pose proof n_bounds.
  assert (G : (fun k (K : array int) => PArray.length K = PArray.length x /\
     (forall i, (to_Z i < to_Z k)%Z -> K.[i] = Kf i)) (PArray.length x) KY).
  { unfold KY. apply (for_inv (fun k (K : array int) => PArray.length K = PArray.length x /\
     (forall i, (to_Z i < to_Z k)%Z -> K.[i] = Kf i))).
    - change (to_Z 0) with 0%Z. lia.
    - split; [apply ilength_make_n |]. intros i Hi. change (to_Z 0) with 0%Z in Hi.
      pose proof (to_Z_bounded i). lia.
    - intros j K Hj [HL HK]. unfold key_step. split; [rewrite ilength_set; exact HL |].
      intros i Hi. rewrite (succ_Z j) in Hi by lia.
      destruct (Z.eq_dec (to_Z i) (to_Z j)) as [E | E].
      + apply to_Z_inj in E. subst i. apply iget_set_same. rewrite Uint63.ltb_spec, HL. lia.
      + rewrite iget_set_other by (intros ->; lia). apply HK. lia. }
  exact G.
Qed.

Definition CT : array int :=
  loop (PArray.length x) (fun _ _ => true) (count_step KY) 0 (PArray.make (PArray.length x) 0).

Lemma CT_spec : PArray.length CT = PArray.length x /\
  forall b, (to_Z b < to_Z (PArray.length x))%Z -> to_Z CT.[b] = Z.of_nat (cnt NN (to_Z b)).
Proof.
  pose proof n_bounds. destruct KY_spec as [_ HK].
  assert (G : (fun k (C : array int) => PArray.length C = PArray.length x /\
     (forall b, (to_Z b < to_Z (PArray.length x))%Z ->
        to_Z C.[b] = Z.of_nat (cnt (Z.to_nat (to_Z k)) (to_Z b)))) (PArray.length x) CT).
  { unfold CT. apply (for_inv (fun k (C : array int) => PArray.length C = PArray.length x /\
     (forall b, (to_Z b < to_Z (PArray.length x))%Z ->
        to_Z C.[b] = Z.of_nat (cnt (Z.to_nat (to_Z k)) (to_Z b))))).
    - change (to_Z 0) with 0%Z. lia.
    - split; [apply ilength_make_n |]. intros b Hb. rewrite iget_make. reflexivity.
    - intros j C Hj [HL HC]. assert (Pj : Pd j) by (unfold Pd; lia).
      unfold count_step. rewrite (HK j Pj).
      assert (Ej : Z.to_nat (to_Z (j + 1)) = S (Z.to_nat (to_Z j))) by (rewrite (succ_Z j) by lia; lia).
      pose proof (Kf_bound j Pj) as Bj.
      split; [rewrite ilength_set; exact HL |].
      intros b Hb. rewrite Ej. cbn [cnt]. rewrite KZ_int.
      destruct (Z.eq_dec (to_Z b) (to_Z (Kf j))) as [E | E].
      + apply to_Z_inj in E. subst b. rewrite iget_set_same by (rewrite Uint63.ltb_spec, HL; lia).
        rewrite Z.eqb_refl. pose proof (HC (Kf j) Hb) as E1.
        pose proof (cnt_le (Z.to_nat (to_Z j)) (to_Z (Kf j))).
        rewrite add1_small by lia. lia.
      + rewrite iget_set_other by (intros E'; apply E; rewrite E'; reflexivity).
        rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite HC by exact Hb. lia. }
  destruct G as [G1 G2]. split; [exact G1 |]. exact G2.
Qed.

Definition PS : array int * int :=
  loop (PArray.length x) (fun _ _ => true) prefix_step 0 (CT, 0).

Lemma PS_spec : PArray.length (fst PS) = PArray.length x /\
  forall b, (to_Z b < to_Z (PArray.length x))%Z -> to_Z (fst PS).[b] = Z.of_nat (blw NN (to_Z b)).
Proof.
  pose proof n_bounds. destruct CT_spec as [LC HC].
  assert (G : (fun j (st : array int * int) => PArray.length (fst st) = PArray.length x /\
     to_Z (snd st) = Z.of_nat (blw NN (to_Z j)) /\
     (forall b, (to_Z b < to_Z j)%Z -> to_Z (fst st).[b] = Z.of_nat (blw NN (to_Z b))) /\
     (forall b, (to_Z j <= to_Z b < to_Z (PArray.length x))%Z ->
        to_Z (fst st).[b] = Z.of_nat (cnt NN (to_Z b)))) (PArray.length x) PS).
  { unfold PS. apply (for_inv (fun j (st : array int * int) => PArray.length (fst st) = PArray.length x /\
     to_Z (snd st) = Z.of_nat (blw NN (to_Z j)) /\
     (forall b, (to_Z b < to_Z j)%Z -> to_Z (fst st).[b] = Z.of_nat (blw NN (to_Z b))) /\
     (forall b, (to_Z j <= to_Z b < to_Z (PArray.length x))%Z ->
        to_Z (fst st).[b] = Z.of_nat (cnt NN (to_Z b))))).
    - change (to_Z 0) with 0%Z. lia.
    - simpl. split; [exact LC |]. change (to_Z 0) with 0%Z. rewrite blw_0. split; [reflexivity |].
      split; [intros b Hb; pose proof (to_Z_bounded b); lia |]. intros b Hb. apply HC. lia.
    - intros j [C acc] Hj (HL & HA & H1 & H2). simpl in HL, HA, H1, H2. unfold prefix_step. simpl.
      rewrite (succ_Z j) by lia.
      assert (Cj : to_Z C.[j] = Z.of_nat (cnt NN (to_Z j))) by (apply H2; lia).
      pose proof (blw_succ NN (to_Z j)) as Bs. pose proof (blw_le NN (to_Z j + 1)) as Bl.
      assert (NNv : Z.of_nat NN = to_Z (PArray.length x)) by (unfold NN; lia).
      split; [rewrite ilength_set; exact HL |].
      split; [rewrite add_small by lia; lia |].
      split.
      + intros b Hb. destruct (Z.eq_dec (to_Z b) (to_Z j)) as [E | E].
        * apply to_Z_inj in E. subst b. rewrite iget_set_same by (rewrite Uint63.ltb_spec, HL; lia).
          exact HA.
        * rewrite iget_set_other by (intros ->; lia). apply H1. lia.
      + intros b Hb. rewrite iget_set_other by (intros ->; lia). apply H2. lia. }
  destruct G as (G1 & _ & G2 & _). split; [exact G1 |]. intros b Hb. apply G2. exact Hb.
Qed.

Definition PL : array int * array int :=
  loop (PArray.length x) (fun _ _ => true) (place_step KY) 0 (PArray.make (PArray.length x) 0, fst PS).

Lemma PL_spec : PArray.length (fst PL) = PArray.length x /\
  forall i, (i < NN)%nat -> to_Z (fst PL).[of_Z (Z.of_nat (pos i))] = Z.of_nat i.
Proof.
  pose proof n_bounds. destruct KY_spec as [_ HK]. destruct PS_spec as [LS HS].
  assert (NNv : Z.of_nat NN = to_Z (PArray.length x)) by (unfold NN; lia).
  assert (G : (fun j (st : array int * array int) =>
     PArray.length (fst st) = PArray.length x /\ PArray.length (snd st) = PArray.length x /\
     (forall b, (to_Z b < to_Z (PArray.length x))%Z ->
        to_Z (snd st).[b] = Z.of_nat (blw NN (to_Z b) + cnt (Z.to_nat (to_Z j)) (to_Z b))) /\
     (forall i, (i < Z.to_nat (to_Z j))%nat ->
        to_Z (fst st).[of_Z (Z.of_nat (pos i))] = Z.of_nat i)) (PArray.length x) PL).
  { unfold PL. apply (for_inv (fun j (st : array int * array int) =>
     PArray.length (fst st) = PArray.length x /\ PArray.length (snd st) = PArray.length x /\
     (forall b, (to_Z b < to_Z (PArray.length x))%Z ->
        to_Z (snd st).[b] = Z.of_nat (blw NN (to_Z b) + cnt (Z.to_nat (to_Z j)) (to_Z b))) /\
     (forall i, (i < Z.to_nat (to_Z j))%nat ->
        to_Z (fst st).[of_Z (Z.of_nat (pos i))] = Z.of_nat i))).
    - change (to_Z 0) with 0%Z. lia.
    - simpl. split; [apply ilength_make_n |]. split; [exact LS |].
      split; [intros b Hb; rewrite HS by exact Hb; change (to_Z 0) with 0%Z; simpl; lia |].
      intros i Hi. change (to_Z 0) with 0%Z in Hi. simpl in Hi. lia.
    - intros j [P C] Hj (HL & HLC & HC & HP). simpl in HL, HLC, HC, HP. unfold place_step. simpl.
      assert (Pj : Pd j) by (unfold Pd; lia). rewrite (HK j Pj).
      set (jn := Z.to_nat (to_Z j)) in *.
      assert (Ej : Z.to_nat (to_Z (j + 1)) = S jn) by (unfold jn; rewrite (succ_Z j) by lia; lia).
      assert (Hjn : (jn < NN)%nat) by (unfold jn; lia).
      assert (Ejn : Z.of_nat jn = to_Z j) by (unfold jn; pose proof (to_Z_bounded j); lia).
      pose proof (Kf_bound j Pj) as Bj.
      assert (Cv : to_Z C.[Kf j] = Z.of_nat (pos jn)).
      { rewrite HC by lia. unfold pos. rewrite <- (KZ_int j). reflexivity. }
      pose proof (pos_lt jn Hjn) as Pl.
      split; [rewrite ilength_set; exact HL |].
      split; [rewrite ilength_set; exact HLC |].
      split.
      + intros b Hb. assert (Kj : KZ jn = to_Z (Kf j)) by (unfold jn; apply KZ_int).
        rewrite Ej. cbn [cnt]. rewrite Kj.
        destruct (Z.eq_dec (to_Z b) (to_Z (Kf j))) as [E | E].
        * apply to_Z_inj in E. subst b. rewrite iget_set_same by (rewrite Uint63.ltb_spec, HLC; lia).
          rewrite Z.eqb_refl. assert (Bc : (to_Z C.[Kf j] < 4194304)%Z) by (rewrite Cv; lia).
          rewrite (add1_small _ Bc). rewrite HC by exact Hb. lia.
        * rewrite iget_set_other by (intros E'; apply E; rewrite E'; reflexivity).
          rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite HC by exact Hb. lia.
      + intros i Hi. rewrite Ej in Hi.
        destruct (Nat.eq_dec i jn) as [-> | Ne].
        * assert (Ev : of_Z (Z.of_nat (pos jn)) = C.[Kf j]).
          { apply to_Z_inj. rewrite Cv. apply to_Z_of_Z_small. pose proof wB_big. lia. }
          rewrite Ev. rewrite iget_set_same by (rewrite Uint63.ltb_spec, HL, Cv; lia). lia.
        * rewrite iget_set_other.
          -- apply HP. lia.
          -- intros E. apply (f_equal to_Z) in E. rewrite Cv, to_Z_of_Z_small in E
               by (pose proof (pos_lt i ltac:(lia)); pose proof wB_big; lia).
             apply Ne. apply pos_inj; lia. }
  destruct G as (G1 & _ & _ & G2). split; [exact G1 |]. intros i Hi. apply G2. unfold NN in Hi. lia.
Qed.

Definition PA : array int := fst PL.

Lemma PA_pos : forall c, (to_Z c < to_Z (PArray.length x))%Z ->
  exists i, (i < NN)%nat /\ pos i = Z.to_nat (to_Z c) /\ to_Z PA.[c] = Z.of_nat i.
Proof.
  intros c Hc. pose proof (to_Z_bounded c).
  destruct (pos_surj (Z.to_nat (to_Z c)) ltac:(unfold NN; lia)) as (i & Hi & Ei).
  exists i. split; [exact Hi |]. split; [exact Ei |].
  pose proof (proj2 PL_spec i Hi) as E. rewrite Ei, Z2Nat.id, of_to_Z in E by lia. exact E.
Qed.

Lemma PA_in : forall c, (to_Z c < to_Z (PArray.length x))%Z -> Pd PA.[c].
Proof.
  intros c Hc. destruct (PA_pos c Hc) as (i & Hi & _ & E). unfold Pd. rewrite E. unfold NN in Hi. lia.
Qed.

Lemma PA_inj : forall c c', (to_Z c < to_Z (PArray.length x))%Z -> (to_Z c' < to_Z (PArray.length x))%Z ->
  c <> c' -> PA.[c] <> PA.[c'].
Proof.
  intros c c' Hc Hc' N E. destruct (PA_pos c Hc) as (i & Hi & Pi & Ei).
  destruct (PA_pos c' Hc') as (i' & Hi' & Pi' & Ei'). rewrite E in Ei.
  assert (i = i') by lia. subst i'. apply N, to_Z_inj.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded c'). lia.
Qed.

Lemma PA_sorted : forall c c', (to_Z c <= to_Z c' < to_Z (PArray.length x))%Z ->
  (to_Z (Kf PA.[c]) <= to_Z (Kf PA.[c']))%Z.
Proof.
  intros c c' Hc. destruct (PA_pos c ltac:(lia)) as (i & Hi & Pi & Ei).
  destruct (PA_pos c' ltac:(lia)) as (i' & Hi' & Pi' & Ei').
  assert (Ki : forall c i, to_Z PA.[c] = Z.of_nat i -> to_Z (Kf PA.[c]) = KZ i).
  { intros c0 i0 E0. unfold KZ. f_equal. f_equal. apply to_Z_inj. rewrite E0.
    symmetry. apply to_Z_of_Z_small. pose proof (to_Z_bounded PA.[c0]). lia. }
  rewrite (Ki c i Ei), (Ki c' i' Ei').
  destruct (Z_lt_le_dec (KZ i') (KZ i)) as [L | L]; [| exact L].
  pose proof (pos_order i' i Hi' L). lia.
Qed.

Lemma PA_onto : forall p, Pd p -> exists c, (to_Z c < to_Z (PArray.length x))%Z /\ PA.[c] = p.
Proof.
  intros p Hp. unfold Pd in Hp. pose proof (to_Z_bounded p). pose proof n_bounds.
  set (i := Z.to_nat (to_Z p)).
  assert (Hi : (i < NN)%nat) by (unfold i, NN; lia).
  exists (of_Z (Z.of_nat (pos i))).
  pose proof (pos_lt i Hi). pose proof wB_big.
  assert (NNv : Z.of_nat NN = to_Z (PArray.length x)) by (unfold NN; lia).
  split; [rewrite to_Z_of_Z_small by lia; lia |].
  apply to_Z_inj. unfold PA. rewrite (proj2 PL_spec i Hi). unfold i. lia.
Qed.

(* -- The least abscissa of each bucket. -- *)

Definition MN : array float :=
  loop (PArray.length x) (fun _ _ => true) (min_step x KY) 0 (PArray.make (PArray.length x) cinit).

Definition Minv (j : int) (M : array float) (b : int) : Prop :=
  (M.[b] = cinit /\ forall r, (to_Z r < to_Z j)%Z -> Kf r <> b) \/
  (exists r, (to_Z r < to_Z j)%Z /\ Kf r = b /\ M.[b] = x.[r] /\
     forall r', (to_Z r' < to_Z j)%Z -> Kf r' = b -> (X r <= X r')%R).

Lemma Minv_other : forall j (M M' : array float) b, (to_Z j < to_Z (PArray.length x))%Z ->
  Kf j <> b -> M'.[b] = M.[b] -> Minv j M b -> Minv (j + 1) M' b.
Proof.
  intros j M M' b Hj Nb E Hm. unfold Minv in *. rewrite E. rewrite (succ_Z j Hj).
  destruct Hm as [[H1 H2] | (r & Hr & Kr & Er & Hmin)].
  - left. split; [exact H1 |]. intros r Hr. destruct (Z.eq_dec (to_Z r) (to_Z j)) as [Ej | Ej].
    + apply to_Z_inj in Ej. subst r. exact Nb.
    + apply H2. lia.
  - right. exists r. split; [lia |]. split; [exact Kr |]. split; [exact Er |].
    intros r' Hr' Kr'. destruct (Z.eq_dec (to_Z r') (to_Z j)) as [Ej | Ej].
    + apply to_Z_inj in Ej. subst r'. contradiction.
    + apply Hmin; [lia | exact Kr'].
Qed.

Lemma MN_spec : PArray.length MN = PArray.length x /\
  forall b, (to_Z b < to_Z (PArray.length x))%Z -> Minv (PArray.length x) MN b.
Proof.
  pose proof n_bounds. destruct KY_spec as [_ HK].
  assert (G : (fun j (M : array float) => PArray.length M = PArray.length x /\
     forall b, (to_Z b < to_Z (PArray.length x))%Z -> Minv j M b) (PArray.length x) MN).
  { unfold MN. apply (for_inv (fun j (M : array float) => PArray.length M = PArray.length x /\
     forall b, (to_Z b < to_Z (PArray.length x))%Z -> Minv j M b)).
    - change (to_Z 0) with 0%Z. lia.
    - split; [apply flength_make_n |]. intros b Hb. left. split; [apply fget_make |].
      intros r Hr. change (to_Z 0) with 0%Z in Hr. pose proof (to_Z_bounded r). lia.
    - intros j M Hj [HL HM]. assert (Pj : Pd j) by (unfold Pd; lia).
      unfold min_step. rewrite (HK j Pj). pose proof (Kf_bound j Pj) as Bj.
      set (b0 := Kf j) in *.
      assert (Rm : exists v, repr M.[b0] v /\
         ((M.[b0] = cinit /\ v = 200001%R) \/ (exists r, Pd r /\ M.[b0] = x.[r] /\ v = X r))).
      { destruct (HM b0 ltac:(lia)) as [[E _] | (r & Hr & _ & E & _)].
        - exists 200001%R. rewrite E. split; [exact repr_cinit | left; auto].
        - exists (X r). assert (Pr : Pd r) by (unfold Pd; lia). rewrite E.
          split; [exact (repr_X r Pr) | right; exists r; auto]. }
      destruct Rm as (v & Rv & Hv').
      destruct (x.[j] <? M.[b0])%float eqn:Lt.
      + rewrite (repr_ltb_iff _ _ _ _ (repr_X j Pj) Rv) in Lt.
        split; [rewrite flength_set; exact HL |]. intros b Hb.
        destruct (Uint63.eqs b0 b) as [Eb | Nb].
        * subst b. right. exists j. split; [rewrite (succ_Z j) by lia; lia |].
          split; [reflexivity |].
          split; [apply fget_set_same; rewrite Uint63.ltb_spec, HL; lia |].
          intros r' Hr' Kr'. rewrite (succ_Z j) in Hr' by lia.
          destruct (Z.eq_dec (to_Z r') (to_Z j)) as [Ej | Ej];
            [apply to_Z_inj in Ej; subst r'; lra |].
          destruct (HM b0 Hb) as [[_ H2] | (r & Hr & Kr & Er & Hmin)].
          -- exfalso. apply (H2 r'); [lia | exact Kr'].
          -- destruct Hv' as [[E1 _] | (r0 & Pr0 & E0 & ->)].
             ++ rewrite Er in E1. exfalso. pose proof (X_bound r ltac:(unfold Pd; lia)) as B.
                pose proof (repr_X r ltac:(unfold Pd; lia)) as R1. rewrite E1 in R1.
                pose proof (repr_float_iff cinit (X r)) as _.
                assert (X r = 200001%R).
                { destruct R1 as [_ R1]. destruct repr_cinit as [_ R2]. congruence. }
                apply Raux.Rabs_le_inv in B. lra.
             ++ rewrite Er in E0.
                assert (X r = X r0).
                { destruct (repr_X r ltac:(unfold Pd; lia)) as [_ R1].
                  destruct (repr_X r0 Pr0) as [_ R2]. rewrite E0 in R1. congruence. }
                pose proof (Hmin r' ltac:(lia) Kr'). lra.
        * apply (Minv_other j M); [lia | exact Nb | apply fget_set_other; exact Nb | apply HM; exact Hb].
      + assert (Ge : ~ (X j < v)%R) by (rewrite <- (repr_ltb_iff _ _ _ _ (repr_X j Pj) Rv); congruence).
        split; [exact HL |]. intros b Hb.
        destruct (Uint63.eqs b0 b) as [Eb | Nb].
        * subst b. destruct (HM b0 Hb) as [[E1 H2] | (r & Hr & Kr & Er & Hmin)].
          -- exfalso. destruct Hv' as [[_ ->] | (r0 & Pr0 & E0 & ->)].
             ++ pose proof (X_bound j Pj) as B. apply Raux.Rabs_le_inv in B. lra.
             ++ rewrite E1 in E0. destruct (repr_X r0 Pr0) as [_ R2]. rewrite <- E0 in R2.
                destruct repr_cinit as [_ R3]. pose proof (X_bound r0 Pr0) as B.
                apply Raux.Rabs_le_inv in B. rewrite R3 in R2. lra.
          -- right. exists r. rewrite (succ_Z j) by lia. split; [lia |]. split; [exact Kr |].
             split; [exact Er |]. intros r' Hr' Kr'.
             destruct (Z.eq_dec (to_Z r') (to_Z j)) as [Ej | Ej].
             ++ apply to_Z_inj in Ej. subst r'.
                destruct Hv' as [[E1 _] | (r0 & Pr0 & E0 & ->)].
                ** rewrite Er in E1. exfalso. pose proof (X_bound r ltac:(unfold Pd; lia)) as B.
                   destruct (repr_X r ltac:(unfold Pd; lia)) as [_ R1]. rewrite E1 in R1.
                   destruct repr_cinit as [_ R2]. apply Raux.Rabs_le_inv in B. rewrite R2 in R1. lra.
                ** rewrite Er in E0.
                   assert (X r = X r0).
                   { destruct (repr_X r ltac:(unfold Pd; lia)) as [_ R1].
                     destruct (repr_X r0 Pr0) as [_ R2]. rewrite E0 in R1. congruence. }
                   lra.
             ++ apply Hmin; [lia | exact Kr'].
        * apply (Minv_other j M); [lia | exact Nb | reflexivity | apply HM; exact Hb]. }
  exact G.
Qed.

Lemma MN_min : forall q, Pd q -> exists r, Pd r /\ Kf r = Kf q /\ MN.[Kf q] = x.[r] /\
  forall r', Pd r' -> Kf r' = Kf q -> (X r <= X r')%R.
Proof.
  intros q Hq. pose proof (Kf_bound q Hq). destruct (proj2 MN_spec (Kf q) ltac:(lia))
    as [[_ H2] | (r & Hr & Kr & Er & Hmin)].
  - exfalso. apply (H2 q Hq). reflexivity.
  - exists r. split; [exact Hr |]. split; [exact Kr |]. split; [exact Er |].
    intros r' Hr' Kr'. apply Hmin; [exact Hr' | exact Kr'].
Qed.

(* -- The sweep. -- *)

(* the exact squared distance *)
Definition Dx (a b : int) : R :=
  ((X a - X b) * (X a - X b) + (Y a - Y b) * (Y a - Y b))%R.

Definition good (st : float * int * int) : Prop :=
  let '(bf, bi, bj) := st in Pd bi /\ Pd bj /\ bi <> bj /\ repr bf (F bi bj).

Definition Ds (st : float * int * int) : R := let '(_, bi, bj) := st in Dx bi bj.

Lemma diff_bound : forall a b, Pd a -> Pd b -> (Rabs (X a - X b) <= 200000 /\ Rabs (Y a - Y b) <= 200000)%R.
Proof.
  intros a b Ha Hb.
  pose proof (X_bound a Ha). pose proof (X_bound b Hb). pose proof (Y_bound a Ha). pose proof (Y_bound b Hb).
  split; unfold Rminus; (eapply Rle_trans; [apply Rabs_triang |]); rewrite Rabs_Ropp; lra.
Qed.

Lemma F_err : forall a b, Pd a -> Pd b -> (Rabs (F a b - Dx a b) <= 4 / 100000)%R.
Proof. intros a b Ha Hb. destruct (diff_bound a b Ha Hb). unfold F, Dx. apply Fd_err; assumption. Qed.

Lemma F_abs : forall a b, Pd a -> Pd b -> (Rabs (F a b) <= 100000000000)%R.
Proof.
  intros a b Ha Hb. destruct (diff_bound a b Ha Hb) as [B1 B2].
  pose proof (F_err a b Ha Hb) as E. apply Raux.Rabs_le_inv in E.
  pose proof (abs_mul_le _ _ _ _ B1 B1) as M1. pose proof (abs_mul_le _ _ _ _ B2 B2) as M2.
  pose proof (Rle_abs ((X a - X b) * (X a - X b))). pose proof (Rle_abs ((Y a - Y b) * (Y a - Y b))).
  pose proof (Rle_0_sqr (X a - X b)). pose proof (Rle_0_sqr (Y a - Y b)). unfold Rsqr in *.
  apply Rabs_le. unfold Dx in E. lra.
Qed.

Lemma dex_iff : forall a b c d, Pd a -> Pd b -> Pd c -> Pd d ->
  dlt (dex x y a b) (dex x y c d) = true <-> (Dx a b < Dx c d)%R.
Proof.
  intros a b c d Ha Hb Hc Hd. unfold dex. cbv zeta. rewrite dlt_iff.
  rewrite (dex_val4 _ _ _ _ _ _ _ _ (repr_X a Ha) (repr_X b Hb) (repr_Y a Ha) (repr_Y b Hb)).
  rewrite (dex_val4 _ _ _ _ _ _ _ _ (repr_X c Hc) (repr_X d Hd) (repr_Y c Hc) (repr_Y d Hd)).
  reflexivity.
Qed.

Lemma repr_bt : forall bf a b tr, Pd a -> Pd b -> repr bf (F a b) -> repr tol tr -> (1 / 2000 <= tr <= 1)%R ->
  repr (bf + tol)%float (rnd (F a b + tr)).
Proof.
  intros bf a b tr Ha Hb Rb Rt Bt. apply repr_add; auto. apply no_ovf.
  pose proof (F_abs a b Ha Hb). eapply Rle_trans; [apply Rabs_triang |].
  rewrite (Rabs_right tr) by lra. lra.
Qed.

Lemma cand_spec : forall p c st, good st -> Pd p -> Pd PA.[c] -> p <> PA.[c] ->
  let st' := cand_step x y PA p c st in
  good st' /\ (Ds st' <= Ds st)%R /\ (Ds st' <= Dx p PA.[c])%R.
Proof.
  intros p c [[bf bi] bj] (Pi & Pj & Nij & Rb) Pp Pq Npq. cbv zeta. unfold cand_step.
  set (q := PA.[c]) in *.
  destruct tol_spec as (tr & Rt & Bt).
  pose proof (repr_bt bf bi bj tr Pi Pj Rb Rt Bt) as Rs.
  destruct ((bf + tol) <? fd x y p q)%float eqn:E1.
  - rewrite (repr_ltb_iff _ _ _ _ Rs (repr_fd p q Pp Pq)) in E1.
    simpl. split; [auto | split; [lra |]]. apply Rlt_le.
    apply (worse_ok (F bi bj) (F p q) _ _ tr); auto using F_err, F_abs.
  - destruct (dlt (dex x y p q) (dex x y bi bj)) eqn:E2.
    + apply (dex_iff p q bi bj Pp Pq Pi Pj) in E2. simpl.
      split; [split; [exact Pp |]; split; [exact Pq |]; split; [exact Npq | apply repr_fd; auto] |]. lra.
    + simpl. split; [auto |]. split; [lra |].
      destruct (Rlt_or_le (Dx p q) (Dx bi bj)) as [L | L]; [| exact L].
      apply (dex_iff p q bi bj Pp Pq Pi Pj) in L. congruence.
Qed.

Lemma cont_spec : forall p c st, good st -> Pd p -> (to_Z c < to_Z (PArray.length x))%Z ->
  cand_cont x KY MN PA p KY.[p] c st = false ->
  forall c', (to_Z c <= to_Z c' < to_Z (PArray.length x))%Z -> (Ds st < Dx p PA.[c'])%R.
Proof.
  intros p c [[bf bi] bj] (Pi & Pj & Nij & Rb) Pp Hc Ec c' Hc'. unfold cand_cont in Ec.
  pose proof (PA_in c Hc) as Pq. set (q := PA.[c]) in *.
  destruct KY_spec as [_ HK]. rewrite (HK q Pq), (HK p Pp) in Ec.
  destruct (Kf p <? Kf q) eqn:Lk; [| discriminate]. apply Bool.negb_false_iff in Ec.
  rewrite Uint63.ltb_spec in Lk.
  destruct (MN_min q Pq) as (r & Pr & Kr & Mr & Minr). rewrite Mr in Ec.
  unfold gx in Ec. cbv zeta in Ec.
  destruct (repr_sq_diff _ _ _ _ (repr_X r Pr) (repr_X p Pp) (X_bound r Pr) (X_bound p Pp)) as [RG _].
  destruct tol_spec as (tr & Rt & Bt).
  pose proof (repr_bt bf bi bj tr Pi Pj Rb Rt Bt) as Rs.
  rewrite (repr_ltb_iff _ _ _ _ Rs RG) in Ec.
  destruct (diff_bound r p Pr Pp) as [Brp _].
  pose proof (G_err (X r - X p) Brp) as Ge.
  assert (Db : (Dx bi bj < (X r - X p) * (X r - X p))%R)
    by (apply (prune_ok (F bi bj) (G (X r - X p)) _ _ tr); auto using F_err, F_abs).
  pose proof (PA_in c' ltac:(lia)) as Pq'. set (q' := PA.[c']) in *.
  pose proof (PA_sorted c c' Hc') as Ks. fold q q' in Ks.
  assert (Xp : (X p < X r)%R) by (apply (Kf_lt p r Pp Pr); rewrite Kr; exact Lk).
  assert (Xq : (X r <= X q')%R).
  { destruct (Z.eq_dec (to_Z (Kf q')) (to_Z (Kf q))) as [E | E].
    - apply Minr; [exact Pq' | apply to_Z_inj; exact E].
    - apply Rlt_le, (Kf_lt r q' Pr Pq'). rewrite Kr. lia. }
  simpl. unfold Dx at 2.
  assert (S : ((X r - X p) * (X r - X p) <= (X q' - X p) * (X q' - X p))%R)
    by (apply Rmult_le_compat; lra).
  pose proof (Rle_0_sqr (Y p - Y q')). unfold Rsqr in *.
  replace ((X p - X q') * (X p - X q'))%R with ((X q' - X p) * (X q' - X p))%R by ring. lra.
Qed.

Lemma inner_spec : forall a st, (to_Z a < to_Z (PArray.length x))%Z -> good st ->
  let p := PA.[a] in
  let st' := loop (PArray.length x) (cand_cont x KY MN PA p KY.[p]) (cand_step x y PA p) (a + 1) st in
  good st' /\ (Ds st' <= Ds st)%R /\
  forall c', (to_Z a < to_Z c' < to_Z (PArray.length x))%Z -> (Ds st' <= Dx p PA.[c'])%R.
Proof.
  intros a st Ha Gs p st'. pose proof (PA_in a Ha) as Pp. fold p in Pp.
  pose proof (succ_Z a Ha) as Ea.
  destruct (loop_inv (fun c s => good s /\ (Ds s <= Ds st)%R /\
      forall c', (to_Z a < to_Z c' < to_Z c)%Z -> (Ds s <= Dx p PA.[c'])%R)
      (PArray.length x) (a + 1) (cand_cont x KY MN PA p KY.[p]) (cand_step x y PA p) st)
    as (j & Bj & (G1 & G2 & G3) & Ej).
  - lia.
  - split; [exact Gs |]. split; [lra |]. intros c' Hc'. lia.
  - intros j t Hj (T1 & T2 & T3) _.
    assert (Hj' : (to_Z j < to_Z (PArray.length x))%Z) by lia.
    assert (Naj : a <> j) by (intros ->; lia).
    destruct (cand_spec p j t T1 Pp (PA_in j Hj') (PA_inj a j Ha Hj' Naj)) as (C1 & C2 & C3).
    split; [exact C1 |]. split; [lra |]. intros c' Hc'. rewrite (succ_Z j Hj') in Hc'.
    destruct (Z.eq_dec (to_Z c') (to_Z j)) as [E | E].
    + apply to_Z_inj in E. subst c'. exact C3.
    + pose proof (T3 c' ltac:(lia)). lra.
  - fold st' in G1, G2, G3, Ej. split; [exact G1 |]. split; [exact G2 |].
    intros c' Hc'. destruct (Z_lt_le_dec (to_Z c') (to_Z j)) as [L | L].
    + apply G3. lia.
    + destruct Ej as [Ej | [Lj Cj]]; [lia |].
      apply Rlt_le. apply (cont_spec p j st' G1 Pp Lj Cj c'). lia.
Qed.

Lemma good_init : good (fd x y 0 1, 0, 1).
Proof.
  pose proof n_bounds. assert (P0 : Pd 0) by (unfold Pd; change (to_Z 0) with 0%Z; lia).
  assert (P1 : Pd 1) by (unfold Pd; change (to_Z 1) with 1%Z; lia).
  simpl. split; [exact P0 |]. split; [exact P1 |]. split; [intros E; apply (f_equal to_Z) in E; change (0%Z = 1%Z) in E; discriminate |]. apply repr_fd; auto.
Qed.

Lemma sweep_spec :
  let st := loop (PArray.length x) (fun _ _ => true) (sweep_step x y KY MN PA (PArray.length x)) 0
              (fd x y 0 1, 0, 1) in
  good st /\ forall a c, (to_Z a < to_Z c < to_Z (PArray.length x))%Z -> (Ds st <= Dx PA.[a] PA.[c])%R.
Proof.
  cbv zeta. pose proof n_bounds.
  assert (G := for_inv (fun a st => good st /\ forall a' c, (to_Z a' < to_Z a)%Z ->
       (to_Z a' < to_Z c < to_Z (PArray.length x))%Z -> (Ds st <= Dx PA.[a'] PA.[c])%R)
     (PArray.length x) 0 (sweep_step x y KY MN PA (PArray.length x)) (fd x y 0 1, 0, 1)).
  destruct G as [G1 G2].
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact good_init |]. intros a' c Ha'. change (to_Z 0) with 0%Z in Ha'.
    pose proof (to_Z_bounded a'). lia.
  - intros a t Ha (T1 & T2). unfold sweep_step.
    destruct (inner_spec a t ltac:(lia) T1) as (I1 & I2 & I3).
    split; [exact I1 |]. intros a' c Ha' Hc. rewrite (succ_Z a) in Ha' by lia.
    destruct (Z.eq_dec (to_Z a') (to_Z a)) as [E | E].
    + apply to_Z_inj in E. subst a'. apply I3. lia.
    + pose proof (T2 a' c ltac:(lia) Hc). lra.
  - split; [exact G1 |]. intros a c Hac. apply G2; lia.
Qed.

Lemma Dx_sym : forall a b, Dx a b = Dx b a.
Proof. intros a b. unfold Dx. ring. Qed.

Lemma closestpair_main :
  let r := closestpair x y in
  Pd (fst r) /\ Pd (snd r) /\ fst r <> snd r /\
  (forall a b, Pd a -> Pd b -> a <> b -> (Dx (fst r) (snd r) <= Dx a b)%R).
Proof.
  cbv zeta. unfold closestpair.
  pose proof n_bounds as Hn.
  replace (2 <=? PArray.length x) with true
    by (symmetry; rewrite Uint63.leb_spec; change (to_Z 2) with 2%Z; lia).
  cbv zeta. fold sf. fold n1. fold KY. fold CT. fold PS.
  rewrite (surjective_pairing PS). cbv beta iota.
  fold PL. rewrite (surjective_pairing PL). cbv beta iota. fold PA. fold MN.
  pose proof sweep_spec as SW. cbv zeta in SW.
  destruct (loop (PArray.length x) (fun _ _ => true) (sweep_step x y KY MN PA (PArray.length x)) 0
              (fd x y 0 1, 0, 1)) as [[bf i] j].
  destruct SW as [(Pi & Pj & Nij & _) Best]. simpl in Best |- *.
  split; [exact Pi |]. split; [exact Pj |]. split; [exact Nij |].
  intros a b Ha Hb Nab.
  destruct (PA_onto a Ha) as (ca & Hca & Ea). destruct (PA_onto b Hb) as (cb & Hcb & Eb).
  destruct (Z_lt_le_dec (to_Z ca) (to_Z cb)) as [L | L].
  - rewrite <- Ea, <- Eb. apply Best. lia.
  - destruct (Z.eq_dec (to_Z ca) (to_Z cb)) as [E | E].
    + apply to_Z_inj in E. subst cb. congruence.
    + rewrite (Dx_sym a b), <- Ea, <- Eb. apply Best. lia.
Qed.

End Main.

Lemma closestpair_correct_main : forall (xs ys : list R) (x y : array float),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists r : N * N, repr (closestpair x y : uint * uint) r /\ closestpair_spec xs ys r.
Proof.
  intros xs ys x y Hv Hx Hy.
  pose proof (closestpair_main xs ys x y Hv Hx Hy) as (Pi & Pj & Nij & Best).
  destruct (closestpair x y) as [i j]. simpl in Pi, Pj, Nij, Best.
  exists (Z.to_N (to_Z i), Z.to_N (to_Z j)). split; [split; reflexivity |].
  pose proof (len_x xs x Hx) as Lx.
  assert (D : forall a b, dist2 xs ys (Z.to_N (to_Z a)) (Z.to_N (to_Z b)) = Dx xs ys a b).
  { intros a b. unfold dist2, Dx, get_list_R, X, Y. rewrite !Z_N_nat. reflexivity. }
  unfold Pd in Pi, Pj. pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  unfold closestpair_spec, point_pair, len. simpl fst; simpl snd.
  split.
  - split; [lia |]. split; [lia |]. intros E. apply Nij, to_Z_inj. lia.
  - intros p q (Hp & Hq & Npq). unfold len in Hp, Hq.
    set (a := of_Z (Z.of_N p)). set (c := of_Z (Z.of_N q)).
    assert (Ea : to_Z a = Z.of_N p) by (apply to_Z_of_Z_small; pose proof wB_big; lia).
    assert (Ec : to_Z c = Z.of_N q) by (apply to_Z_of_Z_small; pose proof wB_big; lia).
    assert (Pa : Pd x a) by (unfold Pd; lia).
    assert (Pc : Pd x c) by (unfold Pd; lia).
    assert (Nac : a <> c) by (intros E; apply Npq; apply (f_equal to_Z) in E; lia).
    pose proof (Best a c Pa Pc Nac) as B.
    rewrite D. replace p with (Z.to_N (to_Z a)) by lia. replace q with (Z.to_N (to_Z c)) by lia.
    rewrite D. exact B.
Qed.

Lemma closestpair_correct :
  forall (xs ys : list R) (x y : array float),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists r : N * N, repr (closestpair x y) r /\ closestpair_spec xs ys r.
Proof. exact closestpair_correct_main. Qed.
