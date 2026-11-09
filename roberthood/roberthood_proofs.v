(* Correctness proofs for roberthood_implem.v. *)
(* Implementation of roberthood.spec: the diameter of a point set by
   convex hull (Andrew's monotone chain) and rotating calipers, exactly in
   63-bit integers, one float square root at the end. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Sint63.
From Respeced Require Import Repr ReprFloat.
Import ListNotations.
From Stdlib Require Import Bool.

Open Scope uint63_scope.
Open Scope bool_scope.
Unset Lia Cache.

Require Export roberthood_implem.
Open Scope uint63_scope.
Open Scope bool_scope.


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
(* PArray plumbing; arrays read as functions on Z indices              *)
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

Lemma iget_make : forall (m i v : int), (PArray.make m v : array int).[i] = v.
Proof. intros. exact (get_make int v m i). Qed.

Lemma ilength_bound : forall (t : array int), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H. rewrite Uint63.leb_spec in H.
  exact H.
Qed.

Lemma to_Z_of_Z_small : forall z, (0 <= z < wB)%Z -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small; exact Hz. Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma ilength_make_small : forall (n v : int), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v H. rewrite ilength_make.
  replace (n <=? max_length) with true; [reflexivity |].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Definition ag (A : array int) (z : Z) : Z := to_Z (A.[of_Z z]).

Lemma ag_int : forall A (i : int), ag A (to_Z i) = to_Z A.[i].
Proof. intros. unfold ag. rewrite of_to_Z. reflexivity. Qed.

Lemma ag_set_same : forall A (i v : int), (to_Z i < to_Z (PArray.length A))%Z ->
  ag (A.[i <- v]) (to_Z i) = to_Z v.
Proof.
  intros. rewrite ag_int, iget_set_same; [reflexivity |]. rewrite Uint63.ltb_spec. exact H.
Qed.

Lemma ag_set_other : forall A (i v : int) z, (0 <= z < wB)%Z -> z <> to_Z i ->
  ag (A.[i <- v]) z = ag A z.
Proof.
  intros A i v z Hz Hn. unfold ag. rewrite iget_set_other; [reflexivity |].
  intros E. apply Hn. rewrite E, to_Z_of_Z_small by exact Hz. reflexivity.
Qed.

Lemma ag_set : forall A (i v : int) z, (0 <= z < wB)%Z -> (to_Z i < to_Z (PArray.length A))%Z ->
  ag (A.[i <- v]) z = if Z.eqb z (to_Z i) then to_Z v else ag A z.
Proof.
  intros A i v z Hz Hi. destruct (Z.eqb_spec z (to_Z i)) as [E | E].
  - subst z. apply ag_set_same; exact Hi.
  - apply ag_set_other; assumption.
Qed.

Lemma ag_make : forall n v z, ag (PArray.make n v) z = to_Z v.
Proof. intros. unfold ag. rewrite iget_make. reflexivity. Qed.

Lemma int_of_Z : forall z, (0 <= z < wB)%Z -> exists i : int, to_Z i = z.
Proof. intros z Hz. exists (of_Z z). apply to_Z_of_Z_small; exact Hz. Qed.

(* ------------------------------------------------------------------ *)
(* Small signed arithmetic is exact                                    *)
(* ------------------------------------------------------------------ *)

Notation sv := Sint63.to_Z.

Lemma half_wB : (wB / 2 = 4611686018427387904)%Z.
Proof. reflexivity. Qed.

Lemma sv_phi : forall x : int, (to_Z x < 4611686018427387904)%Z -> sv x = to_Z x.
Proof.
  intros x H. rewrite Sint63.to_Z_cmodwB. apply Sint63.cmod_small.
  rewrite half_wB. pose proof (to_Z_bounded x). lia.
Qed.

Lemma phi_sv : forall x : int, (0 <= sv x)%Z -> to_Z x = sv x.
Proof.
  intros x H. rewrite <- Sint63.to_Z_mod_Uint63to_Z. apply Z.mod_small.
  pose proof (Sint63.to_Z_bounded x) as B. rewrite Sint63.to_Z_max in B.
  rewrite wB_val in *. lia.
Qed.

Lemma s_add : forall x y : int, (Z.abs (sv x + sv y) < 4611686018427387904)%Z ->
  sv (x + y) = (sv x + sv y)%Z.
Proof. intros x y H. rewrite Sint63.add_spec. apply Sint63.cmod_small. rewrite half_wB. lia. Qed.

Lemma s_sub : forall x y : int, (Z.abs (sv x - sv y) < 4611686018427387904)%Z ->
  sv (x - y) = (sv x - sv y)%Z.
Proof. intros x y H. rewrite Sint63.sub_spec. apply Sint63.cmod_small. rewrite half_wB. lia. Qed.

Lemma s_mul : forall x y : int, (Z.abs (sv x * sv y) < 4611686018427387904)%Z ->
  sv (x * y) = (sv x * sv y)%Z.
Proof. intros x y H. rewrite Sint63.mul_spec. apply Sint63.cmod_small. rewrite half_wB. lia. Qed.

(* ------------------------------------------------------------------ *)
(* Plane geometry over Z                                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

Lemma pos_mul_nonneg : forall a b, 0 < a -> 0 <= a * b -> 0 <= b.
Proof. intros a b Ha H. destruct (Z_le_gt_dec 0 b); [assumption |]. nia. Qed.

Lemma pos_mul_nonpos : forall a b, 0 < a -> a * b <= 0 -> b <= 0.
Proof. intros a b Ha H. destruct (Z_le_gt_dec b 0); [assumption |]. nia. Qed.

(* lexicographic order of points *)
Definition LEX (ax ay bx bY : Z) : Prop := ax < bx \/ (ax = bx /\ ay <= bY).

Lemma LEX_x : forall ax ay bx bY, LEX ax ay bx bY -> ax <= bx /\ (ax = bx -> ay <= bY).
Proof. unfold LEX. intros. lia. Qed.

(* (b - a) x (c - a) *)
Definition cr (ax ay bx bY cx cy : Z) : Z := (bx - ax) * (cy - ay) - (bY - ay) * (cx - ax).

Lemma rel_pop : forall Px Py Bx By Cx Cy,
  0 <= Px -> Px <= Bx -> Bx <= Cx -> (Px = 0 -> 0 <= Py) ->
  0 <= Bx * Py - By * Px -> Bx * Cy - By * Cx <= 0 ->
  0 <= Cx * Py - Cy * Px.
Proof.
  intros Px Py Bx By Cx Cy H1 H2 H3 H4 H5 H6.
  destruct (Z.eq_dec Bx 0) as [E | E].
  - assert (E2 : Px = 0) by lia. rewrite E2. rewrite Z.mul_0_r, Z.sub_0_r.
    apply Z.mul_nonneg_nonneg; [lia | apply H4; exact E2].
  - assert (A1 : 0 <= Cx * (Bx * Py - By * Px)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (A2 : 0 <= Px * (By * Cx - Bx * Cy)) by (apply Z.mul_nonneg_nonneg; lia).
    apply (pos_mul_nonneg Bx); [lia |].
    replace (Bx * (Cx * Py - Cy * Px)) with (Cx * (Bx * Py - By * Px) + Px * (By * Cx - Bx * Cy))
      by ring. lia.
Qed.

(* the pop: p above (a, b), c not left of a -> b, then p above (a, c) *)
Lemma geo_pop : forall ax ay px py bx bY cx cy,
  LEX ax ay px py -> LEX px py bx bY -> LEX bx bY cx cy ->
  0 <= cr ax ay bx bY px py -> cr ax ay bx bY cx cy <= 0 ->
  0 <= cr ax ay cx cy px py.
Proof.
  intros ax ay px py bx bY cx cy L1 L2 L3 H1 H2. unfold cr in *.
  apply LEX_x in L1, L2, L3.
  apply (rel_pop (px - ax) (py - ay) (bx - ax) (bY - ay)); try lia.
Qed.

Lemma rel_pend : forall Ax Ay Bx By Px Py,
  Ax <= Bx -> Bx <= Px -> Px <= 0 -> (Bx = Px -> By <= Py) -> (Px = 0 -> Py <= 0) ->
  Ax * By - Ay * Bx <= 0 -> Bx * Py - By * Px <= 0 ->
  Ax * Py - Ay * Px <= 0.
Proof.
  intros Ax Ay Bx By Px Py H1 H2 H3 H4 H5 Hab Hbp.
  destruct (Z.eq_dec Bx 0) as [E | E].
  - assert (E2 : Px = 0) by lia. rewrite E2 in *. rewrite Z.mul_0_r, Z.sub_0_r.
    rewrite E in Hab. rewrite Z.mul_0_r, Z.sub_0_r in Hab.
    destruct (Z.eq_dec Ax 0) as [E3 | E3]; [rewrite E3; lia |].
    assert (0 <= By) by (destruct (Z_le_gt_dec 0 By); [assumption | nia]).
    assert (Py = 0) by (specialize (H4 E); specialize (H5 eq_refl); lia).
    subst Py. lia.
  - assert (A1 : (- Ax) * (Bx * Py - By * Px) <= 0)
      by (apply Z.mul_nonneg_nonpos; lia).
    assert (A2 : (- Px) * (Ax * By - Ay * Bx) <= 0)
      by (apply Z.mul_nonneg_nonpos; lia).
    apply (pos_mul_nonpos (- Bx)); [lia |].
    replace (- Bx * (Ax * Py - Ay * Px)) with ((- Ax) * (Bx * Py - By * Px) + (- Px) * (Ax * By - Ay * Bx))
      by ring. lia.
Qed.

(* the pending points: b on or left of a -> c, p left of b -> c, then of a -> c *)
Lemma geo_pend : forall ax ay bx bY px py cx cy,
  LEX ax ay bx bY -> LEX bx bY px py -> LEX px py cx cy ->
  0 <= cr ax ay cx cy bx bY -> 0 <= cr bx bY cx cy px py ->
  0 <= cr ax ay cx cy px py.
Proof.
  intros ax ay bx bY px py cx cy L1 L2 L3 H1 H2. unfold cr in *.
  apply LEX_x in L1, L2, L3.
  pose proof (rel_pend (ax - cx) (ay - cy) (bx - cx) (bY - cy) (px - cx) (py - cy)) as R.
  assert (Hab : (ax - cx) * (bY - cy) - (ay - cy) * (bx - cx) <= 0).
  { replace ((ax - cx) * (bY - cy) - (ay - cy) * (bx - cx))
        with (- ((cx - ax) * (bY - ay) - (cy - ay) * (bx - ax))) by ring. lia. }
  assert (Hbp : (bx - cx) * (py - cy) - (bY - cy) * (px - cx) <= 0).
  { replace ((bx - cx) * (py - cy) - (bY - cy) * (px - cx))
        with (- ((cx - bx) * (py - bY) - (cy - bY) * (px - bx))) by ring. lia. }
  assert (R' : (ax - cx) * (py - cy) - (ay - cy) * (px - cx) <= 0) by (apply R; lia).
  replace ((cx - ax) * (py - ay) - (cy - ay) * (px - ax))
    with (- ((ax - cx) * (py - cy) - (ay - cy) * (px - cx))) by ring. lia.
Qed.

Lemma rel_support : forall Px Py Bx By wx wy,
  0 <= Px -> Px <= Bx -> (Px = 0 -> 0 <= Py) -> (Px = Bx -> Py <= By) ->
  0 <= Bx * Py - By * Px -> 0 < wy ->
  0 <= wx * Px + wy * Py \/ wx * Bx + wy * By <= wx * Px + wy * Py.
Proof.
  intros Px Py Bx By wx wy H1 H2 H3 H4 H5 Hw.
  set (D := wx * Px + wy * Py). set (E := wx * Bx + wy * By).
  destruct (Z_le_gt_dec 0 D) as [G | G]; [left; lia |].
  destruct (Z_le_gt_dec E D) as [G2 | G2]; [right; lia |].
  exfalso.
  destruct (Z.eq_dec Px 0) as [E0 | E0].
  - assert (0 <= Py) by auto.
    destruct (Z.eq_dec Bx 0) as [E1 | E1].
    + unfold D in G. rewrite E0 in G. nia.
    + assert (I : Bx * D - Px * E = wy * (Bx * Py - By * Px)) by (unfold D, E; ring).
      assert (0 <= wy * (Bx * Py - By * Px)) by (apply Z.mul_nonneg_nonneg; lia).
      rewrite E0 in I. assert (0 <= Bx * D) by lia. nia.
  - assert (I : Bx * D - Px * E = wy * (Bx * Py - By * Px)) by (unfold D, E; ring).
    assert (0 <= wy * (Bx * Py - By * Px)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (A2 : Px * D < Px * E) by (apply Z.mul_lt_mono_pos_l; lia).
    assert (A3 : (Bx - Px) * D <= 0) by (apply Z.mul_nonneg_nonpos; lia).
    lia.
Qed.

(* a point above the edge (a, b), between them: for an upward w, not below both *)
Lemma geo_support : forall ax ay px py bx bY wx wy,
  LEX ax ay px py -> LEX px py bx bY -> 0 <= cr ax ay bx bY px py -> 0 < wy ->
  wx * ax + wy * ay <= wx * px + wy * py \/ wx * bx + wy * bY <= wx * px + wy * py.
Proof.
  intros ax ay px py bx bY wx wy L1 L2 H Hw. unfold cr in H.
  apply LEX_x in L1, L2.
  destruct (rel_support (px - ax) (py - ay) (bx - ax) (bY - ay) wx wy) as [R | R];
    try lia.
Qed.

(* a vector is lexicographically positive *)
Definition lexpos (dx dy : Z) : Prop := 0 < dx \/ (dx = 0 /\ 0 < dy).

Definition vcross (ax ay bx bY : Z) : Z := ax * bY - ay * bx.
Definition dot (wx wy ax ay : Z) : Z := wx * ax + wy * ay.

Lemma geo_turn : forall ax ay bx bY wx wy,
  lexpos ax ay -> lexpos bx bY -> 0 < vcross ax ay bx bY -> 0 < wy ->
  0 <= dot wx wy ax ay -> 0 < dot wx wy bx bY.
Proof.
  intros ax ay bx bY wx wy La Lb C Hw D. unfold lexpos, vcross, dot in *.
  destruct La as [La | [La1 La2]].
  - assert (I : ax * (wx * bx + wy * bY) - bx * (wx * ax + wy * ay) = wy * (ax * bY - ay * bx))
      by ring.
    assert (0 < wy * (ax * bY - ay * bx)) by (apply Z.mul_pos_pos; lia).
    assert (0 <= bx * (wx * ax + wy * ay)) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (Z_le_gt_dec (wx * bx + wy * bY) 0) as [G | G]; [| lia].
    assert (ax * (wx * bx + wy * bY) <= 0) by (apply Z.mul_nonneg_nonpos; lia). lia.
  - subst ax. rewrite Z.mul_0_l in C. assert (ay * bx >= 0) by (apply Z.le_ge, Z.mul_nonneg_nonneg; lia).
    lia.
Qed.

Lemma geo_turn' : forall ax ay bx bY wx wy,
  lexpos ax ay -> lexpos bx bY -> 0 <= vcross bx bY ax ay -> 0 < wy ->
  0 < dot wx wy bx bY -> 0 <= dot wx wy ax ay.
Proof.
  intros ax ay bx bY wx wy La Lb C Hw D. unfold lexpos, vcross, dot in *.
  destruct Lb as [Lb | [Lb1 Lb2]].
  - assert (I : bx * (wx * ax + wy * ay) - ax * (wx * bx + wy * bY) = wy * (bx * ay - bY * ax))
      by ring.
    assert (0 <= wy * (bx * ay - bY * ax)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= ax * (wx * bx + wy * bY)) by (apply Z.mul_nonneg_nonneg; lia).
    apply (pos_mul_nonneg bx); lia.
  - subst bx. rewrite Z.mul_0_l in C.
    assert (ax = 0).
    { destruct La as [La | [La1 _]]; [| exact La1].
      assert (0 < bY * ax) by (apply Z.mul_pos_pos; lia). lia. }
    subst ax. destruct La as [La | [_ La2]]; [lia |].
    rewrite Z.mul_0_r, Z.add_0_l. apply Z.mul_nonneg_nonneg; lia.
Qed.

(* Cauchy-Schwarz, in the form used: w.w <= w.d implies w.w <= d.d *)
Lemma geo_cs : forall wx wy dx dy,
  wx * wx + wy * wy <= dot wx wy dx dy -> wx * wx + wy * wy <= dx * dx + dy * dy.
Proof.
  intros wx wy dx dy H. unfold dot in H.
  set (W := wx * wx + wy * wy) in *. set (Dd := dx * dx + dy * dy).
  set (P := wx * dx + wy * dy) in *.
  assert (L : P * P <= W * Dd).
  { assert (E : W * Dd - P * P = (wx * dy - wy * dx) * (wx * dy - wy * dx))
      by (unfold W, Dd, P; ring).
    pose proof (Z.square_nonneg (wx * dy - wy * dx)). lia. }
  assert (W0 : 0 <= W) by (unfold W; pose proof (Z.square_nonneg wx); pose proof (Z.square_nonneg wy); lia).
  assert (D0 : 0 <= Dd) by (unfold Dd; pose proof (Z.square_nonneg dx); pose proof (Z.square_nonneg dy); lia).
  destruct (Z.eq_dec W 0) as [E | E]; [lia |].
  assert (WW : W * W <= P * P) by (apply Z.mul_le_mono_nonneg; lia).
  destruct (Z_le_gt_dec W Dd) as [G | G]; [exact G |].
  assert (W * Dd < W * W) by (apply Z.mul_lt_mono_pos_l; lia). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Keys                                                                *)
(* ------------------------------------------------------------------ *)

Definition PX (k : Z) : Z := k / 2048 - 1000.
Definition PY (k : Z) : Z := k mod 2048 - 1000.
Definition KR (k : Z) : Prop := 0 <= k < 4194304.
Definition EK (X Y : Z) : Z := (X + 1000) * 2048 + (Y + 1000).
(* the keys of the statement's points *)
Definition VK (k : Z) : Prop :=
  exists X Y, -1000 <= X <= 1000 /\ -1000 <= Y <= 1000 /\ k = EK X Y.

(* the squared distance between the point of key a and the opposite of the point of key b *)
Definition SQ (a b : Z) : Z :=
  (PX a + PX b) * (PX a + PX b) + (PY a + PY b) * (PY a + PY b).

(* the squared distance between two points *)
Definition sqd (a b : Z) : Z :=
  (PX a - PX b) * (PX a - PX b) + (PY a - PY b) * (PY a - PY b).

Lemma PX_EK : forall X Y, -1000 <= X <= 1000 -> -1000 <= Y <= 1000 -> PX (EK X Y) = X.
Proof. intros. unfold PX, EK. sia. Qed.

Lemma PY_EK : forall X Y, -1000 <= X <= 1000 -> -1000 <= Y <= 1000 -> PY (EK X Y) = Y.
Proof. intros. unfold PY, EK. sia. Qed.

Lemma VK_KR : forall k, VK k -> KR k.
Proof. intros k (X & Y & HX & HY & ->). unfold KR, EK. lia. Qed.

Lemma VK_neg : forall k, VK k -> VK (4098000 - k) /\ PX (4098000 - k) = - PX k /\ PY (4098000 - k) = - PY k.
Proof.
  intros k (X & Y & HX & HY & ->).
  replace (4098000 - EK X Y) with (EK (- X) (- Y)) by (unfold EK; ring).
  rewrite !PX_EK, !PY_EK by lia.
  split; [exists (- X), (- Y); repeat split; lia | lia].
Qed.

Lemma KR_coords : forall k, KR k -> -1000 <= PX k <= 1048 /\ -1000 <= PY k <= 1047.
Proof. unfold KR, PX, PY. intros. sia. Qed.

Lemma key_lex : forall a b, 0 <= a -> a <= b -> LEX (PX a) (PY a) (PX b) (PY b).
Proof.
  intros a b Ha Hab. unfold LEX, PX, PY.
  assert (a / 2048 <= b / 2048) by (apply Z.div_le_mono; lia).
  destruct (Z.eq_dec (a / 2048) (b / 2048)) as [E | E]; [| left; lia].
  right. split; [lia |].
  rewrite (Z.mod_eq a 2048), (Z.mod_eq b 2048) by lia. rewrite E. lia.
Qed.

Lemma key_lexpos : forall a b, 0 <= a -> a < b -> lexpos (PX b - PX a) (PY b - PY a).
Proof.
  intros a b Ha Hab. unfold lexpos, PX, PY.
  assert (a / 2048 <= b / 2048) by (apply Z.div_le_mono; lia).
  destruct (Z.eq_dec (a / 2048) (b / 2048)) as [E | E]; [| left; lia].
  right. split; [lia |].
  rewrite (Z.mod_eq a 2048), (Z.mod_eq b 2048) by lia. rewrite E. lia.
Qed.

Lemma sv_cx : forall k : int, KR (to_Z k) -> sv (cx k) = PX (to_Z k).
Proof.
  intros k Hk. unfold cx, PX, KR in *.
  assert (D : to_Z (k / 2048)%uint63 = to_Z k / 2048) by (rewrite Uint63.div_spec; reflexivity).
  rewrite s_sub; rewrite sv_phi with (x := (k / 2048)%uint63) by lia; rewrite D;
    change (sv 1000) with 1000; [reflexivity |].
  assert (0 <= to_Z k / 2048 < 2048) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  lia.
Qed.

Lemma sv_cy : forall k : int, KR (to_Z k) -> sv (cy k) = PY (to_Z k).
Proof.
  intros k Hk. unfold cy, PY, KR in *.
  assert (D : to_Z (k mod 2048)%uint63 = to_Z k mod 2048) by (rewrite Uint63.mod_spec; reflexivity).
  assert (0 <= to_Z k mod 2048 < 2048) by (apply Z.mod_pos_bound; lia).
  rewrite s_sub; rewrite sv_phi with (x := (k mod 2048)%uint63) by lia; rewrite D;
    change (sv 1000) with 1000; [reflexivity |].
  lia.
Qed.

Lemma sv_mcross : forall a1 a2 b1 b2 : int,
  KR (to_Z a1) -> KR (to_Z a2) -> KR (to_Z b1) -> KR (to_Z b2) ->
  sv (mcross a1 a2 b1 b2) =
  vcross (PX (to_Z a2) - PX (to_Z a1)) (PY (to_Z a2) - PY (to_Z a1))
         (PX (to_Z b2) - PX (to_Z b1)) (PY (to_Z b2) - PY (to_Z b1)).
Proof.
  intros a1 a2 b1 b2 H1 H2 H3 H4. unfold mcross, vcross.
  pose proof (KR_coords _ H1). pose proof (KR_coords _ H2).
  pose proof (KR_coords _ H3). pose proof (KR_coords _ H4).
  pose proof (sv_cx _ H1). pose proof (sv_cx _ H2). pose proof (sv_cx _ H3). pose proof (sv_cx _ H4).
  pose proof (sv_cy _ H1). pose proof (sv_cy _ H2). pose proof (sv_cy _ H3). pose proof (sv_cy _ H4).
  assert (Ax : sv (cx a2 - cx a1) = PX (to_Z a2) - PX (to_Z a1)) by (rewrite s_sub; lia).
  assert (Ay : sv (cy a2 - cy a1) = PY (to_Z a2) - PY (to_Z a1)) by (rewrite s_sub; lia).
  assert (Bx : sv (cx b2 - cx b1) = PX (to_Z b2) - PX (to_Z b1)) by (rewrite s_sub; lia).
  assert (By : sv (cy b2 - cy b1) = PY (to_Z b2) - PY (to_Z b1)) by (rewrite s_sub; lia).
  assert (M1 : sv ((cx a2 - cx a1) * (cy b2 - cy b1)) =
               (PX (to_Z a2) - PX (to_Z a1)) * (PY (to_Z b2) - PY (to_Z b1)))
    by (rewrite s_mul; rewrite Ax, By; [reflexivity | nia]).
  assert (M2 : sv ((cy a2 - cy a1) * (cx b2 - cx b1)) =
               (PY (to_Z a2) - PY (to_Z a1)) * (PX (to_Z b2) - PX (to_Z b1)))
    by (rewrite s_mul; rewrite Ay, Bx; [reflexivity | nia]).
  rewrite s_sub; rewrite M1, M2; [reflexivity | nia].
Qed.

Lemma phi_msq : forall a b : int, KR (to_Z a) -> KR (to_Z b) ->
  to_Z (msq a b) = SQ (to_Z a) (to_Z b).
Proof.
  intros a b H1 H2. unfold msq, SQ.
  pose proof (KR_coords _ H1). pose proof (KR_coords _ H2).
  pose proof (sv_cx _ H1). pose proof (sv_cx _ H2).
  pose proof (sv_cy _ H1). pose proof (sv_cy _ H2).
  assert (Dx : sv (cx a + cx b) = PX (to_Z a) + PX (to_Z b)) by (rewrite s_add; lia).
  assert (Dy : sv (cy a + cy b) = PY (to_Z a) + PY (to_Z b)) by (rewrite s_add; lia).
  assert (M1 : sv ((cx a + cx b) * (cx a + cx b)) = (PX (to_Z a) + PX (to_Z b)) * (PX (to_Z a) + PX (to_Z b)))
    by (rewrite s_mul; rewrite Dx; [reflexivity | nia]).
  assert (M2 : sv ((cy a + cy b) * (cy a + cy b)) = (PY (to_Z a) + PY (to_Z b)) * (PY (to_Z a) + PY (to_Z b)))
    by (rewrite s_mul; rewrite Dy; [reflexivity | nia]).
  assert (S : sv ((cx a + cx b) * (cx a + cx b) + (cy a + cy b) * (cy a + cy b)) =
     (PX (to_Z a) + PX (to_Z b)) * (PX (to_Z a) + PX (to_Z b)) + (PY (to_Z a) + PY (to_Z b)) * (PY (to_Z a) + PY (to_Z b)))
    by (rewrite s_add; rewrite M1, M2; [reflexivity | nia]).
  unfold msq. rewrite (phi_sv ((cx a + cx b) * (cx a + cx b) + (cy a + cy b) * (cy a + cy b))%uint63);
    rewrite S; [reflexivity |].
  pose proof (Z.square_nonneg (PX (to_Z a) + PX (to_Z b))).
  pose proof (Z.square_nonneg (PY (to_Z a) + PY (to_Z b))). lia.
Qed.

Lemma SQ_bound : forall a b, KR a -> KR b -> 0 <= SQ a b <= 20000000.
Proof.
  intros a b H1 H2. pose proof (KR_coords _ H1). pose proof (KR_coords _ H2). unfold SQ.
  assert (B : forall u, -2000 <= u <= 2096 -> 0 <= u * u <= 2096 * 2096) by (intros; nia).
  pose proof (B (PX a + PX b) ltac:(lia)). pose proof (B (PY a + PY b) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Merge sort                                                          *)
(* ------------------------------------------------------------------ *)

Definition sorted_on (A : array int) (lo hi : Z) : Prop :=
  forall s t, lo <= s -> s <= t -> t < hi -> ag A s <= ag A t.

(* every value of A on [lo, hi) is a value of B on [lo, hi) *)
Definition sub_on (A B : array int) (lo hi : Z) : Prop :=
  forall z, lo <= z < hi -> exists s, lo <= s < hi /\ ag A z = ag B s.

Lemma ltb_Z : forall a b : int, (a <? b)%uint63 = true <-> to_Z a < to_Z b.
Proof. intros. apply Uint63.ltb_spec. Qed.

Lemma ltb_Z_false : forall a b : int, (a <? b)%uint63 = false <-> to_Z b <= to_Z a.
Proof. intros. rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec. lia. Qed.

Lemma leb_Z : forall a b : int, (a <=? b)%uint63 = true <-> to_Z a <= to_Z b.
Proof. intros. apply Uint63.leb_spec. Qed.

Lemma leb_Z_false : forall a b : int, (a <=? b)%uint63 = false <-> to_Z b < to_Z a.
Proof. intros. rewrite <- Bool.not_true_iff_false, Uint63.leb_spec. lia. Qed.

Lemma eqb_Z : forall a b : int, (a =? b)%uint63 = true <-> to_Z a = to_Z b.
Proof. intros. rewrite Uint63.eqb_spec. split; [intros ->; reflexivity | apply to_Z_inj]. Qed.

Lemma eqb_Z_false : forall a b : int, (a =? b)%uint63 = false <-> to_Z a <> to_Z b.
Proof. intros. rewrite <- Bool.not_true_iff_false, eqb_Z. reflexivity. Qed.

Lemma succ_Z : forall i : int, to_Z i < 4194304 -> to_Z (i + 1)%uint63 = to_Z i + 1.
Proof. intros. sia. Qed.

Section Merge.
Variables (src D0 : array int) (lo mid hi : int).
Let n := to_Z (PArray.length D0).
Hypothesis Hord : to_Z lo <= to_Z mid <= to_Z hi.
Hypothesis Hhi : to_Z hi <= n.
Hypothesis Hs1 : sorted_on src (to_Z lo) (to_Z mid).
Hypothesis Hs2 : sorted_on src (to_Z mid) (to_Z hi).

Definition MI (k : int) (st : int * int * array int) : Prop :=
  let '(i, j, D) := st in
  to_Z lo <= to_Z i <= to_Z mid /\ to_Z mid <= to_Z j <= to_Z hi /\
  to_Z k = to_Z i + to_Z j - to_Z mid /\
  PArray.length D = PArray.length D0 /\
  (forall z, 0 <= z < n -> z < to_Z lo \/ to_Z k <= z -> ag D z = ag D0 z) /\
  sorted_on D (to_Z lo) (to_Z k) /\
  (forall z, to_Z lo <= z < to_Z k ->
     (to_Z i < to_Z mid -> ag D z <= ag src (to_Z i)) /\
     (to_Z j < to_Z hi -> ag D z <= ag src (to_Z j))) /\
  (forall z, to_Z lo <= z < to_Z k -> exists s,
     (to_Z lo <= s < to_Z i \/ to_Z mid <= s < to_Z j) /\ ag D z = ag src s) /\
  (forall s, (to_Z lo <= s < to_Z i \/ to_Z mid <= s < to_Z j) ->
     exists z, to_Z lo <= z < to_Z k /\ ag D z = ag src s).

Lemma MI_step : forall k st, to_Z lo <= to_Z k < to_Z hi -> MI k st ->
  MI (k + 1)%uint63 (merge_step src mid hi k st).
Proof.
  intros k [[i j] D] Hk (Hi & Hj & Ek & Hlen & Hout & Hsort & Hhead & Hm1 & Hm2).
  pose proof (ilength_bound D0) as LB.
  assert (Ek1 : to_Z (k + 1)%uint63 = to_Z k + 1) by (apply succ_Z; lia).
  assert (Kin : to_Z k < to_Z (PArray.length D)) by (rewrite Hlen; fold n; lia).
  unfold merge_step.
  destruct ((i <? mid) && ((hi <=? j) || (src.[i] <=? src.[j])))%uint63 eqn:C.
  - apply andb_prop in C. destruct C as [C1 C2]. rewrite ltb_Z in C1.
    assert (C2' : to_Z hi <= to_Z j \/ to_Z src.[i] <= to_Z src.[j]).
    { apply orb_prop in C2. destruct C2 as [C2 | C2]; [left | right]; apply leb_Z in C2; lia. }
    assert (Ei1 : to_Z (i + 1)%uint63 = to_Z i + 1) by (apply succ_Z; lia).
    set (D' := D.[k <- src.[i]]).
    assert (AD : forall z, 0 <= z < wB -> ag D' z = if Z.eqb z (to_Z k) then to_Z src.[i] else ag D z)
      by (intros z Hz; apply ag_set; assumption).
    assert (Hhd : to_Z i + 1 < to_Z mid -> to_Z src.[i] <= ag src (to_Z i + 1)).
    { intros H. rewrite <- ag_int. apply Hs1; lia. }
    assert (W : forall z, to_Z lo <= z < to_Z k + 1 -> 0 <= z < wB)
      by (intros; pose proof (to_Z_bounded lo); rewrite wB_val; lia).
    repeat split; try lia.
    + unfold D'. rewrite ilength_set. exact Hlen.
    + intros z Hz Hz'. rewrite AD by (rewrite wB_val; lia).
      destruct (Z.eqb_spec z (to_Z k)); [lia |]. apply Hout; lia.
    + intros s t H1 H2 H3. rewrite !AD by (apply W; lia).
      destruct (Z.eqb_spec t (to_Z k)), (Z.eqb_spec s (to_Z k)); try lia.
      * rewrite <- ag_int. apply (proj1 (Hhead s ltac:(lia))). exact C1.
      * apply Hsort; lia.
    + intros Hc. rewrite Ei1 in Hc |- *. rewrite AD by (apply W; lia).
      destruct (Z.eqb_spec z (to_Z k)); [apply Hhd; exact Hc |].
      etransitivity; [apply (proj1 (Hhead z ltac:(lia))); exact C1 |].
      rewrite ag_int. apply Hhd; exact Hc.
    + intros Hc. rewrite AD by (apply W; lia).
      destruct (Z.eqb_spec z (to_Z k)).
      * rewrite ag_int. destruct C2' as [C2' | C2']; [exfalso; clear - C2' Hc; lia | exact C2'].
      * apply (proj2 (Hhead z ltac:(lia))). exact Hc.
    + intros z Hz. rewrite AD by (apply W; lia). rewrite Ei1.
      destruct (Z.eqb_spec z (to_Z k)).
      * exists (to_Z i). split; [lia | rewrite ag_int; reflexivity].
      * destruct (Hm1 z ltac:(lia)) as (s & Hs & E). exists s. split; [lia | exact E].
    + intros s Hs. rewrite Ei1 in Hs.
      destruct (Z.eq_dec s (to_Z i)) as [E | E].
      * exists (to_Z k). split; [lia |]. rewrite AD by (apply W; lia).
        rewrite Z.eqb_refl, E, ag_int. reflexivity.
      * destruct (Hm2 s ltac:(lia)) as (z & Hz & Ez). exists z. split; [lia |].
        rewrite AD by (apply W; lia). destruct (Z.eqb_spec z (to_Z k)); [lia | exact Ez].
  - assert (C' : to_Z mid <= to_Z i \/ (to_Z j < to_Z hi /\ to_Z src.[j] < to_Z src.[i])).
    { apply Bool.andb_false_iff in C. destruct C as [C | C]; [left; apply ltb_Z_false; exact C |].
      apply Bool.orb_false_iff in C. destruct C as [C3 C4].
      apply leb_Z_false in C3, C4. right. lia. }
    assert (Jhi : to_Z j < to_Z hi) by lia.
    assert (Ej1 : to_Z (j + 1)%uint63 = to_Z j + 1) by (apply succ_Z; lia).
    set (D' := D.[k <- src.[j]]).
    assert (AD : forall z, 0 <= z < wB -> ag D' z = if Z.eqb z (to_Z k) then to_Z src.[j] else ag D z)
      by (intros z Hz; apply ag_set; assumption).
    assert (Hhd : to_Z j + 1 < to_Z hi -> to_Z src.[j] <= ag src (to_Z j + 1)).
    { intros H. rewrite <- ag_int. apply Hs2; lia. }
    assert (W : forall z, to_Z lo <= z < to_Z k + 1 -> 0 <= z < wB)
      by (intros; pose proof (to_Z_bounded lo); rewrite wB_val; lia).
    repeat split; try lia.
    + unfold D'. rewrite ilength_set. exact Hlen.
    + intros z Hz Hz'. rewrite AD by (rewrite wB_val; lia).
      destruct (Z.eqb_spec z (to_Z k)); [lia |]. apply Hout; lia.
    + intros s t H1 H2 H3. rewrite !AD by (apply W; lia).
      destruct (Z.eqb_spec t (to_Z k)), (Z.eqb_spec s (to_Z k)); try lia.
      * rewrite <- ag_int. apply (proj2 (Hhead s ltac:(lia))). exact Jhi.
      * apply Hsort; lia.
    + intros Hc. rewrite AD by (apply W; lia).
      destruct (Z.eqb_spec z (to_Z k)).
      * rewrite ag_int. destruct C' as [C' | [_ C']]; [exfalso; clear - C' Hc; lia | lia].
      * apply (proj1 (Hhead z ltac:(lia))). exact Hc.
    + intros Hc. rewrite Ej1 in Hc |- *. rewrite AD by (apply W; lia).
      destruct (Z.eqb_spec z (to_Z k)); [apply Hhd; exact Hc |].
      etransitivity; [apply (proj2 (Hhead z ltac:(lia))); exact Jhi |].
      rewrite ag_int. apply Hhd; exact Hc.
    + intros z Hz. rewrite AD by (apply W; lia). rewrite Ej1.
      destruct (Z.eqb_spec z (to_Z k)).
      * exists (to_Z j). split; [lia | rewrite ag_int; reflexivity].
      * destruct (Hm1 z ltac:(lia)) as (s & Hs & E). exists s. split; [lia | exact E].
    + intros s Hs. rewrite Ej1 in Hs.
      destruct (Z.eq_dec s (to_Z j)) as [E | E].
      * exists (to_Z k). split; [lia |]. rewrite AD by (apply W; lia).
        rewrite Z.eqb_refl, E, ag_int. reflexivity.
      * destruct (Hm2 s ltac:(lia)) as (z & Hz & Ez). exists z. split; [lia |].
        rewrite AD by (apply W; lia). destruct (Z.eqb_spec z (to_Z k)); [lia | exact Ez].
Qed.

Lemma merge_spec :
  let D := merge src lo mid hi D0 in
  PArray.length D = PArray.length D0 /\
  (forall z, 0 <= z < n -> z < to_Z lo \/ to_Z hi <= z -> ag D z = ag D0 z) /\
  sorted_on D (to_Z lo) (to_Z hi) /\
  sub_on D src (to_Z lo) (to_Z hi) /\ sub_on src D (to_Z lo) (to_Z hi).
Proof.
  cbv zeta. unfold merge.
  pose proof (for_inv MI hi lo (merge_step src mid hi) (lo, mid, D0) ltac:(lia)) as F.
  destruct (loop hi (fun _ _ => true) (merge_step src mid hi) lo (lo, mid, D0)) as [[i j] D].
  destruct F as (Hi & Hj & Ek & Hlen & Hout & Hsort & _ & Hm1 & Hm2).
  - unfold MI. split; [lia |]. split; [lia |]. split; [lia |]. split; [reflexivity |].
    split; [intros; reflexivity |]. split; [unfold sorted_on; intros; lia |].
    split; [intros; lia |]. split; [intros; lia |]. intros; lia.
  - intros k st Hk Hst. apply MI_step; assumption.
  - repeat split; try assumption.
    + intros z Hz. destruct (Hm1 z Hz) as (s & Hs & E). exists s. split; [lia | exact E].
    + intros s Hs. destruct (Hm2 s ltac:(lia)) as (z & Hz & E). exists z. split; [lia | exact (eq_sym E)].
Qed.

End Merge.

Definition blocks (A : array int) (W N : Z) : Prop :=
  forall s t, 0 <= s -> s <= t -> t < N -> s / W = t / W -> ag A s <= ag A t.

Section Pass.
Variables (src D0 : array int) (n w : int).
Let N := to_Z n.
Let W := to_Z w.
Hypothesis Hsl : PArray.length src = n.
Hypothesis Hdl : PArray.length D0 = n.
Hypothesis Hw : 1 <= W < N.
Hypothesis Hb : blocks src W N.

Lemma N_bound : N <= 4194303.
Proof. unfold N. rewrite <- Hdl. apply ilength_bound. Qed.

Definition PI (c : int) (D : array int) : Prop :=
  let lo := Z.min (to_Z c * (2 * W)) N in
  PArray.length D = n /\ blocks D (2 * W) lo /\ sub_on D src 0 lo /\ sub_on src D 0 lo.

Lemma ww_Z : to_Z (w + w)%uint63 = 2 * W.
Proof. pose proof N_bound. unfold W, N in *. sia. Qed.

Lemma nb_Z : to_Z ((n + (w + w) - 1) / (w + w))%uint63 = (N + 2 * W - 1) / (2 * W).
Proof.
  pose proof N_bound. pose proof ww_Z.
  rewrite Uint63.div_spec, H0.
  assert (to_Z (n + (w + w) - 1)%uint63 = N + 2 * W - 1) by (unfold W, N in *; sia).
  rewrite H1. reflexivity.
Qed.

Lemma PI_step : forall c D, 0 <= to_Z c < (N + 2 * W - 1) / (2 * W) -> PI c D ->
  PI (c + 1)%uint63 (pass_step src n w c D).
Proof.
  intros c D Hc (Hl & Hbl & Hs1 & Hs2).
  pose proof N_bound as NB. pose proof ww_Z as WW.
  set (C := to_Z c) in *.
  assert (Hlo : C * (2 * W) < N).
  { assert (C + 1 <= (N + 2 * W - 1) / (2 * W)) by lia.
    assert ((C + 1) * (2 * W) <= N + 2 * W - 1).
    { apply Z.le_trans with (((N + 2 * W - 1) / (2 * W)) * (2 * W)); [nia |].
      rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
    lia. }
  assert (CN : C < N) by nia.
  assert (C1 : to_Z (c + 1)%uint63 = C + 1) by (apply succ_Z; lia).
  assert (Elo : to_Z (c * (w + w))%uint63 = C * (2 * W)).
  { rewrite Uint63.mul_spec, WW. apply Z.mod_small. rewrite wB_val. nia. }
  set (lo := (c * (w + w))%uint63) in *.
  set (mid := if (lo + w <? n)%uint63 then (lo + w)%uint63 else n).
  set (hi := if (lo + (w + w) <? n)%uint63 then (lo + (w + w))%uint63 else n).
  assert (Emid : to_Z mid = Z.min (C * (2 * W) + W) N).
  { unfold mid. assert (E : to_Z (lo + w)%uint63 = C * (2 * W) + W) by (unfold W in *; sia).
    destruct (lo + w <? n)%uint63 eqn:T; [apply ltb_Z in T | apply ltb_Z_false in T];
      rewrite ?E in *; unfold N in *; lia. }
  assert (Ehi : to_Z hi = Z.min (C * (2 * W) + 2 * W) N).
  { unfold hi. assert (E : to_Z (lo + (w + w))%uint63 = C * (2 * W) + 2 * W) by (unfold W in *; sia).
    destruct (lo + (w + w) <? n)%uint63 eqn:T; [apply ltb_Z in T | apply ltb_Z_false in T];
      rewrite ?E in *; unfold N in *; lia. }
  assert (Wpos : 0 < 2 * W) by lia.
  assert (S1 : sorted_on src (to_Z lo) (to_Z mid)).
  { intros s t H1 H2 H3. apply Hb; try lia. rewrite Elo in H1. rewrite Emid in H3.
    assert (s / W = 2 * C) by (symmetry; apply Z.div_unique with (s - 2 * C * W); [left; lia | ring]).
    assert (t / W = 2 * C) by (symmetry; apply Z.div_unique with (t - 2 * C * W); [left; lia | ring]). lia. }
  assert (S2 : sorted_on src (to_Z mid) (to_Z hi)).
  { intros s t H1 H2 H3. apply Hb; try lia. rewrite Emid in H1. rewrite Ehi in H3.
    assert (s / W = 2 * C + 1) by (symmetry; apply Z.div_unique with (s - (2 * C + 1) * W); [left; lia | ring]).
    assert (t / W = 2 * C + 1) by (symmetry; apply Z.div_unique with (t - (2 * C + 1) * W); [left; lia | ring]). lia. }
  assert (Ord : to_Z lo <= to_Z mid <= to_Z hi) by lia.
  assert (Hhi : to_Z hi <= to_Z (PArray.length D)) by (rewrite Hl; fold N; lia).
  pose proof (merge_spec src D lo mid hi Ord Hhi S1 S2) as M. cbv zeta in M.
  unfold pass_step. fold lo. fold mid. fold hi.
  destruct M as (Ml & Mout & Msort & Mm1 & Mm2).
  set (D' := merge src lo mid hi D) in *.
  unfold PI. rewrite C1.
  replace (Z.min ((C + 1) * (2 * W)) N) with (to_Z hi) by lia.
  replace (Z.min (C * (2 * W)) N) with (to_Z lo) in Hbl, Hs1, Hs2 by lia.
  assert (Old : forall z, 0 <= z < to_Z lo -> ag D' z = ag D z)
    by (intros z Hz; apply Mout; [rewrite Hl; fold N; lia | lia]).
  assert (LH : to_Z lo <= to_Z hi) by lia.
  assert (HN : to_Z hi <= N) by lia.
  assert (Ehi' : to_Z hi = Z.min (C * (2 * W) + 2 * W) N) by exact Ehi.
  clear Hhi Ord S1 S2 Emid Ehi Mout Hb.
  split; [rewrite Ml; exact Hl |].
  split; [| split].
  - intros s t H1 H2 H3 H4.
    destruct (Z_lt_le_dec t (to_Z lo)) as [T | T].
    + rewrite (Old s ltac:(lia)), (Old t ltac:(lia)). apply Hbl; lia.
    + assert (t / (2 * W) = C) by (symmetry; apply Z.div_unique with (t - C * (2 * W)); [left; lia | ring]).
      assert (to_Z lo <= s).
      { destruct (Z_lt_le_dec s (to_Z lo)) as [S | S]; [| exact S].
        assert (s / (2 * W) < C) by (apply Z.div_lt_upper_bound; lia). lia. }
      apply Msort; lia.
  - intros z Hz. destruct (Z_lt_le_dec z (to_Z lo)) as [T | T].
    + rewrite (Old z ltac:(lia)). destruct (Hs1 z ltac:(lia)) as (s & Hs & E). exists s. split; [lia | exact E].
    + destruct (Mm1 z ltac:(lia)) as (s & Hs & E). exists s. split; [lia | exact E].
  - intros s Hs. destruct (Z_lt_le_dec s (to_Z lo)) as [T | T].
    + destruct (Hs2 s ltac:(lia)) as (z & Hz & E). exists z. split; [lia |].
      rewrite E, (Old z ltac:(lia)). reflexivity.
    + destruct (Mm2 s ltac:(lia)) as (z & Hz & E). exists z. split; [lia | exact E].
Qed.

Lemma merge_pass_spec :
  let D := merge_pass src D0 n w in
  PArray.length D = n /\ blocks D (2 * W) N /\ sub_on D src 0 N /\ sub_on src D 0 N.
Proof.
  cbv zeta. unfold merge_pass.
  pose proof N_bound as NB.
  set (nb := ((n + (w + w) - 1) / (w + w))%uint63).
  assert (Enb : to_Z nb = (N + 2 * W - 1) / (2 * W)) by apply nb_Z.
  assert (P : PI nb (loop nb (fun _ _ => true) (pass_step src n w) 0 D0)).
  { apply for_inv.
    - change (to_Z 0) with 0. apply to_Z_bounded.
    - unfold PI. change (to_Z 0) with 0. rewrite Z.mul_0_l.
      replace (Z.min 0 N) with 0 by lia.
      split; [exact Hdl |]. split; [intros s t H1 H2 H3; exfalso; lia |].
      split; intros z Hz; exfalso; lia.
    - intros c D Hc HP. apply PI_step; [rewrite <- Enb; change (to_Z 0) with 0 in Hc; lia | exact HP]. }
  unfold PI in P. rewrite Enb in P.
  replace (Z.min ((N + 2 * W - 1) / (2 * W) * (2 * W)) N) with N in P; [exact P |].
  assert (N <= (N + 2 * W - 1) / (2 * W) * (2 * W)).
  { pose proof (Z.mod_pos_bound (N + 2 * W - 1) (2 * W) ltac:(lia)).
    pose proof (Z.div_mod (N + 2 * W - 1) (2 * W) ltac:(lia)). lia. }
  lia.
Qed.

End Pass.

Lemma msort_rec_eq : forall n w A B H,
  msort_rec n w A B H =
  match bdec ((w <? n) && (w <? w + w))%uint63 with
  | left Hw => msort_rec n (w + w) (merge_pass A B n w) A (Acc_inv H (dec_double n w Hw))
  | right _ => A
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma msort_spec : forall (A0 : array int) (n : int), PArray.length A0 = n ->
  let R := msort A0 n in
  PArray.length R = n /\ sorted_on R 0 (to_Z n) /\
  sub_on R A0 0 (to_Z n) /\ sub_on A0 R 0 (to_Z n).
Proof.
  intros A0 n Hl. cbv zeta. unfold msort.
  pose proof (ilength_bound A0) as NB. rewrite Hl in NB.
  assert (G : forall g w A B (H : Acc (Zwf 0) (gap n w)), gap n w = g ->
    1 <= to_Z w -> PArray.length A = n -> PArray.length B = n ->
    blocks A (to_Z w) (to_Z n) -> sub_on A A0 0 (to_Z n) -> sub_on A0 A 0 (to_Z n) ->
    let R := msort_rec n w A B H in
    PArray.length R = n /\ sorted_on R 0 (to_Z n) /\
    sub_on R A0 0 (to_Z n) /\ sub_on A0 R 0 (to_Z n)).
  { intros g. induction g as [g IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros w A B H Eg Hw HA HB Hbl Hs1 Hs2. cbv zeta. rewrite msort_rec_eq.
    destruct (bdec ((w <? n) && (w <? w + w))%uint63) as [T | T].
    - pose proof T as T'. apply andb_prop in T'. destruct T' as [T1 _]. apply ltb_Z in T1.
      assert (Eww : to_Z (w + w)%uint63 = 2 * to_Z w) by sia.
      pose proof (merge_pass_spec A B n w HA HB ltac:(lia) Hbl) as (Ml & Mb & Mm1 & Mm2).
      apply (IH (gap n (w + w))); try assumption.
      + rewrite <- Eg. apply dec_double. exact T.
      + reflexivity.
      + lia.
      + rewrite Eww. exact Mb.
      + intros z Hz. destruct (Mm1 z Hz) as (s & Hs & E). destruct (Hs1 s Hs) as (s' & Hs' & E').
        exists s'. split; [exact Hs' | lia].
      + intros z Hz. destruct (Hs2 z Hz) as (s & Hs & E). destruct (Mm2 s Hs) as (s' & Hs' & E').
        exists s'. split; [exact Hs' | lia].
    - assert (Wn : to_Z n <= to_Z w).
      { apply Bool.andb_false_iff in T. destruct T as [T | T]; [apply ltb_Z_false in T; exact T |].
        apply ltb_Z_false in T. destruct (Z_lt_le_dec (to_Z w) (to_Z n)) as [L | L]; [| exact L].
        exfalso. assert (to_Z (w + w)%uint63 = 2 * to_Z w) by sia. lia. }
      split; [exact HA |]. split; [| split; assumption].
      intros s t H1 H2 H3. apply Hbl; try lia.
      rewrite !Z.div_small by lia. reflexivity. }
  apply G with (g := gap n 1); try reflexivity.
  - change (to_Z 1) with 1. lia.
  - apply ilength_make_small. exact NB.
  - intros s t H1 H2 H3 H4. change (to_Z 1) with 1 in H4. rewrite !Z.div_1_r in H4. subst. lia.
  - intros z Hz. exists z. split; [exact Hz | reflexivity].
  - intros z Hz. exists z. split; [exact Hz | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Removal of duplicates, negation                                      *)
(* ------------------------------------------------------------------ *)

Definition incr_on (Q : array int) (m : Z) : Prop :=
  forall s t, 0 <= s -> s < t -> t < m -> ag Q s < ag Q t.

Section Dedup.
Variables (A : array int) (n : int).
Let N := to_Z n.
Hypothesis Hl : PArray.length A = n.
Hypothesis Hn : 1 <= N.
Hypothesis Hs : sorted_on A 0 N.

Definition DI (i : int) (st : array int * int) : Prop :=
  let '(Q, m) := st in
  PArray.length Q = n /\ 1 <= to_Z m <= to_Z i /\ incr_on Q (to_Z m) /\
  ag Q (to_Z m - 1) = ag A (to_Z i - 1) /\
  (forall z, 0 <= z < to_Z m -> exists s, 0 <= s < to_Z i /\ ag Q z = ag A s) /\
  (forall s, 0 <= s < to_Z i -> exists z, 0 <= z < to_Z m /\ ag A s = ag Q z).

Lemma DI_step : forall i st, 1 <= to_Z i < N -> DI i st -> DI (i + 1)%uint63 (dedup_step A i st).
Proof.
  intros i [Q m] Hi (HQ & Hm & Hinc & Htop & H1 & H2).
  pose proof (ilength_bound A) as NB. rewrite Hl in NB. fold N in NB.
  assert (Ei : to_Z (i + 1)%uint63 = to_Z i + 1) by (apply succ_Z; lia).
  assert (Em : to_Z (m - 1)%uint63 = to_Z m - 1) by sia.
  assert (Ale : ag A (to_Z i - 1) <= ag A (to_Z i)) by (apply Hs; lia).
  unfold dedup_step.
  destruct (A.[i] =? Q.[m - 1])%uint63 eqn:E; unfold DI; rewrite Ei.
  - apply eqb_Z in E. rewrite <- !ag_int, Em in E.
    split; [exact HQ |]. split; [lia |]. split; [exact Hinc |]. split; [| split].
    + rewrite <- E. f_equal. lia.
    + intros z Hz. destruct (H1 z Hz) as (s & Hs' & Es). exists s. split; [lia | exact Es].
    + intros s Hs'. destruct (Z.eq_dec s (to_Z i)) as [-> | Ns].
      * exists (to_Z m - 1). split; [lia |]. rewrite E. reflexivity.
      * destruct (H2 s ltac:(lia)) as (z & Hz & Ez). exists z. split; [exact Hz | exact Ez].
  - apply eqb_Z_false in E. rewrite <- !ag_int, Em in E.
    assert (Mlt : to_Z m < to_Z (PArray.length Q)) by (rewrite HQ; fold N; lia).
    assert (Em1 : to_Z (m + 1)%uint63 = to_Z m + 1) by (apply succ_Z; lia).
    assert (AQ : forall z, 0 <= z < wB -> ag (Q.[m <- A.[i]]) z =
                   if Z.eqb z (to_Z m) then to_Z A.[i] else ag Q z)
      by (intros; apply ag_set; assumption).
    assert (W : forall z, 0 <= z <= to_Z m -> 0 <= z < wB) by (intros; rewrite wB_val; lia).
    rewrite Em1. split; [| split; [lia | split; [| split; [| split]]]].
    + rewrite ilength_set. exact HQ.
    + intros s t S1 S2 S3. rewrite !AQ by (apply W; lia).
      destruct (Z.eqb_spec t (to_Z m)), (Z.eqb_spec s (to_Z m)); try lia.
      * rewrite <- ag_int. assert (ag Q s <= ag Q (to_Z m - 1)).
        { destruct (Z.eq_dec s (to_Z m - 1)) as [-> | Ns]; [lia |].
          apply Z.lt_le_incl, Hinc; lia. }
        lia.
      * apply Hinc; lia.
    + rewrite AQ by (apply W; lia). replace (to_Z m + 1 - 1) with (to_Z m) by lia.
      rewrite Z.eqb_refl, <- ag_int. f_equal. lia.
    + intros z Hz. rewrite AQ by (apply W; lia). destruct (Z.eqb_spec z (to_Z m)).
      * exists (to_Z i). split; [lia | rewrite ag_int; reflexivity].
      * destruct (H1 z ltac:(lia)) as (s & Hs' & Es). exists s. split; [lia | exact Es].
    + intros s Hs'. destruct (Z.eq_dec s (to_Z i)) as [-> | Ns].
      * exists (to_Z m). split; [lia |]. rewrite AQ by (apply W; lia). rewrite Z.eqb_refl, ag_int. reflexivity.
      * destruct (H2 s ltac:(lia)) as (z & Hz & Ez). exists z. split; [lia |].
        rewrite AQ by (apply W; lia). destruct (Z.eqb_spec z (to_Z m)); [lia | exact Ez].
Qed.

Lemma dedup_spec :
  let '(Q, m) := loop n (fun _ _ => true) (dedup_step A) 1 (PArray.make n A.[0], 1%uint63) in
  PArray.length Q = n /\ 1 <= to_Z m <= N /\ incr_on Q (to_Z m) /\
  (forall z, 0 <= z < to_Z m -> exists s, 0 <= s < N /\ ag Q z = ag A s) /\
  (forall s, 0 <= s < N -> exists z, 0 <= z < to_Z m /\ ag A s = ag Q z).
Proof.
  pose proof (ilength_bound A) as NB. rewrite Hl in NB. fold N in NB.
  pose proof (for_inv DI n 1 (dedup_step A) (PArray.make n A.[0], 1%uint63)) as F.
  destruct (loop n (fun _ _ => true) (dedup_step A) 1 (PArray.make n A.[0], 1%uint63)) as [Q m].
  destruct F as (HQ & Hm & Hinc & _ & H1 & H2).
  - change (to_Z 1) with 1. fold N. lia.
  - unfold DI. change (to_Z 1) with 1. simpl Z.sub.
    split; [apply ilength_make_small; fold N; lia |]. split; [lia |].
    split; [intros s t S1 S2 S3; exfalso; lia |].
    split; [rewrite !ag_make; unfold ag; reflexivity |].
    split; intros z Hz; exists 0; (split; [lia |]); assert (z = 0) by lia; subst z;
      rewrite ?ag_make; unfold ag; reflexivity.
  - intros j t Hj Ht. apply DI_step; [fold N in Hj; change (to_Z 1) with 1 in Hj; lia | exact Ht].
  - exact (conj HQ (conj Hm (conj Hinc (conj H1 H2)))).
Qed.

End Dedup.

Section Neg.
Variables (Q : array int) (m : int).
Let M := to_Z m.
Hypothesis Hm : 1 <= M <= 4194303.
Hypothesis Hv : forall z, 0 <= z < M -> 0 <= ag Q z <= 4098000.

Lemma neg_spec :
  let B := loop m (fun _ _ => true) (neg_step Q m) 0%uint63 (PArray.make m 0%uint63) in
  PArray.length B = m /\ forall z, 0 <= z < M -> ag B z = 4098000 - ag Q (M - 1 - z).
Proof.
  cbv zeta. apply (for_inv (fun i B => PArray.length B = m /\
      forall z, 0 <= z < to_Z i -> ag B z = 4098000 - ag Q (M - 1 - z))).
  - change (to_Z 0) with 0. lia.
  - split; [apply ilength_make_small; fold M; lia |]. intros z Hz. change (to_Z 0) with 0 in Hz. lia.
  - intros i B Hi (HB & Hz). change (to_Z 0) with 0 in Hi. fold M in Hi.
    assert (Ei : to_Z (i + 1)%uint63 = to_Z i + 1) by (apply succ_Z; lia).
    unfold neg_step. split; [rewrite ilength_set; exact HB |].
    intros z Hz'. rewrite Ei in Hz'.
    rewrite ag_set by (rewrite ?HB; fold M; rewrite ?wB_val; lia).
    destruct (Z.eqb_spec z (to_Z i)) as [-> | Nz]; [| apply Hz; lia].
    assert (E1 : to_Z (m - 1 - i)%uint63 = M - 1 - to_Z i) by (fold M; sia).
    pose proof (Hv (M - 1 - to_Z i) ltac:(lia)) as V. rewrite <- E1, ag_int in V |- *.
    rewrite Uint63.sub_spec. change (to_Z Kneg) with 4098000. apply Z.mod_small. rewrite wB_val. lia.
Qed.

End Neg.

(* ------------------------------------------------------------------ *)
(* The monotone chain                                                  *)
(* ------------------------------------------------------------------ *)

Definition crk (a b c : Z) : Z := cr (PX a) (PY a) (PX b) (PY b) (PX c) (PY c).

Lemma crk_swap : forall a b c, crk a c b = - crk a b c.
Proof. intros. unfold crk, cr. ring. Qed.

Lemma sv_mcross3 : forall a b c : int, KR (to_Z a) -> KR (to_Z b) -> KR (to_Z c) ->
  sv (mcross a b a c) = crk (to_Z a) (to_Z b) (to_Z c).
Proof.
  intros a b c Ha Hb Hc. rewrite sv_mcross by assumption. unfold vcross, crk, cr. ring.
Qed.

Lemma sltb0 : forall x : int, Sint63.ltb 0 x = true <-> 0 < sv x.
Proof.
  intros x. destruct (Sint63.ltbP 0 x) as [H | H]; change (sv 0) with 0 in H;
    split; intros; try lia; try reflexivity; discriminate.
Qed.

(* p is on the chain S[0 .. T), or above one of its edges, between its ends *)
Definition supp (S : array int) (T p : Z) : Prop :=
  (exists a, 0 <= a < T /\ ag S a = p) \/
  (exists a, 0 <= a /\ a + 1 < T /\ ag S a <= p <= ag S (a + 1) /\
             0 <= crk (ag S a) (ag S (a + 1)) p).

Section Chain.
Variables (Q : array int) (m : int).
Let M := to_Z m.
Hypothesis HmQ : M <= to_Z (PArray.length Q).
Hypothesis Hm2 : 2 <= M.
Hypothesis Hinc : incr_on Q M.
Hypothesis HKR : forall z, 0 <= z < M -> KR (ag Q z).

Lemma M_bound : M <= 4194303.
Proof. pose proof (ilength_bound Q). lia. Qed.

Definition SI (S : array int) (T : Z) : Prop :=
  PArray.length S = m /\ 1 <= T /\ ag S 0 = ag Q 0 /\
  (forall a, 0 <= a < T -> exists r, 0 <= r < M /\ ag S a = ag Q r) /\
  (forall a, 0 <= a -> a + 1 < T -> ag S a < ag S (a + 1)) /\
  (forall a, 0 <= a -> a + 2 < T -> 0 < crk (ag S a) (ag S (a + 1)) (ag S (a + 2))).

Lemma SI_KR : forall S T a, SI S T -> 0 <= a < T -> KR (ag S a).
Proof.
  intros S T a (_ & _ & _ & H & _) Ha. destruct (H a Ha) as (r & Hr & ->). apply HKR; exact Hr.
Qed.

Lemma SI_mono : forall S T a b, SI S T -> 0 <= a -> a <= b -> b < T -> ag S a <= ag S b.
Proof.
  intros S T a b HS Ha Hab Hb. destruct HS as (_ & _ & _ & _ & H5 & _).
  assert (G : forall d, 0 <= d -> a + d < T -> ag S a <= ag S (a + d)).
  { intros d Hd. pattern d. apply natlike_ind; [ | | exact Hd].
    - rewrite Z.add_0_r; lia.
    - intros x Hx IH Hx'. pose proof (IH ltac:(lia)). pose proof (H5 (a + x) ltac:(lia) ltac:(lia)).
      replace (a + Z.succ x) with (a + x + 1) by lia. lia. }
  replace b with (a + (b - a)) by lia. apply G; lia.
Qed.

Lemma SI_shrink : forall S T T', SI S T -> 1 <= T' <= T -> SI S T'.
Proof.
  intros S T T' (H1 & H2 & H3 & H4 & H5 & H6) HT.
  split; [exact H1 |]. split; [lia |]. split; [exact H3 |].
  split; [intros a Ha; apply H4; lia |]. split; [intros a Ha Ha'; apply H5; lia |].
  intros a Ha Ha'; apply H6; lia.
Qed.

Lemma supp_shrink : forall S T T' p, T' <= T -> supp S T' p -> supp S T p.
Proof.
  intros S T T' p HT [(a & Ha & E) | (a & Ha & Ha' & B & C)]; [left | right]; exists a; repeat split; lia.
Qed.

(* the pop loop: c = Q[i], every point before it supported, or pending on (top, c) *)
Definition POPI (S : array int) (i : Z) (T : Z) : Prop :=
  SI S T /\ T <= i /\ ag S (T - 1) < ag Q i /\
  forall r, 0 <= r < i -> supp S T (ag Q r) \/
    (ag S (T - 1) <= ag Q r <= ag Q i /\ 0 <= crk (ag S (T - 1)) (ag Q i) (ag Q r)).

Lemma pops_eq : forall S c t H, pops S c t H =
  match bdec ((1 <? t) && negb (Sint63.ltb 0 (mcross S.[t - 2] S.[t - 1] S.[t - 2] c)))%uint63 with
  | left Hc => pops S c (t - 1) (Acc_inv H (dec_pred t _ Hc))
  | right _ => t
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma lex_of : forall a b, KR a -> a <= b -> LEX (PX a) (PY a) (PX b) (PY b).
Proof. intros a b Ha Hab. apply key_lex; unfold KR in Ha; lia. Qed.

Lemma pop_one : forall S i T, 0 <= i < M -> 2 <= T -> POPI S i T ->
  crk (ag S (T - 2)) (ag S (T - 1)) (ag Q i) <= 0 -> POPI S i (T - 1).
Proof.
  intros S i T Hi HT (HS & HTi & Htop & Hsup) Hcr.
  assert (KA : KR (ag S (T - 2))) by (apply (SI_KR S T); [exact HS | lia]).
  assert (KB : KR (ag S (T - 1))) by (apply (SI_KR S T); [exact HS | lia]).
  assert (KC : KR (ag Q i)) by (apply HKR; lia).
  assert (AB : ag S (T - 2) < ag S (T - 1))
    by (destruct HS as (_ & _ & _ & _ & H5 & _); replace (T - 1) with (T - 2 + 1) by lia; apply H5; lia).
  unfold POPI. replace (T - 1 - 1) with (T - 2) by lia.
  split; [apply (SI_shrink S T); [exact HS | lia] |].
  split; [lia |]. split; [lia |].
  intros r Hr.
  assert (KP : KR (ag Q r)) by (apply HKR; lia).
  assert (Prc : ag Q r < ag Q i) by (apply Hinc; lia).
  destruct (Hsup r Hr) as [[(a & Ha & E) | (a & Ha & Ha' & B & C)] | (B & C)].
  - destruct (Z.eq_dec a (T - 1)) as [-> | Na].
    + right. rewrite <- E. split; [lia |]. rewrite crk_swap. lia.
    + left. left. exists a. split; [lia | exact E].
  - destruct (Z.eq_dec (a + 1) (T - 1)) as [Ea | Na].
    + right. replace a with (T - 2) in * by lia. rewrite Ea in B, C. split; [lia |].
      exact (geo_pop _ _ _ _ _ _ _ _ (lex_of (ag S (T - 2)) (ag Q r) KA ltac:(lia))
               (lex_of (ag Q r) (ag S (T - 1)) KP ltac:(lia))
               (lex_of (ag S (T - 1)) (ag Q i) KB ltac:(lia)) C Hcr).
    + left. right. exists a. repeat split; lia.
  - right. split; [lia |].
    assert (H1 : 0 <= crk (ag S (T - 2)) (ag Q i) (ag S (T - 1))) by (rewrite crk_swap; lia).
    exact (geo_pend _ _ _ _ _ _ _ _ (lex_of (ag S (T - 2)) (ag S (T - 1)) KA ltac:(lia))
             (lex_of (ag S (T - 1)) (ag Q r) KB ltac:(lia))
             (lex_of (ag Q r) (ag Q i) KP ltac:(lia)) H1 C).
Qed.

Lemma pops_spec : forall S (i : int) g (t : int) H, gap t 0 = g ->
  0 <= to_Z i < M -> POPI S (to_Z i) (to_Z t) ->
  let t' := pops S Q.[i] t H in
  POPI S (to_Z i) (to_Z t') /\
  (to_Z t' = 1 \/ 0 < crk (ag S (to_Z t' - 2)) (ag S (to_Z t' - 1)) (ag Q (to_Z i))).
Proof.
  intros S i g. induction g as [g IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros t H Eg Hi HP. cbv zeta. rewrite pops_eq.
  pose proof HP as (HS & HTi & _ & _).
  pose proof (to_Z_bounded t) as Bt.
  destruct (bdec ((1 <? t) && negb (Sint63.ltb 0 (mcross S.[t - 2] S.[t - 1] S.[t - 2] Q.[i]))))%uint63
    as [T | T].
  - pose proof T as T'. apply andb_prop in T'. destruct T' as [T1 T2]. apply ltb_Z in T1.
    change (to_Z 1) with 1 in T1.
    assert (E2 : to_Z (t - 2)%uint63 = to_Z t - 2) by sia.
    assert (E1 : to_Z (t - 1)%uint63 = to_Z t - 1) by sia.
    apply Bool.negb_true_iff in T2. rewrite <- Bool.not_true_iff_false, sltb0 in T2.
    rewrite sv_mcross3 in T2 by (rewrite ?E1, ?E2, <- ?ag_int, ?E1, ?E2;
      first [apply (SI_KR S (to_Z t)); [exact HS | lia] | apply HKR; lia]).
    rewrite <- !ag_int, E1, E2 in T2.
    apply (IH (gap (t - 1) 0)); [| reflexivity | exact Hi |].
    + rewrite <- Eg. unfold gap, Zwf. change (to_Z 0) with 0. lia.
    + rewrite E1. apply pop_one; [lia | lia | exact HP | lia].
  - split; [exact HP |].
    destruct (Z.eq_dec (to_Z t) 1) as [E | E]; [left; exact E |].
    right. apply Bool.andb_false_iff in T. destruct T as [T | T].
    + exfalso. apply ltb_Z_false in T. change (to_Z 1) with 1 in T.
      destruct HS as (_ & HT1 & _). lia.
    + apply Bool.negb_false_iff, sltb0 in T.
      assert (Ht2 : 1 < to_Z t) by (destruct HS as (_ & HT1 & _); lia).
      assert (E2 : to_Z (t - 2)%uint63 = to_Z t - 2) by sia.
      assert (E1 : to_Z (t - 1)%uint63 = to_Z t - 1) by sia.
      rewrite sv_mcross3 in T by (rewrite ?E1, ?E2, <- ?ag_int, ?E1, ?E2;
        first [apply (SI_KR S (to_Z t)); [exact HS | lia] | apply HKR; lia]).
      rewrite <- !ag_int, E1, E2 in T. exact T.
Qed.

Definition CI (i : int) (st : array int * int) : Prop :=
  let '(Sk, t) := st in
  SI Sk (to_Z t) /\ to_Z t <= to_Z i /\ ag Sk (to_Z t - 1) = ag Q (to_Z i - 1) /\
  forall r, 0 <= r < to_Z i -> supp Sk (to_Z t) (ag Q r).

Lemma CI_step : forall i st, 1 <= to_Z i < M -> CI i st -> CI (i + 1)%uint63 (chain_step Q i st).
Proof.
  intros i [S t] Hi (HS & Hti & Htop & Hsup).
  pose proof M_bound as MB.
  assert (Ei : to_Z (i + 1)%uint63 = to_Z i + 1) by (apply succ_Z; lia).
  unfold chain_step.
  assert (P0 : POPI S (to_Z i) (to_Z t)).
  { split; [exact HS |]. split; [lia |]. split.
    - rewrite Htop. apply Hinc; lia.
    - intros r Hr. left. apply Hsup; exact Hr. }
  pose proof (pops_spec S i _ t (Zwf_well_founded 0 (to_Z t)) eq_refl ltac:(lia) P0) as PS.
  cbv zeta in PS.
  set (t' := pops S Q.[i] t (Zwf_well_founded 0 (to_Z t))) in *.
  destruct PS as ((HS' & Hti' & Htop' & Hsup') & Hend).
  pose proof HS' as (Hl & HT1 & H0 & H4 & H5 & H6).
  assert (Et : to_Z (t' + 1)%uint63 = to_Z t' + 1) by (apply succ_Z; lia).
  assert (Tin : to_Z t' < to_Z (PArray.length S)) by (rewrite Hl; fold M; lia).
  set (S' := S.[t' <- Q.[i]]).
  assert (AS : forall z, 0 <= z < wB -> ag S' z = if Z.eqb z (to_Z t') then ag Q (to_Z i) else ag S z)
    by (intros; unfold S'; rewrite ag_set by assumption; rewrite ag_int; reflexivity).
  assert (W : forall z, 0 <= z <= to_Z t' -> 0 <= z < wB) by (intros; rewrite wB_val; lia).
  assert (Old : forall z, 0 <= z < to_Z t' -> ag S' z = ag S z).
  { intros z Hz. rewrite AS by (apply W; lia). destruct (Z.eqb_spec z (to_Z t')); [lia | reflexivity]. }
  assert (New : ag S' (to_Z t') = ag Q (to_Z i)) by (rewrite AS by (apply W; lia); rewrite Z.eqb_refl; reflexivity).
  unfold CI. rewrite Et, Ei.
  split; [| split; [lia | split]].
  - split; [unfold S'; rewrite ilength_set; exact Hl |]. split; [lia |].
    split; [rewrite Old by lia; exact H0 |].
    split; [| split].
    + intros a Ha. destruct (Z.eq_dec a (to_Z t')) as [-> | Na].
      * exists (to_Z i). split; [lia | exact New].
      * rewrite Old by lia. apply H4; lia.
    + intros a Ha Ha'. destruct (Z.eq_dec (a + 1) (to_Z t')) as [Ea | Na].
      * rewrite <- Ea in New. rewrite New, Old by lia. replace a with (to_Z t' - 1) by lia. exact Htop'.
      * rewrite !Old by lia. apply H5; lia.
    + intros a Ha Ha'. destruct (Z.eq_dec (a + 2) (to_Z t')) as [Ea | Na].
      * rewrite <- Ea in New. rewrite New, !Old by lia.
        destruct Hend as [Hend | Hend]; [lia |].
        replace (to_Z t' - 2) with a in Hend by lia. replace (to_Z t' - 1) with (a + 1) in Hend by lia.
        exact Hend.
      * rewrite !Old by lia. apply H6; lia.
  - replace (to_Z t' + 1 - 1) with (to_Z t') by lia. replace (to_Z i + 1 - 1) with (to_Z i) by lia.
    exact New.
  - intros r Hr. destruct (Z.eq_dec r (to_Z i)) as [-> | Nr].
    + left. exists (to_Z t'). split; [lia | exact New].
    + destruct (Hsup' r ltac:(lia)) as [[(a & Ha & E) | (a & Ha & Ha' & B & C)] | (B & C)].
      * left. exists a. split; [lia |]. rewrite Old by lia. exact E.
      * right. exists a. rewrite !Old by lia. repeat split; lia.
      * right. exists (to_Z t' - 1). replace (to_Z t' - 1 + 1) with (to_Z t') by lia.
        rewrite New, Old by lia. repeat split; lia.
Qed.

Lemma chain_spec :
  let '(Sk, t) := chain Q m in
  SI Sk (to_Z t) /\ 2 <= to_Z t <= M /\ ag Sk (to_Z t - 1) = ag Q (M - 1) /\
  forall r, 0 <= r < M -> supp Sk (to_Z t) (ag Q r).
Proof.
  pose proof M_bound as MB.
  unfold chain.
  pose proof (for_inv CI m 1 (chain_step Q) (PArray.make m Q.[0], 1%uint63)) as F.
  destruct (loop m (fun _ _ => true) (chain_step Q) 1 (PArray.make m Q.[0], 1%uint63)) as [S t].
  destruct F as (HS & Hti & Htop & Hsup).
  - change (to_Z 1) with 1. fold M. lia.
  - unfold CI. change (to_Z 1) with 1. simpl Z.sub.
    assert (E0 : forall z, ag (PArray.make m Q.[0]) z = ag Q 0)
      by (intros z; rewrite ag_make; change 0 with (to_Z 0%uint63); rewrite ag_int; reflexivity).
    split; [| split; [lia | split; [apply E0 |]]].
    + split; [apply ilength_make_small; fold M; lia |]. split; [lia |]. split; [apply E0 |].
      split; [intros a Ha; exists 0; split; [lia | apply E0] |].
      split; intros a Ha Ha'; exfalso; lia.
    + intros r Hr. left. exists 0. split; [lia |]. replace r with 0 by lia. apply E0.
  - intros j st Hj Hst. apply CI_step; [change (to_Z 1) with 1 in Hj; fold M in Hj; lia | exact Hst].
  - split; [exact HS |]. split; [| split; [exact Htop | exact Hsup]].
    split; [| exact Hti].
    destruct HS as (_ & HT1 & H0 & _).
    destruct (Z.eq_dec (to_Z t) 1) as [E | E]; [| lia].
    rewrite E in Htop. simpl in Htop. rewrite H0 in Htop.
    pose proof (Hinc 0 (M - 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold M in *. lia.
Qed.

End Chain.

Lemma lexk : forall a b, KR a -> a <= b -> LEX (PX a) (PY a) (PX b) (PY b).
Proof. intros a b Ha Hab. apply key_lex; unfold KR in Ha; lia. Qed.

(* the linear functional w on the point of key a *)
Definition dw (wx wy a : Z) : Z := wx * PX a + wy * PY a.

(* an upward direction is minimised on the chain *)
Lemma supp_min : forall S T p wx wy, (forall a, 0 <= a < T -> KR (ag S a)) -> KR p -> 0 < wy ->
  supp S T p -> exists a, 0 <= a < T /\ dw wx wy (ag S a) <= dw wx wy p.
Proof.
  intros S T p wx wy HK Hp Hw [(a & Ha & E) | (a & Ha & Ha' & B & C)].
  - exists a. split; [exact Ha | rewrite E; lia].
  - assert (KA : KR (ag S a)) by (apply HK; lia).
    assert (KB : KR (ag S (a + 1))) by (apply HK; lia).
    destruct (geo_support _ _ _ _ _ _ wx wy (lexk (ag S a) p KA ltac:(lia))
                (lexk p (ag S (a + 1)) Hp ltac:(lia)) C Hw) as [G | G].
    + exists a. split; [lia | unfold dw; lia].
    + exists (a + 1). split; [lia | unfold dw; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Edge sequences of a convex chain                                     *)
(* ------------------------------------------------------------------ *)

Definition ex (S : array int) (j : Z) : Z := PX (ag S (j + 1)) - PX (ag S j).
Definition ey (S : array int) (j : Z) : Z := PY (ag S (j + 1)) - PY (ag S j).
Definition de (wx wy : Z) (S : array int) (j : Z) : Z := dot wx wy (ex S j) (ey S j).

(* S[0 .. l] is a convex chain: increasing keys, left turns *)
Definition convex (S : array int) (l : Z) : Prop :=
  (forall j, 0 <= j <= l -> KR (ag S j)) /\
  (forall j, 0 <= j < l -> ag S j < ag S (j + 1)) /\
  (forall j, 0 <= j -> j + 1 < l -> 0 < crk (ag S j) (ag S (j + 1)) (ag S (j + 2))).

Lemma convex_lexpos : forall S l j, convex S l -> 0 <= j < l -> lexpos (ex S j) (ey S j).
Proof.
  intros S l j (HK & Hi & _) Hj. unfold ex, ey. apply key_lexpos; [| apply Hi; lia].
  pose proof (HK j ltac:(lia)) as K. unfold KR in K. lia.
Qed.

Lemma convex_turn : forall S l j, convex S l -> 0 <= j -> j + 1 < l ->
  0 < vcross (ex S j) (ey S j) (ex S (j + 1)) (ey S (j + 1)).
Proof.
  intros S l j (_ & _ & Hc) H1 H2. pose proof (Hc j H1 H2) as C.
  unfold vcross, ex, ey. replace (j + 1 + 1) with (j + 2) by lia.
  unfold crk, cr in C. lia.
Qed.

Lemma convex_suffix : forall S l wx wy j, convex S l -> 0 < wy -> 0 <= j < l ->
  0 <= de wx wy S j -> forall j', j <= j' < l -> 0 <= de wx wy S j'.
Proof.
  intros S l wx wy j HC Hw Hj H0 j' Hj'.
  assert (G : forall d, 0 <= d -> j + d < l -> 0 <= de wx wy S (j + d)).
  { intros d Hd. pattern d. apply natlike_ind; [ | | exact Hd].
    - rewrite Z.add_0_r. intros; exact H0.
    - intros x Hx IH Hx'. pose proof (IH ltac:(lia)) as P.
      replace (j + Z.succ x) with (j + x + 1) by lia.
      apply Z.lt_le_incl. unfold de in *.
      apply (geo_turn (ex S (j + x)) (ey S (j + x))); try assumption.
      + apply (convex_lexpos S l); [exact HC | lia].
      + apply (convex_lexpos S l); [exact HC | lia].
      + apply (convex_turn S l); [exact HC | lia | lia]. }
  replace j' with (j + (j' - j)) by lia. apply G; lia.
Qed.

(* telescoping: a good index minimises w on the chain *)
Lemma de_tele : forall S wx wy j, de wx wy S j = dw wx wy (ag S (j + 1)) - dw wx wy (ag S j).
Proof. intros. unfold de, dot, dw, ex, ey. ring. Qed.

Lemma good_min : forall S l wx wy j, 0 <= j <= l ->
  (forall j', 0 <= j' < j -> de wx wy S j' <= 0) ->
  (forall j', j <= j' < l -> 0 <= de wx wy S j') ->
  forall i, 0 <= i <= l -> dw wx wy (ag S j) <= dw wx wy (ag S i).
Proof.
  intros S l wx wy j Hj Hpre Hsuf i Hi.
  destruct (Z_le_gt_dec j i) as [L | L].
  - assert (G : forall d, 0 <= d -> j + d <= l -> dw wx wy (ag S j) <= dw wx wy (ag S (j + d))).
    { intros d Hd. pattern d. apply natlike_ind; [ | | exact Hd].
      - rewrite Z.add_0_r. intros; lia.
      - intros x Hx IH Hx'. pose proof (IH ltac:(lia)).
        pose proof (Hsuf (j + x) ltac:(lia)) as P. rewrite de_tele in P.
        replace (j + Z.succ x) with (j + x + 1) by lia. lia. }
    replace i with (j + (i - j)) by lia. apply G; lia.
  - assert (G : forall d, 0 <= d -> d <= j -> dw wx wy (ag S j) <= dw wx wy (ag S (j - d))).
    { intros d Hd. pattern d. apply natlike_ind; [ | | exact Hd].
      - rewrite Z.sub_0_r. intros; lia.
      - intros x Hx IH Hx'. pose proof (IH ltac:(lia)).
        pose proof (Hpre (j - x - 1) ltac:(lia)) as P. rewrite de_tele in P.
        replace (j - x - 1 + 1) with (j - x) in P by lia.
        replace (j - Z.succ x) with (j - x - 1) by lia. lia. }
    replace i with (j - (j - i)) by lia. apply G; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Rotating calipers                                                   *)
(* ------------------------------------------------------------------ *)

Lemma vcross_anti : forall a b c d, vcross c d a b = - vcross a b c d.
Proof. intros. unfold vcross. ring. Qed.

Section Cal.
Variables (L N : array int) (lL lN : int).
Let A := to_Z lL.
Let B := to_Z lN.
Hypothesis HA : 1 <= A.
Hypothesis HB : 1 <= B.
Hypothesis HAB : A + B < 4194304.
Hypothesis CL : convex L A.
Hypothesis CN : convex N B.

Definition cellv (j k : Z) : Z := SQ (ag L j) (ag N k).

Definition Rw (wx wy j k : Z) : Prop :=
  (forall j', 0 <= j' < j -> de wx wy L j' <= 0) /\ (forall k', 0 <= k' < k -> de wx wy N k' <= 0).

Definition good (wx wy j k : Z) : Prop :=
  Rw wx wy j k /\ (forall j', j <= j' < A -> 0 <= de wx wy L j') /\
  (forall k', k <= k' < B -> 0 <= de wx wy N k').

Definition found (wx wy bst : Z) : Prop :=
  exists j k, 0 <= j <= A /\ 0 <= k <= B /\ good wx wy j k /\ cellv j k <= bst.

Definition CAI (s : int) (st : int * int * int) : Prop :=
  let '(j, k, best) := st in
  0 <= to_Z j <= A /\ 0 <= to_Z k <= B /\ to_Z j + to_Z k = to_Z s /\
  (to_Z best = 0 \/ exists j' k', 0 <= j' <= A /\ 0 <= k' <= B /\ to_Z best = cellv j' k') /\
  (1 <= to_Z s -> cellv 0 0 <= to_Z best) /\
  forall wx wy, 0 < wy -> found wx wy (to_Z best) \/ Rw wx wy (to_Z j) (to_Z k).

Lemma KL : forall j, 0 <= j <= A -> KR (ag L j).
Proof. destruct CL as (H & _). exact H. Qed.
Lemma KN : forall k, 0 <= k <= B -> KR (ag N k).
Proof. destruct CN as (H & _). exact H. Qed.

Lemma cell_nonneg : forall j k, 0 <= j <= A -> 0 <= k <= B -> 0 <= cellv j k.
Proof. intros. apply SQ_bound; [apply KL | apply KN]; lia. Qed.

Lemma bmax : forall (best d : int),
  to_Z (if (best <? d)%uint63 then d else best) = Z.max (to_Z best) (to_Z d).
Proof.
  intros. destruct (best <? d)%uint63 eqn:E; [apply ltb_Z in E | apply ltb_Z_false in E]; lia.
Qed.

Lemma found_mono : forall wx wy b b', b <= b' -> found wx wy b -> found wx wy b'.
Proof.
  intros wx wy b b' H (j & k & H1 & H2 & H3 & H4). exists j, k.
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 | lia].
Qed.

Lemma CAI_step : forall s st, 0 <= to_Z s < A + B -> CAI s st ->
  CAI (s + 1)%uint63 (cal_step L N lL lN s st).
Proof.
  intros s [[j k] best] Hs (Hj & Hk & Ejk & Hat & H00 & Hw).
  assert (Es : to_Z (s + 1)%uint63 = to_Z s + 1) by (apply succ_Z; lia).
  unfold cal_step.
  assert (Ed : to_Z (msq L.[j] N.[k]) = cellv (to_Z j) (to_Z k))
    by (rewrite phi_msq, <- !ag_int; [reflexivity | rewrite <- ag_int; apply KL; lia
                                       | rewrite <- ag_int; apply KN; lia]).
  set (bst := if (best <? msq L.[j] N.[k])%uint63 then msq L.[j] N.[k] else best).
  assert (Eb : to_Z bst = Z.max (to_Z best) (cellv (to_Z j) (to_Z k))) by (unfold bst; rewrite bmax, Ed; reflexivity).
  assert (Cnn : 0 <= cellv (to_Z j) (to_Z k)) by (apply cell_nonneg; lia).
  assert (Gat : to_Z bst = 0 \/ exists j' k', 0 <= j' <= A /\ 0 <= k' <= B /\ to_Z bst = cellv j' k').
  { destruct (Z_le_gt_dec (cellv (to_Z j) (to_Z k)) (to_Z best)) as [G | G].
    - rewrite Eb, Z.max_l by exact G. exact Hat.
    - right. exists (to_Z j), (to_Z k). split; [lia |]. split; [lia |]. lia. }
  assert (G00 : 1 <= to_Z s + 1 -> cellv 0 0 <= to_Z bst).
  { intros _. destruct (Z.eq_dec (to_Z s) 0) as [E | E].
    - replace (to_Z j) with 0 in Eb by lia. replace (to_Z k) with 0 in Eb by lia. lia.
    - pose proof (H00 ltac:(lia)). lia. }
  assert (Fcur : forall wx wy, 0 < wy -> Rw wx wy (to_Z j) (to_Z k) ->
     (forall j', to_Z j <= j' < A -> 0 <= de wx wy L j') ->
     (forall k', to_Z k <= k' < B -> 0 <= de wx wy N k') -> found wx wy (to_Z bst)).
  { intros wx wy Hwy HR H1 H2. exists (to_Z j), (to_Z k). split; [lia |]. split; [lia |].
    split; [split; [exact HR | split; assumption] | lia]. }
  assert (Fold : forall wx wy, found wx wy (to_Z best) -> found wx wy (to_Z bst))
    by (intros wx wy; apply found_mono; lia).
  assert (Sfx : forall S l wx wy i, convex S l -> 0 < wy -> 0 <= i < l -> 0 <= de wx wy S i ->
             forall i', i <= i' < l -> 0 <= de wx wy S i')
    by (intros; eapply convex_suffix; eassumption).
  destruct ((j <? lL) && ((k =? lN) || Sint63.ltb 0 (mcross L.[j] L.[j + 1] N.[k] N.[k + 1])))%uint63 eqn:C.
  - apply andb_prop in C. destruct C as [C1 C2]. apply ltb_Z in C1.
    assert (Ej : to_Z (j + 1)%uint63 = to_Z j + 1) by (apply succ_Z; lia).
    assert (C2' : to_Z k = B \/ 0 < vcross (ex L (to_Z j)) (ey L (to_Z j)) (ex N (to_Z k)) (ey N (to_Z k))).
    { apply orb_prop in C2. destruct C2 as [C2 | C2]; [left; apply eqb_Z in C2; exact C2 |].
      destruct (Z.eq_dec (to_Z k) B) as [E | E]; [left; exact E | right].
      assert (Ek : to_Z (k + 1)%uint63 = to_Z k + 1) by (apply succ_Z; lia).
      apply sltb0 in C2. rewrite sv_mcross in C2;
        rewrite <- ?ag_int, ?Ej, ?Ek; try (apply KL; lia); try (apply KN; lia).
      rewrite <- !ag_int, Ej, Ek in C2. exact C2. }
    unfold CAI. rewrite Es, Ej.
    split; [lia |]. split; [lia |]. split; [lia |]. split; [exact Gat |]. split; [exact G00 |].
    intros wx wy Hwy. destruct (Hw wx wy Hwy) as [F | HR]; [left; apply Fold; exact F |].
    destruct (Z_le_gt_dec (de wx wy L (to_Z j)) 0) as [D | D].
    + right. destruct HR as [R1 R2]. split; [| exact R2].
      intros j' Hj'. destruct (Z.eq_dec j' (to_Z j)) as [-> | Nj]; [exact D | apply R1; lia].
    + left. apply Fcur; [exact Hwy | exact HR | |].
      * apply (Sfx L A wx wy (to_Z j)); [exact CL | exact Hwy | lia | lia].
      * intros k' Hk'. destruct C2' as [C2' | C2']; [lia |].
        destruct (Z_le_gt_dec 0 (de wx wy N (to_Z k))) as [D2 | D2].
        -- apply (Sfx N B wx wy (to_Z k)); [exact CN | exact Hwy | lia | exact D2 | lia].
        -- exfalso. assert (0 < de wx wy N (to_Z k)); [| lia]. unfold de.
           apply (geo_turn (ex L (to_Z j)) (ey L (to_Z j))); try assumption.
           ++ apply (convex_lexpos L A); [exact CL | lia].
           ++ apply (convex_lexpos N B); [exact CN | lia].
           ++ unfold de in D. lia.
  - assert (C' : to_Z j = A \/ (to_Z k < B /\
        vcross (ex L (to_Z j)) (ey L (to_Z j)) (ex N (to_Z k)) (ey N (to_Z k)) <= 0)).
    { apply Bool.andb_false_iff in C. destruct C as [C | C]; [left; apply ltb_Z_false in C; lia |].
      apply Bool.orb_false_iff in C. destruct C as [C3 C4]. apply eqb_Z_false in C3.
      destruct (Z.eq_dec (to_Z j) A) as [E | E]; [left; exact E | right].
      assert (Ej : to_Z (j + 1)%uint63 = to_Z j + 1) by (apply succ_Z; lia).
      assert (Ek : to_Z (k + 1)%uint63 = to_Z k + 1) by (apply succ_Z; lia).
      split; [lia |].
      rewrite <- Bool.not_true_iff_false, sltb0 in C4. rewrite sv_mcross in C4;
        rewrite <- ?ag_int, ?Ej, ?Ek; try (apply KL; lia); try (apply KN; lia).
      rewrite <- !ag_int, Ej, Ek in C4. apply (proj1 (Z.nlt_ge _ _)). exact C4. }
    assert (Kb : to_Z k < B) by lia.
    assert (Ek : to_Z (k + 1)%uint63 = to_Z k + 1) by (apply succ_Z; lia).
    unfold CAI. rewrite Es, Ek.
    split; [lia |]. split; [lia |]. split; [lia |]. split; [exact Gat |]. split; [exact G00 |].
    intros wx wy Hwy. destruct (Hw wx wy Hwy) as [F | HR]; [left; apply Fold; exact F |].
    destruct (Z_le_gt_dec (de wx wy N (to_Z k)) 0) as [D | D].
    + right. destruct HR as [R1 R2]. split; [exact R1 |].
      intros k' Hk'. destruct (Z.eq_dec k' (to_Z k)) as [-> | Nk]; [exact D | apply R2; lia].
    + left. apply Fcur; [exact Hwy | exact HR | |].
      * intros j' Hj'. destruct C' as [C' | [_ C']]; [lia |].
        destruct (Z_le_gt_dec 0 (de wx wy L (to_Z j))) as [D2 | D2].
        -- apply (Sfx L A wx wy (to_Z j)); [exact CL | exact Hwy | lia | exact D2 | lia].
        -- exfalso. assert (0 <= de wx wy L (to_Z j)); [| lia]. unfold de.
           apply (geo_turn' _ _ (ex N (to_Z k)) (ey N (to_Z k)) _ _); try assumption.
           ++ apply (convex_lexpos L A); [exact CL | lia].
           ++ apply (convex_lexpos N B); [exact CN | lia].
           ++ rewrite vcross_anti. lia.
           ++ unfold de in D. lia.
      * apply (Sfx N B wx wy (to_Z k)); [exact CN | exact Hwy | lia | lia].
Qed.

Lemma cal_spec :
  let D := calipers L N lL lN in
  (exists j k, 0 <= j <= A /\ 0 <= k <= B /\ to_Z D = cellv j k) /\
  cellv 0 0 <= to_Z D /\
  forall wx wy, 0 < wy -> found wx wy (to_Z D).
Proof.
  cbv zeta. unfold calipers.
  assert (EAB : to_Z (lL + lN)%uint63 = A + B) by (unfold A, B in *; sia).
  pose proof (for_inv CAI (lL + lN) 0 (cal_step L N lL lN) (0%uint63, 0%uint63, 0%uint63)) as F.
  destruct (loop (lL + lN) (fun _ _ => true) (cal_step L N lL lN) 0 (0%uint63, 0%uint63, 0%uint63))
    as [[j k] best].
  destruct F as (Hj & Hk & Ejk & Hat & H00 & Hw).
  - change (to_Z 0) with 0. lia.
  - unfold CAI. change (to_Z 0) with 0. split; [lia |]. split; [lia |]. split; [lia |].
    split; [left; reflexivity |]. split; [intros; lia |].
    intros wx wy _. right. split; intros; lia.
  - intros s st Hs Hst. apply CAI_step; [rewrite EAB in Hs; change (to_Z 0) with 0 in Hs; lia | exact Hst].
  - rewrite EAB in Ejk, H00.
    assert (EJ : to_Z j = A) by lia. assert (EK : to_Z k = B) by lia.
    assert (Ed : to_Z (msq L.[j] N.[k]) = cellv A B)
      by (rewrite phi_msq, <- !ag_int, EJ, EK; [reflexivity | rewrite <- ag_int, EJ; apply KL; lia
                                       | rewrite <- ag_int, EK; apply KN; lia]).
    rewrite bmax, Ed.
    assert (Cnn : 0 <= cellv A B) by (apply cell_nonneg; lia).
    split; [| split].
    + destruct (Z_le_gt_dec (cellv A B) (to_Z best)) as [G | G].
      * rewrite Z.max_l by exact G. destruct Hat as [Hat | Hat]; [| exact Hat].
        exists A, B. split; [lia |]. split; [lia |]. lia.
      * rewrite Z.max_r by lia. exists A, B. split; [lia |]. split; [lia | reflexivity].
    + pose proof (H00 ltac:(lia)). lia.
    + intros wx wy Hwy. destruct (Hw wx wy Hwy) as [Fd | HR].
      * eapply found_mono; [| exact Fd]. lia.
      * exists A, B. split; [lia |]. split; [lia |]. split; [| lia].
        rewrite EJ, EK in HR. split; [exact HR |]. split; intros; lia.
Qed.

End Cal.

(* ------------------------------------------------------------------ *)
(* The diameter, exactly                                               *)
(* ------------------------------------------------------------------ *)

Lemma phi_encode : forall a b : int, Z.abs (sv a) <= 1000 -> Z.abs (sv b) <= 1000 ->
  to_Z (encode a b) = EK (sv a) (sv b).
Proof.
  intros a b Ha Hb. unfold encode, EK.
  assert (E1 : sv (a + 1000)%uint63 = sv a + 1000) by (rewrite s_add; change (sv 1000) with 1000; lia).
  assert (E2 : sv (b + 1000)%uint63 = sv b + 1000) by (rewrite s_add; change (sv 1000) with 1000; lia).
  assert (E3 : sv ((a + 1000) * 2048)%uint63 = (sv a + 1000) * 2048)
    by (rewrite s_mul, E1; change (sv 2048) with 2048; lia).
  assert (E4 : sv ((a + 1000) * 2048 + (b + 1000))%uint63 = (sv a + 1000) * 2048 + (sv b + 1000))
    by (rewrite s_add, E3, E2; lia).
  rewrite phi_sv; rewrite E4; [reflexivity | lia].
Qed.

Lemma SQ_neg : forall a b, VK a -> VK b -> SQ a (4098000 - b) = sqd a b.
Proof.
  intros a b Ha Hb. destruct (VK_neg b Hb) as (_ & E1 & E2). unfold SQ, sqd. rewrite E1, E2. ring.
Qed.

Lemma SI_convex : forall Q m S T, (forall z, 0 <= z < to_Z m -> KR (ag Q z)) ->
  SI Q m S T -> convex S (T - 1).
Proof.
  intros Q m S T HK HS. pose proof HS as (_ & HT & _ & H4 & H5 & H6).
  split; [| split].
  - intros j Hj. apply (SI_KR Q m HK S T); [exact HS | lia].
  - intros j Hj. apply H5; lia.
  - intros j Hj Hj'. apply H6; lia.
Qed.

Lemma upward : forall L N lL lN wx wy D P Qb,
  convex L (to_Z lL) -> convex N (to_Z lN) ->
  found L N lL lN wx wy D -> 0 < wy ->
  wx = PX P - PX Qb -> wy = PY P - PY Qb -> VK P -> KR Qb ->
  supp L (to_Z lL + 1) Qb -> supp N (to_Z lN + 1) (4098000 - P) ->
  sqd P Qb <= D.
Proof.
  intros L N lL lN wx wy D P Qb CL CN (j & k & Hj & Hk & ((R1 & R2) & HsL & HsN) & Hc) Hwy
    Ewx Ewy VP KQ SL SN.
  pose proof (good_min L (to_Z lL) wx wy j Hj R1 HsL) as G1.
  pose proof (good_min N (to_Z lN) wx wy k Hk R2 HsN) as G2.
  destruct CL as (KL & _). destruct CN as (KN & _).
  destruct (supp_min L (to_Z lL + 1) Qb wx wy ltac:(intros; apply KL; lia) KQ Hwy SL) as (a & Ha & Da).
  destruct (VK_neg P VP) as (VP' & EX & EY).
  destruct (supp_min N (to_Z lN + 1) (4098000 - P) wx wy ltac:(intros; apply KN; lia)
              (VK_KR _ VP') Hwy SN) as (b & Hb & Db).
  pose proof (G1 a ltac:(lia)) as G1a. pose proof (G2 b ltac:(lia)) as G2b.
  unfold dw in *. rewrite EX, EY in Db.
  set (dx := - PX (ag N k) - PX (ag L j)). set (dy := - PY (ag N k) - PY (ag L j)).
  assert (Hd : wx * wx + wy * wy <= dot wx wy dx dy).
  { unfold dot, dx, dy.
    assert (E : wx * wx + wy * wy = wx * (PX P - PX Qb) + wy * (PY P - PY Qb))
      by (rewrite <- Ewx, <- Ewy; ring).
    lia. }
  pose proof (geo_cs wx wy dx dy Hd) as CS.
  unfold cellv, SQ in Hc. unfold sqd. rewrite <- Ewx, <- Ewy.
  assert (E2 : dx * dx + dy * dy = (PX (ag L j) + PX (ag N k)) * (PX (ag L j) + PX (ag N k)) +
                                  (PY (ag L j) + PY (ag N k)) * (PY (ag L j) + PY (ag N k)))
    by (unfold dx, dy; ring).
  lia.
Qed.

Lemma sqd_sym : forall a b, sqd a b = sqd b a.
Proof. intros. unfold sqd. ring. Qed.

Section Main.
Variables (xs ys : list Z) (x y : array sint).
Hypothesis Hv : valid_input xs ys.
Hypothesis Hx : repr x xs.
Hypothesis Hy : repr y ys.

Let n := PArray.length x.
Let NN := to_Z n.

Definition X (a : Z) : Z := nth (Z.to_nat a) xs 0.
Definition Y (a : Z) : Z := nth (Z.to_nat a) ys 0.
Definition KEY (a : Z) : Z := EK (X a) (Y a).

Lemma len_x : Z.of_nat (List.length xs) = NN.
Proof. exact (proj1 Hx). Qed.

Lemma len_y : Z.of_nat (List.length ys) = NN.
Proof. rewrite <- len_x. pose proof (vi_ys _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma NN_bounds : 2 <= NN <= 100000.
Proof. rewrite <- len_x. pose proof (vi_n _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma repr_get : forall (l : list Z) (t : array sint) (i : int), repr t l ->
  to_Z i < Z.of_nat (List.length l) -> sv t.[i] = nth (Z.to_nat (to_Z i)) l 0.
Proof.
  intros l t i [_ H] Hi. destruct (H (Z.to_nat (to_Z i)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in R. exact R.
Qed.

Lemma bound_nth : forall (l : list Z) (a : Z), Forall (fun c => Z.abs c <= 1000) l ->
  0 <= a < Z.of_nat (List.length l) -> Z.abs (nth (Z.to_nat a) l 0) <= 1000.
Proof. intros l a H Ha. rewrite Forall_forall in H. apply H, nth_In. lia. Qed.

Lemma X_bound : forall a, 0 <= a < NN -> -1000 <= X a <= 1000.
Proof. intros a Ha. pose proof (bound_nth xs a (vi_x _ _ Hv) ltac:(rewrite len_x; lia)). unfold X. lia. Qed.

Lemma Y_bound : forall a, 0 <= a < NN -> -1000 <= Y a <= 1000.
Proof. intros a Ha. pose proof (bound_nth ys a (vi_y _ _ Hv) ltac:(rewrite len_y; lia)). unfold Y. lia. Qed.

Lemma KEY_VK : forall a, 0 <= a < NN -> VK (KEY a).
Proof. intros a Ha. exists (X a), (Y a). split; [apply X_bound; exact Ha |]. split; [apply Y_bound; exact Ha | reflexivity]. Qed.

Lemma KEY_sqd : forall a b, 0 <= a < NN -> 0 <= b < NN ->
  sqd (KEY a) (KEY b) = (X a - X b) * (X a - X b) + (Y a - Y b) * (Y a - Y b).
Proof.
  intros a b Ha Hb. pose proof (X_bound a Ha). pose proof (X_bound b Hb).
  pose proof (Y_bound a Ha). pose proof (Y_bound b Hb).
  unfold sqd, KEY. rewrite !PX_EK, !PY_EK by lia. reflexivity.
Qed.

Definition A0 : array int := loop n (fun _ _ => true) (key_step x y) 0%uint63 (PArray.make n 0%uint63).

Lemma A0_spec : PArray.length A0 = n /\ forall a, 0 <= a < NN -> ag A0 a = KEY a.
Proof.
  pose proof NN_bounds as NB.
  apply (for_inv (fun i A => PArray.length A = n /\ forall a, 0 <= a < to_Z i -> ag A a = KEY a)).
  - change (to_Z 0) with 0. lia.
  - split; [apply ilength_make_small; fold NN; lia |]. intros a Ha. change (to_Z 0) with 0 in Ha. lia.
  - intros i A Hi (HA & Ha). change (to_Z 0) with 0 in Hi. fold NN in Hi.
    assert (Ei : to_Z (i + 1)%uint63 = to_Z i + 1) by (apply succ_Z; lia).
    unfold key_step. split; [rewrite ilength_set; exact HA |].
    intros a Ha'. rewrite Ei in Ha'.
    rewrite ag_set by (rewrite ?HA; fold NN; rewrite ?wB_val; lia).
    destruct (Z.eqb_spec a (to_Z i)) as [-> | Na]; [| apply Ha; lia].
    assert (EX : sv x.[i] = X (to_Z i)) by (apply repr_get; [exact Hx | rewrite len_x; lia]).
    assert (EY : sv y.[i] = Y (to_Z i)) by (apply repr_get; [exact Hy | rewrite len_y; lia]).
    pose proof (X_bound (to_Z i) ltac:(lia)). pose proof (Y_bound (to_Z i) ltac:(lia)).
    assert (B1 : Z.abs (sv x.[i]) <= 1000) by (rewrite EX; apply (proj2 (Z.abs_le _ _)); lia).
    assert (B2 : Z.abs (sv y.[i]) <= 1000) by (rewrite EY; apply (proj2 (Z.abs_le _ _)); lia).
    etransitivity; [exact (phi_encode _ _ B1 B2) |]. rewrite EX, EY. reflexivity.
Qed.

Definition A1 : array int := msort A0 n.

Lemma A1_spec : PArray.length A1 = n /\ sorted_on A1 0 NN /\
  (forall z, 0 <= z < NN -> exists a, 0 <= a < NN /\ ag A1 z = KEY a) /\
  (forall a, 0 <= a < NN -> exists z, 0 <= z < NN /\ KEY a = ag A1 z).
Proof.
  destruct A0_spec as [HL HK].
  unfold A1. destruct (msort_spec A0 n HL) as (L1 & S1 & M1 & M2). fold NN in S1, M1, M2.
  split; [exact L1 |]. split; [exact S1 |]. split.
  - intros z Hz. destruct (M1 z Hz) as (s & Hs & E). exists s. split; [exact Hs |]. rewrite E. apply HK; exact Hs.
  - intros a Ha. destruct (M2 a Ha) as (s & Hs & E). exists s. split; [exact Hs |]. rewrite <- E. symmetry. apply HK; exact Ha.
Qed.


Lemma diam2_main :
  (exists a b, 0 <= a < NN /\ 0 <= b < NN /\ to_Z (diam2 x y) = sqd (KEY a) (KEY b)) /\
  (forall a b, 0 <= a < NN -> 0 <= b < NN -> sqd (KEY a) (KEY b) <= to_Z (diam2 x y)).
Proof.
  pose proof NN_bounds as NB.
  destruct A1_spec as (L1 & S1 & M1 & M2).
  unfold diam2. cbv zeta.
  change (loop (PArray.length x) (fun _ _ => true) (key_step x y) 0%uint63
            (PArray.make (PArray.length x) 0%uint63)) with A0.
  change (msort A0 (PArray.length x)) with A1.
  assert (EN : to_Z (@PArray.length int x) = NN) by reflexivity.
  pose proof (dedup_spec A1 (@PArray.length int x) L1 ltac:(rewrite EN; lia) S1) as DS.
  destruct (loop (@PArray.length int x) (fun _ _ => true) (dedup_step A1) 1
              (PArray.make (@PArray.length int x) A1.[0], 1%uint63)) as [Q m].
  destruct DS as (HQl & Hm & Hinc & D1 & D2). rewrite EN in Hm, D1, D2.
  assert (QK : forall z, 0 <= z < to_Z m -> exists a, 0 <= a < NN /\ ag Q z = KEY a).
  { intros z Hz. destruct (D1 z Hz) as (s & Hs & E). destruct (M1 s Hs) as (a & Ha & E').
    exists a. split; [exact Ha | lia]. }
  assert (KQ : forall a, 0 <= a < NN -> exists z, 0 <= z < to_Z m /\ KEY a = ag Q z).
  { intros a Ha. destruct (M2 a Ha) as (s & Hs & E). destruct (D2 s Hs) as (z & Hz & E').
    exists z. split; [exact Hz | lia]. }
  assert (QV : forall z, 0 <= z < to_Z m -> VK (ag Q z)).
  { intros z Hz. destruct (QK z Hz) as (a & Ha & ->). apply KEY_VK; exact Ha. }
  assert (QR : forall z, 0 <= z < to_Z m -> KR (ag Q z)) by (intros; apply VK_KR, QV; assumption).
  destruct (m <? 2)%uint63 eqn:E2; cbv beta iota.
  - apply ltb_Z in E2. change (to_Z 2) with 2 in E2.
    assert (Same : forall a, 0 <= a < NN -> KEY a = ag Q 0).
    { intros a Ha. destruct (KQ a Ha) as (z & Hz & E). replace z with 0 in E by lia. exact E. }
    change (to_Z 0) with 0. split.
    + exists 0, 0. split; [lia |]. split; [lia |]. unfold sqd. ring.
    + intros a b Ha Hb. rewrite (Same a Ha), (Same b Hb). unfold sqd. lia.
  - apply ltb_Z_false in E2. change (to_Z 2) with 2 in E2.
    assert (Mb : to_Z m <= 4194303) by lia.
    assert (Qb : forall z, 0 <= z < to_Z m -> 0 <= ag Q z <= 4098000).
    { intros z Hz. destruct (QV z Hz) as (X0 & Y0 & HX & HY & ->). unfold EK. lia. }
    pose proof (neg_spec Q m ltac:(lia) Qb) as (HQ2l & HQ2). cbv zeta in HQ2l, HQ2.
    set (Q2 := loop m (fun _ _ => true) (neg_step Q m) 0%uint63 (PArray.make m 0%uint63)) in *.
    assert (Q2V : forall z, 0 <= z < to_Z m -> VK (ag Q2 z)).
    { intros z Hz. rewrite HQ2 by exact Hz. apply VK_neg, QV. lia. }
    assert (Q2R : forall z, 0 <= z < to_Z m -> KR (ag Q2 z)) by (intros; apply VK_KR, Q2V; assumption).
    assert (Inc2 : incr_on Q2 (to_Z m)).
    { intros s t Hs Hst Ht. rewrite !HQ2 by lia. pose proof (Hinc (to_Z m - 1 - t) (to_Z m - 1 - s)
        ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
    assert (NegQ : forall a, 0 <= a < NN -> exists z, 0 <= z < to_Z m /\ 4098000 - KEY a = ag Q2 z).
    { intros a Ha. destruct (KQ a Ha) as (z & Hz & E). exists (to_Z m - 1 - z). split; [lia |].
      rewrite HQ2 by lia. replace (to_Z m - 1 - (to_Z m - 1 - z)) with z by lia. rewrite E. reflexivity. }
    assert (Q2K : forall z, 0 <= z < to_Z m -> exists a, 0 <= a < NN /\ ag Q2 z = 4098000 - KEY a).
    { intros z Hz. destruct (QK (to_Z m - 1 - z) ltac:(lia)) as (a & Ha & E). exists a.
      split; [exact Ha |]. rewrite HQ2 by lia. rewrite E. reflexivity. }
    pose proof (chain_spec Q m ltac:(rewrite HQl, EN; lia) ltac:(lia) Hinc QR) as CS1.
    pose proof (chain_spec Q2 m ltac:(rewrite HQ2l; lia) ltac:(lia) Inc2 Q2R) as CS2.
    destruct (chain Q m) as [L tL]. destruct (chain Q2 m) as [N tN].
    destruct CS1 as (SL & [TL TLm] & _ & SpL). destruct CS2 as (SN & [TN TNm] & _ & SpN).
    pose proof SL as (_ & _ & L0 & ML & _). pose proof SN as (_ & _ & N0 & MN & _).
    assert (ElL : to_Z (tL - 1)%uint63 = to_Z tL - 1) by sia.
    assert (ElN : to_Z (tN - 1)%uint63 = to_Z tN - 1) by sia.
    pose proof (SI_convex Q m L (to_Z tL) QR SL) as CvL. rewrite <- ElL in CvL.
    pose proof (SI_convex Q2 m N (to_Z tN) Q2R SN) as CvN. rewrite <- ElN in CvN.
    pose proof (cal_spec L N (tL - 1) (tN - 1) ltac:(lia) ltac:(lia) ltac:(lia) CvL CvN)
      as (Att & C00 & Fnd). cbv zeta in Att, C00, Fnd.
    set (D := calipers L N (tL - 1) (tN - 1)) in *.
    assert (LK : forall j, 0 <= j < to_Z tL -> exists a, 0 <= a < NN /\ ag L j = KEY a).
    { intros j Hj. destruct (ML j Hj) as (r & Hr & E). destruct (QK r Hr) as (a & Ha & E').
      exists a. split; [exact Ha | lia]. }
    assert (NK : forall k, 0 <= k < to_Z tN -> exists a, 0 <= a < NN /\ ag N k = 4098000 - KEY a).
    { intros k Hk. destruct (MN k Hk) as (r & Hr & E). destruct (Q2K r Hr) as (a & Ha & E').
      exists a. split; [exact Ha | lia]. }
    split.
    + destruct Att as (j & k & Hj & Hk & E). rewrite ElL in Hj. rewrite ElN in Hk.
      destruct (LK j ltac:(lia)) as (a & Ha & Ea). destruct (NK k ltac:(lia)) as (b & Hb & Eb).
      exists a, b. split; [exact Ha |]. split; [exact Hb |].
      rewrite E. unfold cellv. rewrite Ea, Eb. apply SQ_neg; apply KEY_VK; assumption.
    + (* the upward case, for an ordered pair *)
      assert (Up : forall a b, 0 <= a < NN -> 0 <= b < NN -> 0 < PY (KEY a) - PY (KEY b) ->
                 sqd (KEY a) (KEY b) <= to_Z D).
      { intros a b Ha Hb Hy0.
        apply (upward L N (tL - 1) (tN - 1) (PX (KEY a) - PX (KEY b)) (PY (KEY a) - PY (KEY b)));
          try assumption; try reflexivity.
        - apply Fnd. exact Hy0.
        - apply KEY_VK; exact Ha.
        - apply VK_KR, KEY_VK; exact Hb.
        - rewrite ElL. replace (to_Z tL - 1 + 1) with (to_Z tL) by lia.
          destruct (KQ b Hb) as (z & Hz & ->). apply SpL; exact Hz.
        - rewrite ElN. replace (to_Z tN - 1 + 1) with (to_Z tN) by lia.
          destruct (NegQ a Ha) as (z & Hz & ->). apply SpN; exact Hz. }
      intros a b Ha Hb.
      destruct (Z_lt_le_dec 0 (PY (KEY a) - PY (KEY b))) as [G | G]; [apply Up; assumption |].
      destruct (Z_lt_le_dec 0 (PY (KEY b) - PY (KEY a))) as [G' | G'].
      { rewrite sqd_sym. apply Up; assumption. }
      (* horizontal: bounded by the leftmost and rightmost points *)
      assert (C0 : cellv L N 0 0 = sqd (ag Q 0) (ag Q (to_Z m - 1))).
      { unfold cellv. rewrite L0, N0, HQ2 by lia. replace (to_Z m - 1 - 0) with (to_Z m - 1) by lia.
        apply SQ_neg; apply QV; lia. }
      assert (XB : forall c, 0 <= c < NN -> PX (ag Q 0) <= PX (KEY c) <= PX (ag Q (to_Z m - 1))).
      { intros c Hc. destruct (KQ c Hc) as (z & Hz & ->).
        assert (H1 : ag Q 0 <= ag Q z)
          by (destruct (Z.eq_dec z 0) as [-> | Nz]; [lia | apply Z.lt_le_incl, Hinc; lia]).
        assert (H2 : ag Q z <= ag Q (to_Z m - 1))
          by (destruct (Z.eq_dec z (to_Z m - 1)) as [-> | Nz]; [lia | apply Z.lt_le_incl, Hinc; lia]).
        apply lexk in H1; [| apply QR; lia]. apply lexk in H2; [| apply QR; lia].
        apply LEX_x in H1, H2. lia. }
      pose proof (XB a Ha) as Xa. pose proof (XB b Hb) as Xb.
      assert (Hor : sqd (KEY a) (KEY b) <= sqd (ag Q 0) (ag Q (to_Z m - 1))).
      { unfold sqd. replace (PY (KEY a) - PY (KEY b)) with 0 by lia.
        set (u := PX (KEY a) - PX (KEY b)). set (v := PX (ag Q 0) - PX (ag Q (to_Z m - 1))).
        assert (Z.abs u <= Z.abs v) by (unfold u, v; lia).
        assert (u * u <= v * v) by (rewrite <- (Z.abs_square u), <- (Z.abs_square v); apply Z.mul_le_mono_nonneg; lia).
        pose proof (Z.square_nonneg (PY (ag Q 0) - PY (ag Q (to_Z m - 1)))). lia. }
      lia.
Qed.

End Main.

(* ------------------------------------------------------------------ *)
(* The square root, and the contract                                   *)
(* ------------------------------------------------------------------ *)

Lemma Z_N_nat' : forall i : N, Z.to_nat (Z.of_N i) = N.to_nat i.
Proof. intros. lia. Qed.

Lemma sq_le_sqrt : forall a b, a <= b -> (R_sqrt.sqrt (IZR a) <= R_sqrt.sqrt (IZR b))%R.
Proof. intros a b H. apply R_sqrt.sqrt_le_1_alt, IZR_le, H. Qed.

Lemma roberthood_correct_main : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists r : R, repr (roberthood x y) r /\ roberthood_spec xs ys r.
Proof.
  intros xs ys x y Hv Hx Hy.
  pose proof (NN_bounds xs ys x Hv Hx) as NB.
  destruct (diam2_main xs ys x y Hv Hx Hy) as [(a & b & Ha & Hb & E) Hall].
  set (NN := to_Z (PArray.length x)) in *.
  set (Dz := to_Z (diam2 x y)) in *.
  assert (Bd : forall a b, 0 <= a < NN -> 0 <= b < NN -> 0 <= sqd (KEY xs ys a) (KEY xs ys b) <= 8000000).
  { intros a' b' Ha' Hb'. rewrite (KEY_sqd xs ys x Hv Hx) by assumption.
    pose proof (X_bound xs ys x Hv Hx a' Ha'). pose proof (X_bound xs ys x Hv Hx b' Hb').
    pose proof (Y_bound xs ys x Hv Hx a' Ha'). pose proof (Y_bound xs ys x Hv Hx b' Hb').
    assert (B : forall u, -2000 <= u <= 2000 -> 0 <= u * u <= 4000000) by (intros; nia).
    pose proof (B (X xs a' - X xs b') ltac:(lia)). pose proof (B (Y ys a' - Y ys b') ltac:(lia)). lia. }
  pose proof (Bd a b Ha Hb) as BD. rewrite <- E in BD.
  assert (Rd : repr (of_uint63 (diam2 x y)) (IZR Dz))
    by (apply repr_of_uint63_exact; unfold Dz; lia).
  pose proof (repr_sqrt _ _ Rd ltac:(apply IZR_le; lia)) as Rs.
  exists (rnd (R_sqrt.sqrt (IZR Dz))). split; [exact Rs |].
  exists (R_sqrt.sqrt (IZR Dz)). split.
  - (* the longest distance *)
    assert (Dist : forall i j : N, (Z.of_N i < NN)%Z -> (Z.of_N j < NN)%Z ->
              Prelude.dist xs ys i j = R_sqrt.sqrt (IZR (sqd (KEY xs ys (Z.of_N i)) (KEY xs ys (Z.of_N j))))).
    { intros i j Hi Hj. rewrite (KEY_sqd xs ys x Hv Hx) by lia. unfold Prelude.dist, get_list_Z, X, Y.
      rewrite !Z_N_nat'. reflexivity. }
    pose proof (len_x xs x Hx) as LX. fold NN in LX.
    split.
    + destruct (Z.eq_dec a b) as [Eab | Nab].
      * exists 0%N, 1%N. split; [unfold arrow_pair, len; split; [lia | split; [lia | discriminate]] |].
        rewrite Dist by (simpl; lia). f_equal. f_equal.
        subst b. assert (Dz = 0) by (rewrite E; unfold sqd; ring).
        pose proof (Hall 0 1 ltac:(lia) ltac:(lia)). pose proof (Bd 0 1 ltac:(lia) ltac:(lia)).
        simpl Z.of_N. lia.
      * exists (Z.to_N a), (Z.to_N b). split; [unfold arrow_pair, len; split; [lia | split; lia] |].
        rewrite Dist by lia. rewrite !Z2N.id by lia. rewrite E. reflexivity.
    + intros i j (Hi & Hj & _). unfold len in Hi, Hj.
      rewrite Dist by lia. apply sq_le_sqrt. apply Hall; lia.
  - (* the tolerance *)
    unfold within_tolerance. left.
    set (d := R_sqrt.sqrt (IZR Dz)).
    assert (D0 : (0 <= d)%R) by apply R_sqrt.sqrt_pos.
    assert (Dsq : (d * d = IZR Dz)%R) by (apply R_sqrt.sqrt_sqrt, IZR_le; lia).
    assert (D5 : (d <= 5000)%R).
    { assert (IZR Dz <= 25000000)%R by (apply IZR_le; lia). nra. }
    destruct (rnd_model d) as (eps & eta & He & Heta & _ & Er). rewrite Er.
    pose proof u_pos. pose proof eta_max_le_u. pose proof u_val.
    replace (d * (1 + eps) + eta - d)%R with (d * eps + eta)%R by ring.
    apply Rle_lt_trans with (d * Rabs eps + Rabs eta)%R.
    + eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_mult, (Rabs_right d) by lra. lra.
    + assert (d * Rabs eps <= 5000 * (u / 2))%R.
      { apply Rmult_le_compat; try lra. apply Rabs_pos. }
      rewrite u_val in *. lra.
Qed.

Lemma roberthood_correct :
  forall (xs ys : list Z) (x y : array sint),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists r : R, repr (roberthood x y) r /\ roberthood_spec xs ys r.
Proof. exact roberthood_correct_main. Qed.
