(* Correctness proofs for generalchineseremainder_implem.v. *)
(* Implementation of generalchineseremainder (generalchineseremainder.spec):
   the general Chinese remainder theorem for two moduli, CRT via the
   extended Euclidean algorithm.

   Code.  [egcd_loop] runs Euclid on (n, m) and tracks, for every remainder
   r of the sequence, a coefficient s in [0, m) with  s * n = r (mod m)
   (the Bezout coefficient of n, kept reduced modulo m so that it stays an
   unsigned word: s' = (s0 + m - (q * s1 mod m)) mod m).  It returns
   g = gcd(n, m) and s with s * n = g (mod m), hence
   s * (n/g) = 1 (mod m/g).  Then, with d = (b - a) mod m computed as
   (b + m - a mod m) mod m:
     - g does not divide d       -> None;
     - otherwise t = (d/g * s) mod (m/g), x = a + n * t, K = n * (m/g).
   Every intermediate value is below 10^18 < 2^63 under valid_input: no Z,
   no signed word.

   Termination: [egcd_loop] recurses structurally on an erased
   [Acc (Zwf 0) (φ r1)] proof, the shape of the loops of
   template/polymul1/implem-bens-1/polymul1_implem.v. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.

Unset Lia Cache.

Require Export generalchineseremainder_implem.
Open Scope uint63_scope.


Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* lia, once the hypotheses about compound machine words are cleared *)
Ltac plia :=
  repeat match goal with
         | H : context [to_Z (_ _ _)] |- _ => clear H
         | H : context [PrimInt63.eqb _ _] |- _ => clear H
         end; lia.

Lemma egcd_loop_eq : forall m r0 r1 s0 s1 H,
  egcd_loop m r0 r1 s0 s1 H =
  match bdec (r1 =? 0) with
  | left _ => (r0, s0)
  | right Hne =>
      egcd_loop m r1 (r0 mod r1) s1 ((s0 + m - (r0 / r1 * s1) mod m) mod m)
        (Acc_inv H (dec_mod r0 r1 Hne))
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Prop side: arithmetic over Z                                        *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Definition bnd : Z := 10 ^ 9.

Lemma wB_value : wB = 9223372036854775808.
Proof. reflexivity. Qed.

(* the update of the coefficient keeps s * N = r (mod M) *)
Lemma step_inv : forall M N s0 s1 r0 r1,
  0 < M -> 0 < r1 ->
  (M | s0 * N - r0) -> (M | s1 * N - r1) ->
  (M | ((s0 + M - (r0 / r1 * s1) mod M) mod M) * N - r0 mod r1).
Proof.
  intros M N s0 s1 r0 r1 HM Hr1 D0 D1.
  set (q := r0 / r1).
  set (v := s0 + M - (q * s1) mod M).
  assert (Hv : v mod M = v - M * (v / M)) by (apply Z.mod_eq; lia).
  assert (Hu : (q * s1) mod M = q * s1 - M * (q * s1 / M)) by (apply Z.mod_eq; lia).
  assert (Hr : r0 mod r1 = r0 - r1 * q) by (unfold q; apply Z.mod_eq; lia).
  rewrite Hv, Hr. generalize (v / M) as e2. intros e2.
  unfold v. rewrite Hu. generalize (q * s1 / M) as e1. intros e1.
  replace ((s0 + M - (q * s1 - M * e1) - M * e2) * N - (r0 - r1 * q))
    with ((s0 * N - r0) - q * (s1 * N - r1) + M * (N + e1 * N - e2 * N)) by ring.
  apply Z.divide_add_r; [apply Z.divide_sub_r; [exact D0 | apply Z.divide_mul_r; exact D1]
                        | apply Z.divide_factor_l].
Qed.

Lemma gcd_step : forall r0 r1, r1 <> 0 ->
  Z.gcd r1 (r0 mod r1) = Z.gcd r0 r1.
Proof.
  intros r0 r1 H. rewrite Z.gcd_comm, Z.gcd_mod by exact H.
  apply Z.gcd_comm.
Qed.

(* The loop: it returns the gcd and a coefficient s with s * N = g (mod M). *)
Lemma egcd_loop_spec : forall (m xn : int) (N M G : Z),
  (φ m) = M -> (φ xn) = N -> 0 < M <= bnd -> 0 < N <= bnd ->
  forall (z : Z) (r0 r1 s0 s1 : int) (H : Acc (Zwf 0) (φ r1)),
  (φ r1) = z ->
  (φ r0) <= bnd -> (φ r1) <= bnd -> (φ s0) < M -> (φ s1) < M ->
  Z.gcd (φ r0) (φ r1) = G ->
  (M | (φ s0) * N - (φ r0)) -> (M | (φ s1) * N - (φ r1)) ->
  let p := egcd_loop m r0 r1 s0 s1 H in
  (φ (fst p)) = G /\ (φ (snd p)) < M /\ (M | (φ (snd p)) * N - (φ (fst p))).
Proof.
  intros m xn N M G Hm Hn HM HN z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros r0 r1 s0 s1 H Hz Hr0 Hr1 Hs0 Hs1 HG D0 D1 p.
  unfold p; clear p.
  rewrite egcd_loop_eq.
  destruct (bdec (r1 =? 0)%uint63) as [E | E].
  - rewrite eqb_spec in E. subst r1. simpl.
    rewrite Z.gcd_0_r in HG. pose proof (to_Z_bounded r0).
    rewrite Z.abs_eq in HG by lia. auto.
  - assert (Hr1z : (φ r1) <> 0).
    { intros E'. assert (r1 = 0%uint63) by (apply to_Z_inj; exact E'). subst.
      discriminate. }
    pose proof (to_Z_bounded r0). pose proof (to_Z_bounded r1).
    pose proof (to_Z_bounded s0). pose proof (to_Z_bounded s1).
    assert (Hq : (φ (r0 / r1)) <= bnd).
    { rewrite div_spec. apply Z.le_trans with (φ r0); [|lia].
      apply Z.div_le_upper_bound; nia. }
    assert (Hmod : (φ (r0 mod r1)) = (φ r0) mod (φ r1)) by apply mod_spec.
    assert (Hprod : (φ (r0 / r1 * s1)) = (φ (r0 / r1)) * (φ s1)).
    { rewrite mul_spec. apply Z.mod_small. pose proof (to_Z_bounded (r0 / r1)).
      unfold bnd in *. split; [nia|]. rewrite wB_value. nia. }
    assert (Hpm : (φ ((r0 / r1 * s1) mod m)) = ((φ (r0 / r1)) * (φ s1)) mod M).
    { rewrite mod_spec, Hprod, Hm. reflexivity. }
    pose proof (Z.mod_pos_bound ((φ (r0 / r1)) * (φ s1)) M ltac:(lia)) as Bpm.
    assert (Hsum : (φ (s0 + m - (r0 / r1 * s1) mod m))
                   = (φ s0) + M - ((φ (r0 / r1)) * (φ s1)) mod M).
    { rewrite sub_spec, add_spec, Hpm, Hm.
      rewrite (Z.mod_small ((φ s0) + M)) by (unfold bnd in *; rewrite wB_value; lia).
      apply Z.mod_small. unfold bnd in *; rewrite wB_value; lia. }
    assert (Hs' : (φ ((s0 + m - (r0 / r1 * s1) mod m) mod m))
                  = ((φ s0) + M - ((φ r0) / (φ r1) * (φ s1)) mod M) mod M).
    { rewrite mod_spec, Hsum, Hm, div_spec. reflexivity. }
    pose proof (Z.mod_pos_bound (φ r0) (φ r1) ltac:(lia)) as Bm.
    eapply (IH (φ (r0 mod r1))); [ | reflexivity | lia | lia | lia | | | | ].
    + rewrite <- Hz. apply dec_mod. exact E.
    + rewrite Hs'. apply Z.mod_pos_bound. lia.
    + rewrite Hmod, gcd_step by exact Hr1z. exact HG.
    + exact D1.
    + rewrite Hs', Hmod. apply step_inv; [lia | lia | exact D0 | exact D1].
Qed.

Lemma repr_uint_Z : forall (x : uint) (n : N), repr x n -> (φ x) = Z.of_N n.
Proof.
  intros x n H. unfold repr, repr_uint in H. subst n.
  rewrite Z2N.id; [reflexivity|]. apply to_Z_bounded.
Qed.

Lemma repr_uint_of : forall (x : uint) (z : Z), (φ x) = z -> repr x (Z.to_N z).
Proof. intros x z H. unfold repr, repr_uint. rewrite H. reflexivity. Qed.

Lemma N_gcd_Z : forall n m : N, Z.of_N (N.gcd n m) = Z.gcd (Z.of_N n) (Z.of_N m).
Proof. intros [|p] [|q]; reflexivity. Qed.

Lemma mod_of_divide : forall M x B, 0 <= B < M -> (M | x - B) -> x mod M = B.
Proof.
  intros M x B HB [c Hc].
  replace x with (c * M + B) by lia.
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. exact HB.
Qed.

Lemma div_le_self : forall a b, 0 <= a -> 0 < b -> 0 <= a / b <= a.
Proof. intros a b Ha Hb. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia. Qed.

Lemma bnd_prod : forall x y, 0 <= x <= bnd -> 0 <= y <= bnd -> 0 <= x * y < wB.
Proof. intros x y Hx Hy. rewrite wB_value. unfold bnd in *. nia. Qed.

Lemma xbound : forall A N t K, 0 <= A < N -> 0 <= t < K -> 0 <= A + N * t < N * K.
Proof. intros. nia. Qed.

Lemma mul_le_bound : forall N t K, 0 <= N -> 0 <= t < K -> 0 <= N * t <= N * K.
Proof. intros. nia. Qed.

(* The combination step, over Z. *)
Lemma combine_ok : forall A N B M g s d t,
  0 <= A < N -> 0 <= B < M -> 0 < g -> (g | N) -> (g | M) ->
  (M | s * N - g) ->
  d = (B + M - A mod M) mod M -> (g | d) ->
  t = (d / g * s) mod (M / g) ->
  (A + N * t) mod N = A /\ (A + N * t) mod M = B.
Proof.
  intros A N B M g s d t HA HB Hg [N' HN'] [M' HM'] [k Hk] Hd [D HD] Ht.
  split.
  - rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. exact HA.
  - apply mod_of_divide; [exact HB|].
    assert (HM'0 : 0 < M').
    { apply (Z.mul_pos_cancel_r M' g); [lia|]. rewrite <- HM'. lia. }
    assert (Hdg : d / g = D) by (rewrite HD; apply Z.div_mul; lia).
    assert (Hmg : M / g = M') by (rewrite HM'; apply Z.div_mul; lia).
    rewrite Hdg, Hmg in Ht.
    assert (Hk' : s * N' = 1 + k * M').
    { subst N M. apply (Z.mul_reg_r _ _ g); [lia|]. lia. }
    rewrite (Z.mod_eq (D * s) M') in Ht by lia.
    set (j := D * s / M') in Ht.
    set (v := B + M - A mod M) in Hd.
    rewrite (Z.mod_eq v M) in Hd by lia.
    set (w := v / M) in Hd.
    unfold v in Hd. rewrite (Z.mod_eq A M) in Hd by lia.
    set (qa := A / M) in Hd.
    exists (1 + qa - w + D * k - N' * j).
    subst t.
    replace (N * (D * s - M' * j)) with (g * D * (s * N') - N' * j * M)
      by (subst N M; ring).
    rewrite Hk'.
    replace (g * D * (1 + k * M')) with (d + D * k * M) by (rewrite HD, HM'; ring).
    rewrite Hd. ring.
Qed.

(* No integer solves the system when g does not divide d. *)
Lemma none_ok : forall A N B M g d,
  0 < M -> 0 < N -> (g | N) -> (g | M) ->
  d = (B + M - A mod M) mod M -> ~ (g | d) ->
  ~ exists x : Z, x mod N = A /\ x mod M = B.
Proof.
  intros A N B M g d HM HN [N' HN'] [M' HM'] Hd Hnd [x [HxA HxB]].
  apply Hnd.
  rewrite (Z.mod_eq _ M) in Hd by lia.
  rewrite (Z.mod_eq A M) in Hd by lia.
  rewrite (Z.mod_eq x N) in HxA by lia.
  rewrite (Z.mod_eq x M) in HxB by lia.
  exists (M' + M' * (A / M) - M' * ((B + M - (A - M * (A / M))) / M)
          - M' * (x / M) + N' * (x / N)).
  rewrite Hd, <- HxA, <- HxB. subst N M. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma crt_impl_correct :
  forall (a n b m : N) (xa xn xb xm : uint),
  valid_input a n b m ->
  repr xa a -> repr xn n -> repr xb b -> repr xm m ->
  exists o : option (N * N), repr (crt_impl xa xn xb xm) o /\ crt_spec a n b m o.
Proof.
  intros a n b m xa xn xb xm [Vn Vm Va Vb] Ra Rn Rb Rm.
  apply repr_uint_Z in Ra, Rn, Rb, Rm.
  set (A := Z.of_N a) in *. set (N0 := Z.of_N n) in *.
  set (B := Z.of_N b) in *. set (M := Z.of_N m) in *.
  assert (HA : 0 <= A < N0) by lia.
  assert (HB : 0 <= B < M) by lia.
  assert (HN : 0 < N0 <= bnd) by (unfold bnd; lia).
  assert (HM : 0 < M <= bnd) by (unfold bnd; lia).
  clear Vn Vm Va Vb.
  unfold crt_impl.
  assert (Hone : (φ (1 mod xm)) < M /\ (M | (φ (1 mod xm)) * N0 - (φ xn))).
  { rewrite mod_spec, Rm. replace (φ 1) with 1 by reflexivity.
    split; [apply Z.mod_pos_bound; lia|].
    rewrite Z.mod_eq by lia. rewrite Rn.
    exists (- (1 / M) * N0). ring. }
  destruct Hone as [Hone1 Hone2].
  pose proof (egcd_loop_spec xm xn N0 M (Z.gcd N0 M) Rm Rn HM HN (φ xm)
                xn xm (1 mod xm) 0 (Zwf_well_founded 0 (φ xm)) eq_refl
                ltac:(lia) ltac:(lia) Hone1 ltac:(change (φ 0) with 0; lia)
                ltac:(rewrite Rn, Rm; reflexivity) Hone2
                ltac:(change (φ 0) with 0; rewrite Rm; exists (-1); ring))
    as Hloop.
  destruct (egcd_loop xm xn xm (1 mod xm) 0 (Zwf_well_founded 0 (φ xm)))
    as [g s].
  simpl in Hloop. destruct Hloop as [Hg [Hs HgsD]].
  set (G := Z.gcd N0 M) in *.
  assert (HGpos : 0 < G).
  { assert (0 <= G) by apply Z.gcd_nonneg.
    assert (G <> 0); [|lia].
    intros E. apply Z.gcd_eq_0_l in E. lia. }
  assert (HGN : (G | N0)) by apply Z.gcd_divide_l.
  assert (HGM : (G | M)) by apply Z.gcd_divide_r.
  assert (HGleM : G <= M) by (apply Z.divide_pos_le; [lia|exact HGM]).
  pose proof (to_Z_bounded s) as Bs.
  (* d *)
  set (dZ := (B + M - A mod M) mod M).
  assert (Hd : (φ ((xb + xm - xa mod xm) mod xm)) = dZ).
  { pose proof (Z.mod_pos_bound A M ltac:(lia)).
    rewrite mod_spec, sub_spec, add_spec, mod_spec, Ra, Rb, Rm.
    rewrite (Z.mod_small (B + M)) by (unfold bnd in *; rewrite wB_value; lia).
    rewrite (Z.mod_small (B + M - A mod M))
      by (unfold bnd in *; rewrite wB_value; lia).
    reflexivity. }
  pose proof (Z.mod_pos_bound (B + M - A mod M) M ltac:(lia)) as Bd.
  fold dZ in Bd.
  destruct (bdec ((((xb + xm - xa mod xm) mod xm) mod g =? 0)%uint63)) as [E | E];
    rewrite E.
  - (* a solution *)
    assert (HdG : (G | dZ)).
    { rewrite eqb_spec in E. apply (f_equal to_Z) in E.
      rewrite mod_spec, Hd, Hg in E. change (φ 0) with 0 in E.
      apply Z.mod_divide; lia. }
    set (MG := M / G).
    assert (HMG : 1 <= MG <= M).
    { unfold MG. destruct HGM as [c Hc]. rewrite Hc, Z.div_mul by lia.
      assert (Hc0 : 0 < c)
        by (apply (Z.mul_pos_cancel_r c G HGpos); rewrite <- Hc; exact (proj1 HM)).
      clear -Hc0 HGpos. split; [lia|]. nia. }
    assert (Hmg : (φ (xm / g)) = MG) by (rewrite div_spec, Rm, Hg; reflexivity).
    assert (HdgZ : (φ (((xb + xm - xa mod xm) mod xm) / g)) = dZ / G)
      by (rewrite div_spec, Hd, Hg; reflexivity).
    assert (HdgB : 0 <= dZ / G <= dZ) by (apply div_le_self; plia).
    set (tZ := (dZ / G * (φ s)) mod MG).
    assert (HdsB : 0 <= dZ / G * (φ s) < wB)
      by (apply bnd_prod; plia).
    assert (Ht : (φ ((((xb + xm - xa mod xm) mod xm) / g * s) mod (xm / g))) = tZ).
    { rewrite mod_spec, mul_spec, HdgZ, Hmg.
      rewrite (Z.mod_small (dZ / G * (φ s)) wB HdsB). reflexivity. }
    pose proof (Z.mod_pos_bound (dZ / G * (φ s)) MG ltac:(plia)) as Bt.
    fold tZ in Bt.
    assert (HKB : 0 <= N0 * MG < wB) by (apply bnd_prod; plia).
    assert (HxB : 0 <= A + N0 * tZ < N0 * MG) by (apply xbound; plia).
    assert (HNtB : 0 <= N0 * tZ <= N0 * MG) by (apply mul_le_bound; plia).
    assert (Hx : (φ (xa + xn * ((((xb + xm - xa mod xm) mod xm) / g * s)
                                 mod (xm / g)))) = A + N0 * tZ).
    { rewrite add_spec, mul_spec, Ht, Ra, Rn.
      rewrite (Z.mod_small (N0 * tZ))
        by (split; [apply HNtB | eapply Z.le_lt_trans; [apply HNtB | apply HKB]]).
      apply Z.mod_small.
      split; [apply HxB | eapply Z.lt_trans; [apply HxB | apply HKB]]. }
    assert (HKm : (φ (xn * (xm / g))) = N0 * MG).
    { rewrite mul_spec, Hmg, Rn. apply Z.mod_small. exact HKB. }
    exists (Some (Z.to_N (A + N0 * tZ), Z.to_N (N0 * MG))).
    split.
    + split; apply repr_uint_of; assumption.
    + destruct (combine_ok A N0 B M G (φ s) dZ tZ HA HB HGpos HGN HGM
                  ltac:(rewrite <- Hg; exact HgsD) eq_refl HdG eq_refl)
        as [C1 C2].
      refine (conj _ (conj _ _)).
      * apply N2Z.inj. rewrite Z2N.id by plia.
        unfold N.lcm. rewrite N2Z.inj_mul, N2Z.inj_div, N_gcd_Z. reflexivity.
      * apply N2Z.inj_lt. rewrite !Z2N.id by plia. exact (proj2 HxB).
      * unfold solves. rewrite Z2N.id by plia. split; assumption.
  - (* no solution *)
    exists None. split; [exact I|].
    simpl. intros Hex.
    refine (none_ok A N0 B M G dZ ltac:(plia) ltac:(plia) HGN HGM eq_refl _ Hex).
    intros HdG. apply Z.mod_divide in HdG; [|plia].
    rewrite <- Bool.not_true_iff_false in E. apply E.
    rewrite eqb_spec. apply to_Z_inj.
    rewrite mod_spec, Hd, Hg. exact HdG.
Qed.

Definition crt_correct :
  forall (a n b m : N) (xa xn xb xm : uint),
  valid_input a n b m ->
  repr xa a -> repr xn n -> repr xb b -> repr xm m ->
  exists o : option (N * N), repr (crt xa xn xb xm) o /\ crt_spec a n b m o
  := crt_impl_correct.
