From Largesttriangle.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From StdGalilei Require Import repr repr_float.
From Flocq Require Core.Core.
From KattisLib Require Import Cost.
Import ListNotations.

Unset Lia Cache.

(* ================================================================== *)
(* Geometry over Z                                                     *)
(* ================================================================== *)

Local Open Scope Z_scope.

Definition cross (a b c : Z * Z) : Z :=
  (fst b - fst a) * (snd c - snd a) - (fst c - fst a) * (snd b - snd a).

(* the cross product of two vectors *)
Definition vx (v w : Z * Z) : Z := fst v * snd w - snd v * fst w.
Definition vsub (a b : Z * Z) : Z * Z := (fst a - fst b, snd a - snd b).
Definition pneg (a : Z * Z) : Z * Z := (- fst a, - snd a).

Definition lexpos (v : Z * Z) : Prop := 0 < fst v \/ (fst v = 0 /\ 0 < snd v).
Definition lexnn (v : Z * Z) : Prop := 0 < fst v \/ (fst v = 0 /\ 0 <= snd v).
Definition lexlt (a b : Z * Z) : Prop := lexpos (vsub b a).

Lemma cross_vx : forall a b c, cross a b c = vx (vsub b a) (vsub c a).
Proof. intros. unfold cross, vx, vsub; simpl. ring. Qed.

Lemma cross_vx2 : forall a b c, cross a b c = vx (vsub b a) (vsub c b).
Proof. intros. unfold cross, vx, vsub; simpl. ring. Qed.

Lemma cross_cyc : forall a b c, cross a b c = cross b c a.
Proof. intros. unfold cross. ring. Qed.

Lemma cross_swap : forall a b c, cross a b c = - cross a c b.
Proof. intros. unfold cross. ring. Qed.

Lemma cross_neg : forall a b c, cross (pneg a) (pneg b) (pneg c) = cross a b c.
Proof. intros. unfold cross, pneg; simpl. ring. Qed.

Lemma cross_aa : forall a c, cross a a c = 0.
Proof. intros. unfold cross. ring. Qed.

Lemma cross_bb : forall a b, cross a b b = 0.
Proof. intros. unfold cross. ring. Qed.

Lemma lexpos_nn : forall v, lexpos v -> lexnn v.
Proof. unfold lexpos, lexnn. intros v [H | [H1 H2]]; [left | right]; lia. Qed.

(* the transitivity of the angular order on a half-plane of directions *)
Lemma vx_trans : forall v f w, lexnn v -> lexpos f -> lexnn w ->
  0 <= vx v f -> 0 <= vx f w -> 0 <= vx v w.
Proof.
  intros [v1 v2] [f1 f2] [w1 w2]. unfold lexnn, lexpos, vx; simpl.
  intros Hv Hf Hw H1 H2.
  assert (I1 : (v1 * w2 - v2 * w1) * f1 = (v1 * f2 - v2 * f1) * w1 + (f1 * w2 - f2 * w1) * v1) by ring.
  assert (I2 : (v1 * w2 - v2 * w1) * f2 = (v1 * f2 - v2 * f1) * w2 + (f1 * w2 - f2 * w1) * v2) by ring.
  destruct Hf as [Hf | [Hf1 Hf2]].
  - assert (0 <= (v1 * f2 - v2 * f1) * w1) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= (f1 * w2 - f2 * w1) * v1) by (apply Z.mul_nonneg_nonneg; lia).
    nia.
  - subst f1. destruct Hv as [Hv | [Hv1 Hv2]]; destruct Hw as [Hw | [Hw1 Hw2]]; subst; nia.
Qed.

Lemma vx_trans_strict : forall v f w, lexnn v -> lexpos f -> lexpos w ->
  0 < vx v f -> 0 < vx f w -> 0 < vx v w.
Proof.
  intros [v1 v2] [f1 f2] [w1 w2]. unfold lexnn, lexpos, vx; simpl.
  intros Hv Hf Hw H1 H2.
  assert (I1 : (v1 * w2 - v2 * w1) * f1 = (v1 * f2 - v2 * f1) * w1 + (f1 * w2 - f2 * w1) * v1) by ring.
  assert (I2 : (v1 * w2 - v2 * w1) * f2 = (v1 * f2 - v2 * f1) * w2 + (f1 * w2 - f2 * w1) * v2) by ring.
  destruct Hf as [Hf | [Hf1 Hf2]]; destruct Hv as [Hv | [Hv1 Hv2]]; destruct Hw as [Hw | [Hw1 Hw2]];
    subst; nia.
Qed.

Lemma vx_anti : forall v w, vx v w = - vx w v.
Proof. intros. unfold vx. ring. Qed.

Lemma cross_shift : forall a b c d, cross a b c = cross a b d + vx (vsub b a) (vsub c d).
Proof. intros. unfold cross, vx, vsub; simpl. ring. Qed.

Lemma cross_back : forall c a q, cross c a q = vx (vsub a q) (vsub a c).
Proof. intros. unfold cross, vx, vsub; simpl. ring. Qed.

Lemma vsub_self : forall a, vsub a a = (0, 0).
Proof. intros [a1 a2]. unfold vsub; simpl. f_equal; ring. Qed.

Lemma lexnn_zero : lexnn (0, 0).
Proof. unfold lexnn; simpl. lia. Qed.

(* ------------------------------------------------------------------ *)
(* The chain of Andrew's monotone chain, on the math side              *)
(* ------------------------------------------------------------------ *)

(* Q : the points, in processing order ; l : the stack (indices into Q) ;
   r : its size ; s : the number of points processed *)
Definition Qinc (Q : Z -> Z * Z) (m : Z) : Prop :=
  forall a b, 0 <= a /\ a < b < m -> lexlt (Q a) (Q b).

Definition E (Q : Z -> Z * Z) (l : Z -> Z) (t : Z) : Z * Z := vsub (Q (l (t + 1))) (Q (l t)).

Record chain_ok (Q : Z -> Z * Z) (s : Z) (l : Z -> Z) (r : Z) : Prop := {
  ch_r : 1 <= r;
  ch_0 : l 0 = 0;
  ch_top : l (r - 1) = s - 1;
  ch_inc : forall t, 0 <= t < r - 1 -> l t < l (t + 1);
  ch_edge : forall t1 t2, 0 <= t1 /\ t1 < t2 < r - 1 -> 0 < vx (E Q l t1) (E Q l t2);
  ch_left : forall u t, 0 <= u < s -> 0 <= t < r - 1 -> 0 <= cross (Q (l t)) (Q (l (t + 1))) (Q u)
}.

Definition upd (l : Z -> Z) (p v : Z) : Z -> Z := fun t => if Z.eq_dec t p then v else l t.

Lemma ch_mono : forall Q s l r, chain_ok Q s l r ->
  forall a b, 0 <= a -> a < b -> b < r -> l a < l b.
Proof.
  intros Q s l r C a b Ha Hab Hb.
  assert (G : forall n : nat, a + 1 + Z.of_nat n < r -> l a < l (a + 1 + Z.of_nat n)).
  { induction n as [| n IH]; intros Hn.
    - replace (a + 1 + Z.of_nat 0) with (a + 1) by lia. apply (ch_inc _ _ _ _ C). lia.
    - pose proof (IH ltac:(lia)) as H1.
      pose proof (ch_inc _ _ _ _ C (a + 1 + Z.of_nat n) ltac:(lia)) as H2.
      replace (a + 1 + Z.of_nat n + 1) with (a + 1 + Z.of_nat (S n)) in H2 by lia. lia. }
  replace b with (a + 1 + Z.of_nat (Z.to_nat (b - a - 1))) by lia. apply G; lia.
Qed.

Lemma ch_range : forall Q s l r, chain_ok Q s l r ->
  forall t, 0 <= t < r -> 0 <= l t <= s - 1.
Proof.
  intros Q s l r C t Ht.
  pose proof (ch_0 _ _ _ _ C). pose proof (ch_top _ _ _ _ C).
  assert (l 0 <= l t).
  { destruct (Z.eq_dec t 0) as [E0 | N0]; [rewrite E0; lia |].
    pose proof (ch_mono _ _ _ _ C 0 t ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  assert (l t <= l (r - 1)).
  { destruct (Z.eq_dec t (r - 1)) as [E0 | N0]; [rewrite E0; lia |].
    pose proof (ch_mono _ _ _ _ C t (r - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  lia.
Qed.

Lemma cross_aba : forall a b, cross a b a = 0.
Proof. intros. unfold cross. ring. Qed.

Lemma chain_push : forall Q s l r0 r',
  Qinc Q (s + 1) -> 1 <= s -> chain_ok Q s l r0 -> 1 <= r' <= r0 ->
  (r' < r0 -> cross (Q (l (r' - 1))) (Q (l r')) (Q s) <= 0) ->
  (2 <= r' -> 0 < cross (Q (l (r' - 2))) (Q (l (r' - 1))) (Q s)) ->
  chain_ok Q (s + 1) (upd l r' s) (r' + 1).
Proof.
  intros Q s l r0 r' HQ Hs C Hr Pa Pb.
  pose proof (ch_range _ _ _ _ C) as Rg.
  assert (U1 : forall t, t <> r' -> upd l r' s t = l t)
    by (intros t Ht; unfold upd; destruct (Z.eq_dec t r'); [contradiction | reflexivity]).
  assert (U2 : upd l r' s r' = s) by (unfold upd; destruct (Z.eq_dec r' r'); [reflexivity | contradiction]).
  (* lex positivity of the old edges and of the new one *)
  assert (Epos : forall t, 0 <= t < r0 - 1 -> lexpos (E Q l t)).
  { intros t Ht. unfold E. apply HQ. pose proof (ch_inc _ _ _ _ C t Ht). pose proof (Rg t ltac:(lia)).
    pose proof (Rg (t + 1) ltac:(lia)). lia. }
  set (a := Q (l (r' - 1))).
  set (v := vsub (Q s) a).
  assert (Vpos : lexpos v).
  { unfold v, a. apply HQ. pose proof (Rg (r' - 1) ltac:(lia)). lia. }
  (* E (r'-2) x v > 0 *)
  assert (Ev : 2 <= r' -> 0 < vx (E Q l (r' - 2)) v).
  { intros H2. specialize (Pb H2). rewrite cross_vx2 in Pb. unfold E, v, a.
    replace (r' - 2 + 1) with (r' - 1) by lia. exact Pb. }
  assert (Etv : forall t, 0 <= t <= r' - 2 -> 0 < vx (E Q l t) v).
  { intros t Ht. destruct (Z.eq_dec t (r' - 2)) as [-> | N].
    - apply Ev. lia.
    - apply (vx_trans_strict _ (E Q l (r' - 2))).
      + apply lexpos_nn, Epos. lia.
      + apply Epos. lia.
      + exact Vpos.
      + apply (ch_edge _ _ _ _ C). lia.
      + apply Ev. lia. }
  constructor.
  - lia.
  - rewrite U1 by lia. apply (ch_0 _ _ _ _ C).
  - replace (r' + 1 - 1) with r' by lia. rewrite U2. lia.
  - intros t Ht. rewrite U1 by lia.
    destruct (Z.eq_dec (t + 1) r') as [E1 | N1].
    + rewrite E1, U2. pose proof (Rg t ltac:(lia)). lia.
    + rewrite U1 by lia. apply (ch_inc _ _ _ _ C). lia.
  - intros t1 t2 Ht.
    assert (EE : forall t, 0 <= t < r' - 1 -> E Q (upd l r' s) t = E Q l t).
    { intros t Ht'. unfold E. rewrite !U1 by lia. reflexivity. }
    rewrite EE by lia.
    destruct (Z.eq_dec t2 (r' - 1)) as [E2 | N2].
    + assert (E3 : E Q (upd l r' s) t2 = v).
      { unfold E. rewrite E2. replace (r' - 1 + 1) with r' by lia. rewrite U2, U1 by lia. reflexivity. }
      rewrite E3. apply Etv. lia.
    + rewrite EE by lia. apply (ch_edge _ _ _ _ C). lia.
  - intros u t Hu Ht. rewrite U1 by lia.
    destruct (Z.eq_dec (t + 1) r') as [E1 | N1].
    + (* the new edge, from a to Q s *)
      rewrite E1, U2. replace t with (r' - 1) by lia. fold a.
      destruct (Z.eq_dec u s) as [-> | Nus].
      { rewrite cross_bb. lia. }
      destruct (Z_le_gt_dec u (l (r' - 1))) as [Lu | Gu].
      * destruct (Z.eq_dec r' 1) as [R1 | R1].
        -- assert (Hl0 : l (r' - 1) = 0) by (replace (r' - 1) with 0 by lia; apply (ch_0 _ _ _ _ C)).
           replace u with (l (r' - 1)) by lia. fold a. rewrite cross_aba. lia.
        -- set (c := Q (l (r' - 2))).
           set (w := vsub a (Q u)).
           assert (Wnn : lexnn w).
           { unfold w, a. destruct (Z.eq_dec u (l (r' - 1))) as [Eu | Nu].
             - rewrite <- Eu, vsub_self. apply lexnn_zero.
             - apply lexpos_nn, HQ. pose proof (Rg (r' - 1) ltac:(lia)). lia. }
           assert (Hl : 0 <= cross c a (Q u)).
           { unfold c, a. pose proof (ch_left _ _ _ _ C u (r' - 2) ltac:(lia) ltac:(lia)) as H.
             replace (r' - 2 + 1) with (r' - 1) in H by lia. exact H. }
           rewrite cross_back in Hl. fold w in Hl.
           assert (Ee : vsub a c = E Q l (r' - 2)).
           { unfold E, a, c. replace (r' - 2 + 1) with (r' - 1) by lia. reflexivity. }
           rewrite Ee in Hl.
           assert (T := vx_trans w (E Q l (r' - 2)) v Wnn (Epos (r' - 2) ltac:(lia)) (lexpos_nn _ Vpos) Hl
                          (Z.lt_le_incl _ _ (Ev ltac:(lia)))).
           rewrite cross_vx. unfold v in T. unfold w in T.
           replace (vsub (Q u) a) with (pneg (vsub a (Q u))) by (unfold pneg, vsub; simpl; f_equal; ring).
           unfold vx, pneg in *; simpl in *. lia.
      * assert (Hr0 : r' < r0).
        { destruct (Z.eq_dec r' r0) as [Er | Nr]; [| lia].
          pose proof (ch_top _ _ _ _ C) as Ht0. rewrite <- Er in Ht0. lia. }
        set (b := Q (l r')).
        assert (Ha1 : 0 <= cross a b (Q u)).
        { unfold a, b. pose proof (ch_left _ _ _ _ C u (r' - 1) ltac:(lia) ltac:(lia)) as H.
          replace (r' - 1 + 1) with r' in H by lia. exact H. }
        assert (Ha2 := Pa Hr0). fold a b in Ha2.
        rewrite cross_vx in Ha1, Ha2. fold v in Ha2.
        assert (Fpos : lexpos (vsub b a)).
        { unfold a, b. replace r' with (r' - 1 + 1) at 1 by lia. apply (Epos (r' - 1)). lia. }
        assert (Upos : lexnn (vsub (Q u) a)).
        { apply lexpos_nn. unfold a. apply HQ. pose proof (Rg (r' - 1) ltac:(lia)). lia. }
        rewrite cross_vx. fold v.
        apply (vx_trans v (vsub b a) (vsub (Q u) a) (lexpos_nn _ Vpos) Fpos Upos); [| exact Ha1].
        rewrite vx_anti. lia.
    + rewrite U1 by lia.
      destruct (Z.eq_dec u s) as [-> | Nus].
      * (* an old edge and the new point *)
        rewrite (cross_shift _ _ _ a).
        pose proof (ch_left _ _ _ _ C (l (r' - 1)) t ltac:(pose proof (Rg (r' - 1)); lia) ltac:(lia)) as H1.
        fold a in H1. fold v.
        assert (H2 : 0 < vx (E Q l t) v) by (apply Etv; lia).
        unfold E in H2. lia.
      * apply (ch_left _ _ _ _ C); lia.
Qed.

Lemma vx_split_l : forall a y z w, vx (vsub z a) w = vx (vsub y a) w + vx (vsub z y) w.
Proof. intros. unfold vx, vsub; simpl. ring. Qed.

Lemma vx_split_r : forall a y z w, vx w (vsub z a) = vx w (vsub y a) + vx w (vsub z y).
Proof. intros. unfold vx, vsub; simpl. ring. Qed.

Lemma ch_chord_edge : forall Q s l r, chain_ok Q s l r ->
  forall a b t, 0 <= a -> a < b -> b <= t -> t < r - 1 ->
  0 < vx (vsub (Q (l b)) (Q (l a))) (E Q l t).
Proof.
  intros Q s l r C a b t Ha Hab Hbt Ht.
  assert (G : forall n : nat, a + 1 + Z.of_nat n <= t ->
            0 < vx (vsub (Q (l (a + 1 + Z.of_nat n))) (Q (l a))) (E Q l t)).
  { induction n as [| n IH]; intros Hn.
    - replace (a + 1 + Z.of_nat 0) with (a + 1) by lia. apply (ch_edge _ _ _ _ C). lia.
    - rewrite (vx_split_l _ (Q (l (a + 1 + Z.of_nat n)))).
      pose proof (IH ltac:(lia)).
      pose proof (ch_edge _ _ _ _ C (a + 1 + Z.of_nat n) t ltac:(lia)) as H2.
      unfold E at 1 in H2. replace (a + 1 + Z.of_nat n + 1) with (a + 1 + Z.of_nat (S n)) in H2 by lia.
      lia. }
  replace b with (a + 1 + Z.of_nat (Z.to_nat (b - a - 1))) by lia. apply G; lia.
Qed.

Lemma ch_convex : forall Q s l r, chain_ok Q s l r ->
  forall a b c, 0 <= a -> a < b -> b < c -> c < r ->
  0 < cross (Q (l a)) (Q (l b)) (Q (l c)).
Proof.
  intros Q s l r C a b c Ha Hab Hbc Hc. rewrite cross_vx2.
  assert (G : forall n : nat, b + 1 + Z.of_nat n < r ->
            0 < vx (vsub (Q (l b)) (Q (l a))) (vsub (Q (l (b + 1 + Z.of_nat n))) (Q (l b)))).
  { induction n as [| n IH]; intros Hn.
    - replace (b + 1 + Z.of_nat 0) with (b + 1) by lia.
      pose proof (ch_chord_edge _ _ _ _ C a b b Ha Hab ltac:(lia) ltac:(lia)) as H. exact H.
    - rewrite (vx_split_r _ (Q (l (b + 1 + Z.of_nat n)))).
      pose proof (IH ltac:(lia)).
      pose proof (ch_chord_edge _ _ _ _ C a b (b + 1 + Z.of_nat n) Ha Hab ltac:(lia) ltac:(lia)) as H2.
      unfold E in H2. replace (b + 1 + Z.of_nat n + 1) with (b + 1 + Z.of_nat (S n)) in H2 by lia.
      lia. }
  replace c with (b + 1 + Z.of_nat (Z.to_nat (c - b - 1))) by lia. apply G; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* A point beyond the closing chord of a chain is left of every chord   *)
(* ------------------------------------------------------------------ *)

Definition lexle (a b : Z * Z) : Prop := lexnn (vsub b a).

Lemma beyond_arith : forall x0 y0 xn yn xi yi xj yj ux uy,
  x0 <= ux <= xn -> (ux = xn -> uy <= yn) ->
  (xi < xj \/ (xi = xj /\ yi < yj)) -> xi <= xn ->
  0 <= cross (xi, yi) (xj, yj) (x0, y0) -> 0 <= cross (xi, yi) (xj, yj) (xn, yn) ->
  0 < cross (x0, y0) (xn, yn) (ux, uy) ->
  0 < cross (xi, yi) (xj, yj) (ux, uy).
Proof.
  intros x0 y0 xn yn xi yi xj yj ux uy Hx Hxn Hd Hin G0 Gn HD.
  unfold cross in *; simpl in *.
  assert (I : (xn - x0) * ((xj - xi) * (uy - yi) - (ux - xi) * (yj - yi)) =
              (xj - xi) * ((xn - x0) * (uy - y0) - (ux - x0) * (yn - y0))
              + (xn - ux) * ((xj - xi) * (y0 - yi) - (x0 - xi) * (yj - yi))
              + (ux - x0) * ((xj - xi) * (yn - yi) - (xn - xi) * (yj - yi))) by ring.
  assert (Dx : x0 < xn).
  { destruct (Z.eq_dec x0 xn) as [E0 | N]; [| lia]. subst xn.
    assert (ux = x0) by lia. subst ux. nia. }
  assert (Ux : ux < xn).
  { destruct (Z.eq_dec ux xn) as [E0 | N]; [| lia]. subst ux.
    specialize (Hxn eq_refl). nia. }
  set (g := (xj - xi) * (uy - yi) - (ux - xi) * (yj - yi)) in *.
  set (h := (xn - x0) * (uy - y0) - (ux - x0) * (yn - y0)) in *.
  set (g0 := (xj - xi) * (y0 - yi) - (x0 - xi) * (yj - yi)) in *.
  set (gn := (xj - xi) * (yn - yi) - (xn - xi) * (yj - yi)) in *.
  assert (P2 : 0 <= (ux - x0) * gn) by (apply Z.mul_nonneg_nonneg; lia).
  destruct Hd as [Hd | [Hd1 Hd2]].
  - assert (P1 : 0 < (xj - xi) * h) by (apply Z.mul_pos_pos; lia).
    assert (P3 : 0 <= (xn - ux) * g0) by (apply Z.mul_nonneg_nonneg; lia).
    nia.
  - subst xj. unfold g0, gn in *.
    assert (Exi : xi = xn) by nia. subst xi.
    assert (P3 : 0 < (xn - ux) * g0).
    { apply Z.mul_pos_pos; [lia |]. unfold g0. nia. }
    unfold g0 in P3. nia.
Qed.

Lemma beyond_chain : forall (c : Z -> Z * Z) (n : Z) (u : Z * Z),
  (forall a b, 0 <= a -> a < b -> b <= n -> lexlt (c a) (c b)) ->
  (forall a b d, 0 <= a -> a < b -> b < d -> d <= n -> 0 < cross (c a) (c b) (c d)) ->
  lexle (c 0) u -> lexle u (c n) -> 0 < cross (c 0) (c n) u ->
  forall i j, 0 <= i -> i < j -> j <= n -> 0 < cross (c i) (c j) u.
Proof.
  intros c n u Hinc Hcv H0 Hn HD i j Hi Hij Hj.
  assert (G0 : 0 <= cross (c i) (c j) (c 0)).
  { destruct (Z.eq_dec i 0) as [E0 | N0].
    - rewrite E0, cross_aba. lia.
    - rewrite <- cross_cyc. pose proof (Hcv 0 i j ltac:(lia) ltac:(lia) Hij Hj). lia. }
  assert (Gn : 0 <= cross (c i) (c j) (c n)).
  { destruct (Z.eq_dec j n) as [E0 | N0].
    - rewrite E0, cross_bb. lia.
    - pose proof (Hcv i j n Hi Hij ltac:(lia) ltac:(lia)). lia. }
  assert (Lij := Hinc i j Hi Hij Hj).
  assert (Lin : lexle (c i) (c n)).
  { destruct (Z.eq_dec i n) as [E0 | N0]; [lia |]. apply lexpos_nn, Hinc; lia. }
  destruct (c 0) as [x0 y0], (c n) as [xn yn], (c i) as [xi yi], (c j) as [xj yj], u as [ux uy].
  unfold lexle, lexlt, lexnn, lexpos, vsub in *; simpl in *.
  apply (beyond_arith x0 y0 xn yn xi yi xj yj ux uy); try assumption; try lia.
Qed.

Lemma lexle_pneg : forall x y, lexle (pneg x) (pneg y) <-> lexle y x.
Proof. intros [x1 x2] [y1 y2]. unfold lexle, lexnn, pneg, vsub; simpl. lia. Qed.

Lemma lexlt_pneg : forall x y, lexlt (pneg x) (pneg y) <-> lexlt y x.
Proof. intros [x1 x2] [y1 y2]. unfold lexlt, lexpos, pneg, vsub; simpl. lia. Qed.

Lemma lexlt_le : forall x y, lexlt x y -> lexle x y.
Proof. intros x y H. apply lexpos_nn, H. Qed.

Lemma lexle_refl : forall x, lexle x x.
Proof. intros x. unfold lexle. rewrite vsub_self. apply lexnn_zero. Qed.

(* ------------------------------------------------------------------ *)
(* The hull: the lower chain, then the inner points of the upper one   *)
(* ------------------------------------------------------------------ *)

Section Hull.
Variable q : Z -> Z * Z.
Variable m : Z.
Hypothesis Hq : Qinc q m.
Hypothesis Hm : 2 <= m.

Definition Qu (s : Z) : Z * Z := pneg (q (m - 1 - s)).

Lemma Qu_inc : Qinc Qu m.
Proof. intros x y Hxy. unfold Qu. apply lexlt_pneg, Hq. lia. Qed.

Variables (lw uw : Z -> Z) (a b : Z).
Hypothesis Hlw : chain_ok q m lw a.
Hypothesis Huw : chain_ok Qu m uw b.

Definition Lp (t : Z) : Z * Z := q (lw t).
Definition Up (t : Z) : Z * Z := q (m - 1 - uw t).
Definition hh : Z := a + b - 2.
Definition Hp (t : Z) : Z * Z := if Z_lt_dec t a then Lp t else Up (t - a + 1).

Lemma q_min : forall v, 0 <= v < m -> lexle (q 0) (q v).
Proof.
  intros v Hv. destruct (Z.eq_dec v 0) as [-> | N]; [apply lexle_refl | apply lexlt_le, Hq; lia].
Qed.

Lemma q_max : forall v, 0 <= v < m -> lexle (q v) (q (m - 1)).
Proof.
  intros v Hv. destruct (Z.eq_dec v (m - 1)) as [-> | N]; [apply lexle_refl | apply lexlt_le, Hq; lia].
Qed.

Lemma a_ge2 : 2 <= a.
Proof.
  pose proof (ch_r _ _ _ _ Hlw). destruct (Z.eq_dec a 1) as [E1 | N]; [| lia].
  pose proof (ch_0 _ _ _ _ Hlw). pose proof (ch_top _ _ _ _ Hlw). rewrite E1 in *. simpl in *. lia.
Qed.

Lemma b_ge2 : 2 <= b.
Proof.
  pose proof (ch_r _ _ _ _ Huw). destruct (Z.eq_dec b 1) as [E1 | N]; [| lia].
  pose proof (ch_0 _ _ _ _ Huw). pose proof (ch_top _ _ _ _ Huw). rewrite E1 in *. simpl in *. lia.
Qed.

Lemma Lp_first : Lp 0 = q 0.
Proof. unfold Lp. rewrite (ch_0 _ _ _ _ Hlw). reflexivity. Qed.

Lemma Lp_last : Lp (a - 1) = q (m - 1).
Proof. unfold Lp. rewrite (ch_top _ _ _ _ Hlw). reflexivity. Qed.

Lemma Up_first : Up 0 = q (m - 1).
Proof. unfold Up. rewrite (ch_0 _ _ _ _ Huw). f_equal. lia. Qed.

Lemma Up_last : Up (b - 1) = q 0.
Proof. unfold Up. rewrite (ch_top _ _ _ _ Huw). f_equal. lia. Qed.

Lemma Lp_in : forall t, 0 <= t < a -> exists v, 0 <= v < m /\ Lp t = q v.
Proof. intros t Ht. exists (lw t). split; [pose proof (ch_range _ _ _ _ Hlw t Ht); lia | reflexivity]. Qed.

Lemma Up_in : forall t, 0 <= t < b -> exists v, 0 <= v < m /\ Up t = q v.
Proof.
  intros t Ht. exists (m - 1 - uw t). split; [pose proof (ch_range _ _ _ _ Huw t Ht); lia | reflexivity].
Qed.

Lemma Hp_in : forall t, 0 <= t < hh -> exists v, 0 <= v < m /\ Hp t = q v.
Proof.
  intros t Ht. unfold Hp, hh in *. destruct (Z_lt_dec t a).
  - apply Lp_in. lia.
  - apply Up_in. lia.
Qed.

Lemma Hp_low : forall t, 0 <= t < a -> Hp t = Lp t.
Proof. intros t Ht. unfold Hp. destruct (Z_lt_dec t a); [reflexivity | lia]. Qed.

Lemma Hp_up : forall t, a - 1 <= t -> Hp t = Up (t - a + 1).
Proof.
  intros t Ht. unfold Hp. destruct (Z_lt_dec t a); [| reflexivity].
  replace t with (a - 1) by lia. replace (a - 1 - a + 1) with 0 by lia. rewrite Lp_last, Up_first. reflexivity.
Qed.

Lemma Lp_convex : forall i j k, 0 <= i -> i < j -> j < k -> k < a -> 0 < cross (Lp i) (Lp j) (Lp k).
Proof. intros. apply (ch_convex _ _ _ _ Hlw); lia. Qed.

Lemma Up_convex : forall i j k, 0 <= i -> i < j -> j < k -> k < b -> 0 < cross (Up i) (Up j) (Up k).
Proof.
  intros. pose proof (ch_convex _ _ _ _ Huw i j k) as Hc. unfold Qu in Hc. rewrite !cross_neg in Hc.
  apply Hc; lia.
Qed.

Lemma Lp_inc : forall i j, 0 <= i -> i < j -> j <= a - 1 -> lexlt (Lp i) (Lp j).
Proof.
  intros i j Hi Hij Hj. unfold Lp. pose proof (ch_mono _ _ _ _ Hlw i j Hi Hij ltac:(lia)).
  pose proof (ch_range _ _ _ _ Hlw j ltac:(lia)). pose proof (ch_range _ _ _ _ Hlw i ltac:(lia)).
  apply Hq. lia.
Qed.

Lemma Up_dec : forall i j, 0 <= i -> i < j -> j <= b - 1 -> lexlt (pneg (Up i)) (pneg (Up j)).
Proof.
  intros i j Hi Hij Hj. unfold Up. pose proof (ch_mono _ _ _ _ Huw i j Hi Hij ltac:(lia)).
  pose proof (ch_range _ _ _ _ Huw j ltac:(lia)). pose proof (ch_range _ _ _ _ Huw i ltac:(lia)).
  apply lexlt_pneg, Hq. lia.
Qed.

(* lower, lower, upper *)
Lemma LLU : forall i j k, 0 <= i -> i < j -> j <= a - 1 -> 1 <= k <= b - 2 ->
  0 < cross (Lp i) (Lp j) (Up k).
Proof.
  intros i j k Hi Hij Hj Hk.
  destruct (Up_in k ltac:(lia)) as (v & Hv & Ev).
  apply (beyond_chain Lp (a - 1) (Up k)); try lia.
  - intros. apply Lp_inc; lia.
  - intros. apply Lp_convex; lia.
  - rewrite Lp_first, Ev. apply q_min. exact Hv.
  - rewrite Lp_last, Ev. apply q_max. exact Hv.
  - rewrite Lp_first, Lp_last, <- Up_first, <- Up_last, cross_cyc. apply Up_convex; lia.
Qed.

(* lower, upper, upper *)
Lemma LUU : forall i j k, 0 <= i <= a - 1 -> 1 <= j -> j < k -> k <= b - 2 ->
  0 < cross (Lp i) (Up j) (Up k).
Proof.
  intros i j k Hi Hj Hjk Hk.
  destruct (Z.eq_dec i 0) as [-> | N0].
  { rewrite Lp_first, <- Up_last, cross_cyc. apply Up_convex; lia. }
  destruct (Z.eq_dec i (a - 1)) as [-> | N1].
  { rewrite Lp_last, <- Up_first. apply Up_convex; lia. }
  rewrite cross_cyc, <- cross_neg.
  destruct (Lp_in i ltac:(lia)) as (v & Hv & Ev).
  apply (beyond_chain (fun t => pneg (Up t)) (b - 1) (pneg (Lp i))); try lia.
  - intros. apply Up_dec; lia.
  - intros. rewrite cross_neg. apply Up_convex; lia.
  - rewrite Up_first, Ev. apply lexle_pneg, q_max. exact Hv.
  - rewrite Up_last, Ev. apply lexle_pneg, q_min. exact Hv.
  - rewrite cross_neg, Up_first, Up_last, <- Lp_first, <- Lp_last, cross_cyc.
    apply Lp_convex; lia.
Qed.

Lemma Hp_convex : forall i j k, 0 <= i -> i < j -> j < k -> k < hh ->
  0 < cross (Hp i) (Hp j) (Hp k).
Proof.
  intros i j k Hi Hij Hjk Hk. unfold hh in Hk.
  destruct (Z_lt_dec k a).
  - rewrite !Hp_low by lia. apply Lp_convex; lia.
  - destruct (Z_lt_dec j a).
    + rewrite (Hp_low i), (Hp_low j), (Hp_up k) by lia. apply LLU; lia.
    + destruct (Z_lt_dec i a).
      * rewrite (Hp_low i), (Hp_up j), (Hp_up k) by lia. apply LUU; lia.
      * rewrite !Hp_up by lia. apply Up_convex; lia.
Qed.

(* every point is left of (or on) every edge of the hull *)
Lemma Hp_left : forall u t, 0 <= u < m -> 0 <= t < hh - 1 ->
  0 <= cross (Hp t) (Hp (t + 1)) (q u).
Proof.
  intros u t Hu Ht. unfold hh in Ht. destruct (Z_lt_dec t (a - 1)).
  - rewrite !Hp_low by lia. apply (ch_left _ _ _ _ Hlw); lia.
  - rewrite !Hp_up by lia.
    pose proof (ch_left _ _ _ _ Huw (m - 1 - u) (t - a + 1) ltac:(lia) ltac:(lia)) as H.
    unfold Qu in H. rewrite cross_neg in H. replace (m - 1 - (m - 1 - u)) with u in H by lia.
    replace (t + 1 - a + 1) with (t - a + 1 + 1) by lia. exact H.
Qed.

Lemma Hp_left_close : forall u, 0 <= u < m -> 0 <= cross (Hp (hh - 1)) (Hp 0) (q u).
Proof.
  intros u Hu. pose proof a_ge2. pose proof b_ge2. unfold hh.
  rewrite (Hp_up (a + b - 2 - 1)) by lia. rewrite (Hp_low 0) by lia. rewrite Lp_first, <- Up_last.
  pose proof (ch_left _ _ _ _ Huw (m - 1 - u) (b - 2) ltac:(lia) ltac:(lia)) as Hc.
  unfold Qu in Hc. rewrite cross_neg in Hc. replace (m - 1 - (m - 1 - u)) with u in Hc by lia.
  replace (a + b - 2 - 1 - a + 1) with (b - 2) by lia. replace (b - 2 + 1) with (b - 1) in Hc by lia.
  exact Hc.
Qed.

End Hull.

(* ------------------------------------------------------------------ *)
(* The two facts behind the rotating sweep                             *)
(* ------------------------------------------------------------------ *)

(* for fixed corners A, B the area against the points of a convex chain
   C, E, F is unimodal: once it stops increasing it strictly decreases *)
Lemma unimodal_step : forall A B C E F,
  0 < cross A C F -> 0 < cross A E F -> 0 < cross A C E -> 0 < cross C E F ->
  0 < cross A B E ->
  cross A B E <= cross A B C -> cross A B F < cross A B E.
Proof.
  intros A B C E F H1 H2 H3 H4 H5 H6.
  assert (I1 : cross A C F * cross A B E = cross A E F * cross A B C + cross A C E * cross A B F)
    by (unfold cross; ring).
  assert (I2 : cross A E F + cross A C E = cross A C F + cross C E F) by (unfold cross; ring).
  set (d := cross A C F) in *. set (al := cross A E F) in *. set (be := cross A C E) in *.
  set (ga := cross C E F) in *. set (gE := cross A B E) in *. set (gC := cross A B C) in *.
  set (gF := cross A B F) in *.
  destruct (Z_lt_le_dec gF gE) as [L | L]; [exact L | exfalso].
  assert (al * gE <= al * gC) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (be * gE <= be * gF) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (0 < ga * gE) by (apply Z.mul_pos_pos; lia).
  nia.
Qed.

(* moving the second corner forward keeps an increasing step increasing *)
Lemma shift_step : forall A B B' C E,
  0 < cross A B C -> 0 < cross A B' C -> 0 < cross A B B' -> 0 < cross A C E ->
  cross A B C <= cross A B E -> cross A B' C < cross A B' E.
Proof.
  intros A B B' C E H1 H2 H3 H4 H5.
  assert (I : cross A B C * (cross A B' E - cross A B' C) =
              cross A B' C * (cross A B E - cross A B C) + cross A B B' * cross A C E)
    by (unfold cross; ring).
  assert (0 <= cross A B' C * (cross A B E - cross A B C)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (0 < cross A B B' * cross A C E) by (apply Z.mul_pos_pos; lia).
  nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Every point is a convex combination of hull vertices: the area      *)
(* against a fixed pair is largest at a vertex                          *)
(* ------------------------------------------------------------------ *)

Section Fan.
Variable p : Z -> Z * Z.
Variable h : Z.
Hypothesis Hh : 3 <= h.
Hypothesis Hc : forall i j k, 0 <= i -> i < j -> j < k -> k < h -> 0 < cross (p i) (p j) (p k).
Variable x : Z * Z.
Hypothesis Hl : forall t, 0 <= t < h - 1 -> 0 <= cross (p t) (p (t + 1)) x.
Hypothesis Hcl : 0 <= cross (p (h - 1)) (p 0) x.

Lemma fan_find : exists s, 1 <= s <= h - 2 /\ 0 <= cross (p 0) (p s) x /\ cross (p 0) (p (s + 1)) x <= 0.
Proof.
  assert (Last : cross (p 0) (p (h - 1)) x <= 0).
  { rewrite cross_cyc in Hcl. rewrite cross_swap. lia. }
  assert (G : forall k : nat, forall s, s = h - 2 - Z.of_nat k -> 1 <= s -> 0 <= cross (p 0) (p s) x ->
            exists s', 1 <= s' <= h - 2 /\ 0 <= cross (p 0) (p s') x /\ cross (p 0) (p (s' + 1)) x <= 0).
  { induction k as [| k IH]; intros s Es Hs Ps.
    - exists s. split; [lia |]. split; [exact Ps |]. replace (s + 1) with (h - 1) by lia. exact Last.
    - destruct (Z_le_gt_dec (cross (p 0) (p (s + 1)) x) 0) as [L | L].
      + exists s. split; [lia |]. auto.
      + apply (IH (s + 1)); lia. }
  apply (G (Z.to_nat (h - 3)) 1); [lia | lia |].
  pose proof (Hl 0 ltac:(lia)) as H0. exact H0.
Qed.

Lemma fan_max : forall B C, exists t, 0 <= t < h /\ Z.abs (cross x B C) <= Z.abs (cross (p t) B C).
Proof.
  intros B C. destruct fan_find as (s & Hs & P1 & P2).
  set (D := cross (p 0) (p s) (p (s + 1))).
  set (c0 := cross (p s) (p (s + 1)) x).
  set (c1 := - cross (p 0) (p (s + 1)) x).
  set (c2 := cross (p 0) (p s) x).
  assert (HD : 0 < D) by (apply Hc; lia).
  assert (H0 : 0 <= c0) by (apply Hl; lia).
  assert (I1 : D * cross x B C = c0 * cross (p 0) B C + c1 * cross (p s) B C + c2 * cross (p (s + 1)) B C)
    by (unfold D, c0, c1, c2, cross; ring).
  assert (I2 : D = c0 + c1 + c2) by (unfold D, c0, c1, c2, cross; ring).
  set (F0 := cross (p 0) B C) in *. set (F1 := cross (p s) B C) in *. set (F2 := cross (p (s + 1)) B C) in *.
  set (M := Z.max (Z.abs F0) (Z.max (Z.abs F1) (Z.abs F2))).
  assert (Hle : Z.abs (cross x B C) <= M).
  { assert (A0 : Z.abs (c0 * F0) <= c0 * M) by (rewrite Z.abs_mul, Z.abs_eq by lia; apply Z.mul_le_mono_nonneg_l; lia).
    assert (A1 : Z.abs (c1 * F1) <= c1 * M) by (rewrite Z.abs_mul, (Z.abs_eq c1) by lia; apply Z.mul_le_mono_nonneg_l; lia).
    assert (A2 : Z.abs (c2 * F2) <= c2 * M) by (rewrite Z.abs_mul, (Z.abs_eq c2) by lia; apply Z.mul_le_mono_nonneg_l; lia).
    assert (A : Z.abs (D * cross x B C) <= D * M).
    { rewrite I1. rewrite I2. rewrite !Z.mul_add_distr_r.
      pose proof (Z.abs_triangle (c0 * F0 + c1 * F1) (c2 * F2)).
      pose proof (Z.abs_triangle (c0 * F0) (c1 * F1)). lia. }
    rewrite Z.abs_mul, (Z.abs_eq D) in A by lia.
    apply (Z.mul_le_mono_pos_l _ _ D HD). exact A. }
  assert (Hm : M = Z.abs F0 \/ M = Z.abs F1 \/ M = Z.abs F2) by (unfold M; lia).
  destruct Hm as [Em | [Em | Em]]; rewrite Em in Hle.
  - exists 0. split; [lia | exact Hle].
  - exists s. split; [lia | exact Hle].
  - exists (s + 1). split; [lia | exact Hle].
Qed.

End Fan.

(* all points on one line through two distinct points: no area *)
Lemma collinear : forall p0 p1 A B C, p0 <> p1 ->
  cross p0 p1 A = 0 -> cross p0 p1 B = 0 -> cross p0 p1 C = 0 -> cross A B C = 0.
Proof.
  intros [x0 y0] [x1 y1] [ax ay] [bx by_] [cx cy] N HA HB HC.
  unfold cross in *; simpl in *.
  assert (I1 : ((bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay)) * (x1 - x0) =
     ((bx - ax) * (y1 - y0) - (by_ - ay) * (x1 - x0)) * (cx - ax) +
     ((x1 - x0) * (cy - ay) - (y1 - y0) * (cx - ax)) * (bx - ax)) by ring.
  assert (I2 : ((bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay)) * (y1 - y0) =
     ((bx - ax) * (y1 - y0) - (by_ - ay) * (x1 - x0)) * (cy - ay) +
     ((x1 - x0) * (cy - ay) - (y1 - y0) * (cx - ax)) * (by_ - ay)) by ring.
  assert (Z1 : (bx - ax) * (y1 - y0) - (by_ - ay) * (x1 - x0) = 0) by nia.
  assert (Z2 : (x1 - x0) * (cy - ay) - (y1 - y0) * (cx - ax) = 0) by nia.
  rewrite Z1, Z2 in I1, I2. simpl in I1, I2.
  destruct (Z.eq_dec x1 x0) as [Ex | Nx].
  - destruct (Z.eq_dec y1 y0) as [Ey | Ny]; [subst; contradiction |].
    apply Z.mul_eq_0 in I2. destruct I2 as [I2 | I2]; [exact I2 | lia].
  - apply Z.mul_eq_0 in I1. destruct I1 as [I1 | I1]; [exact I1 | lia].
Qed.

Local Close Scope Z_scope.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

Local Open Scope bool_scope.
Local Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.
Elpi complexity sumbool.
Elpi complexity bdec.
Arguments bdec_cost : simpl never.
Elpi complexity andb.
Arguments andb_cost : simpl never.
Elpi complexity orb.
Arguments orb_cost : simpl never.
Elpi complexity fst.
Arguments fst_cost : simpl never.

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

Lemma dec_r : forall r : int, (1 <? r) = true -> Zwf 0 (to_Z (r - 1)) (to_Z r).
Proof.
  intros r H. rewrite Uint63.ltb_spec in H. change (to_Z 1) with 1%Z in H.
  assert (to_Z (r - 1) = (to_Z r - 1)%Z) by sia. unfold Zwf. lia.
Qed.

Lemma ms_dec1 : forall lo hi : int, ((lo <? hi) && (1 <? hi - lo)) = true ->
  Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof.
  intros lo hi H. apply andb_prop in H as [H1 H2]. rewrite Uint63.ltb_spec in H1, H2.
  change (to_Z 1) with 1%Z in H2. pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
  assert (E : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
  assert (E2 : to_Z ((hi - lo) / 2) = ((to_Z hi - to_Z lo) / 2)%Z) by (rewrite Uint63.div_spec, E; reflexivity).
  assert (E3 : to_Z (lo + (hi - lo) / 2) = (to_Z lo + (to_Z hi - to_Z lo) / 2)%Z).
  { rewrite Uint63.add_spec, E2. apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
    assert ((to_Z hi - to_Z lo) / 2 <= to_Z hi - to_Z lo)%Z by (apply Z.div_le_upper_bound; lia). lia. }
  unfold Zwf, gap. rewrite E3. split; [lia |].
  assert ((to_Z hi - to_Z lo) / 2 < to_Z hi - to_Z lo)%Z by (apply Z.div_lt; lia). lia.
Qed.

Lemma ms_dec2 : forall lo hi : int, ((lo <? hi) && (1 <? hi - lo)) = true ->
  Zwf 0 (gap hi (lo + (hi - lo) / 2)) (gap hi lo).
Proof.
  intros lo hi H. apply andb_prop in H as [H1 H2]. rewrite Uint63.ltb_spec in H1, H2.
  change (to_Z 1) with 1%Z in H2. pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
  assert (E : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
  assert (E2 : to_Z ((hi - lo) / 2) = ((to_Z hi - to_Z lo) / 2)%Z) by (rewrite Uint63.div_spec, E; reflexivity).
  assert (E3 : to_Z (lo + (hi - lo) / 2) = (to_Z lo + (to_Z hi - to_Z lo) / 2)%Z).
  { rewrite Uint63.add_spec, E2. apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
    assert ((to_Z hi - to_Z lo) / 2 <= to_Z hi - to_Z lo)%Z by (apply Z.div_le_upper_bound; lia). lia. }
  unfold Zwf, gap. rewrite E3. split; [lia |].
  assert (1 <= (to_Z hi - to_Z lo) / 2)%Z by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(* The one generic loop: for i = lo, lo+1, ... while i < hi and [cont i s], s := f i s. *)
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
Elpi complexity wloop.
Arguments wloop_cost : simpl never.
Elpi complexity loop.
Arguments loop_cost : simpl never.

(* -- Cross products, exact in 63 bits ------------------------------- *)

Definition SH : int := 67108864.               (* 2^26 > 4 * 10^7 *)
Definition OFF : int := 1152921504606846976.   (* 2^60 *)
Elpi complexity SH.
Arguments SH_cost : simpl never.
Elpi complexity OFF.
Arguments OFF_cost : simpl never.

(* the cross product (B - A) x (C - A), plus OFF so that it is non-negative *)
Definition crs (ax ay bx by_ cx cy : int) : int :=
  (bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay) + OFF.
Elpi complexity crs.
Arguments crs_cost : simpl never.

(* -- The sort: top-down merge sort of the keys ----------------------- *)

Definition merge_step (A : array int) (mid hi : int) (k : int) (st : array int * int * int)
    : array int * int * int :=
  let '(T, i, j) := st in
  if (i <? mid) && ((hi <=? j) || (A.[i] <=? A.[j])) then (T.[k <- A.[i]], i + 1, j)
  else (T.[k <- A.[j]], i, j + 1).
Elpi complexity merge_step.
Arguments merge_step_cost : simpl never.

Definition merge (A T : array int) (lo mid hi : int) : array int :=
  let '(T', _, _) := loop hi (fun _ _ => true) (merge_step A mid hi) lo (T, lo, mid) in T'.
Elpi complexity merge.
Arguments merge_cost : simpl never.

Definition copy_step (T : array int) (k : int) (A : array int) : array int := A.[k <- T.[k]].
Elpi complexity copy_step.
Arguments copy_step_cost : simpl never.

Fixpoint msort (A T : array int) (lo hi : int) (H : Acc (Zwf 0) (gap hi lo)) {struct H}
    : array int * array int :=
  match bdec ((lo <? hi) && (1 <? hi - lo)) with
  | left Hlt =>
      let mid := lo + (hi - lo) / 2 in
      let '(A1, T1) := msort A T lo mid (Acc_inv H (ms_dec1 lo hi Hlt)) in
      let '(A2, T2) := msort A1 T1 mid hi (Acc_inv H (ms_dec2 lo hi Hlt)) in
      let T3 := merge A2 T2 lo mid hi in
      (loop hi (fun _ _ => true) (copy_step T3) lo A2, T3)
  | right _ => (A, T)
  end.
Elpi complexity msort.
Arguments msort_cost : simpl never.

Definition sort (K : array int) (n : int) : array int :=
  fst (msort K (PArray.make n 0) 0 n (Zwf_well_founded 0 (gap n 0))).
Elpi complexity sort.
Arguments sort_cost : simpl never.

(* -- Distinct points ------------------------------------------------- *)

Definition dedup_step (S : array int) (t : int) (st : array int * int) : array int * int :=
  let '(D, m) := st in
  if (m =? 0) || (D.[m - 1] <? S.[t]) then (D.[m <- S.[t]], m + 1) else (D, m).
Elpi complexity dedup_step.
Arguments dedup_step_cost : simpl never.

Definition decode_step (D : array int) (u : int) (st : array int * array int) : array int * array int :=
  let '(PX, PY) := st in let d := D.[u] in (PX.[u <- d / SH], PY.[u <- d mod SH]).
Elpi complexity decode_step.
Arguments decode_step_cost : simpl never.

(* -- One chain of Andrew's monotone chain ---------------------------- *)

Fixpoint popl (X Y ST : array int) (s r : int) (H : Acc (Zwf 0) (to_Z r)) {struct H} : int :=
  match bdec (1 <? r) with
  | left Hr =>
      let i1 := ST.[r - 2] in let i2 := ST.[r - 1] in
      if crs X.[i1] Y.[i1] X.[i2] Y.[i2] X.[s] Y.[s] <=? OFF
      then popl X Y ST s (r - 1) (Acc_inv H (dec_r r Hr))
      else r
  | right _ => r
  end.
Elpi complexity popl.
Arguments popl_cost : simpl never.

Definition pass_step (X Y : array int) (s : int) (st : array int * int) : array int * int :=
  let '(ST, r) := st in
  let r' := popl X Y ST s r (Zwf_well_founded 0 (to_Z r)) in
  (ST.[r' <- s], r' + 1).
Elpi complexity pass_step.
Arguments pass_step_cost : simpl never.

Definition pass (X Y : array int) (m : int) : array int * int :=
  loop m (fun _ _ => true) (pass_step X Y) 1 (PArray.make m 0, 1).
Elpi complexity pass.
Arguments pass_cost : simpl never.

Definition rev_step (X : array int) (m : int) (s : int) (R : array int) : array int :=
  R.[s <- X.[m - 1 - s]].
Elpi complexity rev_step.
Arguments rev_step_cost : simpl never.

Definition low_step (PX PY LS : array int) (t : int) (st : array int * array int) : array int * array int :=
  let '(HX, HY) := st in let v := LS.[t] in (HX.[t <- PX.[v]], HY.[t <- PY.[v]]).
Elpi complexity low_step.
Arguments low_step_cost : simpl never.

Definition up_step (RX RY US : array int) (a : int) (t : int) (st : array int * array int)
    : array int * array int :=
  let '(HX, HY) := st in let v := US.[t - a + 1] in (HX.[t <- RX.[v]], HY.[t <- RY.[v]]).
Elpi complexity up_step.
Arguments up_step_cost : simpl never.

(* -- The rotating sweep ---------------------------------------------- *)

(* the third corner k climbs while the area does not decrease *)
Fixpoint climb (HX HY : array int) (hm xi yi xj yj k gk : int)
    (H : Acc (Zwf 0) (gap hm k)) {struct H} : int :=
  match bdec (k <? hm) with
  | left Hk =>
      let k1 := k + 1 in
      let g1 := crs xi yi xj yj HX.[k1] HY.[k1] in
      if gk <=? g1 then climb HX HY hm xi yi xj yj k1 g1 (Acc_inv H (dec_step hm k Hk)) else k
  | right _ => k
  end.
Elpi complexity climb.
Arguments climb_cost : simpl never.

(* the second corner j = j, j+1, ..., hm - 1 ; the best area found so far *)
Fixpoint jloop (HX HY : array int) (hm xi yi j k best : int)
    (H : Acc (Zwf 0) (gap hm j)) {struct H} : int :=
  match bdec (j <? hm) with
  | left Hj =>
      let xj := HX.[j] in let yj := HY.[j] in
      let k1 := if j <? k then k else j + 1 in
      let k2 := climb HX HY hm xi yi xj yj k1 (crs xi yi xj yj HX.[k1] HY.[k1])
                  (Zwf_well_founded 0 (gap hm k1)) in
      let g := crs xi yi xj yj HX.[k2] HY.[k2] in
      jloop HX HY hm xi yi (j + 1) k2 (if best <? g then g else best) (Acc_inv H (dec_step hm j Hj))
  | right _ => best
  end.
Elpi complexity jloop.
Arguments jloop_cost : simpl never.

Definition sweep_step (HX HY : array int) (h : int) (i best : int) : int :=
  jloop HX HY (h - 1) HX.[i] HY.[i] (i + 1) (i + 2) best (Zwf_well_founded 0 (gap (h - 1) (i + 1))).
Elpi complexity sweep_step.
Arguments sweep_step_cost : simpl never.

Definition sweep (HX HY : array int) (h : int) : int :=
  loop (h - 2) (fun _ _ => true) (sweep_step HX HY h) 0 OFF.
Elpi complexity sweep.
Arguments sweep_cost : simpl never.

(* -- The whole ------------------------------------------------------- *)

Definition fzero : float := of_uint63 0.
Elpi complexity fzero.
Arguments fzero_cost : simpl never.

Definition largest_triangle_impl (x y : array uint) : float :=
  let n := PArray.length x in
  let K := loop n (fun _ _ => true) (fun i K => K.[i <- x.[i] * SH + y.[i]]) 0 (PArray.make n 0) in
  let S := sort K n in
  let '(D, m) := loop n (fun _ _ => true) (dedup_step S) 0 (PArray.make n 0, 0) in
  if m <? 3 then fzero else
  let '(PX, PY) := loop m (fun _ _ => true) (decode_step D) 0 (PArray.make m 0, PArray.make m 0) in
  let '(LS, a) := pass PX PY m in
  let RX := loop m (fun _ _ => true) (rev_step PX m) 0 (PArray.make m 0) in
  let RY := loop m (fun _ _ => true) (rev_step PY m) 0 (PArray.make m 0) in
  let '(US, b) := pass RX RY m in
  let h := a + b - 2 in
  if h <? 3 then fzero else
  let '(HX1, HY1) := loop a (fun _ _ => true) (low_step PX PY LS) 0 (PArray.make h 0, PArray.make h 0) in
  let '(HX, HY) := loop h (fun _ _ => true) (up_step RX RY US a) a (HX1, HY1) in
  let best := sweep HX HY h in
  (of_uint63 (best - OFF) / of_uint63 2)%float.
Elpi complexity largest_triangle_impl.
Arguments largest_triangle_impl_cost : simpl never.

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
  destruct (loop_inv P hi lo (fun _ _ => true) f s Hle Hp) as (j & _ & Pj & [E0 | [_ E0]]).
  - intros j t Hj Pt _. apply Hstep; auto.
  - apply to_Z_inj in E0. subst j. exact Pj.
  - discriminate.
Qed.

End LoopProof.

(* ------------------------------------------------------------------ *)
(* PArray plumbing at [array int]                                      *)
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

Lemma iget_make : forall (m i v : int), (PArray.make m v : array int).[i] = v.
Proof. intros. exact (get_make int v m i). Qed.

Lemma ilength_make_small : forall (n v : int), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v H. rewrite ilength_make.
  replace (n <=? max_length) with true; [reflexivity |].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

(* reading a cell after a write, by the index *)
Lemma iget_set : forall (t : array int) (i j v : int), (to_Z i < to_Z (PArray.length t))%Z ->
  t.[i <- v].[j] = if (to_Z j =? to_Z i)%Z then v else t.[j].
Proof.
  intros t i j v H. destruct (Z.eqb_spec (to_Z j) (to_Z i)) as [E | N].
  - apply to_Z_inj in E. subst j. apply iget_set_same. rewrite Uint63.ltb_spec. exact H.
  - apply iget_set_other. intros ->. contradiction.
Qed.

Lemma succ_small : forall j : int, (to_Z j < 4611686018427387904)%Z -> to_Z (j + 1) = (to_Z j + 1)%Z.
Proof. intros j H. pose proof (to_Z_bounded j). sia. Qed.

Lemma to_Z_of_Z_small : forall z, (0 <= z < 9223372036854775808)%Z -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small; exact Hz. Qed.

(* ------------------------------------------------------------------ *)
(* The cross product in 63 bits                                        *)
(* ------------------------------------------------------------------ *)

Definition C26 : Z := 67108864%Z.
Definition C60 : Z := 1152921504606846976%Z.

Definition ipt (a b : int) : Z * Z := (to_Z a, to_Z b).

Lemma prod_bound : forall a b c : Z, (- c <= a <= c -> - c <= b <= c -> - (c * c) <= a * b <= c * c)%Z.
Proof. intros a b c Ha Hb. nia. Qed.

Lemma crs_spec : forall ax ay bx by_ cx cy : int,
  (to_Z ax < C26)%Z -> (to_Z ay < C26)%Z -> (to_Z bx < C26)%Z -> (to_Z by_ < C26)%Z ->
  (to_Z cx < C26)%Z -> (to_Z cy < C26)%Z ->
  to_Z (crs ax ay bx by_ cx cy) = (cross (ipt ax ay) (ipt bx by_) (ipt cx cy) + C60)%Z.
Proof.
  intros ax ay bx by_ cx cy H1 H2 H3 H4 H5 H6. unfold crs, cross, ipt, C26, C60 in *; simpl.
  rewrite Uint63.add_spec, Uint63.sub_spec, !Uint63.mul_spec, !Uint63.sub_spec.
  rewrite <- !Zmult_mod. rewrite <- Zminus_mod. rewrite Zplus_mod_idemp_l.
  change (to_Z OFF) with 1152921504606846976%Z.
  pose proof (to_Z_bounded ax). pose proof (to_Z_bounded ay). pose proof (to_Z_bounded bx).
  pose proof (to_Z_bounded by_). pose proof (to_Z_bounded cx). pose proof (to_Z_bounded cy).
  pose proof (prod_bound (to_Z bx - to_Z ax) (to_Z cy - to_Z ay) 67108864 ltac:(lia) ltac:(lia)).
  pose proof (prod_bound (to_Z cx - to_Z ax) (to_Z by_ - to_Z ay) 67108864 ltac:(lia) ltac:(lia)).
  apply Z.mod_small. change wB with 9223372036854775808%Z. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The merge sort: sorted, and the same set of values                  *)
(* ------------------------------------------------------------------ *)

Definition In (A : array int) (lo hi : Z) (v : int) : Prop :=
  exists k : int, (lo <= to_Z k < hi)%Z /\ A.[k] = v.

Definition Sorted (A : array int) (lo hi : Z) : Prop :=
  forall k1 k2 : int, (lo <= to_Z k1)%Z -> (to_Z k1 <= to_Z k2)%Z -> (to_Z k2 < hi)%Z ->
  (to_Z A.[k1] <= to_Z A.[k2])%Z.

Lemma In_split : forall A lo mid hi v, (lo <= mid <= hi)%Z ->
  In A lo hi v <-> In A lo mid v \/ In A mid hi v.
Proof.
  intros A lo mid hi v H. unfold In. split.
  - intros (k & Hk & Ek). destruct (Z_lt_le_dec (to_Z k) mid); [left | right]; exists k; split; auto; lia.
  - intros [(k & Hk & Ek) | (k & Hk & Ek)]; exists k; split; auto; lia.
Qed.

Lemma In_frame : forall A A' lo hi v,
  (forall t : int, (lo <= to_Z t < hi)%Z -> A'.[t] = A.[t]) -> (In A' lo hi v <-> In A lo hi v).
Proof.
  intros A A' lo hi v H. unfold In. split; intros (k & Hk & Ek); exists k; split; auto;
    [rewrite <- H | rewrite H]; auto.
Qed.

Lemma Sorted_frame : forall A A' lo hi,
  (forall t : int, (lo <= to_Z t < hi)%Z -> A'.[t] = A.[t]) -> Sorted A lo hi -> Sorted A' lo hi.
Proof.
  intros A A' lo hi H S k1 k2 H1 H2 H3. rewrite !H by lia. apply S; lia.
Qed.

Lemma In_snoc : forall A lo (i : int) v, (lo <= to_Z i)%Z ->
  In A lo (to_Z i + 1) v <-> In A lo (to_Z i) v \/ A.[i] = v.
Proof.
  intros A lo i v H. unfold In. split.
  - intros (k & Hk & Ek). destruct (Z.eq_dec (to_Z k) (to_Z i)) as [E | N].
    + right. apply to_Z_inj in E. subst. reflexivity.
    + left. exists k. split; [lia | exact Ek].
  - intros [(k & Hk & Ek) | Ek]; [exists k | exists i]; split; auto; lia.
Qed.

Lemma In_set_snoc : forall T lo (k : int) w v, (lo <= to_Z k < to_Z (PArray.length T))%Z ->
  In T.[k <- w] lo (to_Z k + 1) v <-> In T lo (to_Z k) v \/ w = v.
Proof.
  intros T lo k w v H. rewrite In_snoc by lia. rewrite iget_set_same by (rewrite Uint63.ltb_spec; lia).
  rewrite (In_frame T); [tauto |].
  intros t Ht. apply iget_set_other. intros ->. lia.
Qed.

Section Merge.
Variables (A : array int) (lo mid hi : int) (N : int).
Hypothesis HA : PArray.length A = N.
Hypothesis Hb : (to_Z lo <= to_Z mid <= to_Z hi)%Z.
Hypothesis HN : (to_Z hi <= to_Z N)%Z.
Hypothesis S1 : Sorted A (to_Z lo) (to_Z mid).
Hypothesis S2 : Sorted A (to_Z mid) (to_Z hi).

Definition Mi (k : int) (st : array int * int * int) : Prop :=
  let '(T, i, j) := st in
  PArray.length T = N /\
  (to_Z lo <= to_Z i <= to_Z mid)%Z /\ (to_Z mid <= to_Z j <= to_Z hi)%Z /\
  (to_Z k - to_Z lo = (to_Z i - to_Z lo) + (to_Z j - to_Z mid))%Z /\
  Sorted T (to_Z lo) (to_Z k) /\
  (forall t : int, (to_Z lo <= to_Z t < to_Z k)%Z ->
     ((to_Z i < to_Z mid)%Z -> (to_Z T.[t] <= to_Z A.[i])%Z) /\
     ((to_Z j < to_Z hi)%Z -> (to_Z T.[t] <= to_Z A.[j])%Z)) /\
  (forall v, In T (to_Z lo) (to_Z k) v <-> In A (to_Z lo) (to_Z i) v \/ In A (to_Z mid) (to_Z j) v).

Lemma Mi_step : forall k st, (to_Z lo <= to_Z k < to_Z hi)%Z -> Mi k st ->
  Mi (k + 1) (merge_step A mid hi k st).
Proof.
  intros k [[T i] j] Hk (L & Hi & Hj & Hc & Hs & Hbd & Hin).
  pose proof (ilength_bound A). rewrite HA in *.
  assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
  unfold merge_step.
  destruct ((i <? mid) && ((hi <=? j) || (A.[i] <=? A.[j]))) eqn:C.
  - apply andb_prop in C as [C1 C2]. rewrite Uint63.ltb_spec in C1.
    assert (Ei : to_Z (i + 1) = (to_Z i + 1)%Z) by (apply succ_small; lia).
    assert (C3 : (to_Z j < to_Z hi)%Z -> (to_Z A.[i] <= to_Z A.[j])%Z).
    { intros Hjh. apply Bool.orb_prop in C2 as [C2 | C2]; rewrite Uint63.leb_spec in C2; lia. }
    unfold Mi. rewrite Ek, Ei. rewrite ilength_set.
    split; [exact L |]. split; [lia |]. split; [lia |]. split; [lia |].
    split; [| split].
    + intros k1 k2 H1 H2 H3. rewrite !iget_set by lia.
      destruct (Z.eqb_spec (to_Z k2) (to_Z k)), (Z.eqb_spec (to_Z k1) (to_Z k)).
      * lia.
      * apply (proj1 (Hbd k1 ltac:(lia))); lia.
      * lia.
      * apply Hs; lia.
    + intros t Ht. rewrite iget_set by lia.
      split.
      * intros Hi1. assert (Sa : (to_Z A.[i] <= to_Z A.[i + 1])%Z) by (apply S1; lia).
        destruct (Z.eqb_spec (to_Z t) (to_Z k)); [lia |].
        pose proof (proj1 (Hbd t ltac:(lia)) ltac:(lia)). lia.
      * intros Hj1. destruct (Z.eqb_spec (to_Z t) (to_Z k)); [apply C3; lia |].
        apply (proj2 (Hbd t ltac:(lia))). lia.
    + intros v. rewrite In_set_snoc by lia. rewrite In_snoc by lia. rewrite Hin. tauto.
  - assert (Hjh : (to_Z j < to_Z hi)%Z) by lia.
    assert (C4 : (to_Z i < to_Z mid)%Z -> (to_Z A.[j] < to_Z A.[i])%Z).
    { intros Him. assert (Ci : (i <? mid) = true) by (rewrite Uint63.ltb_spec; lia).
      rewrite Ci in C. simpl in C. apply Bool.orb_false_iff in C as [_ C].
      rewrite <- Bool.not_true_iff_false, Uint63.leb_spec in C. lia. }
    assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by (apply succ_small; lia).
    unfold Mi. rewrite Ek, Ej. rewrite ilength_set.
    split; [exact L |]. split; [lia |]. split; [lia |]. split; [lia |].
    split; [| split].
    + intros k1 k2 H1 H2 H3. rewrite !iget_set by lia.
      destruct (Z.eqb_spec (to_Z k2) (to_Z k)), (Z.eqb_spec (to_Z k1) (to_Z k)).
      * lia.
      * apply (proj2 (Hbd k1 ltac:(lia))); lia.
      * lia.
      * apply Hs; lia.
    + intros t Ht. rewrite iget_set by lia.
      split.
      * intros Hi1. destruct (Z.eqb_spec (to_Z t) (to_Z k)); [pose proof (C4 Hi1); lia |].
        apply (proj1 (Hbd t ltac:(lia))). exact Hi1.
      * intros Hj1. assert (Sa : (to_Z A.[j] <= to_Z A.[j + 1])%Z) by (apply S2; lia).
        destruct (Z.eqb_spec (to_Z t) (to_Z k)); [lia |].
        pose proof (proj2 (Hbd t ltac:(lia)) ltac:(lia)). lia.
    + intros v. rewrite In_set_snoc by lia. rewrite (In_snoc A (to_Z mid)) by lia. rewrite Hin. tauto.
Qed.

Lemma merge_spec : forall T, PArray.length T = N ->
  let T' := merge A T lo mid hi in
  PArray.length T' = N /\ Sorted T' (to_Z lo) (to_Z hi) /\
  (forall t : int, (to_Z t < to_Z lo \/ to_Z hi <= to_Z t)%Z -> T'.[t] = T.[t]) /\
  (forall v, In T' (to_Z lo) (to_Z hi) v <-> In A (to_Z lo) (to_Z hi) v).
Proof.
  intros T HT. cbv zeta. unfold merge.
  pose proof (for_inv (fun k st => Mi k st /\
       forall t : int, (to_Z t < to_Z lo \/ to_Z hi <= to_Z t)%Z -> (fst (fst st)).[t] = T.[t])
     hi lo (merge_step A mid hi) (T, lo, mid) ltac:(lia)) as G.
  destruct (loop hi (fun _ _ => true) (merge_step A mid hi) lo (T, lo, mid)) as [[T' i] j].
  destruct G as [(L & Hi & Hj & Hc & Hs & _ & Hin) Hfr].
  - split.
    + unfold Mi. split; [exact HT |]. split; [lia |]. split; [lia |]. split; [lia |].
      split; [intros k1 k2; lia |]. split; [intros t; lia |].
      intros v. unfold In. split; [intros (k & Hk & _); lia | intros [(k & Hk & _) | (k & Hk & _)]; lia].
    + intros t _. reflexivity.
  - intros k st Hk [M F]. split; [apply Mi_step; assumption |].
    intros t Ht. destruct st as [[T0 i0] j0]. unfold merge_step.
    destruct ((i0 <? mid) && ((hi <=? j0) || (A.[i0] <=? A.[j0]))); simpl;
      rewrite iget_set_other by (intros ->; lia); apply F; exact Ht.
  - simpl in Hfr. split; [exact L |]. split; [exact Hs |]. split; [exact Hfr |].
    intros v. rewrite Hin. rewrite (In_split A (to_Z lo) (to_Z mid) (to_Z hi)) by lia.
    replace (to_Z i) with (to_Z mid) by lia. replace (to_Z j) with (to_Z hi) by lia. tauto.
Qed.

End Merge.

Lemma copy_spec : forall (T A : array int) (lo hi : int), (to_Z lo <= to_Z hi)%Z ->
  (to_Z hi <= to_Z (PArray.length A))%Z ->
  let A' := loop hi (fun _ _ => true) (copy_step T) lo A in
  PArray.length A' = PArray.length A /\
  (forall t : int, (to_Z lo <= to_Z t < to_Z hi)%Z -> A'.[t] = T.[t]) /\
  (forall t : int, (to_Z t < to_Z lo \/ to_Z hi <= to_Z t)%Z -> A'.[t] = A.[t]).
Proof.
  intros T A lo hi H1 H2. cbv zeta.
  apply (for_inv (fun k A' => PArray.length A' = PArray.length A /\
     (forall t : int, (to_Z lo <= to_Z t < to_Z k)%Z -> A'.[t] = T.[t]) /\
     (forall t : int, (to_Z t < to_Z lo \/ to_Z k <= to_Z t)%Z -> A'.[t] = A.[t]))).
  - exact H1.
  - split; [reflexivity |]. split; [intros t; lia | intros t _; reflexivity].
  - intros k A' Hk (L & F1 & F2). unfold copy_step. pose proof (ilength_bound A).
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
    rewrite Ek. split; [rewrite ilength_set; exact L |]. split.
    + intros t Ht. rewrite iget_set by lia. destruct (Z.eqb_spec (to_Z t) (to_Z k)).
      * apply to_Z_inj in e. subst. reflexivity.
      * apply F1. lia.
    + intros t Ht. rewrite iget_set by lia. destruct (Z.eqb_spec (to_Z t) (to_Z k)); [lia |].
      apply F2. lia.
Qed.

Definition msort_P (A : array int) (lo hi : int) (p : array int * array int) : Prop :=
  let '(A', T') := p in
  PArray.length A' = PArray.length A /\ PArray.length T' = PArray.length A /\
  (forall t : int, (to_Z t < to_Z lo \/ to_Z hi <= to_Z t)%Z -> A'.[t] = A.[t]) /\
  Sorted A' (to_Z lo) (to_Z hi) /\
  (forall v, In A' (to_Z lo) (to_Z hi) v <-> In A (to_Z lo) (to_Z hi) v).

Lemma msort_eq : forall A T lo hi H, msort A T lo hi H =
  match bdec ((lo <? hi) && (1 <? hi - lo)) with
  | left Hlt =>
      let mid := lo + (hi - lo) / 2 in
      let '(A1, T1) := msort A T lo mid (Acc_inv H (ms_dec1 lo hi Hlt)) in
      let '(A2, T2) := msort A1 T1 mid hi (Acc_inv H (ms_dec2 lo hi Hlt)) in
      let T3 := merge A2 T2 lo mid hi in
      (loop hi (fun _ _ => true) (copy_step T3) lo A2, T3)
  | right _ => (A, T)
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma msort_spec : forall z A T lo hi H, gap hi lo = z ->
  PArray.length T = PArray.length A -> (to_Z lo <= to_Z hi <= to_Z (PArray.length A))%Z ->
  msort_P A lo hi (msort A T lo hi H).
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros A T lo hi H Hz HT Hb. rewrite msort_eq.
  pose proof (ilength_bound A) as BA.
  destruct (bdec ((lo <? hi) && (1 <? hi - lo))) as [Hlt | Hge].
  - cbv zeta.
    set (D1 := ms_dec1 lo hi Hlt). set (D2 := ms_dec2 lo hi Hlt).
    pose proof D1 as D1'. pose proof D2 as D2'.
    set (mid := lo + (hi - lo) / 2) in *.
    assert (Hm : (to_Z lo <= to_Z mid <= to_Z hi)%Z) by (unfold Zwf, gap in D1', D2'; lia).
    pose proof (IH (gap mid lo) ltac:(rewrite <- Hz; exact D1) A T lo mid (Acc_inv H D1) eq_refl HT ltac:(lia)) as R1.
    destruct (msort A T lo mid (Acc_inv H D1)) as [A1 T1].
    destruct R1 as (L1 & LT1 & F1 & So1 & In1).
    pose proof (IH (gap hi mid) ltac:(rewrite <- Hz; exact D2) A1 T1 mid hi (Acc_inv H D2) eq_refl
                  ltac:(congruence) ltac:(lia)) as R2.
    destruct (msort A1 T1 mid hi (Acc_inv H D2)) as [A2 T2].
    destruct R2 as (L2 & LT2 & F2 & So2 & In2).
    assert (So1' : Sorted A2 (to_Z lo) (to_Z mid)).
    { apply (Sorted_frame A1); [| exact So1]. intros t Ht. apply F2. lia. }
    destruct (merge_spec A2 lo mid hi (PArray.length A2) eq_refl Hm ltac:(rewrite L2, L1; lia) So1' So2 T2
                ltac:(congruence)) as (ML & MS & MF & MI).
    set (T3 := merge A2 T2 lo mid hi) in *.
    destruct (copy_spec T3 A2 lo hi ltac:(lia) ltac:(rewrite L2, L1; lia)) as (CL & C1 & C2).
    unfold msort_P.
    split; [rewrite CL, L2, L1; reflexivity |].
    split; [rewrite ML, L2, L1; reflexivity |].
    split; [| split].
    + intros t Ht. rewrite C2 by exact Ht. rewrite F2 by lia. apply F1. lia.
    + apply (Sorted_frame T3); [exact C1 | exact MS].
    + intros v. rewrite (In_frame T3) by exact C1. rewrite MI.
      rewrite !(In_split _ (to_Z lo) (to_Z mid) (to_Z hi)) by lia.
      rewrite (In_frame A1 A2 (to_Z lo) (to_Z mid)) by (intros t Ht; apply F2; lia).
      rewrite In2. rewrite In1.
      rewrite (In_frame A A1 (to_Z mid) (to_Z hi)) by (intros t Ht; apply F1; lia). tauto.
  - unfold msort_P. split; [reflexivity |]. split; [exact HT |]. split; [reflexivity |].
    split; [| tauto].
    intros k1 k2 H1 H2 H3.
    assert (E : to_Z k1 = to_Z k2).
    { destruct (Z.eq_dec (to_Z k1) (to_Z k2)) as [E | N]; [exact E | exfalso].
      apply Bool.andb_false_iff in Hge.
      destruct Hge as [G | G]; rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in G; [lia |].
      change (to_Z 1) with 1%Z in G. assert (to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia. lia. }
    apply to_Z_inj in E. subst. lia.
Qed.

Lemma sort_spec : forall K n, PArray.length K = n ->
  let S := sort K n in
  PArray.length S = n /\ Sorted S 0 (to_Z n) /\ (forall v, In S 0 (to_Z n) v <-> In K 0 (to_Z n) v).
Proof.
  intros K n HK. cbv zeta. unfold sort.
  pose proof (ilength_bound K).
  pose proof (msort_spec _ K (PArray.make n 0) 0 n (Zwf_well_founded 0 (gap n 0)) eq_refl) as R.
  destruct (msort K (PArray.make n 0) 0 n (Zwf_well_founded 0 (gap n 0))) as [S T].
  destruct R as (L & _ & _ & So & Hin).
  - rewrite ilength_make_small; [congruence | subst; lia].
  - change (to_Z 0) with 0%Z. subst. pose proof (to_Z_bounded (PArray.length K)). lia.
  - simpl. split; [congruence |]. split; [exact So | exact Hin].
Qed.

(* ------------------------------------------------------------------ *)
(* Decoding a key                                                      *)
(* ------------------------------------------------------------------ *)

Definition dec (d : Z) : Z * Z := (d / C26, d mod C26)%Z.

Lemma dec_key : forall X Y, (0 <= Y < C26)%Z -> dec (X * C26 + Y) = (X, Y).
Proof.
  intros X Y H. unfold dec, C26 in *. f_equal.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma dec_lt : forall d1 d2, (0 <= d1 < d2)%Z -> lexlt (dec d1) (dec d2).
Proof.
  intros d1 d2 H. unfold lexlt, lexpos, vsub, dec, C26; simpl.
  pose proof (Z.div_le_mono d1 d2 67108864 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod d1 67108864 ltac:(lia)). pose proof (Z.div_mod d2 67108864 ltac:(lia)).
  destruct (Z.eq_dec (d1 / 67108864) (d2 / 67108864)) as [E | N]; [right | left]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Distinct keys                                                       *)
(* ------------------------------------------------------------------ *)

Definition SInc (D : array int) (m : Z) : Prop :=
  forall u1 u2 : int, (to_Z u1 < to_Z u2 < m)%Z -> (to_Z D.[u1] < to_Z D.[u2])%Z.

Lemma dedup_spec : forall (S : array int) (n : int), PArray.length S = n ->
  Sorted S 0 (to_Z n) ->
  let '(D, m) := loop n (fun _ _ => true) (dedup_step S) 0 (PArray.make n 0, 0) in
  PArray.length D = n /\ (to_Z m <= to_Z n)%Z /\ SInc D (to_Z m) /\
  (forall v, In D 0 (to_Z m) v <-> In S 0 (to_Z n) v) /\ ((0 < to_Z n)%Z -> (0 < to_Z m)%Z).
Proof.
  intros S n HS So.
  pose proof (ilength_bound S) as BS.
  pose proof (for_inv (fun t (st : array int * int) => let '(D, m) := st in
     PArray.length D = n /\ (to_Z m <= to_Z t)%Z /\ SInc D (to_Z m) /\
     (forall v, In D 0 (to_Z m) v <-> In S 0 (to_Z t) v) /\
     ((0 < to_Z m)%Z -> forall t' : int, (to_Z t' < to_Z t)%Z -> (to_Z S.[t'] <= to_Z D.[m - 1])%Z) /\
     ((0 < to_Z t)%Z -> (0 < to_Z m)%Z))
     n 0 (dedup_step S) (PArray.make n 0, 0)) as G.
  destruct (loop n (fun _ _ => true) (dedup_step S) 0 (PArray.make n 0, 0)) as [D m].
  destruct G as (L & Hm & Hs & Hin & _ & Hp).
  - change (to_Z 0) with 0%Z. lia.
  - change (to_Z 0) with 0%Z. split; [apply ilength_make_small; subst; lia |].
    split; [lia |]. split; [intros u1 u2; lia |]. split; [| split; intros; lia].
    intros v. unfold In. split; intros (k & Hk & _); lia.
  - intros t [D0 m0] Ht (L0 & Hm0 & Hs0 & Hin0 & Hmax & Hpos).
    change (to_Z 0) with 0%Z in Ht.
    assert (Et : to_Z (t + 1) = (to_Z t + 1)%Z) by (apply succ_small; lia).
    unfold dedup_step.
    destruct ((m0 =? 0) || (D0.[m0 - 1] <? S.[t])) eqn:C.
    + assert (Em : to_Z (m0 + 1) = (to_Z m0 + 1)%Z) by (apply succ_small; lia).
      assert (Cg : (0 < to_Z m0)%Z -> (to_Z D0.[m0 - 1] < to_Z S.[t])%Z).
      { intros Hp0. apply Bool.orb_prop in C as [C | C].
        - rewrite Uint63.eqb_spec in C. subst. change (to_Z 0) with 0%Z in Hp0. lia.
        - rewrite Uint63.ltb_spec in C. exact C. }
      rewrite Et, Em. split; [rewrite ilength_set; exact L0 |]. split; [lia |]. split; [| split; [| split]].
      * intros u1 u2 Hu. rewrite !iget_set by lia.
        destruct (Z.eqb_spec (to_Z u2) (to_Z m0)), (Z.eqb_spec (to_Z u1) (to_Z m0)); try lia.
        -- assert (Em1 : to_Z (m0 - 1) = (to_Z m0 - 1)%Z) by sia.
           pose proof (Cg ltac:(lia)).
           destruct (Z.eq_dec (to_Z u1) (to_Z (m0 - 1))) as [E1 | N1].
           ++ apply to_Z_inj in E1. subst u1. lia.
           ++ pose proof (Hs0 u1 (m0 - 1) ltac:(lia)). lia.
        -- apply Hs0. lia.
      * intros v. rewrite In_set_snoc by lia. rewrite In_snoc by lia. rewrite Hin0. tauto.
      * intros _ t' Ht'. replace (m0 + 1 - 1) with m0 by (apply to_Z_inj; sia).
        rewrite iget_set_same by (rewrite Uint63.ltb_spec; lia). apply So; lia.
      * intros _. lia.
    + apply Bool.orb_false_iff in C as [C1 C2].
      rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in C1.
      rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in C2.
      assert (Hm1 : (0 < to_Z m0)%Z) by (destruct (Z.eq_dec (to_Z m0) 0) as [E | N];
        [exfalso; apply C1, to_Z_inj; exact E | pose proof (to_Z_bounded m0); lia]).
      assert (Em1 : to_Z (m0 - 1) = (to_Z m0 - 1)%Z) by sia.
      (* the top of D is in S before t, so S.[t] equals it *)
      assert (Etop : D0.[m0 - 1] = S.[t]).
      { assert (Hd : In D0 0 (to_Z m0) D0.[m0 - 1]) by (exists (m0 - 1); split; [lia | reflexivity]).
        apply Hin0 in Hd. destruct Hd as (k & Hk & Ek).
        pose proof (So k t ltac:(lia) ltac:(lia) ltac:(lia)). apply to_Z_inj. rewrite <- Ek. lia. }
      rewrite Et. split; [exact L0 |]. split; [lia |]. split; [exact Hs0 |]. split; [| split].
      * intros v. rewrite In_snoc by lia. rewrite <- Hin0. split; [tauto |].
        intros [H | H]; [exact H |]. exists (m0 - 1). split; [lia |]. congruence.
      * intros _ t' Ht'. destruct (Z.eq_dec (to_Z t') (to_Z t)) as [E | N].
        -- apply to_Z_inj in E. subst. lia.
        -- apply Hmax; lia.
      * intros _. exact Hm1.
  - change (to_Z 0) with 0%Z in *. split; [exact L |]. split; [exact Hm |]. split; [exact Hs |].
    split; [exact Hin | exact Hp].
Qed.

Lemma decode_spec : forall (D : array int) (m : int), (to_Z m <= 4194303)%Z ->
  let '(PX, PY) := loop m (fun _ _ => true) (decode_step D) 0 (PArray.make m 0, PArray.make m 0) in
  PArray.length PX = m /\ PArray.length PY = m /\
  forall u : int, (to_Z u < to_Z m)%Z -> ipt PX.[u] PY.[u] = dec (to_Z D.[u]).
Proof.
  intros D m Hm.
  pose proof (for_inv (fun t (st : array int * array int) => let '(PX, PY) := st in
     PArray.length PX = m /\ PArray.length PY = m /\
     forall u : int, (to_Z u < to_Z t)%Z -> ipt PX.[u] PY.[u] = dec (to_Z D.[u]))
     m 0 (decode_step D) (PArray.make m 0, PArray.make m 0)) as G.
  destruct (loop m (fun _ _ => true) (decode_step D) 0 (PArray.make m 0, PArray.make m 0)) as [PX PY].
  apply G.
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded m). lia.
  - split; [apply ilength_make_small; lia |]. split; [apply ilength_make_small; lia |].
    intros u Hu. change (to_Z 0) with 0%Z in Hu. pose proof (to_Z_bounded u). lia.
  - intros t [X Y] Ht (L1 & L2 & F). unfold decode_step.
    change (to_Z 0) with 0%Z in Ht.
    assert (Et : to_Z (t + 1) = (to_Z t + 1)%Z) by (apply succ_small; lia).
    split; [rewrite ilength_set; exact L1 |]. split; [rewrite ilength_set; exact L2 |].
    intros u Hu. rewrite Et in Hu. rewrite !iget_set by lia.
    destruct (Z.eqb_spec (to_Z u) (to_Z t)) as [E | N].
    + apply to_Z_inj in E. subst. unfold ipt, dec, C26. rewrite Uint63.div_spec, Uint63.mod_spec. reflexivity.
    + apply F. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* One pass of the monotone chain                                      *)
(* ------------------------------------------------------------------ *)

Lemma chain_ok_ext : forall Q s l l' r, (forall t, (0 <= t < r)%Z -> l t = l' t) ->
  chain_ok Q s l r -> chain_ok Q s l' r.
Proof.
  intros Q s l l' r Ee C. pose proof (ch_r _ _ _ _ C).
  constructor.
  - exact (ch_r _ _ _ _ C).
  - rewrite <- Ee by lia. exact (ch_0 _ _ _ _ C).
  - rewrite <- Ee by lia. exact (ch_top _ _ _ _ C).
  - intros t Ht. rewrite <- !Ee by lia. apply (ch_inc _ _ _ _ C). exact Ht.
  - intros t1 t2 Ht. unfold E. rewrite <- !Ee by lia. apply (ch_edge _ _ _ _ C). exact Ht.
  - intros u t Hu Ht. rewrite <- !Ee by lia. apply (ch_left _ _ _ _ C); assumption.
Qed.

Definition lst (ST : array int) (t : Z) : Z := to_Z ST.[of_Z t].

Lemma lst_int : forall ST i, lst ST (to_Z i) = to_Z ST.[i].
Proof. intros. unfold lst. rewrite of_to_Z. reflexivity. Qed.

Lemma popl_eq : forall X Y ST s r H, popl X Y ST s r H =
  match bdec (1 <? r) with
  | left Hr =>
      let i1 := ST.[r - 2] in let i2 := ST.[r - 1] in
      if crs X.[i1] Y.[i1] X.[i2] Y.[i2] X.[s] Y.[s] <=? OFF
      then popl X Y ST s (r - 1) (Acc_inv H (dec_r r Hr))
      else r
  | right _ => r
  end.
Proof. intros. destruct H; reflexivity. Qed.

Section Pass.
Variables (X Y : array int) (m : int) (Q : Z -> Z * Z).
Hypothesis Hm : (2 <= to_Z m <= 5000)%Z.
Hypothesis HQ : Qinc Q (to_Z m).
Hypothesis HX : forall a b c : int, (to_Z a < to_Z m)%Z -> (to_Z b < to_Z m)%Z -> (to_Z c < to_Z m)%Z ->
  to_Z (crs X.[a] Y.[a] X.[b] Y.[b] X.[c] Y.[c]) = (cross (Q (to_Z a)) (Q (to_Z b)) (Q (to_Z c)) + C60)%Z.

Lemma popl_spec : forall ST s r0, (1 <= to_Z s < to_Z m)%Z ->
  chain_ok Q (to_Z s) (lst ST) (to_Z r0) ->
  let r' := popl X Y ST s r0 (Zwf_well_founded 0 (to_Z r0)) in
  (1 <= to_Z r' <= to_Z r0)%Z /\
  ((to_Z r' < to_Z r0)%Z -> (cross (Q (lst ST (to_Z r' - 1))) (Q (lst ST (to_Z r'))) (Q (to_Z s)) <= 0)%Z) /\
  ((2 <= to_Z r')%Z -> (0 < cross (Q (lst ST (to_Z r' - 2))) (Q (lst ST (to_Z r' - 1))) (Q (to_Z s)))%Z).
Proof.
  intros ST s r0 Hs C. cbv zeta.
  pose proof (ch_range _ _ _ _ C) as Rg. pose proof (ch_r _ _ _ _ C) as R1.
  assert (Rs : (to_Z r0 <= to_Z s)%Z).
  { pose proof (ch_0 _ _ _ _ C). pose proof (ch_top _ _ _ _ C).
    destruct (Z.eq_dec (to_Z r0) 1) as [E1 | N1]; [lia |].
    assert (G : forall t, (0 <= t < to_Z r0)%Z -> (t <= lst ST t)%Z).
    { intros t Ht. assert (Gn : forall k : nat, (Z.of_nat k < to_Z r0)%Z -> (Z.of_nat k <= lst ST (Z.of_nat k))%Z).
      { induction k as [| k IH]; intros Hk; [simpl; lia |].
        pose proof (IH ltac:(lia)). pose proof (ch_inc _ _ _ _ C (Z.of_nat k) ltac:(lia)).
        replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia. lia. }
      replace t with (Z.of_nat (Z.to_nat t)) by lia. apply Gn. lia. }
    pose proof (G (to_Z r0 - 1)%Z ltac:(lia)). lia. }
  assert (Gen : forall z (r : int) (H : Acc (Zwf 0) (to_Z r)), to_Z r = z ->
     (1 <= to_Z r <= to_Z r0)%Z ->
     ((to_Z r < to_Z r0)%Z -> (cross (Q (lst ST (to_Z r - 1))) (Q (lst ST (to_Z r))) (Q (to_Z s)) <= 0)%Z) ->
     let r' := popl X Y ST s r H in
     (1 <= to_Z r' <= to_Z r0)%Z /\
     ((to_Z r' < to_Z r0)%Z -> (cross (Q (lst ST (to_Z r' - 1))) (Q (lst ST (to_Z r'))) (Q (to_Z s)) <= 0)%Z) /\
     ((2 <= to_Z r')%Z -> (0 < cross (Q (lst ST (to_Z r' - 2))) (Q (lst ST (to_Z r' - 1))) (Q (to_Z s)))%Z)).
  { intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros r H Ez Hr Pa. cbv zeta. rewrite popl_eq.
    destruct (bdec (1 <? r)) as [Hr1 | Hr1].
    - pose proof Hr1 as Hr1'. rewrite Uint63.ltb_spec in Hr1'. change (to_Z 1) with 1%Z in Hr1'.
      cbv zeta.
      assert (E2 : to_Z (r - 2) = (to_Z r - 2)%Z) by sia.
      assert (E1 : to_Z (r - 1) = (to_Z r - 1)%Z) by sia.
      pose proof (Rg (to_Z r - 2)%Z ltac:(lia)) as B2. pose proof (Rg (to_Z r - 1)%Z ltac:(lia)) as B1.
      rewrite <- E2, lst_int in B2. rewrite <- E1, lst_int in B1.
      destruct (Z.leb_spec (cross (Q (lst ST (to_Z r - 2))) (Q (lst ST (to_Z r - 1))) (Q (to_Z s)) + C60)
                  (to_Z OFF)) as [L | L].
      + replace (_ <=? OFF) with true by (symmetry; rewrite Uint63.leb_spec; rewrite HX by lia;
                                         rewrite <- !lst_int, E1, E2; exact L).
        apply (IH (to_Z (r - 1))).
        * rewrite <- Ez. apply dec_r. exact Hr1.
        * reflexivity.
        * lia.
        * intros _. rewrite E1. replace (to_Z r - 1 - 1)%Z with (to_Z r - 2)%Z by lia.
          replace (to_Z r - 1 + 1)%Z with (to_Z r) by lia. change (to_Z OFF) with C60 in L. lia.
      + replace (_ <=? OFF) with false by (symmetry; rewrite <- Bool.not_true_iff_false, Uint63.leb_spec;
                                          rewrite HX by lia; rewrite <- !lst_int, E1, E2; lia).
        split; [lia |]. split; [exact Pa |]. intros _. change (to_Z OFF) with C60 in L. lia.
    - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hr1. change (to_Z 1) with 1%Z in Hr1.
      split; [lia |]. split; [exact Pa | lia]. }
  apply (Gen _ r0 _ eq_refl); lia.
Qed.

Lemma pass_spec :
  let '(ST, r) := pass X Y m in
  chain_ok Q (to_Z m) (lst ST) (to_Z r) /\ PArray.length ST = m /\ (to_Z r <= to_Z m)%Z.
Proof.
  unfold pass.
  pose proof (for_inv (fun s (st : array int * int) => let '(ST, r) := st in
     chain_ok Q (to_Z s) (lst ST) (to_Z r) /\ PArray.length ST = m /\ (to_Z r <= to_Z s)%Z)
     m 1 (pass_step X Y) (PArray.make m 0, 1)) as G.
  destruct (loop m (fun _ _ => true) (pass_step X Y) 1 (PArray.make m 0, 1)) as [ST r].
  apply G.
  - change (to_Z 1) with 1%Z. lia.
  - change (to_Z 1) with 1%Z. split; [| split; [apply ilength_make_small; lia | lia]].
    constructor; try (intros; lia).
    + unfold lst. rewrite iget_make. reflexivity.
    + unfold lst. rewrite iget_make. reflexivity.
  - intros s [ST0 r0] Hs (C & L & Hr). change (to_Z 1) with 1%Z in Hs.
    unfold pass_step.
    destruct (popl_spec ST0 s r0 ltac:(lia) C) as (P1 & Pa & Pb).
    set (r' := popl X Y ST0 s r0 (Zwf_well_founded 0 (to_Z r0))) in *.
    assert (Es : to_Z (s + 1) = (to_Z s + 1)%Z) by (apply succ_small; lia).
    assert (Er : to_Z (r' + 1) = (to_Z r' + 1)%Z) by (apply succ_small; lia).
    rewrite Es, Er. split; [| split; [rewrite ilength_set; exact L | lia]].
    apply (chain_ok_ext Q _ (upd (lst ST0) (to_Z r') (to_Z s))).
    + intros t Ht. unfold upd, lst. rewrite iget_set by lia.
      rewrite to_Z_of_Z_small by lia.
      destruct (Z.eq_dec t (to_Z r')), (Z.eqb_spec t (to_Z r')); try lia; reflexivity.
    + apply (chain_push Q (to_Z s) (lst ST0) (to_Z r0) (to_Z r')).
      * intros a b Hab. apply HQ. lia.
      * lia.
      * exact C.
      * exact P1.
      * exact Pa.
      * exact Pb.
Qed.

End Pass.

(* ------------------------------------------------------------------ *)
(* The sweep, on the math side                                         *)
(* ------------------------------------------------------------------ *)

Section SweepMath.
Local Open Scope Z_scope.
Variable p : Z -> Z * Z.
Variable h : Z.
Hypothesis Hc : forall i j k, 0 <= i -> i < j -> j < k -> k < h -> 0 < cross (p i) (p j) (p k).
Variable ii : Z.
Hypothesis Hii : 0 <= ii.

Definition G (j t : Z) : Z := cross (p ii) (p j) (p t).

Definition Mono (j lo hi : Z) : Prop := forall t, lo <= t -> t < hi -> G j t <= G j (t + 1).

Lemma mono_peak_le : forall j lo k, Mono j lo k -> forall t, lo <= t <= k -> G j t <= G j k.
Proof.
  intros j lo k M t Ht.
  assert (Gn : forall n : nat, k - Z.of_nat n >= lo -> G j (k - Z.of_nat n) <= G j k).
  { induction n as [| n IH]; intros Hn; [replace (k - Z.of_nat 0) with k by lia; lia |].
    pose proof (IH ltac:(lia)).
    pose proof (M (k - Z.of_nat (S n)) ltac:(lia) ltac:(lia)).
    replace (k - Z.of_nat (S n) + 1) with (k - Z.of_nat n) in * by lia. lia. }
  replace t with (k - Z.of_nat (Z.to_nat (k - t))) by lia. apply Gn. lia.
Qed.

Lemma peak : forall j k, ii < j -> j < k -> k <= h - 1 -> Mono j (j + 1) k ->
  (k = h - 1 \/ G j (k + 1) < G j k) ->
  forall t, j < t < h -> G j t <= G j k.
Proof.
  intros j k Hij Hjk Hk M Hend t Ht.
  destruct (Z_le_gt_dec t k) as [L | L].
  - apply (mono_peak_le j (j + 1) k M). lia.
  - destruct Hend as [Hend | Hend]; [lia |].
    assert (Gn : forall n : nat, k + 1 + Z.of_nat n < h ->
              G j (k + 1 + Z.of_nat n) < G j (k + Z.of_nat n) /\ G j (k + 1 + Z.of_nat n) < G j k).
    { induction n as [| n IH]; intros Hn.
      - replace (k + 1 + Z.of_nat 0) with (k + 1) by lia. replace (k + Z.of_nat 0) with k by lia. lia.
      - destruct (IH ltac:(lia)) as [I1 I2].
        assert (Sx : G j (k + 1 + Z.of_nat (S n)) < G j (k + 1 + Z.of_nat n)).
        { unfold G. replace (k + 1 + Z.of_nat (S n)) with (k + 1 + Z.of_nat n + 1) by lia.
          apply (unimodal_step (p ii) (p j) (p (k + Z.of_nat n)) (p (k + 1 + Z.of_nat n))).
          - apply Hc; lia.
          - apply Hc; lia.
          - apply Hc; lia.
          - apply Hc; lia.
          - apply Hc; lia.
          - unfold G in I1. lia. }
        replace (k + Z.of_nat (S n)) with (k + 1 + Z.of_nat n) by lia. lia. }
    replace t with (k + 1 + Z.of_nat (Z.to_nat (t - k - 1))) by lia.
    pose proof (Gn (Z.to_nat (t - k - 1)) ltac:(lia)). lia.
Qed.

Lemma mono_shift : forall j k, ii < j -> k <= h - 1 -> Mono j (j + 1) k -> Mono (j + 1) (j + 2) k.
Proof.
  intros j k Hij Hk M t H1 H2. unfold G.
  apply Z.lt_le_incl, (shift_step (p ii) (p j) (p (j + 1)) (p t) (p (t + 1))).
  - apply Hc; lia.
  - apply Hc; lia.
  - apply Hc; lia.
  - apply Hc; lia.
  - apply (M t); lia.
Qed.

End SweepMath.

(* ------------------------------------------------------------------ *)
(* The sweep, on the code                                              *)
(* ------------------------------------------------------------------ *)

Lemma climb_eq : forall HX HY hm xi yi xj yj k gk H, climb HX HY hm xi yi xj yj k gk H =
  match bdec (k <? hm) with
  | left Hk =>
      let k1 := k + 1 in
      let g1 := crs xi yi xj yj HX.[k1] HY.[k1] in
      if gk <=? g1 then climb HX HY hm xi yi xj yj k1 g1 (Acc_inv H (dec_step hm k Hk)) else k
  | right _ => k
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma jloop_eq : forall HX HY hm xi yi j k best H, jloop HX HY hm xi yi j k best H =
  match bdec (j <? hm) with
  | left Hj =>
      let xj := HX.[j] in let yj := HY.[j] in
      let k1 := if j <? k then k else j + 1 in
      let k2 := climb HX HY hm xi yi xj yj k1 (crs xi yi xj yj HX.[k1] HY.[k1])
                  (Zwf_well_founded 0 (gap hm k1)) in
      let g := crs xi yi xj yj HX.[k2] HY.[k2] in
      jloop HX HY hm xi yi (j + 1) k2 (if best <? g then g else best) (Acc_inv H (dec_step hm j Hj))
  | right _ => best
  end.
Proof. intros. destruct H; reflexivity. Qed.

Section SweepCode.
Variables (HX HY : array int) (h : int).
Hypothesis Hh : (3 <= to_Z h <= 10000)%Z.
Hypothesis Hco : forall t : int, (to_Z t < to_Z h)%Z -> (to_Z HX.[t] < C26)%Z /\ (to_Z HY.[t] < C26)%Z.

Definition Pz (z : Z) : Z * Z := ipt HX.[of_Z z] HY.[of_Z z].

Hypothesis Hcv : forall a b c, (0 <= a)%Z -> (a < b)%Z -> (b < c)%Z -> (c < to_Z h)%Z ->
  (0 < cross (Pz a) (Pz b) (Pz c))%Z.

Lemma Pz_int : forall t : int, Pz (to_Z t) = ipt HX.[t] HY.[t].
Proof. intros t. unfold Pz. rewrite of_to_Z. reflexivity. Qed.

Lemma crs_at : forall i j k : int, (to_Z i < to_Z h)%Z -> (to_Z j < to_Z h)%Z -> (to_Z k < to_Z h)%Z ->
  to_Z (crs HX.[i] HY.[i] HX.[j] HY.[j] HX.[k] HY.[k]) =
  (cross (Pz (to_Z i)) (Pz (to_Z j)) (Pz (to_Z k)) + C60)%Z.
Proof.
  intros i j k Hi Hj Hk. rewrite !Pz_int.
  destruct (Hco i Hi), (Hco j Hj), (Hco k Hk). apply crs_spec; assumption.
Qed.

Definition hm : int := h - 1.

Lemma hm_val : to_Z hm = (to_Z h - 1)%Z.
Proof. unfold hm. sia. Qed.

Definition Bok (best : int) : Prop :=
  exists Bv, to_Z best = (Bv + C60)%Z /\ (0 <= Bv)%Z /\
    (Bv = 0%Z \/ exists a b c, (0 <= a)%Z /\ (a < b)%Z /\ (b < c)%Z /\ (c < to_Z h)%Z /\
                              Bv = cross (Pz a) (Pz b) (Pz c)).

Section Fixed_i.
Variable i : int.
Hypothesis Hi : (to_Z i < to_Z h - 2)%Z.

Notation GG := (G Pz (to_Z i)).

Lemma climb_spec : forall (j : int), (to_Z i < to_Z j)%Z ->
  forall z k gk H, gap hm k = z -> (to_Z j < to_Z k <= to_Z hm)%Z ->
  to_Z gk = (GG (to_Z j) (to_Z k) + C60)%Z ->
  Mono Pz (to_Z i) (to_Z j) (to_Z j + 1) (to_Z k) ->
  let k2 := climb HX HY hm HX.[i] HY.[i] HX.[j] HY.[j] k gk H in
  (to_Z k <= to_Z k2 <= to_Z hm)%Z /\ Mono Pz (to_Z i) (to_Z j) (to_Z j + 1) (to_Z k2) /\
  (to_Z k2 = to_Z hm \/ (GG (to_Z j) (to_Z k2 + 1) < GG (to_Z j) (to_Z k2))%Z).
Proof.
  intros j Hij z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros k gk H Hz Hk Hg M. cbv zeta. rewrite climb_eq. pose proof hm_val.
  destruct (bdec (k <? hm)) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'. cbv zeta.
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
    assert (Hg1 : to_Z (crs HX.[i] HY.[i] HX.[j] HY.[j] HX.[k + 1] HY.[k + 1]) =
                  (GG (to_Z j) (to_Z (k + 1)) + C60)%Z).
    { rewrite crs_at by lia. reflexivity. }
    destruct (Z.leb_spec (to_Z gk) (to_Z (crs HX.[i] HY.[i] HX.[j] HY.[j] HX.[k + 1] HY.[k + 1]))) as [L | L].
    + replace (gk <=? _) with true by (symmetry; rewrite Uint63.leb_spec; exact L).
      assert (M' : Mono Pz (to_Z i) (to_Z j) (to_Z j + 1) (to_Z (k + 1))).
      { intros t H1 H2. rewrite Ek in H2. destruct (Z.eq_dec t (to_Z k)) as [-> | N].
        - rewrite Hg, Hg1, Ek in L. lia.
        - apply M; lia. }
      assert (Hk' : (to_Z j < to_Z (k + 1) <= to_Z hm)%Z) by lia.
      assert (Dz : Zwf 0 (gap hm (k + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hlt).
      pose proof (IH (gap hm (k + 1)) Dz (k + 1) (crs HX.[i] HY.[i] HX.[j] HY.[j] HX.[k + 1] HY.[k + 1]) (Acc_inv H (dec_step hm k Hlt)) eq_refl Hk' Hg1 M') as R.
      cbv zeta in R. destruct R as (R1 & R2 & R3).
      split; [lia |]. split; [exact R2 | exact R3].
    + replace (gk <=? _) with false by (symmetry; rewrite <- Bool.not_true_iff_false, Uint63.leb_spec; lia).
      split; [lia |]. split; [exact M |]. right. rewrite Hg, Hg1, Ek in L. lia.
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hge.
    split; [lia |]. split; [exact M | left; lia].
Qed.

Lemma jloop_spec : forall z j k best H, gap hm j = z ->
  (to_Z i < to_Z j <= to_Z hm)%Z -> (to_Z j <= to_Z k <= to_Z hm)%Z ->
  Mono Pz (to_Z i) (to_Z j) (to_Z j + 1) (to_Z k) -> Bok best ->
  let r := jloop HX HY hm HX.[i] HY.[i] j k best H in
  Bok r /\ (to_Z best <= to_Z r)%Z /\
  forall b c, (to_Z j <= b < to_Z hm)%Z -> (b < c < to_Z h)%Z -> (GG b c + C60 <= to_Z r)%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros j k best H Hz Hj Hk M B. cbv zeta. rewrite jloop_eq. pose proof hm_val.
  destruct (bdec (j <? hm)) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'. cbv zeta.
    assert (Ej : to_Z (j + 1) = (to_Z j + 1)%Z) by (apply succ_small; lia).
    set (k1 := if j <? k then k else j + 1).
    assert (Hk1 : (to_Z j < to_Z k1 <= to_Z hm)%Z /\ Mono Pz (to_Z i) (to_Z j) (to_Z j + 1) (to_Z k1)).
    { unfold k1. destruct (Uint63.ltb_spec j k) as [_ ?]. destruct (j <? k) eqn:Cjk.
      - rewrite Uint63.ltb_spec in Cjk. split; [lia | exact M].
      - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Cjk. rewrite Ej. split; [lia |].
        intros t T1 T2. lia. }
    destruct Hk1 as [Hk1 M1].
    destruct (climb_spec j (proj1 Hj) _ k1 (crs HX.[i] HY.[i] HX.[j] HY.[j] HX.[k1] HY.[k1]) (Zwf_well_founded 0 (gap hm k1)) eq_refl Hk1
                ltac:(rewrite crs_at by lia; reflexivity) M1) as (C1 & C2 & C3).
    set (k2 := climb HX HY hm HX.[i] HY.[i] HX.[j] HY.[j] k1 _ _) in *.
    assert (Pk : forall t, (to_Z j < t < to_Z h)%Z -> (GG (to_Z j) t <= GG (to_Z j) (to_Z k2))%Z).
    { intros t Ht. rewrite H0 in C3.
      apply (peak Pz (to_Z h) Hcv (to_Z i)); [pose proof (to_Z_bounded i); lia | lia | lia | lia | exact C2 | exact C3 | lia]. }
    assert (Hg : to_Z (crs HX.[i] HY.[i] HX.[j] HY.[j] HX.[k2] HY.[k2]) = (GG (to_Z j) (to_Z k2) + C60)%Z)
      by (rewrite crs_at by lia; reflexivity).
    set (g := crs HX.[i] HY.[i] HX.[j] HY.[j] HX.[k2] HY.[k2]) in *.
    set (best' := if best <? g then g else best).
    assert (B' : Bok best' /\ (to_Z best <= to_Z best')%Z /\ (to_Z g <= to_Z best')%Z).
    { unfold best'. destruct (best <? g) eqn:Cb.
      - rewrite Uint63.ltb_spec in Cb. split; [| lia].
        exists (GG (to_Z j) (to_Z k2)). split; [exact Hg |].
        assert (Pos : (0 < GG (to_Z j) (to_Z k2))%Z) by (apply Hcv; lia).
        split; [lia |]. right. exists (to_Z i), (to_Z j), (to_Z k2).
        split; [pose proof (to_Z_bounded i); lia |]. split; [lia |]. split; [lia |]. split; [lia | reflexivity].
      - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Cb. split; [exact B | lia]. }
    destruct B' as (B1 & B2 & B3).
    destruct (IH (gap hm (j + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hlt) (j + 1) k2 best'
                (Acc_inv H (dec_step hm j Hlt)) eq_refl ltac:(lia) ltac:(lia)
                ltac:(rewrite Ej; replace (to_Z j + 1 + 1)%Z with (to_Z j + 2)%Z by lia;
                      apply (mono_shift Pz (to_Z h) Hcv); [pose proof (to_Z_bounded i); lia | lia | lia | exact C2])
                B1) as (R1 & R2 & R3).
    split; [exact R1 |]. split; [lia |].
    intros b c Hb Hc. destruct (Z.eq_dec b (to_Z j)) as [-> | N].
    + pose proof (Pk c ltac:(lia)). lia.
    + apply R3; lia.
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Hge.
    split; [exact B |]. split; [lia |]. intros b c Hb. lia.
Qed.

End Fixed_i.

Lemma sweep_spec : let best := sweep HX HY h in
  Bok best /\ forall a b c, (0 <= a)%Z -> (a < b)%Z -> (b < c)%Z -> (c < to_Z h)%Z ->
    (cross (Pz a) (Pz b) (Pz c) + C60 <= to_Z best)%Z.
Proof.
  cbv zeta. unfold sweep.
  assert (Eh2 : to_Z (h - 2) = (to_Z h - 2)%Z) by sia.
  pose proof (for_inv (fun i best => Bok best /\ forall a b c, (0 <= a)%Z -> (a < to_Z i)%Z -> (a < b)%Z ->
       (b < c)%Z -> (c < to_Z h)%Z -> (cross (Pz a) (Pz b) (Pz c) + C60 <= to_Z best)%Z)
     (h - 2) 0 (sweep_step HX HY h) OFF) as G.
  destruct G as [B F].
  - change (to_Z 0) with 0%Z. lia.
  - split.
    + exists 0%Z. split; [reflexivity |]. split; [lia | left; reflexivity].
    + intros a b c Ha Ha'. change (to_Z 0) with 0%Z in Ha'. lia.
  - intros i best Hi [B F]. change (to_Z 0) with 0%Z in Hi. unfold sweep_step.
    pose proof hm_val.
    assert (Ei1 : to_Z (i + 1) = (to_Z i + 1)%Z) by (apply succ_small; lia).
    assert (Ei2 : to_Z (i + 2) = (to_Z i + 2)%Z) by sia.
    assert (Ei : to_Z (i + 1) = (to_Z i + 1)%Z) by (apply succ_small; lia).
    destruct (jloop_spec i ltac:(lia) _ (i + 1) (i + 2) best (Zwf_well_founded 0 (gap (h - 1) (i + 1)))
                eq_refl ltac:(lia) ltac:(lia) ltac:(intros t H1 H2; lia) B) as (R1 & R2 & R3).
    unfold hm in *.
    split; [exact R1 |].
    intros a b c Ha Hai Hab Hbc Hc. rewrite Ei in Hai.
    destruct (Z.eq_dec a (to_Z i)) as [-> | N].
    + pose proof (R3 b c ltac:(lia) ltac:(lia)) as R. unfold G in R. exact R.
    + pose proof (F a b c Ha ltac:(lia) Hab Hbc Hc). lia.
  - split; [exact B |]. intros a b c Ha Hab Hbc Hc. apply F; lia.
Qed.

End SweepCode.

(* ------------------------------------------------------------------ *)
(* From the hull triples to all triples                                *)
(* ------------------------------------------------------------------ *)

Section Reduce.
Local Open Scope Z_scope.

Lemma abs_sorted : forall (p : Z -> Z * Z) (h M : Z), 3 <= h ->
  (forall i j k, 0 <= i -> i < j -> j < k -> k < h -> 0 < cross (p i) (p j) (p k)) ->
  (forall i j k, 0 <= i -> i < j -> j < k -> k < h -> cross (p i) (p j) (p k) <= M) ->
  forall t1 t2 t3, 0 <= t1 < h -> 0 <= t2 < h -> 0 <= t3 < h ->
  Z.abs (cross (p t1) (p t2) (p t3)) <= M /\ 0 <= M.
Proof.
  intros p h M Hh Hc Hm t1 t2 t3 H1 H2 H3.
  assert (M0 : 0 <= M) by (pose proof (Hc 0 1 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
    pose proof (Hm 0 1 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); lia).
  split; [| exact M0].
  assert (P1 : forall a b c, cross a b c = - cross a c b) by (intros; unfold cross; ring).
  assert (P2 : forall a b c, cross a b c = - cross b a c) by (intros; unfold cross; ring).
  assert (P3 : forall a b c, cross a b c = cross b c a) by (intros; unfold cross; ring).
  assert (P4 : forall a b c, cross a b c = cross c a b) by (intros; unfold cross; ring).
  assert (P5 : forall a b c, cross a b c = - cross c b a) by (intros; unfold cross; ring).
  destruct (Z.lt_total t1 t2) as [L12 | [E12 | G12]];
  [| subst t2; rewrite cross_aa; lia |];
  (destruct (Z.lt_total t2 t3) as [L23 | [E23 | G23]];
   [| subst t3; rewrite cross_bb; lia |]);
  (destruct (Z.lt_total t1 t3) as [L13 | [E13 | G13]];
   [| subst t3; rewrite cross_aba; lia |]); try lia.
  - pose proof (Hc t1 t2 t3 ltac:(lia) L12 L23 ltac:(lia)). pose proof (Hm t1 t2 t3 ltac:(lia) L12 L23 ltac:(lia)). lia.
  - rewrite P1. pose proof (Hc t1 t3 t2 ltac:(lia) L13 G23 ltac:(lia)). pose proof (Hm t1 t3 t2 ltac:(lia) L13 G23 ltac:(lia)). lia.
  - rewrite P4. pose proof (Hc t3 t1 t2 ltac:(lia) G13 L12 ltac:(lia)). pose proof (Hm t3 t1 t2 ltac:(lia) G13 L12 ltac:(lia)). lia.
  - rewrite P2. pose proof (Hc t2 t1 t3 ltac:(lia) G12 L13 ltac:(lia)). pose proof (Hm t2 t1 t3 ltac:(lia) G12 L13 ltac:(lia)). lia.
  - rewrite P3. pose proof (Hc t2 t3 t1 ltac:(lia) L23 G13 ltac:(lia)). pose proof (Hm t2 t3 t1 ltac:(lia) L23 G13 ltac:(lia)). lia.
  - rewrite P5. pose proof (Hc t3 t2 t1 ltac:(lia) G23 G12 ltac:(lia)). pose proof (Hm t3 t2 t1 ltac:(lia) G23 G12 ltac:(lia)). lia.
Qed.

Variables (q : Z -> Z * Z) (m : Z).
Hypothesis Hq : Qinc q m.
Hypothesis Hm : 2 <= m.
Variables (lw uw : Z -> Z) (a b : Z).
Hypothesis Hlw : chain_ok q m lw a.
Hypothesis Huw : chain_ok (Qu q m) m uw b.

Lemma hull_bound : forall M, 3 <= hh a b ->
  (forall i j k, 0 <= i -> i < j -> j < k -> k < hh a b ->
     cross (Hp q m lw uw a i) (Hp q m lw uw a j) (Hp q m lw uw a k) <= M) ->
  forall u1 u2 u3, 0 <= u1 < m -> 0 <= u2 < m -> 0 <= u3 < m ->
  Z.abs (cross (q u1) (q u2) (q u3)) <= M.
Proof.
  intros M Hh HM u1 u2 u3 H1 H2 H3.
  set (P := Hp q m lw uw a).
  assert (Cv : forall i j k, 0 <= i -> i < j -> j < k -> k < hh a b -> 0 < cross (P i) (P j) (P k))
    by (intros; apply (Hp_convex q m Hq lw uw a b Hlw Huw); assumption).
  assert (Fan : forall u B C, 0 <= u < m -> exists t, 0 <= t < hh a b /\
                  Z.abs (cross (q u) B C) <= Z.abs (cross (P t) B C)).
  { intros u B C Hu. apply (fan_max P (hh a b) Hh Cv).
    - intros t Ht. apply (Hp_left q m lw uw a b Hlw Huw); lia.
    - apply (Hp_left_close q m Hm lw uw a b Hlw Huw). exact Hu. }
  destruct (Fan u1 (q u2) (q u3) H1) as (t1 & T1 & F1).
  rewrite (cross_cyc (P t1)) in F1.
  destruct (Fan u2 (q u3) (P t1) H2) as (t2 & T2 & F2).
  rewrite (cross_cyc (P t2)) in F2.
  destruct (Fan u3 (P t1) (P t2) H3) as (t3 & T3 & F3).
  destruct (abs_sorted P (hh a b) M Hh Cv HM t3 t1 t2 T3 T1 T2) as [B _].
  lia.
Qed.

Lemma hull_collinear : hh a b = 2 ->
  forall u1 u2 u3, 0 <= u1 < m -> 0 <= u2 < m -> 0 <= u3 < m -> cross (q u1) (q u2) (q u3) = 0.
Proof.
  intros Hh u1 u2 u3 H1 H2 H3.
  pose proof (a_ge2 q m Hm lw a Hlw). pose proof (b_ge2 q m Hm uw b Huw). unfold hh in Hh.
  set (P := Hp q m lw uw a).
  assert (Z0 : forall u, 0 <= u < m -> cross (P 0) (P 1) (q u) = 0).
  { intros u Hu. pose proof (Hp_left q m lw uw a b Hlw Huw u 0 Hu ltac:(unfold hh; lia)) as L1.
    pose proof (Hp_left_close q m Hm lw uw a b Hlw Huw u Hu) as L2.
    unfold hh in L2. replace (a + b - 2 - 1) with 1 in L2 by lia. simpl in L1. fold P in L1, L2.
    assert (E2 : cross (P 1) (P 0) (q u) = - cross (P 0) (P 1) (q u)) by (unfold cross; ring).
    lia. }
  assert (Nd : P 0 <> P 1).
  { unfold P. rewrite (Hp_low q m lw uw a 0) by lia. rewrite (Hp_low q m lw uw a 1) by lia.
    replace 1 with (a - 1) by lia. rewrite (Lp_first q m lw a Hlw), (Lp_last q m lw a Hlw).
    intros E. pose proof (Hq 0 (m - 1) ltac:(lia)) as L. rewrite E in L.
    unfold lexlt, lexpos in L. rewrite vsub_self in L. simpl in L. lia. }
  apply (collinear (P 0) (P 1)); [exact Nd | apply Z0 | apply Z0 | apply Z0]; assumption.
Qed.

End Reduce.

(* ------------------------------------------------------------------ *)
(* The copying loops                                                   *)
(* ------------------------------------------------------------------ *)

Lemma rev_spec : forall (X : array int) (m : int), (to_Z m <= 4194303)%Z ->
  let R := loop m (fun _ _ => true) (rev_step X m) 0 (PArray.make m 0) in
  PArray.length R = m /\ forall s : int, (to_Z s < to_Z m)%Z -> R.[s] = X.[m - 1 - s].
Proof.
  intros X m Hm. cbv zeta.
  apply (for_inv (fun k (R : array int) => PArray.length R = m /\
     forall s : int, (to_Z s < to_Z k)%Z -> R.[s] = X.[m - 1 - s])).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded m). lia.
  - split; [apply ilength_make_small; lia |]. intros s Hs. change (to_Z 0) with 0%Z in Hs.
    pose proof (to_Z_bounded s). lia.
  - intros k R Hk [L F]. change (to_Z 0) with 0%Z in Hk. unfold rev_step.
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
    split; [rewrite ilength_set; exact L |]. intros s Hs. rewrite Ek in Hs.
    rewrite iget_set by lia. destruct (Z.eqb_spec (to_Z s) (to_Z k)) as [E0 | N0].
    + apply to_Z_inj in E0. subst. reflexivity.
    + apply F. lia.
Qed.

Lemma low_spec : forall (PX PY LS : array int) (a h : int), (to_Z a <= to_Z h <= 4194303)%Z ->
  let '(HX1, HY1) := loop a (fun _ _ => true) (low_step PX PY LS) 0 (PArray.make h 0, PArray.make h 0) in
  PArray.length HX1 = h /\ PArray.length HY1 = h /\
  forall t : int, (to_Z t < to_Z a)%Z -> HX1.[t] = PX.[LS.[t]] /\ HY1.[t] = PY.[LS.[t]].
Proof.
  intros PX PY LS a h Hah.
  pose proof (for_inv (fun k (st : array int * array int) => let '(HX1, HY1) := st in
     PArray.length HX1 = h /\ PArray.length HY1 = h /\
     forall t : int, (to_Z t < to_Z k)%Z -> HX1.[t] = PX.[LS.[t]] /\ HY1.[t] = PY.[LS.[t]])
     a 0 (low_step PX PY LS) (PArray.make h 0, PArray.make h 0)) as G.
  destruct (loop a (fun _ _ => true) (low_step PX PY LS) 0 (PArray.make h 0, PArray.make h 0)) as [HX1 HY1].
  apply G.
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded a). lia.
  - split; [apply ilength_make_small; lia |]. split; [apply ilength_make_small; lia |].
    intros t Ht. change (to_Z 0) with 0%Z in Ht. pose proof (to_Z_bounded t). lia.
  - intros k [X1 Y1] Hk (L1 & L2 & F). change (to_Z 0) with 0%Z in Hk. unfold low_step.
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
    split; [rewrite ilength_set; exact L1 |]. split; [rewrite ilength_set; exact L2 |].
    intros t Ht. rewrite Ek in Ht. rewrite !iget_set by lia.
    destruct (Z.eqb_spec (to_Z t) (to_Z k)) as [E0 | N0].
    + apply to_Z_inj in E0. subst. split; reflexivity.
    + apply F. lia.
Qed.

Lemma up_spec : forall (RX RY US : array int) (a h : int) (HX1 HY1 : array int),
  PArray.length HX1 = h -> PArray.length HY1 = h -> (to_Z a <= to_Z h <= 4194303)%Z ->
  let '(HX, HY) := loop h (fun _ _ => true) (up_step RX RY US a) a (HX1, HY1) in
  (forall t : int, (to_Z t < to_Z a)%Z -> HX.[t] = HX1.[t] /\ HY.[t] = HY1.[t]) /\
  (forall t : int, (to_Z a <= to_Z t < to_Z h)%Z -> HX.[t] = RX.[US.[t - a + 1]] /\ HY.[t] = RY.[US.[t - a + 1]]).
Proof.
  intros RX RY US a h HX1 HY1 L1 L2 Hah.
  pose proof (for_inv (fun k (st : array int * array int) => let '(HX, HY) := st in
     PArray.length HX = h /\ PArray.length HY = h /\
     (forall t : int, (to_Z t < to_Z a \/ to_Z k <= to_Z t)%Z -> HX.[t] = HX1.[t] /\ HY.[t] = HY1.[t]) /\
     (forall t : int, (to_Z a <= to_Z t < to_Z k)%Z -> HX.[t] = RX.[US.[t - a + 1]] /\ HY.[t] = RY.[US.[t - a + 1]]))
     h a (up_step RX RY US a) (HX1, HY1)) as G.
  destruct (loop h (fun _ _ => true) (up_step RX RY US a) a (HX1, HY1)) as [HX HY].
  destruct G as (_ & _ & F1 & F2).
  - lia.
  - split; [exact L1 |]. split; [exact L2 |]. split; [intros; split; reflexivity | intros t Ht; lia].
  - intros k [X1 Y1] Hk (M1 & M2 & F & G). unfold up_step.
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
    split; [rewrite ilength_set; exact M1 |]. split; [rewrite ilength_set; exact M2 |].
    split.
    + intros t Ht. rewrite Ek in Ht. rewrite !iget_set by lia.
      destruct (Z.eqb_spec (to_Z t) (to_Z k)) as [E0 | N0]; [lia |]. apply F. lia.
    + intros t Ht. rewrite Ek in Ht. rewrite !iget_set by lia.
      destruct (Z.eqb_spec (to_Z t) (to_Z k)) as [E0 | N0].
      * apply to_Z_inj in E0. subst. split; reflexivity.
      * apply G. lia.
  - split; [intros t Ht; apply F1; lia | exact F2].
Qed.

(* ------------------------------------------------------------------ *)
(* The answer as a float: an integer below 2^53, halved, is exact       *)
(* ------------------------------------------------------------------ *)

Lemma half_exact : forall v : int, (to_Z v < 9007199254740992)%Z ->
  repr (of_uint63 v / of_uint63 2)%float (IZR (to_Z v) / 2)%R.
Proof.
  intros v Hv.
  assert (R1 := repr_of_uint63_exact v Hv).
  assert (R2 : repr (of_uint63 2) 2%R) by exact (repr_of_uint63_exact 2 eq_refl).
  pose proof (to_Z_bounded v) as Bv.
  assert (E : rnd (IZR (to_Z v) / 2) = (IZR (to_Z v) / 2)%R).
  { apply rnd_exact. apply FLT.generic_format_FLT.
    exists (Defs.Float Zaux.radix2 (to_Z v) (-1)); [| simpl; lia | simpl; lia].
    unfold Defs.F2R; simpl. unfold Rdiv. f_equal. }
  rewrite <- E. apply repr_div; [exact R1 | exact R2 | lra |].
  apply rnd_no_overflow_small.
  pose proof (Raux.bpow_le Zaux.radix2 60 1000 ltac:(lia)) as H.
  change (Raux.bpow Zaux.radix2 60) with 1152921504606846976%R in H.
  assert (0 <= IZR (to_Z v) <= 9007199254740992)%R by (split; apply IZR_le; lia).
  rewrite Rabs_right by lra. lra.
Qed.

Lemma zero_repr : repr (of_uint63 0) 0%R.
Proof. exact (repr_of_uint63_exact 0 eq_refl). Qed.

(* ------------------------------------------------------------------ *)
(* The input                                                           *)
(* ------------------------------------------------------------------ *)

Section Main.
Variables (xs ys : list N) (x y : array uint).
Hypothesis Hv : valid_input xs ys.
Hypothesis Hx : repr x xs.
Hypothesis Hy : repr y ys.

Definition n : int := PArray.length x.

(* the k-th point of the statement *)
Definition Pin (k : Z) : Z * Z :=
  (Z.of_N (get_list_N xs (Z.to_N k)), Z.of_N (get_list_N ys (Z.to_N k))).

Lemma len_x : Z.of_nat (List.length xs) = to_Z n.
Proof. exact (proj1 Hx). Qed.

Lemma len_y : Z.of_nat (List.length ys) = to_Z (PArray.length y).
Proof. exact (proj1 Hy). Qed.

Lemma n_bounds : (3 <= to_Z n <= 5000)%Z.
Proof. pose proof (vi_n _ _ Hv) as H. unfold len in H. rewrite <- len_x. lia. Qed.

Lemma ny : to_Z (PArray.length y) = to_Z n.
Proof. rewrite <- len_y, <- len_x. pose proof (vi_ys _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma read_uint : forall (l : list N) (t : array uint) (a : int), repr t l ->
  (to_Z a < Z.of_nat (List.length l))%Z ->
  to_Z t.[a] = Z.of_N (get_list_N l (Z.to_N (to_Z a))) /\ List.In (get_list_N l (Z.to_N (to_Z a))) l.
Proof.
  intros l t a [_ H] Ha. destruct (H (Z.to_nat (to_Z a)) ltac:(lia)) as (m & E & R).
  unfold repr, repr_uint in R.
  rewrite Z2Nat.id in R by (pose proof (to_Z_bounded a); lia). rewrite of_to_Z in R.
  unfold get_list_N. rewrite Z_N_nat. rewrite (nth_error_nth _ _ _ E).
  split; [pose proof (to_Z_bounded t.[a]); lia |]. eapply nth_error_In. exact E.
Qed.

Lemma x_val : forall a : int, (to_Z a < to_Z n)%Z -> to_Z x.[a] = fst (Pin (to_Z a)).
Proof.
  intros a Ha. destruct (read_uint xs x a Hx ltac:(rewrite len_x; exact Ha)) as [E I]. exact E.
Qed.

Lemma y_val : forall a : int, (to_Z a < to_Z n)%Z -> to_Z y.[a] = snd (Pin (to_Z a)).
Proof.
  intros a Ha. destruct (read_uint ys y a Hy ltac:(rewrite len_y, ny; exact Ha)) as [E I]. exact E.
Qed.

Lemma get_bound : forall (l : list N) k, Forall (fun c => (c <= 4 * 10 ^ 7)%N) l ->
  (0 <= Z.of_N (get_list_N l k) <= 40000000)%Z.
Proof.
  intros l k F. unfold get_list_N. rewrite Forall_forall in F.
  destruct (Nat.lt_ge_cases (N.to_nat k) (List.length l)) as [L | L].
  - pose proof (F _ (nth_In l 0%N L)) as B. change (4 * 10 ^ 7)%N with 40000000%N in B. lia.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma Pin_bound : forall k, (0 <= fst (Pin k) <= 40000000 /\ 0 <= snd (Pin k) <= 40000000)%Z.
Proof.
  intros k. unfold Pin; simpl. split; apply get_bound; [exact (vi_x _ _ Hv) | exact (vi_y _ _ Hv)].
Qed.

(* -- the keys -- *)

Definition Kf : array int :=
  loop n (fun _ _ => true) (fun i K => K.[i <- x.[i] * SH + y.[i]]) 0 (PArray.make n 0).

Lemma Kf_spec : PArray.length Kf = n /\
  forall i : int, (to_Z i < to_Z n)%Z -> to_Z Kf.[i] = (fst (Pin (to_Z i)) * C26 + snd (Pin (to_Z i)))%Z.
Proof.
  pose proof n_bounds as Hn. unfold Kf.
  apply (for_inv (fun k (K : array int) => PArray.length K = n /\
     forall i : int, (to_Z i < to_Z k)%Z -> to_Z K.[i] = (fst (Pin (to_Z i)) * C26 + snd (Pin (to_Z i)))%Z)).
  - change (to_Z 0) with 0%Z. lia.
  - split; [apply ilength_make_small; lia |]. intros i Hi. change (to_Z 0) with 0%Z in Hi.
    pose proof (to_Z_bounded i). lia.
  - intros k K Hk [L F]. change (to_Z 0) with 0%Z in Hk.
    assert (Ek : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_small; lia).
    split; [rewrite ilength_set; exact L |].
    intros i Hi. rewrite Ek in Hi. rewrite iget_set by lia.
    destruct (Z.eqb_spec (to_Z i) (to_Z k)) as [E0 | N0].
    + apply to_Z_inj in E0. subst i.
      pose proof (x_val k ltac:(lia)) as X1. pose proof (y_val k ltac:(lia)) as Y1.
      rewrite Uint63.add_spec, Uint63.mul_spec. change (to_Z SH) with C26.
      rewrite X1, Y1. pose proof (Pin_bound (to_Z k)). unfold C26 in *.
      rewrite (Z.mod_small (fst (Pin (to_Z k)) * 67108864)) by (change wB with 9223372036854775808%Z; lia).
      apply Z.mod_small. change wB with 9223372036854775808%Z. lia.
    + apply F. lia.
Qed.

Lemma Pin_dec : forall i : int, (to_Z i < to_Z n)%Z -> dec (to_Z Kf.[i]) = Pin (to_Z i).
Proof.
  intros i Hi. destruct Kf_spec as [_ F]. rewrite F by exact Hi.
  pose proof (Pin_bound (to_Z i)).
  rewrite dec_key by (unfold C26; lia). destruct (Pin (to_Z i)). reflexivity.
Qed.

Lemma Kf_small : forall i : int, (to_Z i < to_Z n)%Z -> (to_Z Kf.[i] < 2814749767106560 * 2)%Z.
Proof.
  intros i Hi. destruct Kf_spec as [_ F]. rewrite F by exact Hi.
  pose proof (Pin_bound (to_Z i)). unfold C26. lia.
Qed.

(* -- the distinct points -- *)

Definition qD (D : array int) (z : Z) : Z * Z := dec (to_Z D.[of_Z z]).

Section Distinct.
Variables (D : array int) (m : int).
Hypothesis Hmn : (to_Z m <= to_Z n)%Z.
Hypothesis HD : SInc D (to_Z m).
Hypothesis HIn : forall v, In D 0 (to_Z m) v <-> In Kf 0 (to_Z n) v.

Lemma pin_in_D : forall k, (0 <= k < to_Z n)%Z -> exists u, (0 <= u < to_Z m)%Z /\ Pin k = qD D u.
Proof.
  intros k Hk. pose proof n_bounds.
  assert (I : In Kf 0 (to_Z n) Kf.[of_Z k])
    by (exists (of_Z k); rewrite to_Z_of_Z_small by lia; split; [lia | reflexivity]).
  apply HIn in I. destruct I as (u & Hu & Eu).
  exists (to_Z u). split; [lia |]. unfold qD. rewrite of_to_Z, Eu.
  rewrite Pin_dec by (rewrite to_Z_of_Z_small; lia). rewrite to_Z_of_Z_small by lia. reflexivity.
Qed.

Lemma D_in_pin : forall u, (0 <= u < to_Z m)%Z -> exists k, (0 <= k < to_Z n)%Z /\ qD D u = Pin k.
Proof.
  intros u Hu. pose proof n_bounds.
  assert (I : In D 0 (to_Z m) D.[of_Z u])
    by (exists (of_Z u); rewrite to_Z_of_Z_small by lia; split; [lia | reflexivity]).
  apply HIn in I. destruct I as (k & Hk & Ek).
  exists (to_Z k). split; [lia |]. unfold qD. rewrite <- Ek. apply Pin_dec. lia.
Qed.

Lemma qD_inc : Qinc (qD D) (to_Z m).
Proof.
  intros a b Hab. pose proof n_bounds. unfold qD. apply dec_lt.
  split; [apply to_Z_bounded |]. apply HD. rewrite !to_Z_of_Z_small by lia. lia.
Qed.

Lemma qD_bound : forall u, (0 <= u < to_Z m)%Z ->
  (0 <= fst (qD D u) <= 40000000 /\ 0 <= snd (qD D u) <= 40000000)%Z.
Proof. intros u Hu. destruct (D_in_pin u Hu) as (k & _ & ->). apply Pin_bound. Qed.

Lemma few_points : (to_Z m < 3)%Z -> forall i j k, (0 <= i < to_Z n)%Z -> (0 <= j < to_Z n)%Z ->
  (0 <= k < to_Z n)%Z -> cross (Pin i) (Pin j) (Pin k) = 0%Z.
Proof.
  intros Hm i j k Hi Hj Hk.
  destruct (pin_in_D i Hi) as (u1 & H1 & ->). destruct (pin_in_D j Hj) as (u2 & H2 & ->).
  destruct (pin_in_D k Hk) as (u3 & H3 & ->).
  destruct (Z.eq_dec u1 u2) as [-> | N12]; [apply cross_aa |].
  destruct (Z.eq_dec u2 u3) as [-> | N23]; [apply cross_bb |].
  assert (u1 = u3) as -> by lia. apply cross_aba.
Qed.

End Distinct.

(* -- many distinct points: the hull and the sweep -- *)

Section Many.
Variables (D : array int) (m : int) (PX PY : array int).
Hypothesis Hmn : (to_Z m <= to_Z n)%Z.
Hypothesis HD : SInc D (to_Z m).
Hypothesis HIn : forall v, In D 0 (to_Z m) v <-> In Kf 0 (to_Z n) v.
Hypothesis Hm3 : (3 <= to_Z m)%Z.
Hypothesis HPX : PArray.length PX = m.
Hypothesis HPY : PArray.length PY = m.
Hypothesis Hdec : forall u : int, (to_Z u < to_Z m)%Z -> ipt PX.[u] PY.[u] = dec (to_Z D.[u]).

Definition qq (z : Z) : Z * Z := ipt PX.[of_Z z] PY.[of_Z z].

Lemma m_bounds : (3 <= to_Z m <= 5000)%Z.
Proof. pose proof n_bounds. lia. Qed.

Lemma qq_eq : forall z, (0 <= z < to_Z m)%Z -> qq z = qD D z.
Proof.
  intros z Hz. pose proof m_bounds. unfold qq, qD. rewrite Hdec by (rewrite to_Z_of_Z_small; lia).
  reflexivity.
Qed.

Lemma qq_int : forall a : int, qq (to_Z a) = ipt PX.[a] PY.[a].
Proof. intros a. unfold qq. rewrite of_to_Z. reflexivity. Qed.

Lemma qq_inc : Qinc qq (to_Z m).
Proof. intros a b Hab. rewrite !qq_eq by lia. apply (qD_inc D m Hmn HD). exact Hab. Qed.

Lemma qq_bound : forall u, (0 <= u < to_Z m)%Z ->
  (0 <= fst (qq u) <= 40000000 /\ 0 <= snd (qq u) <= 40000000)%Z.
Proof. intros u Hu. rewrite qq_eq by exact Hu. apply (qD_bound D m Hmn HIn). exact Hu. Qed.

Lemma qq_in : forall u, (0 <= u < to_Z m)%Z -> exists k, (0 <= k < to_Z n)%Z /\ qq u = Pin k.
Proof. intros u Hu. rewrite qq_eq by exact Hu. apply (D_in_pin D m Hmn HIn). exact Hu. Qed.

Lemma pin_in_qq : forall k, (0 <= k < to_Z n)%Z -> exists u, (0 <= u < to_Z m)%Z /\ Pin k = qq u.
Proof.
  intros k Hk. destruct (pin_in_D D m HIn k Hk) as (u & Hu & E).
  exists u. split; [exact Hu |]. rewrite qq_eq by exact Hu. exact E.
Qed.

Lemma P_coord : forall a : int, (to_Z a < to_Z m)%Z -> (to_Z PX.[a] < C26)%Z /\ (to_Z PY.[a] < C26)%Z.
Proof.
  intros a Ha. pose proof (qq_bound (to_Z a) ltac:(pose proof (to_Z_bounded a); lia)) as B.
  rewrite qq_int in B. unfold ipt, C26 in *; simpl in B. lia.
Qed.

Lemma crs_qq : forall a b c : int, (to_Z a < to_Z m)%Z -> (to_Z b < to_Z m)%Z -> (to_Z c < to_Z m)%Z ->
  to_Z (crs PX.[a] PY.[a] PX.[b] PY.[b] PX.[c] PY.[c]) =
  (cross (qq (to_Z a)) (qq (to_Z b)) (qq (to_Z c)) + C60)%Z.
Proof.
  intros a b c Ha Hb Hc. rewrite !qq_int.
  destruct (P_coord a Ha), (P_coord b Hb), (P_coord c Hc). apply crs_spec; assumption.
Qed.

Lemma cross_small : forall A B C : Z * Z,
  (0 <= fst A <= 40000000 /\ 0 <= snd A <= 40000000)%Z ->
  (0 <= fst B <= 40000000 /\ 0 <= snd B <= 40000000)%Z ->
  (0 <= fst C <= 40000000 /\ 0 <= snd C <= 40000000)%Z ->
  (Z.abs (cross A B C) < 9007199254740992)%Z.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2] HA HB HC. unfold cross; simpl in *.
  pose proof (prod_bound (b1 - a1) (c2 - a2) 40000000 ltac:(lia) ltac:(lia)).
  pose proof (prod_bound (c1 - a1) (b2 - a2) 40000000 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma many_core :
  exists M : Z, (0 <= M < 9007199254740992)%Z /\
  repr (let '(LS, a) := pass PX PY m in
        let RX := loop m (fun _ _ => true) (rev_step PX m) 0 (PArray.make m 0) in
        let RY := loop m (fun _ _ => true) (rev_step PY m) 0 (PArray.make m 0) in
        let '(US, b) := pass RX RY m in
        let h := a + b - 2 in
        if h <? 3 then fzero else
        let '(HX1, HY1) := loop a (fun _ _ => true) (low_step PX PY LS) 0 (PArray.make h 0, PArray.make h 0) in
        let '(HX, HY) := loop h (fun _ _ => true) (up_step RX RY US a) a (HX1, HY1) in
        let best := sweep HX HY h in
        (of_uint63 (best - OFF) / of_uint63 2)%float) (IZR M / 2)%R /\
  (forall i j k, (0 <= i < to_Z n)%Z -> (0 <= j < to_Z n)%Z -> (0 <= k < to_Z n)%Z ->
     (Z.abs (cross (Pin i) (Pin j) (Pin k)) <= M)%Z) /\
  (M = 0%Z \/ exists i j k, (0 <= i < to_Z n)%Z /\ (0 <= j < to_Z n)%Z /\ (0 <= k < to_Z n)%Z /\
     i <> j /\ j <> k /\ i <> k /\ cross (Pin i) (Pin j) (Pin k) = M).
Proof.
  pose proof m_bounds as Hmb.
  pose proof (pass_spec PX PY m qq ltac:(lia) qq_inc crs_qq) as PL.
  destruct (pass PX PY m) as [LS a]. destruct PL as (CL & LL & Ha).
  cbv zeta.
  destruct (rev_spec PX m ltac:(lia)) as [RXL RXs].
  destruct (rev_spec PY m ltac:(lia)) as [RYL RYs].
  set (RX := loop m (fun _ _ => true) (rev_step PX m) 0 (PArray.make m 0)) in *.
  set (RY := loop m (fun _ _ => true) (rev_step PY m) 0 (PArray.make m 0)) in *.
  assert (Erev : forall s : int, (to_Z s < to_Z m)%Z -> to_Z (m - 1 - s) = (to_Z m - 1 - to_Z s)%Z)
    by (intros s Hs; sia).
  assert (crs_rr : forall a0 b0 c0 : int, (to_Z a0 < to_Z m)%Z -> (to_Z b0 < to_Z m)%Z -> (to_Z c0 < to_Z m)%Z ->
     to_Z (crs RX.[a0] RY.[a0] RX.[b0] RY.[b0] RX.[c0] RY.[c0]) =
     (cross (Qu qq (to_Z m) (to_Z a0)) (Qu qq (to_Z m) (to_Z b0)) (Qu qq (to_Z m) (to_Z c0)) + C60)%Z).
  { intros a0 b0 c0 H1 H2 H3. rewrite !RXs, !RYs by assumption.
    rewrite crs_qq by (rewrite Erev; lia). unfold Qu. rewrite cross_neg. rewrite !Erev by assumption.
    reflexivity. }
  pose proof (pass_spec RX RY m (Qu qq (to_Z m)) ltac:(lia) (Qu_inc qq (to_Z m) qq_inc) crs_rr) as PU.
  destruct (pass RX RY m) as [US b]. destruct PU as (CU & LU & Hb).
  pose proof (a_ge2 qq (to_Z m) ltac:(lia) (lst LS) (to_Z a) CL) as A2.
  pose proof (b_ge2 qq (to_Z m) ltac:(lia) (lst US) (to_Z b) CU) as B2.
  assert (Eh : to_Z (a + b - 2) = (to_Z a + to_Z b - 2)%Z) by sia.
  set (lw := lst LS) in *. set (uw := lst US) in *.
  set (P := Hp qq (to_Z m) lw uw (to_Z a)).
  destruct (a + b - 2 <? 3) eqn:Ch.
  - (* all the points on one line *)
    rewrite Uint63.ltb_spec, Eh in Ch. change (to_Z 3) with 3%Z in Ch.
    exists 0%Z. split; [lia |]. split.
    { replace (IZR 0 / 2)%R with 0%R by (simpl; lra). exact zero_repr. }
    split; [| left; reflexivity].
    intros i j k Hi Hj Hk.
    destruct (pin_in_qq i Hi) as (u1 & U1 & ->). destruct (pin_in_qq j Hj) as (u2 & U2 & ->).
    destruct (pin_in_qq k Hk) as (u3 & U3 & ->).
    rewrite (hull_collinear qq (to_Z m) qq_inc ltac:(lia) lw uw (to_Z a) (to_Z b) CL CU
               ltac:(unfold hh; lia) u1 u2 u3 U1 U2 U3).
    lia.
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec, Eh in Ch. change (to_Z 3) with 3%Z in Ch.
    set (h := a + b - 2) in *.
    assert (Hh : (to_Z a <= to_Z h <= 4194303)%Z) by lia.
    pose proof (low_spec PX PY LS a h Hh) as LO.
    destruct (loop a (fun _ _ => true) (low_step PX PY LS) 0 (PArray.make h 0, PArray.make h 0)) as [HX1 HY1].
    destruct LO as (L1 & L2 & LF).
    pose proof (up_spec RX RY US a h HX1 HY1 L1 L2 Hh) as UP.
    destruct (loop h (fun _ _ => true) (up_step RX RY US a) a (HX1, HY1)) as [HX HY].
    destruct UP as (UF1 & UF2).
    assert (PH : forall t, (0 <= t < to_Z h)%Z -> Pz HX HY t = P t).
    { intros t Ht. unfold Pz, P.
      set (ti := of_Z t). assert (Et : to_Z ti = t) by (apply to_Z_of_Z_small; lia).
      destruct (Z_lt_le_dec t (to_Z a)) as [Lt | Ge].
      - rewrite (Hp_low qq (to_Z m) lw uw (to_Z a) t) by lia.
        destruct (UF1 ti ltac:(lia)) as [-> ->]. destruct (LF ti ltac:(lia)) as [-> ->].
        rewrite <- qq_int. unfold Lp, lw. rewrite <- Et, lst_int. reflexivity.
      - rewrite (Hp_up qq (to_Z m) lw uw (to_Z a) (to_Z b) CL CU t) by lia.
        destruct (UF2 ti ltac:(lia)) as [-> ->].
        set (v := US.[ti - a + 1]).
        assert (Ev : to_Z (ti - a + 1) = (t - to_Z a + 1)%Z) by sia.
        assert (Rv : (0 <= uw (t - to_Z a + 1) <= to_Z m - 1)%Z)
          by (pose proof (ch_range _ _ _ _ CU (t - to_Z a + 1) ltac:(lia)); lia).
        assert (HvU : to_Z v = uw (t - to_Z a + 1)%Z) by (unfold v, uw; rewrite <- Ev, lst_int; reflexivity).
        rewrite RXs, RYs by lia. rewrite <- qq_int. unfold Up. rewrite Erev by lia. rewrite HvU. reflexivity. }
    assert (Hcv : forall a0 b0 c0, (0 <= a0)%Z -> (a0 < b0)%Z -> (b0 < c0)%Z -> (c0 < to_Z h)%Z ->
              (0 < cross (Pz HX HY a0) (Pz HX HY b0) (Pz HX HY c0))%Z).
    { intros a0 b0 c0 H1 H2 H3 H4. rewrite !PH by lia.
      apply (Hp_convex qq (to_Z m) qq_inc lw uw (to_Z a) (to_Z b) CL CU); unfold hh; lia. }
    assert (Pb : forall t, (0 <= t < to_Z h)%Z ->
              (0 <= fst (Pz HX HY t) <= 40000000 /\ 0 <= snd (Pz HX HY t) <= 40000000)%Z).
    { intros t Ht. rewrite PH by exact Ht.
      destruct (Hp_in qq (to_Z m) lw uw (to_Z a) (to_Z b) CL CU t ltac:(unfold hh; lia)) as (v & HvU & Ev).
      fold P in Ev. rewrite Ev. apply qq_bound. exact HvU. }
    assert (Hco : forall t : int, (to_Z t < to_Z h)%Z -> (to_Z HX.[t] < C26)%Z /\ (to_Z HY.[t] < C26)%Z).
    { intros t Ht. pose proof (Pb (to_Z t) ltac:(pose proof (to_Z_bounded t); lia)) as B.
      rewrite Pz_int in B. unfold ipt, C26 in *; simpl in B. lia. }
    destruct (sweep_spec HX HY h ltac:(lia) Hco Hcv) as [(Bv & EB & B0 & BA) Bbd].
    set (best := sweep HX HY h) in *.
    assert (Bsmall : (Bv < 9007199254740992)%Z).
    { destruct BA as [-> | (a0 & b0 & c0 & H1 & H2 & H3 & H4 & ->)]; [lia |].
      pose proof (cross_small (Pz HX HY a0) (Pz HX HY b0) (Pz HX HY c0)
                    (Pb a0 ltac:(lia)) (Pb b0 ltac:(lia)) (Pb c0 ltac:(lia))). lia. }
    exists Bv. split; [lia |]. split.
    { assert (Ev : to_Z (best - OFF) = Bv).
      { rewrite Uint63.sub_spec, EB. change (to_Z OFF) with C60. unfold C60 in *.
        replace (Bv + 1152921504606846976 - 1152921504606846976)%Z with Bv by lia.
        apply Z.mod_small. change wB with 9223372036854775808%Z. lia. }
      rewrite <- Ev. apply half_exact. lia. }
    split.
    + intros i j k Hi Hj Hk.
      destruct (pin_in_qq i Hi) as (u1 & U1 & ->). destruct (pin_in_qq j Hj) as (u2 & U2 & ->).
      destruct (pin_in_qq k Hk) as (u3 & U3 & ->).
      apply (hull_bound qq (to_Z m) qq_inc ltac:(lia) lw uw (to_Z a) (to_Z b) CL CU Bv
               ltac:(unfold hh; lia)); try assumption.
      intros a0 b0 c0 H1 H2 H3 H4. unfold hh in H4. fold P. rewrite <- !PH by lia.
      pose proof (Bbd a0 b0 c0 H1 H2 H3 ltac:(lia)). lia.
    + destruct BA as [B | (a0 & b0 & c0 & H1 & H2 & H3 & H4 & EB2)]; [left; exact B | right].
      pose proof (Hcv a0 b0 c0 H1 H2 H3 H4) as Pos. rewrite <- EB2 in Pos.
      rewrite !PH in EB2 by lia.
      destruct (Hp_in qq (to_Z m) lw uw (to_Z a) (to_Z b) CL CU a0 ltac:(unfold hh; lia)) as (v1 & V1 & E1).
      destruct (Hp_in qq (to_Z m) lw uw (to_Z a) (to_Z b) CL CU b0 ltac:(unfold hh; lia)) as (v2 & V2 & E2).
      destruct (Hp_in qq (to_Z m) lw uw (to_Z a) (to_Z b) CL CU c0 ltac:(unfold hh; lia)) as (v3 & V3 & E3).
      fold P in E1, E2, E3. rewrite E1, E2, E3 in EB2.
      destruct (qq_in v1 V1) as (k1 & K1 & F1). destruct (qq_in v2 V2) as (k2 & K2 & F2).
      destruct (qq_in v3 V3) as (k3 & K3 & F3). rewrite F1, F2, F3 in EB2.
      exists k1, k2, k3. split; [exact K1 |]. split; [exact K2 |]. split; [exact K3 |].
      split; [intros ->; rewrite cross_aa in EB2; lia |].
      split; [intros ->; rewrite cross_bb in EB2; lia |].
      split; [intros ->; rewrite cross_aba in EB2; lia |].
      symmetry. exact EB2.
Qed.

End Many.

Theorem core : exists M : Z, (0 <= M < 9007199254740992)%Z /\
  repr (largest_triangle_impl x y) (IZR M / 2)%R /\
  (forall i j k, (0 <= i < to_Z n)%Z -> (0 <= j < to_Z n)%Z -> (0 <= k < to_Z n)%Z ->
     (Z.abs (cross (Pin i) (Pin j) (Pin k)) <= M)%Z) /\
  (M = 0%Z \/ exists i j k, (0 <= i < to_Z n)%Z /\ (0 <= j < to_Z n)%Z /\ (0 <= k < to_Z n)%Z /\
     i <> j /\ j <> k /\ i <> k /\ cross (Pin i) (Pin j) (Pin k) = M).
Proof.
  pose proof n_bounds as Hn.
  unfold largest_triangle_impl. cbv zeta. fold n. fold Kf.
  destruct (sort_spec Kf n (proj1 Kf_spec)) as (SL & SS & SI).
  pose proof (dedup_spec (sort Kf n) n SL SS) as DD.
  destruct (loop n (fun _ _ => true) (dedup_step (sort Kf n)) 0 (PArray.make n 0, 0)) as [D m].
  destruct DD as (DL & Dm & DInc & DIn & _).
  assert (HIn : forall v, In D 0 (to_Z m) v <-> In Kf 0 (to_Z n) v) by (intros v; rewrite DIn, SI; tauto).
  destruct (m <? 3) eqn:Cm.
  - rewrite Uint63.ltb_spec in Cm. change (to_Z 3) with 3%Z in Cm.
    exists 0%Z. split; [lia |]. split.
    { replace (IZR 0 / 2)%R with 0%R by (simpl; lra). exact zero_repr. }
    split; [| left; reflexivity].
    intros i j k Hi Hj Hk. rewrite (few_points D m HIn Cm i j k Hi Hj Hk). lia.
  - rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Cm. change (to_Z 3) with 3%Z in Cm.
    pose proof (decode_spec D m ltac:(lia)) as DC.
    destruct (loop m (fun _ _ => true) (decode_step D) 0 (PArray.make m 0, PArray.make m 0)) as [PX PY].
    destruct DC as (LX & LY & Hdec).
    apply (many_core D m PX PY); try assumption. lia.
Qed.

End Main.

Lemma area_eq : forall xs ys (i j k : N),
  area xs ys i j k = (Rabs (IZR (cross (Pin xs ys (Z.of_N i)) (Pin xs ys (Z.of_N j)) (Pin xs ys (Z.of_N k)))) / 2)%R.
Proof. intros. unfold area, Pin, cross; simpl. rewrite !N2Z.id. reflexivity. Qed.

Lemma largest_triangle_correct_main : forall (xs ys : list N) (x y : array uint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists r : R, repr (largest_triangle_impl x y) r /\ largest_triangle_spec xs ys r.
Proof.
  intros xs ys x y Hv Hx Hy.
  destruct (core xs ys x y Hv Hx Hy) as (M & HM & R & Bd & Ex).
  pose proof (len_x xs x Hx) as Lx. pose proof (n_bounds xs ys x Hv Hx) as Hn.
  exists (IZR M / 2)%R. split; [exact R |].
  exists (IZR M / 2)%R. split.
  2: { unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra. }
  assert (Tr : forall i, (i < len xs)%N <-> (0 <= Z.of_N i < to_Z (n x))%Z) by (intros i; unfold len; lia).
  split.
  - destruct Ex as [E0 | (i & j & k & Hi & Hj & Hk & Nij & Njk & Nik & E)].
    + exists 0%N, 1%N, 2%N. split.
      * unfold is_triple. rewrite !Tr. simpl. lia.
      * rewrite area_eq. simpl Z.of_N.
        pose proof (Bd 0%Z 1%Z 2%Z ltac:(lia) ltac:(lia) ltac:(lia)) as B. subst M.
        assert (C0 : cross (Pin xs ys 0) (Pin xs ys 1) (Pin xs ys 2) = 0%Z) by lia.
        rewrite C0. simpl. rewrite Rabs_R0. lra.
    + exists (Z.to_N i), (Z.to_N j), (Z.to_N k). split.
      * unfold is_triple. rewrite !Tr. lia.
      * rewrite area_eq. rewrite !Z2N.id by lia. rewrite E.
        rewrite Rabs_right by (apply Rle_ge, IZR_le; lia). reflexivity.
  - intros i j k (Hi & Hj & Hk & _). rewrite Tr in Hi, Hj, Hk.
    rewrite area_eq. pose proof (Bd _ _ _ Hi Hj Hk) as B.
    rewrite <- abs_IZR. unfold Rdiv. apply Rmult_le_compat_r; [lra |]. apply IZR_le. exact B.
Qed.

Definition largest_triangle : array uint -> array uint -> float := largest_triangle_impl.
Elpi complexity largest_triangle.
Arguments largest_triangle_cost : simpl never.

Lemma largest_triangle_correct :
  forall (xs ys : list N) (x y : array uint),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists r : R, repr (largest_triangle x y) r /\ largest_triangle_spec xs ys r.
Proof. exact largest_triangle_correct_main. Qed.

(* ================================================================== *)
(* Cost                                                                *)
(* ================================================================== *)

(* The cost bound largest_triangle_time.  [Elpi complexity] translates,
   callee first, sumbool, bdec, andb, orb, fst, wloop, loop, SH, OFF,
   crs, the step functions and loops of the program and
   largest_triangle (above, after each definition).  The proof:
   - wloop_time_gen / loop_time_gen: the generic loop, for any state type,
     with an invariant Inv and a potential Pot on the state; each step
     (the test cont and the body f) costing at most Pot s - Pot (f s) + K,
     the loop from i costs at most (2 K + 25) * (hi - i) + Pot s + 30;
   - popl_time (potential 200 * r, the stack size: cost + 200 * r' <=
     200 * r + 200), hence pass_step_time (amortised constant) and
     pass_time (1100 * m + 300, potential 200 * r on the pass state);
   - climb_time (potential 200 * (hm - k)), jloop_time
     (600 * (hm - j) + 200 * (hm - k) + 600: the third corner only moves
     forward), sweep_step_time (800 * h + 700), sweep_time
     ((1600 * h + 2000) * h + 50);
   - merge_time (230 * (hi - lo) + 100), msort_time
     (cost + 1000 <= 400 L log2_up L + 2000 max L 1, L = hi - lo, by
     induction on L, both halves at most log2_up L - 1), sort_time;
   - main_time: the whole, at most Fb (size x), with m <= n, a, b <= m
     and h = a + b - 2 <= 2 n; largest_triangle_time from it, with
     c1 = c2 = 20000.
   cbn (inside cost_simpl) must not unfold φ of a variable (the Acc index
   of popl is φ r) nor the well-founded loops applied to
   Zwf_well_founded: the local [simpl never] below. *)

Local Open Scope uint63_scope.
#[local] Arguments gap : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. unfold bdec_cost. destruct w; cbn; lia. Qed.

Lemma gap_succ hi k : (k <? hi) = true -> Z.to_nat (gap hi (k + 1)) = (Z.to_nat (gap hi k) - 1)%nat /\ (0 < Z.to_nat (gap hi k))%nat.
Proof. intros H. rewrite Uint63.ltb_spec in H. unfold gap.
  assert (φ (k + 1) = φ k + 1)%Z by (pose proof (to_Z_bounded hi); sia). lia. Qed.

Lemma if_le (b : bool) (x y B : nat) : (b = true -> x <= B)%nat -> (b = false -> y <= B)%nat -> ((if b then x else y) <= B)%nat.
Proof. destruct b; auto. Qed.

Section W.
Context {St : Type} (StC : St -> Type).
Lemma wloop_time_gen (Inv : int -> St -> Prop) (Pot : St -> nat) (K : nat)
  hi hiC cont contC f fC 
  (Hc : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z ->
     (cost (contC j jC) + cost (extract (contC j jC) t tC) <= K)%nat)
  (Hf : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z -> cont j t = true ->
     (cost (fC j jC) + cost (extract (fC j jC) t tC) + Pot (f j t) <= Pot t + K)%nat)
  (HI : forall j t, Inv j t -> (φ j < φ hi)%Z -> cont j t = true -> Inv (j + 1) (f j t))
  i iC s sC H HC : Inv i s ->
  (cost (extract (extract (extract (extract (extract (extract (wloop_cost stepsCM St StC) hi hiC) cont contC) f fC) i iC) s sC) H HC) <= (2 * K + 25) * Z.to_nat (gap hi i) + Pot s + 10)%nat.
Proof.
  unfold wloop_cost. cbn.
  match goal with |- context [@cost ?T (?G hi hiC cont contC f fC i iC s sC H HC)] =>
    assert (HG : forall k i iC s sC H HC, (Z.to_nat (gap hi i) <= k)%nat -> Inv i s ->
       (cost (G hi hiC cont contC f fC i iC s sC H HC) <= (2 * K + 25) * k + Pot s + 10)%nat) end.
  { induction k as [|k IH]; intros i' iC' s' sC' [g] HC' Hk Hinv;
      cost_simpl;
      pose proof (bdec_time (i' <? hi) (bool_w (i' <? hi))) as HB;
      cost_destruct (bdec (i' <? hi)); cost_simpl.
    - exfalso. destruct (gap_succ _ _ e). lia.
    - lia.
    - pose proof e as Hlt. rewrite Uint63.ltb_spec in Hlt.
      pose proof (Hc i' iC' s' sC' Hinv Hlt) as HC1. cost_align HC1.
      cost_destruct_eqn (cont i' s') Ec.
      + cost_simpl.
        destruct (gap_succ _ _ e) as [Eg Pg].
        pose proof (Hf i' iC' s' sC' Hinv Hlt Ec) as HF1.
        match goal with |- context [@cost ?T (?G' hi hiC cont contC f fC (i' + 1)%uint63 ?w ?c ?wc ?h ?e)] =>
          pose proof (IH (i' + 1)%uint63 w c wc h e : _ -> _ -> (@cost T (G' hi hiC cont contC f fC (i' + 1)%uint63 w c wc h e) <= _)%nat) as HI2 end.
        specialize (HI2 ltac:(lia) (HI _ _ Hinv Hlt Ec)). cost_align HF1. cost_align HI2. cost_align HC1. clear -HF1 HI2 HC1 HB. assert (EM : ((K + (K + 0) + 25) * S k = (2 * K + 25) * k + 2 * K + 25)%nat) by nia. rewrite EM. lia.
      + cost_simpl. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G hi hiC cont contC f fC i iC s sC H HC)] =>
    exact (HG _ i iC s sC H HC (le_n _) : _ -> (@cost T (G hi hiC cont contC f fC i iC s sC H HC) <= _)%nat) end.
Qed.
End W.
Ltac zero_partials := repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch T with forall _, _ => change (@cost T X) with 0%nat end end.

Section L.
Context {St : Type} (StC : St -> Type).
Lemma loop_time_gen (Inv : int -> St -> Prop) (Pot : St -> nat) (K : nat)
  hi hiC cont contC f fC
  (Hc : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z ->
     (cost (contC j jC) + cost (extract (contC j jC) t tC) <= K)%nat)
  (Hf : forall j jC t tC, Inv j t -> (φ j < φ hi)%Z -> cont j t = true ->
     (cost (fC j jC) + cost (extract (fC j jC) t tC) + Pot (f j t) <= Pot t + K)%nat)
  (HI : forall j t, Inv j t -> (φ j < φ hi)%Z -> cont j t = true -> Inv (j + 1) (f j t))
  i iC s sC : Inv i s ->
  (cost (extract (extract (extract (extract (extract (loop_cost stepsCM St StC) hi hiC) cont contC) f fC) i iC) s sC) <= (2 * K + 25) * Z.to_nat (gap hi i) + Pot s + 30)%nat.
Proof.
  intros Hinv. unfold loop_cost. cost_simpl.
  zero_partials.
  match goal with |- context [@cost ?T ?X] =>
    pose proof (wloop_time_gen StC Inv Pot K hi hiC cont contC f fC Hc Hf HI i iC s sC _ erased_I Hinv : (@cost T X <= _)%nat) end.
  lia.
Qed.
End L.

Ltac if_destruct := match goal with |- context [@cost _ (?F ?w)] =>
  lazymatch F with ?h ?a => fail | _ => match type of w with bool_cost _ ?b => cost_destruct b end end end.

Ltac prim_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | set_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (set_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (set_cost _ _ _) _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (extract (set_cost _ _ _) _ _) _ _) _ _ => change (@cost T X) with 1%nat
  | make_cost _ _ _ => change (@cost T X) with 0%nat
  | extract (make_cost _ _ _) _ _ => change (@cost T X) with 0%nat
  | extract (extract (make_cost _ _ _) _ _) _ _ => change (@cost T X) with 1%nat
  end end.

Lemma orb_time a aC : (cost (orb_cost stepsCM a aC) <= 2)%nat.
Proof. unfold orb_cost. destruct aC; cost_simpl; lia. Qed.
Lemma orb_time2 a aC b bC : (cost (extract (orb_cost stepsCM a aC) b bC) <= 2)%nat.
Proof. unfold orb_cost. destruct aC; cost_simpl; lia. Qed.
Lemma andb_time a aC : (cost (andb_cost stepsCM a aC) <= 2)%nat.
Proof. unfold andb_cost. destruct aC; cost_simpl; lia. Qed.
Lemma andb_time2 a aC b bC : (cost (extract (andb_cost stepsCM a aC) b bC) <= 2)%nat.
Proof. unfold andb_cost. destruct aC; cost_simpl; lia. Qed.

Ltac gen_cost T X lem := let H := fresh "Hc" in let c := fresh "cc" in pose proof (lem : (@cost T X <= _)%nat) as H; revert H; generalize (@cost T X); intros c H.

Ltac bool_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | orb_cost stepsCM ?a ?aC => gen_cost T X (orb_time a aC)
  | extract (orb_cost stepsCM ?a ?aC) ?b ?bC => gen_cost T X (orb_time2 a aC b bC)
  | andb_cost stepsCM ?a ?aC => gen_cost T X (andb_time a aC)
  | extract (andb_cost stepsCM ?a ?aC) ?b ?bC => gen_cost T X (andb_time2 a aC b bC)
  end end.

Lemma crs_time a aC b bC c cC d dC e eC f fC :
  (cost (extract (extract (extract (extract (extract (crs_cost stepsCM a aC) b bC) c cC) d dC) e eC) f fC) <= 40)%nat.
Proof. unfold crs_cost, OFF_cost. cost_simpl. lia. Qed.

Lemma dedup_step_time S SC t tC st stC :
  (cost (dedup_step_cost stepsCM S SC) + cost (extract (dedup_step_cost stepsCM S SC) t tC) + cost (extract (extract (dedup_step_cost stepsCM S SC) t tC) st stC) <= 50)%nat.
Proof. unfold dedup_step_cost. destruct stC. cost_simpl. bool_costs. prim_costs.
  if_destruct; cost_simpl; prim_costs; lia. Qed.

Definition zn (x : int) : nat := Z.to_nat (φ x).
Arguments zn : simpl never.
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments crs : simpl never.
#[local] Arguments OFF : simpl never.

Lemma zn_pred r : (1 <? r) = true -> zn (r - 1) = (zn r - 1)%nat /\ (1 < zn r)%nat.
Proof. intros H. rewrite Uint63.ltb_spec in H. change (φ 1) with 1%Z in H. unfold zn.
  assert (φ (r - 1) = φ r - 1)%Z by sia. lia. Qed.

Lemma popl_time X XC Y YC ST STC s sC r rC H HC :
  (cost (extract (extract (extract (extract (extract (popl_cost stepsCM X XC) Y YC) ST STC) s sC) r rC) H HC)
    + zn (popl X Y ST s r H) * 200 <= zn r * 200 + 200)%nat.
Proof.
  unfold popl_cost. cbn.
  match goal with |- context [@cost ?T (?G X XC Y YC ST STC s sC r rC H HC)] =>
    assert (HG : forall N r rC H HC, (zn r <= N)%nat ->
       (cost (G X XC Y YC ST STC s sC r rC H HC) + zn (popl X Y ST s r H) * 200 <= zn r * 200 + 200)%nat) end.
  { induction N as [|N IH]; intros r' rC' [g] HC' HN;
      cost_simpl;
      pose proof (bdec_time (1 <? r') (bool_w (1 <? r'))) as HB;
      cost_destruct (bdec (1 <? r')); cost_simpl.
    - exfalso. destruct (zn_pred _ e). lia.
    - lia.
    - destruct (zn_pred _ e) as [Ez Hz].
      repeat match goal with |- context [@cost ?T ?X] =>
        match X with
        | extract (extract (extract (extract (extract (crs_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
           gen_cost T X (crs_time a aC b bC c cC d dC e eC f fC) end end.
      if_destruct; cost_simpl.
      + match goal with |- context [@cost ?T (?G' X XC Y YC ST STC s sC (r' - 1)%uint63 ?w ?a ?e)] =>
          pose proof (IH (r' - 1)%uint63 w a e ltac:(lia) : (@cost T (G' X XC Y YC ST STC s sC (r' - 1)%uint63 w a e) + _ <= _)%nat) as HI end.
        rewrite Ez in HI. zero_partials. cost_align HI. lia.
      + zero_partials. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G X XC Y YC ST STC s sC r rC H HC)] =>
    exact (HG _ r rC H HC (le_n _) : (@cost T (G X XC Y YC ST STC s sC r rC H HC) + _ <= _)%nat) end.
Qed.

Definition gn (hm k : int) : nat := Z.to_nat (gap hm k).
Arguments gn : simpl never.

Lemma gn_succ hi k : (k <? hi) = true -> gn hi (k + 1) = (gn hi k - 1)%nat /\ (0 < gn hi k)%nat.
Proof. unfold gn. apply gap_succ. Qed.

Lemma climb_time HX HXC HY HYC hm hmC xi xiC yi yiC xj xjC yj yjC k kC gk gkC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (climb_cost stepsCM HX HXC) HY HYC) hm hmC) xi xiC) yi yiC) xj xjC) yj yjC) k kC) gk gkC) H HC)
    + gn hm (climb HX HY hm xi yi xj yj k gk H) * 200 <= gn hm k * 200 + 200)%nat.
Proof.
  unfold climb_cost. cbn.
  match goal with |- context [@cost ?T (?G HX HXC HY HYC hm hmC xi xiC yi yiC xj xjC yj yjC k kC gk gkC H HC)] =>
    assert (HG : forall N k kC gk gkC H HC, (gn hm k <= N)%nat ->
       (cost (G HX HXC HY HYC hm hmC xi xiC yi yiC xj xjC yj yjC k kC gk gkC H HC) + gn hm (climb HX HY hm xi yi xj yj k gk H) * 200 <= gn hm k * 200 + 200)%nat) end.
  { induction N as [|N IH]; intros k' kC' gk' gkC' [g] HC' HN;
      cost_simpl;
      pose proof (bdec_time (k' <? hm) (bool_w (k' <? hm))) as HB;
      cost_destruct (bdec (k' <? hm)); cost_simpl.
    - exfalso. destruct (gn_succ _ _ e). lia.
    - lia.
    - destruct (gn_succ _ _ e) as [Ez Hz].
      repeat match goal with |- context [@cost ?T ?X] =>
        match X with
        | extract (extract (extract (extract (extract (crs_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
           gen_cost T X (crs_time a aC b bC c cC d dC e eC f fC) end end.
      if_destruct; cost_simpl.
      + match goal with |- context [@cost ?T (?G' HX HXC HY HYC hm hmC xi xiC yi yiC xj xjC yj yjC (k' + 1)%uint63 ?w ?g1 ?g1C ?a ?e)] =>
          pose proof (IH (k' + 1)%uint63 w g1 g1C a e ltac:(lia) : (@cost T (G' HX HXC HY HYC hm hmC xi xiC yi yiC xj xjC yj yjC (k' + 1)%uint63 w g1 g1C a e) + _ <= _)%nat) as HI end.
        rewrite Ez in HI. zero_partials. cost_align HI. lia.
      + zero_partials. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G HX HXC HY HYC hm hmC xi xiC yi yiC xj xjC yj yjC k kC gk gkC H HC)] =>
    exact (HG _ k kC gk gkC H HC (le_n _) : (@cost T (G HX HXC HY HYC hm hmC xi xiC yi yiC xj xjC yj yjC k kC gk gkC H HC) + _ <= _)%nat) end.
Qed.

#[local] Arguments climb : simpl never.
#[local] Arguments jloop : simpl never.
#[local] Arguments popl : simpl never.
#[local] Arguments msort : simpl never.
#[local] Arguments Zwf_well_founded : simpl never.
#[local] Arguments wloop : simpl never.
#[local] Arguments loop : simpl never.
#[local] Arguments sort : simpl never.
#[local] Arguments pass : simpl never.
#[local] Arguments sweep : simpl never.

Lemma gn_k1 hm j k : (j <? hm) = true -> (gn hm (if (j <? k)%uint63 then k else (j + 1)%uint63) <= gn hm k)%nat.
Proof. intros H. destruct (j <? k) eqn:E; [lia|]. unfold gn, gap.
  rewrite Uint63.ltb_spec in H. assert (~ (φ j < φ k)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
  assert (φ (j + 1) = φ j + 1)%Z by (pose proof (to_Z_bounded hm); sia). lia. Qed.

Ltac if_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with ?F ?w => lazymatch F with ?h ?a => fail | _ => match type of w with bool_cost _ ?b =>
    let H := fresh "Hif" in assert (H : (@cost T X <= 10)%nat) by (cost_destruct b; cbn; lia);
    revert H; generalize (@cost T X); intros ? H end end end end.

Lemma jloop_time HX HXC HY HYC hm hmC xi xiC yi yiC j jC k kC best bestC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (jloop_cost stepsCM HX HXC) HY HYC) hm hmC) xi xiC) yi yiC) j jC) k kC) best bestC) H HC)
    <= gn hm j * 600 + gn hm k * 200 + 600)%nat.
Proof.
  unfold jloop_cost. cbn.
  match goal with |- context [@cost ?T (?G HX HXC HY HYC hm hmC xi xiC yi yiC j jC k kC best bestC H HC)] =>
    assert (HG : forall N j jC k kC best bestC H HC, (gn hm j <= N)%nat ->
       (cost (G HX HXC HY HYC hm hmC xi xiC yi yiC j jC k kC best bestC H HC) <= gn hm j * 600 + gn hm k * 200 + 600)%nat) end.
  { induction N as [|N IH]; intros j' jC' k' kC' b' bC' [g] HC' HN;
      cost_simpl;
      pose proof (bdec_time (j' <? hm) (bool_w (j' <? hm))) as HB;
      cost_destruct (bdec (j' <? hm)); cost_simpl.
    - exfalso. destruct (gn_succ _ _ e). lia.
    - lia.
    - destruct (gn_succ _ _ e) as [Ez Hz]. pose proof (gn_k1 hm j' k' e) as Hk1.
      repeat match goal with |- context [@cost ?T ?X] =>
        match X with
        | extract (extract (extract (extract (extract (crs_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
           gen_cost T X (crs_time a aC b bC c cC d dC e eC f fC) end end.
      repeat match goal with |- context [@cost ?T ?X] =>
        match X with
        | extract (extract (extract (extract (extract (extract (extract (extract (extract (climb_cost stepsCM ?a1 ?a1C) ?a2 ?a2C) ?a3 ?a3C) ?a4 ?a4C) ?a5 ?a5C) ?a6 ?a6C) ?a7 ?a7C) ?a8 ?a8C) ?a9 ?a9C) ?a10 ?a10C =>
           let H := fresh "Hc" in let c := fresh "cc" in
           pose proof (climb_time a1 a1C a2 a2C a3 a3C a4 a4C a5 a5C a6 a6C a7 a7C a8 a8C a9 a9C a10 a10C : (@cost T X + _ <= _)%nat) as H;
           revert H; generalize (@cost T X); intros c H
        end end.
      match goal with |- context [@cost ?T (?G' HX HXC HY HYC hm hmC xi xiC yi yiC (j' + 1)%uint63 ?w ?k2 ?k2C ?b2 ?b2C ?a ?e)] =>
          let H := fresh "HI" in let c := fresh "cc" in
          pose proof (IH (j' + 1)%uint63 w k2 k2C b2 b2C a e ltac:(lia) : (@cost T (G' HX HXC HY HYC hm hmC xi xiC yi yiC (j' + 1)%uint63 w k2 k2C b2 b2C a e) <= _)%nat) as H;
          revert H; generalize (@cost T (G' HX HXC HY HYC hm hmC xi xiC yi yiC (j' + 1)%uint63 w k2 k2C b2 b2C a e)); intros c H end.
      zero_partials. if_costs.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G HX HXC HY HYC hm hmC xi xiC yi yiC j jC k kC best bestC H HC)] =>
    exact (HG _ j jC k kC best bestC H HC (le_n _) : (@cost T (G HX HXC HY HYC hm hmC xi xiC yi yiC j jC k kC best bestC H HC) <= _)%nat) end.
Qed.

Lemma ms_facts lo hi : ((lo <? hi) && (1 <? hi - lo))%bool = true ->
  gn (lo + (hi - lo) / 2) lo = (gn hi lo / 2)%nat /\ gn hi (lo + (hi - lo) / 2) = (gn hi lo - gn hi lo / 2)%nat
  /\ (2 <= gn hi lo)%nat.
Proof.
  intros H. apply andb_prop in H as [H1 H2]. rewrite Uint63.ltb_spec in H1, H2.
  change (φ 1) with 1%Z in H2. pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
  assert (E : φ (hi - lo) = (φ hi - φ lo)%Z) by sia.
  assert (E2 : φ ((hi - lo) / 2) = ((φ hi - φ lo) / 2)%Z) by (rewrite Uint63.div_spec, E; reflexivity).
  assert (E3 : φ (lo + (hi - lo) / 2) = (φ lo + (φ hi - φ lo) / 2)%Z).
  { rewrite Uint63.add_spec, E2. apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
    assert ((φ hi - φ lo) / 2 <= φ hi - φ lo)%Z by (apply Z.div_le_upper_bound; lia). lia. }
  unfold gn, gap. rewrite E3.
  replace (φ lo + (φ hi - φ lo) / 2 - φ lo)%Z with ((φ hi - φ lo) / 2)%Z by lia.
  rewrite Z2Nat.inj_div by lia. change (Z.to_nat 2) with 2%nat.
  rewrite E in H2. assert (0 <= (φ hi - φ lo) / 2)%Z by (apply Z.div_pos; lia).
  assert ((φ hi - φ lo) / 2 <= φ hi - φ lo)%Z by (apply Z.div_le_upper_bound; lia).
  split; [reflexivity|]. split; [|lia].
  rewrite <- (Z2Nat.inj_div _ 2) by lia. rewrite <- Z2Nat.inj_sub by lia. f_equal. lia.
Qed.

Lemma half_facts L : (2 * (L / 2) <= L <= 2 * (L / 2) + 1)%nat.
Proof. pose proof (Nat.div_mod L 2 ltac:(lia)). pose proof (Nat.mod_upper_bound L 2 ltac:(lia)). lia. Qed.

Lemma lu_half L : (2 <= L)%nat -> (Nat.log2_up (L - L / 2) <= Nat.log2_up L - 1)%nat.
Proof.
  intros HL. pose proof (Nat.log2_up_spec L ltac:(lia)) as [_ S2].
  assert (1 <= Nat.log2_up L)%nat by (apply Nat.log2_up_pos; lia).
  apply Nat.log2_up_le_pow2; [pose proof (half_facts L); lia|].
  replace (Nat.log2_up L) with (S (Nat.log2_up L - 1)) in S2 by lia. rewrite Nat.pow_succ_r' in S2.
  pose proof (half_facts L). lia.
Qed.

Lemma ms_arith (L l1 l2 lu1 lu2 lu c1 c2 c3 c4 : nat) :
  (2 <= L)%nat -> l1 = (L / 2)%nat -> l2 = (L - L / 2)%nat -> (lu1 <= lu - 1)%nat -> (lu2 <= lu - 1)%nat -> (1 <= lu)%nat ->
  (c1 + 1000 <= 400 * l1 * lu1 + 2000 * Nat.max l1 1)%nat ->
  (c2 + 1000 <= 400 * l2 * lu2 + 2000 * Nat.max l2 1)%nat ->
  (c3 <= L * 230 + 100)%nat -> (c4 <= 85 * L + 30)%nat ->
  (c1 + c2 + c3 + c4 + 300 + 1000 <= 400 * L * lu + 2000 * Nat.max L 1)%nat.
Proof.
  intros HL E1 E2 H1 H2 H3 C1 C2 C3 C4.
  pose proof (half_facts L).
  assert (1 <= l1)%nat by (subst; lia).
  assert (l1 <= l2)%nat by (subst; lia).
  assert (Hs : (l1 + l2 = L)%nat) by (subst; lia).
  rewrite Nat.max_l in C1 by lia. rewrite Nat.max_l in C2 by lia. rewrite Nat.max_l by lia.
  assert (400 * l1 * lu1 <= 400 * l1 * (lu - 1))%nat by (apply Nat.mul_le_mono_l; lia).
  assert (400 * l2 * lu2 <= 400 * l2 * (lu - 1))%nat by (apply Nat.mul_le_mono_l; lia).
  assert (400 * l1 * (lu - 1) + 400 * l2 * (lu - 1) + 400 * L = 400 * L * lu)%nat.
  { replace (400 * L * lu)%nat with (400 * L * (S (lu - 1)))%nat by (f_equal; lia). rewrite <- Hs. nia. }
  lia.
Qed.

Lemma lu_le_log2 N : (Nat.log2_up N <= Nat.log2 N + 1)%nat.
Proof. pose proof (Nat.le_log2_up_succ_log2 N). lia. Qed.

Lemma gn_le h j : (1 <= φ h)%Z -> (gn (h - 1) j <= zn h)%nat.
Proof. intros H. unfold gn, zn, gap. pose proof (to_Z_bounded j).
  assert (φ (h - 1) = φ h - 1)%Z by sia. lia. Qed.

Lemma sweep_step_time HX HXC HY HYC h hC i iC best bestC : (1 <= φ h)%Z ->
  (cost (sweep_step_cost stepsCM HX HXC) + cost (extract (sweep_step_cost stepsCM HX HXC) HY HYC)
   + cost (extract (extract (sweep_step_cost stepsCM HX HXC) HY HYC) h hC)
   + cost (extract (extract (extract (sweep_step_cost stepsCM HX HXC) HY HYC) h hC) i iC)
   + cost (extract (extract (extract (extract (sweep_step_cost stepsCM HX HXC) HY HYC) h hC) i iC) best bestC)
   <= zn h * 800 + 700)%nat.
Proof.
  intros Hh. unfold sweep_step_cost. cost_simpl. zero_partials.
  match goal with |- context [@cost ?T ?X] =>
    match X with
    | extract (extract (extract (extract (extract (extract (extract (extract (jloop_cost stepsCM ?a1 ?a1C) ?a2 ?a2C) ?a3 ?a3C) ?a4 ?a4C) ?a5 ?a5C) ?a6 ?a6C) ?a7 ?a7C) ?a8 ?a8C) ?a9 ?a9C =>
      gen_cost T X (jloop_time a1 a1C a2 a2C a3 a3C a4 a4C a5 a5C a6 a6C a7 a7C a8 a8C a9 a9C)
    end end.
  pose proof (gn_le h (i + 1) Hh). pose proof (gn_le h (i + 2) Hh).
  lia.
Qed.

Lemma sweep_time HX HXC HY HYC h hC : (3 <= φ h)%Z ->
  (cost (extract (extract (sweep_cost stepsCM HX HXC) HY HYC) h hC) <= (zn h * 1600 + 2000) * zn h + 50)%nat.
Proof.
  intros Hh. unfold sweep_cost. cost_simpl. zero_partials.
  match goal with |- context [@cost ?T ?X] =>
    match X with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) (zn h * 800 + 700) hi hiC cont contC f fC
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; pose proof (sweep_step_time HX HXC HY HYC h hC j jC t tC ltac:(lia)) as HH; cost_align HH; lia)
         ltac:(intros; exact I) i iC s sC I : (@cost T X <= _)%nat) as H;
      revert H; generalize (@cost T X); intros c H
    end end.
  assert (gn (h - 2) 0 <= zn h)%nat by (unfold gn, zn, gap; change (φ 0) with 0%Z; pose proof (to_Z_bounded h); assert (φ (h - 2) = φ h - 2)%Z by sia; lia).
  match goal with H : (?c <= ?A * Z.to_nat (gap (h - 2) 0) + _ + _)%nat |- _ =>
    assert (A * Z.to_nat (gap (h - 2) 0) <= A * zn h)%nat by (apply Nat.mul_le_mono_l; unfold gn in *; lia) end.
  nia.
Qed.

Lemma popl_le X Y ST s r H : (1 <= φ r)%Z -> (1 <= φ (popl X Y ST s r H) <= φ r)%Z.
Proof.
  revert r H. intros r H. remember (Z.to_nat (φ r)) as N eqn:EN. revert r H EN.
  induction N as [N IH] using lt_wf_ind. intros r H EN Hr.
  rewrite popl_eq. destruct (bdec (1 <? r)) as [Hr1 | Hr1]; [|lia].
  pose proof Hr1 as Hr1'. rewrite Uint63.ltb_spec in Hr1'. change (φ 1) with 1%Z in Hr1'.
  assert (E1 : φ (r - 1) = (φ r - 1)%Z) by sia.
  cbv zeta. destruct (_ <=? OFF); [|lia].
  pose proof (IH (Z.to_nat (φ (r - 1))) ltac:(lia) (r - 1) (Acc_inv H (dec_r r Hr1)) eq_refl ltac:(lia)). lia.
Qed.

Lemma pass_step_time X XC Y YC s sC st stC : (1 <= φ (snd st) <= φ s)%Z -> (φ s < 4194303)%Z ->
  (cost (pass_step_cost stepsCM X XC) + cost (extract (pass_step_cost stepsCM X XC) Y YC)
   + cost (extract (extract (pass_step_cost stepsCM X XC) Y YC) s sC)
   + cost (extract (extract (extract (pass_step_cost stepsCM X XC) Y YC) s sC) st stC)
   + zn (snd (pass_step X Y s st)) * 200
   <= zn (snd st) * 200 + 500)%nat.
Proof.
  intros Hr Hs. destruct stC as [ST STC r rC]. cbn [snd] in Hr |- *.
  unfold pass_step_cost. cost_simpl. zero_partials. prim_costs.
  match goal with |- context [@cost ?T ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (popl_cost stepsCM ?a1 ?a1C) ?a2 ?a2C) ?a3 ?a3C) ?a4 ?a4C) ?a5 ?a5C) ?a6 ?a6C =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (popl_time a1 a1C a2 a2C a3 a3C a4 a4C a5 a5C a6 a6C : (@cost T XX + _ <= _)%nat) as H;
      revert H; generalize (@cost T XX); intros c H
    end end.
  pose proof (popl_le X Y ST s r (Zwf_well_founded 0 (φ r)) ltac:(lia)) as Hp.
  assert (zn (popl X Y ST s r (Zwf_well_founded 0 (φ r)) + 1)%uint63 = (zn (popl X Y ST s r (Zwf_well_founded 0 (φ r))) + 1)%nat).
  { unfold zn. assert (φ (popl X Y ST s r (Zwf_well_founded 0 (φ r)) + 1) = φ (popl X Y ST s r (Zwf_well_founded 0 (φ r))) + 1)%Z by sia. lia. }
  lia.
Qed.

Lemma pass_snd X Y m : (1 <= φ m <= 4194303)%Z -> (1 <= φ (snd (pass X Y m)) <= φ m)%Z.
Proof.
  intros Hm. unfold pass.
  apply (for_inv (fun j st => 1 <= φ (snd st) <= φ j)%Z); cbn [snd].
  - change (φ 1) with 1%Z. lia.
  - change (φ 1) with 1%Z. lia.
  - intros j [ST r] Hj Hr. unfold pass_step. cbn [snd] in Hr |- *.
    pose proof (popl_le X Y ST j r (Zwf_well_founded 0 (φ r)) ltac:(lia)) as Hp.
    assert (φ (j + 1) = φ j + 1)%Z by sia.
    assert (φ (popl X Y ST j r (Zwf_well_founded 0 (φ r)) + 1) = φ (popl X Y ST j r (Zwf_well_founded 0 (φ r))) + 1)%Z by sia. lia.
Qed.

Lemma pass_time X XC Y YC m mC : (1 <= φ m <= 4194303)%Z ->
  (cost (extract (extract (pass_cost stepsCM X XC) Y YC) m mC) <= zn m * 1100 + 300)%nat.
Proof.
  intros Hm. unfold pass_cost. cost_simpl. zero_partials. prim_costs.
  match goal with |- context [@cost ?T ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun j st => 1 <= φ (snd st) <= φ j)%Z (fun st => zn (snd st) * 200)%nat 500 hi hiC cont contC f fC
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC Ht Hj _; cbv beta in Ht |- *; pose proof (pass_step_time X XC Y YC j jC t tC Ht ltac:(lia)) as HH; cost_align HH; lia)
         ltac:(intros j [ST r] Ht Hj _; cbv beta in Ht |- *; unfold pass_step; cbn [snd] in Ht |- *;
               pose proof (popl_le X Y ST j r (Zwf_well_founded 0 (φ r)) ltac:(lia)) as Hp;
               assert (φ (j + 1) = φ j + 1)%Z by sia;
               assert (φ (popl X Y ST j r (Zwf_well_founded 0 (φ r)) + 1) = φ (popl X Y ST j r (Zwf_well_founded 0 (φ r))) + 1)%Z by sia; lia)
         i iC s sC ltac:(cbn [snd]; change (φ 1) with 1%Z; lia) : (@cost T XX <= _)%nat) as H;
      revert H; generalize (@cost T XX); intros c H
    end end.
  assert (Z.to_nat (gap m 1) <= zn m)%nat by (unfold zn, gap; lia).
  cbn [snd] in *. assert (zn 1 = 1%nat) by reflexivity.
  lia.
Qed.

Ltac if_costs30 := repeat match goal with |- context [@cost ?T ?X] =>
  match X with ?F ?w => lazymatch F with ?h ?a => fail | _ => match type of w with bool_cost _ ?b =>
    let H := fresh "Hif" in assert (H : (@cost T X <= 30)%nat) by (cost_destruct b; cbn; lia);
    revert H; generalize (@cost T X); intros ? H end end end end.

Lemma merge_step_time A AC mid midC hi hiC k kC st stC :
  (cost (merge_step_cost stepsCM A AC) + cost (extract (merge_step_cost stepsCM A AC) mid midC)
   + cost (extract (extract (merge_step_cost stepsCM A AC) mid midC) hi hiC)
   + cost (extract (extract (extract (merge_step_cost stepsCM A AC) mid midC) hi hiC) k kC)
   + cost (extract (extract (extract (extract (merge_step_cost stepsCM A AC) mid midC) hi hiC) k kC) st stC)
   <= 100)%nat.
Proof.
  destruct stC as [p pC j jC]. destruct pC as [T TC i iC].
  unfold merge_step_cost. cost_simpl. zero_partials. prim_costs. bool_costs.
  if_costs30. lia.
Qed.

Lemma copy_step_time T TC k kC A AC :
  (cost (copy_step_cost stepsCM T TC) + cost (extract (copy_step_cost stepsCM T TC) k kC)
   + cost (extract (extract (copy_step_cost stepsCM T TC) k kC) A AC) <= 30)%nat.
Proof. unfold copy_step_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

Lemma merge_time A AC T TC lo loC mid midC hi hiC :
  (cost (extract (extract (extract (extract (merge_cost stepsCM A AC) T TC) lo loC) mid midC) hi hiC) <= gn hi lo * 230 + 100)%nat.
Proof.
  unfold merge_cost. cost_simpl. zero_partials.
  match goal with |- context [@cost ?T ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 100 hi hiC cont contC f fC
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; cbv beta; pose proof (merge_step_time A AC mid midC hi hiC j jC t tC) as HH; cost_align HH; lia)
         ltac:(intros; exact I) i iC s sC I : (@cost T XX <= _)%nat) as H;
      revert H; generalize (@cost T XX); intros c H
    end end.
  cost_destruct_witness (loop hi (fun (_ : int) (_ : array int * int * int) => true) (merge_step A mid hi) lo (T, lo, mid)) as [p pC i iC] eqn:E.
  destruct pC as [T' TC' i' iC']. cost_simpl.
  assert (Z.to_nat (gap hi lo) = gn hi lo) by reflexivity. lia.
Qed.

Lemma bdec_time' b w : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. exact (bdec_time b w). Qed.
Ltac bdec_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with bdec_cost stepsCM ?b ?w => gen_cost T X (bdec_time' b w) end end.

Definition msb (L : nat) : nat := 400 * L * Nat.log2_up L + 2000 * Nat.max L 1.
Arguments msb : simpl never.

Lemma msort_time A AC T TC lo loC hi hiC H HC :
  (cost (extract (extract (extract (extract (msort_cost stepsCM A AC) T TC) lo loC) hi hiC) H HC) + 1000 <= msb (gn hi lo))%nat.
Proof.
  unfold msort_cost. cbn.
  match goal with |- context [@cost ?TT (?G A AC T TC lo loC hi hiC H HC)] =>
    assert (HG : forall N A AC T TC lo loC hi hiC H HC, (gn hi lo <= N)%nat ->
       (cost (G A AC T TC lo loC hi hiC H HC) + 1000 <= msb (gn hi lo))%nat) end.
  { induction N as [|N IH]; intros A' AC' T' TC' lo' loC' hi' hiC' [g] HC' HN;
      cost_simpl;
      bool_costs; bdec_costs.
    all: cost_destruct (bdec ((lo' <? hi') && (1 <? hi' - lo'))%bool); cost_simpl.
    all: zero_partials.
    1: exfalso; destruct (ms_facts _ _ e) as (_ & _ & ?); lia.
    1,3: unfold msb; lia.
    destruct (ms_facts _ _ e) as (Em1 & Em2 & HL).
    match goal with |- context [@cost ?TT (?G' A' AC' T' TC' lo' loC' ?md ?w ?a ?e)] =>
      let H := fresh "HI" in let c := fresh "cc" in
      pose proof (IH A' AC' T' TC' lo' loC' md w a e ltac:(rewrite Em1; pose proof (half_facts (gn hi' lo')); lia) : (@cost TT (G' A' AC' T' TC' lo' loC' md w a e) + _ <= _)%nat) as H;
      revert H; generalize (@cost TT (G' A' AC' T' TC' lo' loC' md w a e)); intros c H end.
    cost_destruct_witness (msort A' T' lo' (lo' + (hi' - lo') / 2) (g (gap (lo' + (hi' - lo') / 2) lo') (ms_dec1 lo' hi' e))) as [A1 A1C T1 T1C] eqn:E1.
    cost_simpl. zero_partials.
    match goal with |- context [@cost ?TT (?G' A1 A1C T1 T1C ?md ?mdC hi' hiC' ?a ?e)] =>
      let H := fresh "HI" in let c := fresh "cc" in
      pose proof (IH A1 A1C T1 T1C md mdC hi' hiC' a e ltac:(rewrite Em2; pose proof (half_facts (gn hi' lo')); lia) : (@cost TT (G' A1 A1C T1 T1C md mdC hi' hiC' a e) + _ <= _)%nat) as H;
      revert H; generalize (@cost TT (G' A1 A1C T1 T1C md mdC hi' hiC' a e)); intros c H end.
    cost_destruct_witness (msort A1 T1 (lo' + (hi' - lo') / 2) hi' (g (gap hi' (lo' + (hi' - lo') / 2)) (ms_dec2 lo' hi' e))) as [A2 A2C T2 T2C] eqn:E2.
    cost_simpl. zero_partials.
    repeat match goal with |- context [@cost ?TT ?XX] =>
      match XX with
      | extract (extract (extract (extract (merge_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
        gen_cost TT XX (merge_time a aC b bC c cC d dC e eC)
      end end.
    match goal with |- context [@cost ?TT ?XX] =>
      match XX with
      | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
        let H := fresh "Hc" in let c := fresh "cc" in
        pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 30 hi hiC cont contC f fC
           ltac:(intros; cbn; lia)
           ltac:(intros j jC t tC _ _ _; cbv beta; match goal with |- context [copy_step_cost stepsCM ?T3 ?T3C] => pose proof (copy_step_time T3 T3C j jC t tC) as HH end; cost_align HH; lia)
           ltac:(intros; exact I) i iC s sC I : (@cost TT XX <= _)%nat) as H;
        revert H; generalize (@cost TT XX); intros c H
      end end.
    clear IH. unfold msb in *. rewrite Em1 in HI. rewrite Em2 in HI0.
    assert (Z.to_nat (gap hi' lo') = gn hi' lo') as EG by reflexivity. rewrite EG in Hc3.
    pose proof (lu_half _ HL) as LU2.
    assert (LU1 : (Nat.log2_up (gn hi' lo' / 2) <= Nat.log2_up (gn hi' lo' - gn hi' lo' / 2))%nat)
      by (apply Nat.log2_up_le_mono; pose proof (half_facts (gn hi' lo')); lia).
    assert (LU : (1 <= Nat.log2_up (gn hi' lo'))%nat) by (apply Nat.log2_up_pos; lia).
    pose proof (ms_arith (gn hi' lo') (gn hi' lo' / 2) (gn hi' lo' - gn hi' lo' / 2) (Nat.log2_up (gn hi' lo' / 2)) (Nat.log2_up (gn hi' lo' - gn hi' lo' / 2)) (Nat.log2_up (gn hi' lo')) cc2 cc3 cc4 cc5 HL eq_refl eq_refl ltac:(lia) LU2 LU HI HI0 Hc2 ltac:(lia)).
    lia. }
  match goal with |- context [@cost ?TT (?G A AC T TC lo loC hi hiC H HC)] =>
    exact (HG _ A AC T TC lo loC hi hiC H HC (le_n _) : (@cost TT (G A AC T TC lo loC hi hiC H HC) + _ <= _)%nat) end.
Qed.

Lemma fst_time A AC B BC p pC : (cost (extract (extract (fst_cost stepsCM A AC) B BC) p pC) <= 3)%nat.
Proof. destruct pC. unfold fst_cost. cost_simpl. lia. Qed.

Lemma sort_time K KC n nC :
  (cost (extract (sort_cost stepsCM K KC) n nC) <= msb (zn n) + 20)%nat.
Proof.
  unfold sort_cost. cost_simpl. zero_partials. prim_costs.
  match goal with |- context [@cost ?TT (extract (extract (extract (extract (msort_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC)] =>
      let H := fresh "Hm" in let cm := fresh "cm" in
      pose proof (msort_time a aC b bC c cC d dC e eC : (@cost TT (extract (extract (extract (extract (msort_cost stepsCM a aC) b bC) c cC) d dC) e eC) + _ <= _)%nat) as H;
      revert H; generalize (@cost TT (extract (extract (extract (extract (msort_cost stepsCM a aC) b bC) c cC) d dC) e eC)); intros cm H end.
  match goal with |- context [@cost ?TT ?XX] =>
    match XX with
    | extract (extract (fst_cost stepsCM ?A ?AC) ?B ?BC) ?p ?pC => gen_cost TT XX (fst_time A AC B BC p pC)
    end end.
  assert (gn n 0 = zn n) as E by (unfold gn, zn, gap; change (φ 0) with 0%Z; f_equal; lia). assert (msb (gn n 0) = msb (zn n)) by (f_equal; exact E). lia.
Qed.

Lemma decode_step_time D DC u uC st stC :
  (cost (decode_step_cost stepsCM D DC) + cost (extract (decode_step_cost stepsCM D DC) u uC)
   + cost (extract (extract (decode_step_cost stepsCM D DC) u uC) st stC) <= 60)%nat.
Proof. destruct stC. unfold decode_step_cost, SH_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

Lemma rev_step_time X XC m mC s sC R RC :
  (cost (rev_step_cost stepsCM X XC) + cost (extract (rev_step_cost stepsCM X XC) m mC)
   + cost (extract (extract (rev_step_cost stepsCM X XC) m mC) s sC)
   + cost (extract (extract (extract (rev_step_cost stepsCM X XC) m mC) s sC) R RC) <= 40)%nat.
Proof. unfold rev_step_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

Lemma low_step_time PX PXC PY PYC LS LSC t tC st stC :
  (cost (low_step_cost stepsCM PX PXC) + cost (extract (low_step_cost stepsCM PX PXC) PY PYC)
   + cost (extract (extract (low_step_cost stepsCM PX PXC) PY PYC) LS LSC)
   + cost (extract (extract (extract (low_step_cost stepsCM PX PXC) PY PYC) LS LSC) t tC)
   + cost (extract (extract (extract (extract (low_step_cost stepsCM PX PXC) PY PYC) LS LSC) t tC) st stC) <= 60)%nat.
Proof. destruct stC. unfold low_step_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

Lemma up_step_time RX RXC RY RYC US USC a aC t tC st stC :
  (cost (up_step_cost stepsCM RX RXC) + cost (extract (up_step_cost stepsCM RX RXC) RY RYC)
   + cost (extract (extract (up_step_cost stepsCM RX RXC) RY RYC) US USC)
   + cost (extract (extract (extract (up_step_cost stepsCM RX RXC) RY RYC) US USC) a aC)
   + cost (extract (extract (extract (extract (up_step_cost stepsCM RX RXC) RY RYC) US USC) a aC) t tC)
   + cost (extract (extract (extract (extract (extract (up_step_cost stepsCM RX RXC) RY RYC) US USC) a aC) t tC) st stC) <= 70)%nat.
Proof. destruct stC. unfold up_step_cost. cost_simpl. zero_partials. prim_costs. lia. Qed.

Ltac gen_witnesses v := repeat match goal with |- context [@extract ?CM ?T ?m] =>
  lazymatch T with
  | forall _, _ => fail
  | context [v] => generalize (@extract CM T m)
  end end.
Ltac fix_cost_types := repeat match goal with
    | |- context [@cost ?T ?m] =>
        lazymatch type of m with
        | @CostM _ ?A =>
            assert_fails (constr_eq A T);
            change (@cost T m) with (@cost A m)
        end
    end.
Ltac gen_value v nm := fix_cost_types; gen_witnesses v; generalize v; intros nm; intros.
Ltac split_pair v a aC b bC := let p := fresh "p" in gen_value v p;
  match goal with w : prod_cost _ _ _ _ _ p |- _ => destruct w as [a aC b bC] end.

Lemma dedup_m S n : (φ n <= 4194303)%Z ->
  (φ (snd (loop n (fun (_ : int) (_ : array int * int) => true) (dedup_step S) 0 (PArray.make n 0, 0)%uint63)) <= φ n)%Z.
Proof.
  intros Hn. apply (for_inv (fun j st => φ (snd st) <= φ j)%Z); cbn [snd].
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - change (φ 0) with 0%Z. lia.
  - intros j [D m] Hj Hm. unfold dedup_step. cbn [snd] in Hm |- *.
    assert (φ (j + 1) = φ j + 1)%Z by (pose proof (to_Z_bounded n); sia).
    destruct (_ || _)%bool; cbn [snd]; [|lia].
    assert (φ (m + 1) = φ m + 1)%Z by sia. lia.
Qed.

Ltac step_bound j jC t tC :=
  let HH := fresh "HH" in
  match goal with
  | |- context [decode_step_cost stepsCM ?D0 ?DC0] => pose proof (decode_step_time D0 DC0 j jC t tC) as HH
  | |- context [rev_step_cost stepsCM ?X0 ?XC0] => match goal with |- context [extract (rev_step_cost stepsCM X0 XC0) ?m0 ?mC0] => pose proof (rev_step_time X0 XC0 m0 mC0 j jC t tC) as HH end
  | |- context [low_step_cost stepsCM ?a1 ?a1C] => match goal with |- context [extract (extract (low_step_cost stepsCM a1 a1C) ?a2 ?a2C) ?a3 ?a3C] => pose proof (low_step_time a1 a1C a2 a2C a3 a3C j jC t tC) as HH end
  | |- context [up_step_cost stepsCM ?a1 ?a1C] => match goal with |- context [extract (extract (extract (up_step_cost stepsCM a1 a1C) ?a2 ?a2C) ?a3 ?a3C) ?a4 ?a4C] => pose proof (up_step_time a1 a1C a2 a2C a3 a3C a4 a4C j jC t tC) as HH end
  end; cost_align HH; lia.

Ltac loop_bound fpat K :=
  match goal with |- context [@cost ?TT ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
      lazymatch fC with context [fpat] => idtac end;
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) K hi hiC cont contC f fC
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; cbv beta; step_bound j jC t tC)
         ltac:(intros; exact I) i iC s sC I : (@cost TT XX <= _)%nat) as H;
      revert H; generalize (@cost TT XX); intros c H
    end end.

Definition Fb (N : nat) : nat := (N + 1) * (N + Nat.log2 N + 1) * 100 * 200 + 100 * 200.
Arguments Fb : simpl never.

Lemma gap0 (X : int) : Z.to_nat (gap X 0) = zn X.
Proof. unfold gap, zn. change (φ 0) with 0%Z. f_equal. lia. Qed.

Lemma zn_len (t : array repr.uint) : zn (PArray.length t) = size t.
Proof. reflexivity. Qed.

Lemma msb_le N : (msb N <= 400 * (N * Nat.log2 N) + 2400 * N + 2000)%nat.
Proof. unfold msb. pose proof (lu_le_log2 N).
  assert (400 * N * Nat.log2_up N <= 400 * N * (Nat.log2 N + 1))%nat by (apply Nat.mul_le_mono_l; lia).
  assert (Nat.max N 1 <= N + 1)%nat by lia. nia. Qed.

Lemma Fb_ge N : ((N * N) * 100 * 200 + (N * Nat.log2 N) * 100 * 200 + N * 100 * 400 + 100 * 200 <= Fb N)%nat.
Proof. unfold Fb. nia. Qed.

Lemma sq_le (H N : nat) : (H <= 2 * N)%nat -> ((H * 1600 + 2000) * H <= (N * N) * 64 * 100 + 4000 * N)%nat.
Proof. intros. nia. Qed.

Lemma gap_le (h a : int) : (Z.to_nat (gap h a) <= zn h)%nat.
Proof. unfold gap, zn. pose proof (to_Z_bounded a). lia. Qed.

Ltac finish x :=
  repeat rewrite gap0 in *;
  match goal with H : (_ <= msb (zn ?L) + _)%nat |- _ => pose proof (msb_le (zn L)); change (size x) with (zn L) end;
  match goal with |- (_ <= Fb ?N)%nat => pose proof (Fb_ge N) end;
  lia.

Lemma main_time x y : (cost2 largest_triangle_cost x y <= Fb (size x))%nat.
Proof.
  unfold cost2, largest_triangle_cost. cost_simpl.
  unfold largest_triangle_impl_cost. fix_cost_types. cost_simpl. zero_partials. prim_costs.
  rewrite cost_bind. cost_simpl. zero_partials. prim_costs.
  (* the key loop *)
  match goal with |- context [@cost ?TT ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f ?fC) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 40 hi hiC cont contC f fC
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; cbv beta; cost_simpl; prim_costs; lia)
         ltac:(intros; exact I) i iC s sC I : (@cost TT XX <= _)%nat) as H;
      revert H; generalize (@cost TT XX); intros c H
    end end.
  match goal with |- context [@cost ?TT ?XX] =>
    match XX with
    | extract (sort_cost stepsCM ?K ?KC) ?n ?nC => 
      let H := fresh "Hs" in let cs := fresh "cs" in
      pose proof (sort_time K KC n nC : (@cost TT XX <= _)%nat) as H;
      revert H; generalize (@cost TT XX); intros cs H
    end end.
  match goal with |- context [sort ?K ?n] => gen_value (sort K n) Srt end.
  match goal with |- context [@cost ?TT ?XX] =>
    match XX with
    | extract (extract (extract (extract (extract (loop_cost stepsCM ?St ?StC) ?hi ?hiC) ?cont ?contC) ?f (extract (dedup_step_cost stepsCM ?S0 ?SC))) ?i ?iC) ?s ?sC =>
      let H := fresh "Hc" in let c := fresh "cc" in
      pose proof (loop_time_gen StC (fun _ _ => True) (fun _ => 0%nat) 50 hi hiC cont contC f (extract (dedup_step_cost stepsCM S0 SC))
         ltac:(intros; cbn; lia)
         ltac:(intros j jC t tC _ _ _; cbv beta; pose proof (dedup_step_time S0 SC j jC t tC) as HH; cost_align HH; lia)
         ltac:(intros; exact I) i iC s sC I : (@cost TT XX <= _)%nat) as H;
      revert H; generalize (@cost TT XX); intros c H
    end end.
  pose proof (ilength_bound x) as Hn.
  match goal with |- context [loop ?n ?c (dedup_step ?S0) ?z ?s0] =>
    pose proof (dedup_m S0 n Hn) as Hm; revert Hm; split_pair (loop n c (dedup_step S0) z s0) D DC m mC end.
  cbn [snd] in Hm.
  match type of Hm with (_ <= φ ?L)%Z => assert (Hn' : (φ L <= 4194303)%Z) by (exact (ilength_bound x)) end.
  cost_simpl.
  cost_destruct_eqn (m <? 3) Em3; cost_simpl.
  1: { unfold fzero_cost. cost_simpl. finish x. }
  zero_partials. prim_costs.
  assert (Hm3 : (3 <= φ m)%Z) by (rewrite <- Uint63.ltb_spec in Em3 || idtac; destruct (Uint63.ltb_spec m 3); change (φ 3) with 3%Z in *; lia).
  (* decode *)
  loop_bound decode_step_cost constr:(60%nat).
  match goal with |- context [loop ?n ?c (decode_step ?D0) ?z ?s0] => split_pair (loop n c (decode_step D0) z s0) PX PXC PY PYC end.
  cost_simpl. zero_partials. prim_costs.
  (* lower chain *)
  match goal with |- context [@cost ?TT (extract (extract (pass_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC)] =>
    gen_cost TT (extract (extract (pass_cost stepsCM a aC) b bC) c cC) (pass_time a aC b bC c cC ltac:(lia)) end.
  pose proof (pass_snd PX PY m ltac:(lia)) as Ha. revert Ha.
  split_pair (pass PX PY m) LS LSC ah ahC. cbn [snd] in Ha.
  cost_simpl. zero_partials. prim_costs.
  (* upper chain *)
  loop_bound rev_step_cost constr:(40%nat).
  loop_bound rev_step_cost constr:(40%nat).
  match goal with |- context [loop ?n ?c (rev_step PX ?m0) ?z ?s0] => gen_value (loop n c (rev_step PX m0) z s0) RX end.
  match goal with |- context [loop ?n ?c (rev_step PY ?m0) ?z ?s0] => gen_value (loop n c (rev_step PY m0) z s0) RY end.
  match goal with |- context [@cost ?TT (extract (extract (pass_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC)] =>
    gen_cost TT (extract (extract (pass_cost stepsCM a aC) b bC) c cC) (pass_time a aC b bC c cC ltac:(lia)) end.
  pose proof (pass_snd RX RY m ltac:(lia)) as Hb. revert Hb.
  split_pair (pass RX RY m) US USC bh bhC. cbn [snd] in Hb.
  cost_simpl. zero_partials. prim_costs.
  cost_destruct_eqn (ah + bh - 2 <? 3) Eh; cost_simpl.
  1: { unfold fzero_cost. cost_simpl.
        match type of Hm with (_ <= φ ?L)%Z => assert (zn m <= zn L)%nat by (unfold zn; lia) end. finish x. }
  zero_partials. prim_costs.
  assert (Hh : (φ (ah + bh - 2) = φ ah + φ bh - 2 /\ 3 <= φ (ah + bh - 2))%Z).
  { destruct (Uint63.ltb_spec (ah + bh - 2) 3) as [_ L]. change (φ 3) with 3%Z in L.
    assert (~ (φ (ah + bh - 2) < 3)%Z) by (intros Hx; specialize (L Hx); congruence).
    assert (φ (ah + bh - 2) = φ ah + φ bh - 2)%Z by sia. lia. }
  (* the hull *)
  loop_bound low_step_cost constr:(60%nat).
  match goal with |- context [loop ?n ?c (low_step ?a1 ?a2 ?a3) ?z ?s0] => split_pair (loop n c (low_step a1 a2 a3) z s0) HX1 HX1C HY1 HY1C end.
  cost_simpl. zero_partials. prim_costs.
  loop_bound up_step_cost constr:(70%nat).
  match goal with |- context [loop ?n ?c (up_step ?a1 ?a2 ?a3 ?a4) ?z ?s0] => split_pair (loop n c (up_step a1 a2 a3 a4) z s0) HX HXC HY HYC end.
  cost_simpl. zero_partials. prim_costs.
  match goal with |- context [@cost ?TT (extract (extract (sweep_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC)] =>
    gen_cost TT (extract (extract (sweep_cost stepsCM a aC) b bC) c cC) (sweep_time a aC b bC c cC ltac:(lia)) end.
  pose proof (gap_le (ah + bh - 2) ah) as G7.
  match type of Hm with (_ <= φ ?L)%Z => assert (zn m <= zn L)%nat by (unfold zn; lia) end.
  assert (zn ah <= zn m)%nat by (unfold zn; lia).
  assert (zn (ah + bh - 2) <= 2 * zn m)%nat by (unfold zn; lia).
  match type of Hm with (_ <= φ ?L)%Z => pose proof (sq_le (zn (ah + bh - 2)) (zn L) ltac:(lia)) end.
  finish x.
Qed.

Theorem largest_triangle_time : exists c1 c2 : nat,
  forall (x_coordinates y_coordinates : list N)
  (x_coordinates_arr y_coordinates_arr : array uint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  (cost2 largest_triangle_cost x_coordinates_arr y_coordinates_arr <= c1 * ((size x_coordinates_arr + 1) * (size x_coordinates_arr + Nat.log2 (size x_coordinates_arr) + 1)) + c2)%nat.
Proof.
  exists 20000%nat, 20000%nat. intros xs ys x y _ _ _.
  pose proof (main_time x y) as H. unfold Fb in H.
  change 20000%nat with (100 * 200)%nat. lia.
Qed.
